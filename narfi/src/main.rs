mod arith;
mod check;
mod parser;
mod prose;
mod syntax;
mod web;

use check::{Env, Report, check_decls};
use std::process::ExitCode;

const PRELUDE: &str = include_str!("prelude.narfi");

fn usage() -> ExitCode {
    eprintln!("使い方:");
    eprintln!("  narfi check [--trace] <ファイル.narfi>...   定理の検証");
    eprintln!("  narfi web [--port 3000] [--no-open]         Mathcha風 Web エディタを起動");
    eprintln!("  narfi prose <ファイル.narfi>                自然な日本語の証明文(Markdown)を出力");
    eprintln!("  narfi latex <ファイル.narfi>                提出用 LaTeX ソースを出力");
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return usage();
    }

    match args[0].as_str() {
        "web" => {
            let mut port: u16 = 3000;
            let mut open_browser = true;
            let mut i = 1;
            while i < args.len() {
                match args[i].as_str() {
                    "--port" | "-p" => {
                        if let Some(p) = args.get(i + 1).and_then(|s| s.parse().ok()) {
                            port = p;
                        }
                        i += 2;
                    }
                    "--no-open" => {
                        open_browser = false;
                        i += 1;
                    }
                    _ => i += 1,
                }
            }
            if let Err(e) = web::serve(port, open_browser) {
                eprintln!("Webサーバーの起動に失敗しました: {e}");
                return ExitCode::FAILURE;
            }
            return ExitCode::SUCCESS;
        }
        "prose" | "latex" => {
            let mode = args[0].as_str();
            let Some(path) = args.get(1) else {
                return usage();
            };
            let src = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{path}: 読めない: {e}");
                    return ExitCode::from(2);
                }
            };
            let decls = match parser::parse_file(&src) {
                Ok(d) => d,
                Err(e) => {
                    eprintln!("構文エラー {path}:{}: {}", e.line, e.msg);
                    return ExitCode::FAILURE;
                }
            };
            let mut env = Env::default();
            let prelude = parser::parse_file(PRELUDE).expect("prelude のパースに失敗");
            let _ = check_decls(&mut env, &prelude, false, true);
            let reports = check_decls(&mut env, &decls, false, false);

            if mode == "prose" {
                for (d, r) in decls.iter().zip(reports.iter()) {
                    println!(
                        "### {} `{}`\n",
                        if d.is_axiom { "公理" } else { "定理" },
                        d.name
                    );
                    for b in prose::decl_to_japanese_prose(d, &r.steps) {
                        println!("{}- {}", "  ".repeat(b.depth), b.text);
                    }
                    println!();
                }
            } else {
                println!("\\documentclass[a4paper,11pt]{{ltjsarticle}}");
                println!("\\usepackage{{amsmath,amssymb,amsthm}}");
                println!("\\newtheorem{{theorem}}{{定理}}");
                println!("\\newtheorem{{axiom}}{{公理}}");
                println!("\\begin{{document}}\n");
                for (d, r) in decls.iter().zip(reports.iter()) {
                    println!("{}", prose::decl_to_latex_env(d, &r.steps));
                }
                println!("\\end{{document}}");
            }
            return ExitCode::SUCCESS;
        }
        _ => {}
    }

    let mut trace = false;
    let mut diag = false;
    let mut files = Vec::new();
    for a in &args {
        match a.as_str() {
            "check" => {}
            "--trace" | "-t" => trace = true,
            // エディタ向けの出力：1行1件、タブ区切り（種類・行・本文。本文の改行は \n）
            "--diag" => diag = true,
            "-h" | "--help" => return usage(),
            _ => files.push(a.clone()),
        }
    }
    if files.is_empty() {
        return usage();
    }

    let mut env = Env::default();
    let prelude = parser::parse_file(PRELUDE).expect("prelude のパースに失敗");
    for r in check_decls(&mut env, &prelude, false, true) {
        assert!(r.err.is_none(), "prelude の定理 {} が通らない", r.name);
    }

    let mut failed = 0;
    let mut unfinished = 0;
    let mut total = 0;
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{path}: 読めない: {e}");
                return ExitCode::from(2);
            }
        };
        if !diag {
            println!("{path}");
        }
        let decls = match parser::parse_file(&src) {
            Ok(d) => d,
            Err(e) => {
                if diag {
                    println!("ERROR\t{}\t構文エラー: {}", e.line, esc(&e.msg));
                    return ExitCode::FAILURE;
                }
                println!("  構文エラー  {path}:{}: {}", e.line, e.msg);
                failed += 1;
                continue;
            }
        };
        for r in check_decls(&mut env, &decls, trace, false) {
            if !r.is_axiom {
                total += 1;
            }
            if diag {
                print_diag(&r);
            } else {
                print_report(path, &r);
            }
            if r.err.is_some() {
                failed += 1;
            } else if r.oracles.contains("sorry") {
                unfinished += 1;
            }
        }
    }
    if diag {
        return if failed == 0 {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        };
    }
    println!();
    if failed == 0 && unfinished == 0 {
        println!("{total} 個の定理をすべて検証しました。");
        ExitCode::SUCCESS
    } else if failed == 0 {
        println!(
            "{total} 個中 {unfinished} 個が未完成（sorry を含む）です。それ以外は検証しました。"
        );
        ExitCode::SUCCESS
    } else {
        println!("{total} 個中 {failed} 個が通りませんでした。");
        ExitCode::FAILURE
    }
}

fn print_report(path: &str, r: &Report) {
    if r.is_axiom {
        println!("  公理  {}", r.name);
        return;
    }
    match &r.err {
        None => {
            let mut notes = Vec::new();
            if !r.axioms.is_empty() {
                notes.push(format!(
                    "公理: {}",
                    r.axioms.iter().cloned().collect::<Vec<_>>().join(", ")
                ));
            }
            let oracles: Vec<String> = r
                .oracles
                .iter()
                .filter(|o| *o != "sorry")
                .cloned()
                .collect();
            if !oracles.is_empty() {
                notes.push(format!("自動証明: {}", oracles.join(", ")));
            }
            let notes = if notes.is_empty() {
                String::new()
            } else {
                format!("   〔{}〕", notes.join(" ／ "))
            };
            if r.oracles.contains("sorry") {
                println!("  △ {}   未完成{}", r.name, notes);
                for (line, ctx, g) in &r.sorries {
                    println!("      ── {path}:{line} の sorry で残っている goal ──");
                    for c in ctx {
                        println!("        {c}");
                    }
                    println!("        ⊢ {g}");
                }
            } else {
                println!("  ✓ {}{}", r.name, notes);
            }
        }
        Some(e) => {
            println!("  ✗ {}   {}:{}", r.name, path, e.line);
            for l in e.msg.lines() {
                println!("      {l}");
            }
            if let Some(g) = &e.goal {
                println!("      ── この行での状態 ──");
                for c in &e.ctx {
                    println!("        {c}");
                }
                println!("        ⊢ {g}");
            }
        }
    }
}

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\").replace('\n', "\\n")
}

fn state(ctx: &[String], g: &syntax::Formula) -> String {
    let mut s: Vec<String> = ctx.to_vec();
    s.push(format!("⊢ {g}"));
    s.join("\n")
}

fn print_diag(r: &Report) {
    if let Some(e) = &r.err {
        let mut msg = format!("{}: {}", r.name, e.msg);
        if let Some(g) = &e.goal {
            msg.push_str(&format!("\n\nこの行での状態:\n{}", state(&e.ctx, g)));
        }
        println!("ERROR\t{}\t{}", e.line, esc(&msg));
    }
    for (line, ctx, g) in &r.sorries {
        println!(
            "SORRY\t{}\t{}",
            line,
            esc(&format!("残っている goal:\n{}", state(ctx, g)))
        );
    }
}
