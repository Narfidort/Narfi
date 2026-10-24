//! コマンド `narfi`（check・web・prose・latex・convert）。検査器の本体は src/lib.rs のライブラリ。

use narfi::elab::{self, Report, check_module};
use narfi::module::Loader;
use narfi::{parser, prose, web};
use std::path::Path;
use std::process::ExitCode;

fn usage() -> ExitCode {
    eprintln!("使い方:");
    eprintln!("  narfi check [--trace] <ファイル.narfi>...   定理の検証");
    eprintln!("  narfi migrate [--write] file.narfi       古い書き方を今の書き方に書き換える");
    eprintln!("  narfi fmt [--write] file.narfi           整形する（空白だけを変える）");
    eprintln!("  narfi web [--port 3000] [--no-open] [--dir フォルダ]  Web エディタを起動");
    eprintln!("  narfi prose <ファイル.narfi>                自然な日本語の証明文(Markdown)を出力");
    eprintln!("  narfi latex <ファイル.narfi>                提出用 LaTeX ソースを出力");
    eprintln!("  narfi convert --jp|--std <ファイル.narfi>   日本語シュガー／標準の ASCII に変換");
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
            let mut dir: Option<std::path::PathBuf> = None;
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
                    "--dir" | "-d" => {
                        dir = args.get(i + 1).map(std::path::PathBuf::from);
                        i += 2;
                    }
                    _ => i += 1,
                }
            }
            if let Err(e) = web::serve(port, open_browser, dir) {
                eprintln!("Webサーバーの起動に失敗しました: {e}");
                return ExitCode::FAILURE;
            }
            return ExitCode::SUCCESS;
        }
        // ソースの変換（JP Sugar View・ASCII 正規化と同じもの）
        // 整形（--write で上書き。なければ標準出力へ）
        "fmt" => {
            let write = args.iter().any(|a| a == "--write");
            let Some(path) = args.iter().skip(1).find(|a| !a.starts_with("--")) else {
                return usage();
            };
            let src = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{path}: 読めない: {e}");
                    return ExitCode::from(2);
                }
            };
            let out = narfi::format::format_source(&src);
            if write {
                if out != src {
                    if let Err(e) = std::fs::write(path, &out) {
                        eprintln!("{path}: 書けない: {e}");
                        return ExitCode::from(2);
                    }
                }
            } else {
                print!("{out}");
            }
            return ExitCode::SUCCESS;
        }
        // 古い書き方を今の書き方に（--write で上書き。なければ標準出力へ）
        "migrate" => {
            let write = args.iter().any(|a| a == "--write");
            let Some(path) = args.iter().skip(1).find(|a| !a.starts_with("--")) else {
                return usage();
            };
            let src = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{path}: 読めない: {e}");
                    return ExitCode::from(2);
                }
            };
            let dir = Path::new(path).parent().map(|d| d.to_path_buf());
            let (out, done) = narfi::migrate::migrate(&src, &|s| narfi::migrate::errors_of(narfi::module::parse_source(s, dir.as_deref())));
            for (l, m) in &done {
                eprintln!("  {path}:{l}: {m}");
            }
            if write {
                if let Err(e) = std::fs::write(path, &out) {
                    eprintln!("{path}: 書けない: {e}");
                    return ExitCode::from(2);
                }
            } else {
                print!("{out}");
            }
            return ExitCode::SUCCESS;
        }
        "convert" => {
            let (Some(mode), Some(path)) = (args.get(1), args.get(2)) else {
                return usage();
            };
            let src = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{path}: 読めない: {e}");
                    return ExitCode::from(2);
                }
            };
            let out = match mode.as_str() {
                "--jp" | "--ja" => prose::convert_source_to_locale(&src, "ja"),
                "--en" => prose::convert_source_to_locale(&src, "en"),
                "--std" => prose::convert_source_to_standard_narfi(&src),
                _ => return usage(),
            };
            print!("{out}");
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
            let (mut ld, mut env) = Loader::new();
            let m = match ld.parse_file(&mut env, &src, Path::new(path)) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("構文エラー {path}:{}: {}", e.line, e.msg);
                    return ExitCode::FAILURE;
                }
            };
            let reports = match check_module(&mut env, &m, false, false) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("エラー {path}:{}: {}", e.line, e.msg);
                    return ExitCode::FAILURE;
                }
            };
            let owned = m.decls_for(&reports);
            let decls: Vec<&parser::Decl> = owned.iter().collect();

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
                let items: Vec<(&parser::Decl, &[elab::StepTrace])> =
                    decls.iter().zip(reports.iter()).map(|(d, r)| (*d, r.steps.as_slice())).collect();
                print!("{}", prose::latex_document("", &items));
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

    let (mut ld, mut env) = Loader::new();

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
        let m = match ld.parse_file(&mut env, &src, Path::new(path)) {
            Ok(m) => m,
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
        if !diag {
            for (l, msg, _) in m.warnings() {
                println!("  警告 {path}:{l}: {msg}");
            }
        }
        let reports = match check_module(&mut env, &m, trace, false) {
            Ok(r) => r,
            Err(e) => {
                if diag {
                    println!("ERROR\t{}\t{}", e.line, esc(&e.msg));
                    return ExitCode::FAILURE;
                }
                println!("  エラー  {path}:{}: {}", e.line, e.msg);
                failed += 1;
                continue;
            }
        };
        for r in reports {
            if !r.is_axiom {
                total += 1;
            }
            if diag {
                print_diag(&r);
            } else {
                print_report(path, &r);
                for (l, m, _) in &r.warnings {
                    println!("      警告 {path}:{l}: {m}");
                }
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
                notes.push(format!("算術: {}", oracles.join(", ")));
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
            if let Some((g, _)) = e.goal_show() {
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

fn state(ctx: &[String], g: &str) -> String {
    let mut s: Vec<String> = ctx.to_vec();
    s.push(format!("⊢ {g}"));
    s.join("\n")
}

fn print_diag(r: &Report) {
    if let Some(e) = &r.err {
        let mut msg = format!("{}: {}", r.name, e.msg);
        if let Some((g, _)) = e.goal_show() {
            msg.push_str(&format!("\n\nこの行での状態:\n{}", state(&e.ctx, &g)));
        }
        println!("ERROR\t{}\t{}", e.line, esc(&msg));
    }
    for (line, ctx, g) in &r.sorries {
        println!(
            "SORRY\t{}\t{}",
            line,
            esc(&format!("残っている goal:\n{}", state(ctx, &g.to_string())))
        );
    }
}
