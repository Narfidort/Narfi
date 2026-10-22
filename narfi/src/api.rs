//! Web の API の応答（JSON）を作る部分。ディスク・ネットワークに依存しないので、
//! ローカルのサーバー（web.rs）とブラウザ版（wasm.rs）の両方から使う。

use crate::elab::Report;
use crate::module::Loaded;
use crate::parser::{Decl, ParseError};
use crate::prose;
use crate::syntax::with_syntax;

// ================================================================ 検証・ノート解析 API

struct NoteBlock {
    line: usize,
    kind: &'static str, // "heading" | "markdown" | "comment"
    text: String,
}

fn extract_notes(src: &str) -> Vec<NoteBlock> {
    let mut notes = Vec::new();
    let mut in_fence = false;
    let mut fence_start = 1;
    let mut fence_buf = String::new();

    for (i, raw) in src.lines().enumerate() {
        let lno = i + 1;
        let trimmed = raw.trim();
        if trimmed.starts_with("```") {
            if in_fence {
                notes.push(NoteBlock {
                    line: fence_start,
                    kind: "markdown",
                    text: fence_buf.trim_end().to_string(),
                });
                fence_buf.clear();
                in_fence = false;
            } else {
                in_fence = true;
                fence_start = lno;
            }
            continue;
        }
        if in_fence {
            fence_buf.push_str(raw);
            fence_buf.push('\n');
            continue;
        }
        if trimmed.starts_with('#') {
            notes.push(NoteBlock {
                line: lno,
                kind: "heading",
                text: trimmed.to_string(),
            });
            continue;
        }
        // 行全体がコメント（`//` または `--`）の場合
        if let Some(c) = trimmed
            .strip_prefix("//")
            .or_else(|| trimmed.strip_prefix("--"))
        {
            let c = c.trim();
            if !c.is_empty() && !c.starts_with("====") {
                notes.push(NoteBlock {
                    line: lno,
                    kind: "comment",
                    text: c.to_string(),
                });
            }
        }
    }
    notes
}

/// /api/check の応答。load は「ソースを読み込んで検査する」関数（ディスク版・ブラウザ版で差し替える）。
pub fn check_json(src: &str, cursor_line: Option<usize>, load: &dyn Fn(&str) -> Result<Loaded, ParseError>) -> String {
    check_json_in(src, cursor_line, "ja", load)
}

/// locale は Prose・LaTeX の言語（ja・en）
pub fn check_json_in(src: &str, cursor_line: Option<usize>, locale: &str, load: &dyn Fn(&str) -> Result<Loaded, ParseError>) -> String {
    crate::locale::set_current(locale);
    let notes = extract_notes(src);

    // まずそのままパースを試みる。もし編集中（空行や入力途中）でパースエラーになった場合、
    // カーソル行を sorry に置き換えたフォールバックも試して Goal 表示を維持する。
    // 試すたびに環境と記法の表を作り直す（load）。
    let mut mod_warnings = vec![];
    let (decls, reports, parse_err) = match load(src) {
        Ok((_, m, r)) => {
            mod_warnings = m.warnings();
            (m.decls_for(&r), r, None)
        }
        Err(e) => {
            let mut lines = vec![];
            lines.extend(cursor_line);
            lines.push(e.line);
            let recovered = lines
                .into_iter()
                .filter_map(|l| load(&patch_line_with_sorry(src, l)).ok())
                .find(|(_, m, _)| m.decls().next().is_some());
            match recovered {
                Some((_, m, r)) => (m.decls_for(&r), r, Some(e)),
                None => (vec![], vec![], Some(e)),
            }
        }
    };

    let mut decls_json = Vec::new();
    for (d, r) in decls.iter().zip(reports.iter()) {
        decls_json.push(format_decl_report_json(d, r));
    }

    let notes_json: Vec<String> = notes
        .iter()
        .map(|n| {
            format!(
                "{{\"line\":{},\"kind\":{},\"text\":{}}}",
                n.line,
                json_str(n.kind),
                json_str(&n.text)
            )
        })
        .collect();

    let perr_json = match parse_err {
        Some(e) => format!(
            "{{\"line\":{},\"msg\":{},\"msg_latex\":{}}}",
            e.line,
            json_str(&e.msg),
            json_str(&crate::parser::msg_latex(&e.msg))
        ),
        None => "null".to_string(),
    };

    // エディタの補完候補に出す notation（import 先のものも含む）
    let notations_json: Vec<String> = with_syntax(|t| {
        t.notations
            .iter()
            .flat_map(|n| {
                // 組み込みで読めない新しい記号だけ（→・( などは除く）
                n.symbols().into_iter().filter(|sym| !crate::parser::lexes_as_itself(sym)).map(move |sym| {
                    format!(
                        "{{\"sym\":{},\"pred\":{},\"latex\":{},\"template\":{}}}",
                        json_str(&sym),
                        json_str(&n.pred),
                        json_str(&crate::syntax::lit_latex(&sym)),
                        json_str(&n.template)
                    )
                })
            })
            .collect()
    });
    // ファイル全体への警告（古い書き方の notation など）。書き換え先は行ごと
    let warnings_json: Vec<String> = mod_warnings
        .iter()
        .map(|(l, m, rep)| format!("{{\"line\":{l},\"msg\":{},\"replace\":{}}}", json_str(m), json_str(rep)))
        .collect();

    format!(
        "{{\"ok\":{},\"parse_error\":{},\"decls\":[{}],\"notes\":[{}],\"notations\":[{}],\"warnings\":[{}]}}",
        perr_json == "null" && reports.iter().all(|r| r.err.is_none()),
        perr_json,
        decls_json.join(","),
        notes_json.join(","),
        notations_json.join(","),
        warnings_json.join(",")
    )
}

fn patch_line_with_sorry(src: &str, target_line: usize) -> String {
    src.lines()
        .enumerate()
        .map(|(i, l)| {
            if i + 1 == target_line {
                let indent: String = l.chars().take_while(|c| *c == ' ' || *c == '\t').collect();
                format!("{indent}sorry")
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_decl_report_json(d: &Decl, r: &Report) -> String {
    let status = if r.is_axiom {
        "axiom"
    } else if r.err.is_some() {
        "error"
    } else if r.oracles.contains("sorry") {
        "sorry"
    } else {
        "ok"
    };

    let header_latex = prose::decl_header_latex(d);
    let concl_latex = d.concl.to_latex();
    // Prose と LaTeX で同じ言い回しになるよう、言い回しの順番をそろえる
    let before = crate::locale::variation_state();
    let latex_env = prose::decl_to_latex_env(d, &r.steps);
    crate::locale::set_variation_state(before);
    let prose_blocks = prose::decl_to_japanese_prose(d, &r.steps);

    let err_json = match &r.err {
        Some(e) => {
            let g_str = e
                .goal
                .as_ref()
                .map(|g| json_str(&g.to_string()))
                .unwrap_or_else(|| "null".into());
            let gl_str = e
                .goal
                .as_ref()
                .map(|g| json_str(&g.to_latex()))
                .unwrap_or_else(|| "null".into());
            format!(
                "{{\"line\":{},\"msg\":{},\"msg_latex\":{},\"goal\":{},\"goal_latex\":{},\"ctx\":{},\"ctx_latex\":{},\"fix\":{},\"alts\":{}}}",
                e.line,
                json_str(&e.msg),
                json_str(&crate::parser::msg_latex(&e.msg)),
                g_str,
                gl_str,
                json_str_array(&e.ctx),
                json_str_array(&e.ctx_latex),
                e.fix.as_ref().map(|f| json_str(f)).unwrap_or_else(|| "null".into()),
                json_str_array(&e.alts)
            )
        }
        None => "null".to_string(),
    };

    let sorries_json: Vec<String> = r
        .sorries
        .iter()
        .map(|(line, ctx, g)| {
            format!(
                "{{\"line\":{},\"ctx\":{},\"goal\":{},\"goal_latex\":{}}}",
                line,
                json_str_array(ctx),
                json_str(&g.to_string()),
                json_str(&g.to_latex())
            )
        })
        .collect();

    let steps_json: Vec<String> = r
        .steps
        .iter()
        .map(|st| {
            let g = st.goal.as_ref().map(|x| json_str(x)).unwrap_or_else(|| "null".into());
            let gl = st.goal_latex.as_ref().map(|x| json_str(x)).unwrap_or_else(|| "null".into());
            format!(
                "{{\"line\":{},\"depth\":{},\"src\":{},\"ctx\":{},\"ctx_latex\":{},\"goal\":{},\"goal_latex\":{},\"hints\":[{}],\"terms\":{},\"seqs\":{}}}",
                st.line,
                st.depth,
                json_str(&st.src),
                json_str_array(&st.ctx),
                json_str_array(&st.ctx_latex),
                g,
                gl,
                st.hints.iter().map(|(c, w)| format!("[{},{}]", json_str(c), json_str(w))).collect::<Vec<_>>().join(","),
                json_str_array(&st.terms),
                json_str_array(&st.seqs)
            )
        })
        .collect();

    let prose_json: Vec<String> = prose_blocks
        .iter()
        .map(|b| format!("{{\"depth\":{},\"text\":{}}}", b.depth, json_str(&b.text)))
        .collect();

    let axioms_vec: Vec<String> = r.axioms.iter().cloned().collect();
    let oracles_vec: Vec<String> = r
        .oracles
        .iter()
        .filter(|o| *o != "sorry")
        .cloned()
        .collect();

    format!(
        "{{\"name\":{},\"line\":{},\"is_axiom\":{},\"status\":{},\"header_latex\":{},\"concl_latex\":{},\"axioms\":{},\"oracles\":{},\"error\":{},\"sorries\":[{}],\"steps\":[{}],\"prose\":[{}],\"latex_env\":{},\"tree\":{},\"warnings\":[{}],\"display_name\":{}}}",
        json_str(&r.name),
        r.line,
        r.is_axiom,
        json_str(status),
        json_str(&header_latex),
        json_str(&concl_latex),
        json_str_array(&axioms_vec),
        json_str_array(&oracles_vec),
        err_json,
        sorries_json.join(","),
        steps_json.join(","),
        prose_json.join(","),
        json_str(&latex_env),
        r.tree.as_deref().unwrap_or("null"),
        r.warnings
            .iter()
            .map(|(l, m, rep)| format!(
                "{{\"line\":{l},\"msg\":{},\"replace\":{}}}",
                json_str(m),
                rep.as_ref().map(|x| json_str(x)).unwrap_or_else(|| "null".into())
            ))
            .collect::<Vec<_>>()
            .join(","),
        crate::syntax::display_name(&d.name, crate::locale::current().name).map(|n| json_str(&n)).unwrap_or_else(|| "null".into())
    )
}

// ================================================================ 軽量 JSON ヘルパ

pub fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn json_str_array(items: &[String]) -> String {
    let v: Vec<String> = items.iter().map(|s| json_str(s)).collect();
    format!("[{}]", v.join(","))
}

pub fn json_get_str(json: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\"");
    let mut search_from = 0;
    while let Some(rel_idx) = json[search_from..].find(&pat) {
        let idx = search_from + rel_idx + pat.len();
        let rest = json[idx..].trim_start();
        if let Some(after_colon) = rest.strip_prefix(':') {
            let after_colon = after_colon.trim_start();
            if let Some(after_quote) = after_colon.strip_prefix('"') {
                return Some(parse_json_string_body(after_quote));
            }
        }
        search_from = idx;
    }
    None
}

pub fn json_get_usize(json: &str, key: &str) -> Option<usize> {
    let pat = format!("\"{key}\"");
    let idx = json.find(&pat)? + pat.len();
    let rest = json[idx..].trim_start().strip_prefix(':')?.trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

pub fn parse_json_string_body(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '"' {
            break;
        }
        if c == '\\' {
            if let Some(esc) = chars.next() {
                match esc {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    '/' => out.push('/'),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    'u' => {
                        let hex: String = chars.by_ref().take(4).collect();
                        if let Ok(code) = u32::from_str_radix(&hex, 16) {
                            if let Some(ch) = char::from_u32(code) {
                                out.push(ch);
                            }
                        }
                    }
                    other => out.push(other),
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}


#[cfg(test)]
mod tests {
    /// 各行の文脈の式（記法の補完に使う）：定義を展開した形も、数列は添字で
    #[test]
    fn steps_carry_context_terms() {
        let src = "def is_lim(a : Nat -> Real, alpha : Real) :<=> forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : is_lim(a, alpha)\n  |- is_lim((n:Nat |-> a_{n+1}), alpha)\n\nFix eps | heps : eps > 0\nsorry\n";
        let out = super::check_json(src, None, &|s| crate::module::load_and_check(s, None));
        for t in ["|a_{n + 1} - α|", "|a_n - α|", "(n : ℕ ↦ a_{n + 1})"] {
            assert!(out.contains(&super::json_str(t)), "{t} がない: {out}");
        }
        assert!(out.contains("\"seqs\":[\"a\"]"));
    }
}
