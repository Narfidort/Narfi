//! 古い書き方を今の書き方に書き換える（v2.11〜v2.13 で消した書き方）。
//!
//! 構文解析を物差しにして直す：読めなかった行と、その理由（消した書き方の案内）から書き換えの候補を作り、
//! その行が読めるようになる候補を採る。直せない行はそのまま残す（勝手に意味を変えない）。

use crate::parser::{Item, Module, ParseError};

/// 読み込みの結果から、構文エラー（読めなかった宣言を含む）を行の順に
pub fn errors_of(r: Result<Module, ParseError>) -> Vec<ParseError> {
    let m = match r {
        Ok(m) => m,
        Err(e) => return vec![e],
    };
    let mut v: Vec<ParseError> = m
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Broken { line, msg, .. } => Some(ParseError { line: *line, msg: msg.clone() }),
            _ => None,
        })
        .collect();
    v.sort_by_key(|e| e.line);
    v
}

/// 書き換えたソースと、直した所（行・内容）。parse は構文エラーを行の順に返す
pub fn migrate(src: &str, parse: &dyn Fn(&str) -> Vec<ParseError>) -> (String, Vec<(usize, String)>) {
    let mut lines: Vec<String> = src.split('\n').map(String::from).collect();
    let mut done = Vec::new();
    let mut given_up: Vec<(usize, String)> = Vec::new();
    for _ in 0..200 {
        let errs = parse(&lines.join("\n"));
        let Some(e) = errs.iter().find(|e| !given_up.contains(&(e.line, e.msg.clone()))) else { break };
        let l = e.line;
        if l == 0 || l > lines.len() {
            given_up.push((l, e.msg.clone()));
            continue;
        }
        // ならばの → は、宣言の前提と結論が何行かにまたがって読まれるので、続く行もまとめて直す
        let mut end = l;
        if e.msg.contains("ならばは ⇒") {
            while end < lines.len() && end < l + 7 && !lines[end].trim().is_empty() {
                end += 1;
            }
        }
        let old = lines[l - 1..end].join("\n");
        let mut fixed = None;
        for c in candidates(&old, &e.msg) {
            let mut t = lines[..l - 1].to_vec();
            t.extend(c.split('\n').map(String::from));
            t.extend(lines[end..].iter().cloned());
            // その行の同じエラーが消え、ほかに新しいエラーが増えないなら採る
            let after = parse(&t.join("\n"));
            let same = after.iter().any(|x| x.line >= l && x.line <= end && x.msg == e.msg);
            if !same && after.len() <= errs.len() {
                fixed = Some(t);
                break;
            }
        }
        match fixed {
            Some(t) => {
                for (k, (a, b)) in lines[l - 1..end].iter().zip(&t[l - 1..end]).enumerate() {
                    if a != b {
                        done.push((l + k, format!("{} → {}", a.trim(), b.trim())));
                    }
                }
                lines = t;
            }
            None => given_up.push((l, e.msg.clone())),
        }
    }
    (lines.join("\n"), done)
}

fn candidates(line: &str, msg: &str) -> Vec<String> {
    let mut out = Vec::new();
    if msg.contains("ならばは ⇒") {
        // → と -> の位置。どれがならばかは、組み合わせを少ない順に試して決める
        let mut pos: Vec<(usize, usize, &str)> = Vec::new();
        for (i, _) in line.match_indices('→') {
            pos.push((i, '→'.len_utf8(), "⇒"));
        }
        for (i, _) in line.match_indices("->") {
            if i > 0 && line.as_bytes()[i - 1] == b'|' {
                continue;
            }
            pos.push((i, 2, "=>"));
        }
        pos.sort();
        let n = pos.len().min(10);
        let mut masks: Vec<u32> = (1..(1u32 << n)).collect();
        masks.sort_by_key(|m| m.count_ones());
        for m in masks {
            let mut s = String::new();
            let mut last = 0;
            for (k, (i, len, rep)) in pos.iter().take(n).enumerate() {
                if m & (1 << k) != 0 {
                    s.push_str(&line[last..*i]);
                    s.push_str(rep);
                    last = i + len;
                }
            }
            s.push_str(&line[last..]);
            out.push(s);
        }
    }
    if msg.contains("{a, b} と書く") {
        // max(a, b) → max{a, b}
        let mut s = line.to_string();
        for f in ["max", "min"] {
            while let Some(i) = s.find(&format!("{f}(")) {
                let open = i + f.len();
                let Some(close) = matching(&s, open) else { break };
                s = format!("{}{{{}}}{}", &s[..open], &s[open + 1..close], &s[close + 1..]);
            }
        }
        out.push(s);
    }
    if msg.contains("述語の定義は :⇔") {
        if let Some(i) = line.find(":=") {
            let rep = if line.is_ascii() { ":<=>" } else { ":⇔" };
            out.push(format!("{}{}{}", &line[..i], rep, &line[i + 2..]));
        }
    }
    if msg.contains("値の定義は := で書く") {
        for (pat, len) in [(":⇔", ":⇔".len()), (":<=>", 4)] {
            if let Some(i) = line.find(pat) {
                out.push(format!("{}:={}", &line[..i], &line[i + len..]));
            }
        }
    }
    if msg.contains("`have` は使わない") {
        // have h : φ := j → h : φ by j。have h : φ（下にブロック）→ h : φ
        let indent = &line[..line.len() - line.trim_start().len()];
        let body = line.trim_start().trim_start_matches("have").trim_start();
        match body.rfind(":=") {
            Some(i) => out.push(format!("{indent}{} by {}", body[..i].trim_end(), body[i + 2..].trim())),
            None => out.push(format!("{indent}{body}")),
        }
    }
    if msg.contains("`unfold` は使わない") {
        let indent = &line[..line.len() - line.trim_start().len()];
        out.push(format!("{indent}-- {}", line.trim_start()));
    }
    if msg.contains("`contradiction` は使わない") {
        // contradiction h k → k(h)
        let indent = &line[..line.len() - line.trim_start().len()];
        let args: Vec<&str> = line.trim_start().trim_start_matches("contradiction").split(|c: char| c == ',' || c.is_whitespace()).filter(|s| !s.is_empty()).collect();
        if args.len() == 2 {
            out.push(format!("{indent}{}({})", args[1], args[0]));
            out.push(format!("{indent}{}({})", args[0], args[1]));
        }
    }
    if msg.contains("記号を宣言するなら `const") {
        if let Some(rest) = line.trim_start().strip_prefix("axiom") {
            out.push(format!("const{rest}"));
        }
    }
    out
}

/// s[open] = '(' に対応する ')' の位置
fn matching(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0;
    for (i, c) in s[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(open + i);
                }
            }
            _ => {}
        }
    }
    None
}

/// /api/convert の mode "migrate" の答え：{"src": …, "changes": ["行: 前 → 後", …]}
pub fn migrate_json(src: &str, dir: Option<&std::path::Path>) -> String {
    let (out, done) = migrate(src, &|s| errors_of(crate::module::parse_source(s, dir)));
    let ch: Vec<String> = done.iter().map(|(l, m)| format!("{l}: {m}")).collect();
    format!("{{\"src\":{},\"changes\":{}}}", crate::api::json_str(&out), crate::api::json_str_array(&ch))
}
