//! ソースの整形（File → Format Document・`narfi fmt`）。
//!
//! 空白だけを変える：行末の空白を消す、続く空白を 1 つにする、`,` の後に空白を 1 つ置く、
//! 連鎖（`= … by …` の行の並び）の `by` の位置をそろえる、空行を 2 つ以上続けない。
//! 字下げ・コメント・Markdown のブロック（```）・`@name` の文字列は変えない。
//! 空白を消して詰めることはしないので、字句の区切りは変わらない（証明の意味は変わらない）。

/// 整形したソース
pub fn format_source(src: &str) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut in_fence = false;
    for raw in src.lines() {
        let line = raw.trim_end().replace('\t', "  ");
        let t = line.trim_start();
        if t.starts_with("```") {
            in_fence = !in_fence;
            out.push(line);
            continue;
        }
        if in_fence || t.starts_with("--") || t.starts_with("//") || t.starts_with('#') || t.starts_with("@name") || t.is_empty() {
            out.push(if t.is_empty() { String::new() } else { line });
            continue;
        }
        let indent = &line[..line.len() - t.len()];
        // 行末のコメントは触らない
        let (code, comment) = split_comment(t);
        out.push(format!("{indent}{}{}", tidy(code), comment));
    }
    align_chains(&mut out);
    // 空行は 2 つ以上続けない。先頭の空行は消す
    let mut res: Vec<String> = Vec::new();
    for l in out {
        if l.is_empty() && (res.is_empty() || res.last().is_some_and(|p| p.is_empty())) {
            continue;
        }
        res.push(l);
    }
    while res.last().is_some_and(|l| l.is_empty()) {
        res.pop();
    }
    let mut s = res.join("\n");
    s.push('\n');
    s
}

/// `code -- comment` を分ける（`--` が文字列の外にあるとき）
fn split_comment(t: &str) -> (&str, &str) {
    match t.find(" --") {
        Some(i) => (&t[..i], &t[i..]),
        None => (t, ""),
    }
}

/// 続く空白を 1 つに、`,` の後に空白を 1 つ
fn tidy(code: &str) -> String {
    let mut s = String::new();
    let chars: Vec<char> = code.chars().collect();
    let mut k = 0;
    while k < chars.len() {
        let c = chars[k];
        if c == ' ' {
            while k + 1 < chars.len() && chars[k + 1] == ' ' {
                k += 1;
            }
            s.push(' ');
        } else if c == ',' {
            s.push(',');
            if k + 1 < chars.len() && chars[k + 1] != ' ' && chars[k + 1] != ')' && chars[k + 1] != ']' {
                s.push(' ');
            }
        } else {
            s.push(c);
        }
        k += 1;
    }
    s.trim_end().to_string()
}

const CHAIN_OPS: [&str; 12] = ["<=>", "<=", ">=", "!=", "=", "<", ">", "≤", "≥", "≠", "⇔", "≈"];

fn is_chain_step(t: &str) -> bool {
    CHAIN_OPS.iter().any(|op| t.starts_with(op) && t[op.len()..].starts_with(' ')) && by_pos(t).is_some()
}

/// トップレベル（括弧の外）の ` by ` の位置
fn by_pos(t: &str) -> Option<usize> {
    let mut depth = 0i32;
    let b = t.as_bytes();
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b' ' if depth == 0 && t[i..].starts_with(" by ") => return Some(i),
            _ => {}
        }
    }
    None
}

/// 連鎖の各段の `by` を同じ列にそろえる（同じ字下げで続く段ごと。いちばん長い段の後に空白 3 つ）
fn align_chains(lines: &mut [String]) {
    let mut k = 0;
    while k < lines.len() {
        let indent = |l: &str| l.len() - l.trim_start().len();
        if !is_chain_step(lines[k].trim_start()) {
            k += 1;
            continue;
        }
        let ind = indent(&lines[k]);
        let mut end = k;
        while end < lines.len() && indent(&lines[end]) == ind && is_chain_step(lines[end].trim_start()) {
            end += 1;
        }
        // 列は文字数で数える（ℝ・≤ なども 1 文字）
        let width = |s: &str| s.chars().count();
        let col = (k..end).map(|j| width(&lines[j][..ind + by_pos(lines[j].trim_start()).unwrap()])).max().unwrap() + 2;
        for j in k..end {
            let p = ind + by_pos(lines[j].trim_start()).unwrap();
            let (a, b) = lines[j].split_at(p);
            let pad = col - width(a);
            lines[j] = format!("{a}{}{b}", " ".repeat(pad));
        }
        k = end;
    }
}

/// 空白を除いた中身が同じか（整形が意味を変えていないことの確かめ）
pub fn same_up_to_space(a: &str, b: &str) -> bool {
    let f = |s: &str| s.chars().filter(|c| !c.is_whitespace()).collect::<String>();
    f(a) == f(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aligns_and_tidies() {
        let src = "thm t :\n  x : ℝ,y : ℝ\n  ⊢ x = x\n\n\n\nx\n  = x   by ring\n  = (x)      by ring  \n";
        let out = format_source(src);
        assert!(out.contains("x : ℝ, y : ℝ"), "{out}");
        assert!(out.contains("  = x     by ring\n  = (x)   by ring"), "{out}");
        assert!(!out.contains("\n\n\n"), "{out}");
        assert!(same_up_to_space(src, &out));
    }
}
