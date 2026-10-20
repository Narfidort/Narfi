//! ロケール：言語の核（標準の書き方）と、自然言語での読み（日本語シュガーなど）の対応表。
//!
//! 設計原則（docs/principles.md）：言語の核は自然言語に依存しない。日本語などの読みは表示の層で、
//! このモジュールの表（`ja.txt`・`en.txt`）だけが知っている。読み（入力）と書き（エディタの表示・変換）は
//! 同じ表から作るので、ずれない。
//!
//! 表の 1 行は「標準の書き方 ⇄ この言語での書き方」の型紙の組。`{名前}` が中身の入る所。

use std::collections::HashMap;
use std::sync::OnceLock;

#[derive(Debug, Clone, Copy, PartialEq)]
enum Class {
    /// 空でない何でも
    Any,
    /// 空白を含まない名前
    Id,
    /// 関係の記号
    Rel,
}

#[derive(Debug, Clone)]
enum Part {
    Lit(String),
    Ph(String, Class),
}

#[derive(Debug, Clone)]
pub struct Rule {
    /// 読みも書きも（false なら読むだけ）
    canonical: bool,
    std: Vec<Part>,
    loc: Vec<Part>,
}

#[derive(Debug)]
pub struct Locale {
    pub name: &'static str,
    statements: Vec<Rule>,
    declarations: Vec<Rule>,
    /// 証明の文章の型紙（[prose]）
    prose: HashMap<String, String>,
    /// 表の元の文字列（エディタに渡す）
    pub source: &'static str,
}

const JA: &str = include_str!("ja.txt");
const EN: &str = include_str!("en.txt");

fn parse_template(t: &str) -> Vec<Part> {
    let mut parts = Vec::new();
    let mut lit = String::new();
    let mut rest = t;
    while let Some(k) = rest.find('{') {
        let Some(e) = rest[k..].find('}') else { break };
        lit.push_str(&rest[..k]);
        if !lit.is_empty() {
            parts.push(Part::Lit(std::mem::take(&mut lit)));
        }
        let inner = &rest[k + 1..k + e];
        let (name, class) = match inner.split_once(':') {
            Some((n, "id")) => (n, Class::Id),
            Some((n, "rel")) => (n, Class::Rel),
            Some((n, _)) => (n, Class::Any),
            None => (inner, Class::Any),
        };
        parts.push(Part::Ph(name.to_string(), class));
        rest = &rest[k + e + 1..];
    }
    lit.push_str(rest);
    if !lit.is_empty() {
        parts.push(Part::Lit(lit));
    }
    parts
}

fn parse_locale(name: &'static str, source: &'static str) -> Locale {
    let mut statements = Vec::new();
    let mut declarations = Vec::new();
    let mut prose = HashMap::new();
    let mut section = "";
    for line in source.lines() {
        let l = line.trim_end();
        if l.trim().is_empty() || l.starts_with('#') {
            continue;
        }
        if l.starts_with('[') {
            section = match l {
                "[declarations]" => "decl",
                "[prose]" => "prose",
                _ => "stmt",
            };
            continue;
        }
        if section == "prose" {
            // 型紙の前後の空白は意味がある（「 かつ 」など）ので、行の末尾を削らずに読む
            if let Some((k, v)) = line.trim_end_matches(['\r', '\n']).split_once('\t') {
                prose.insert(k.to_string(), v.to_string());
            }
            continue;
        }
        let cols: Vec<&str> = l.split('\t').collect();
        if cols.len() != 3 {
            continue;
        }
        let rule = Rule { canonical: cols[0] == "=", std: parse_template(cols[1]), loc: parse_template(cols[2]) };
        if section == "decl" {
            declarations.push(rule);
        } else {
            statements.push(rule);
        }
    }
    Locale { name, statements, declarations, prose, source }
}

impl Locale {
    /// 証明の文章の型紙 key に値を入れる（型紙がなければ日本語の表から）
    pub fn t(&self, key: &str, vals: &[(&str, &str)]) -> String {
        let tpl = self
            .prose
            .get(key)
            .or_else(|| locale("ja").and_then(|j| j.prose.get(key)))
            .cloned()
            .unwrap_or_else(|| format!("[{key}]"));
        let mut out = tpl;
        for (k, v) in vals {
            out = out.replace(&format!("{{{k}}}"), v);
        }
        out
    }
}

/// 使えるロケール（日本語・英語）
pub fn locales() -> &'static [Locale] {
    static L: OnceLock<Vec<Locale>> = OnceLock::new();
    L.get_or_init(|| vec![parse_locale("ja", JA), parse_locale("en", EN)])
}

pub fn locale(name: &str) -> Option<&'static Locale> {
    locales().iter().find(|l| l.name == name)
}

thread_local! {
    /// 証明の文章（Prose・LaTeX）を書くロケール。既定は日本語
    static CURRENT: std::cell::Cell<&'static str> = const { std::cell::Cell::new("ja") };
}

/// これ以降の Prose・LaTeX の言語を決める（知らない名前なら日本語）
pub fn set_current(name: &str) {
    let n = locale(name).map(|l| l.name).unwrap_or("ja");
    CURRENT.with(|c| c.set(n));
}

pub fn current() -> &'static Locale {
    CURRENT.with(|c| locale(c.get())).unwrap_or_else(|| &locales()[0])
}

fn class_ok(c: Class, s: &str) -> bool {
    match c {
        Class::Any => !s.is_empty(),
        Class::Id => !s.is_empty() && !s.chars().any(char::is_whitespace),
        Class::Rel => ["=", "<", "≤", ">", "≥", "≠"].contains(&s),
    }
}

/// 空白の並びを 1 つにする（型紙は空白 1 つで書く）
fn squash(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn match_parts(parts: &[Part], text: &str, caps: &mut HashMap<String, String>) -> bool {
    match parts.first() {
        None => text.is_empty(),
        Some(Part::Lit(l)) => text.strip_prefix(l.as_str()).is_some_and(|r| match_parts(&parts[1..], r, caps)),
        Some(Part::Ph(name, class)) => {
            // 次の文字どおりの部分が現れる所で切る（左から順に試す）
            match parts.get(1) {
                None => {
                    let v = text.trim();
                    if class_ok(*class, v) {
                        caps.insert(name.clone(), v.to_string());
                        true
                    } else {
                        false
                    }
                }
                Some(Part::Lit(next)) => {
                    let mut from = 0;
                    while let Some(k) = text[from..].find(next.as_str()) {
                        let at = from + k;
                        let v = text[..at].trim();
                        if class_ok(*class, v) {
                            let mut c2 = caps.clone();
                            c2.insert(name.clone(), v.to_string());
                            if match_parts(&parts[1..], &text[at..], &mut c2) {
                                *caps = c2;
                                return true;
                            }
                        }
                        from = at + next.len().max(1);
                        while !text.is_char_boundary(from) && from < text.len() {
                            from += 1;
                        }
                        if from > text.len() {
                            break;
                        }
                    }
                    false
                }
                Some(Part::Ph(..)) => false,
            }
        }
    }
}

fn render(parts: &[Part], caps: &HashMap<String, String>) -> Option<String> {
    let mut out = String::new();
    for p in parts {
        match p {
            Part::Lit(l) => out.push_str(l),
            Part::Ph(n, _) => out.push_str(caps.get(n)?),
        }
    }
    Some(out)
}

fn rewrite(rules: &[Rule], text: &str, from_std: bool) -> Option<String> {
    let t = squash(text);
    for r in rules {
        if from_std && !r.canonical {
            continue;
        }
        let (src, dst) = if from_std { (&r.std, &r.loc) } else { (&r.loc, &r.std) };
        let mut caps = HashMap::new();
        if match_parts(src, &t, &mut caps) {
            if let Some(s) = render(dst, &caps) {
                return Some(s);
            }
        }
    }
    None
}

/// どれかのロケールで書かれた 1 行を、標準の書き方にする（読めなければ None）
pub fn to_standard(line: &str) -> Option<String> {
    for l in locales() {
        if let Some(s) = rewrite(&l.statements, line, false).or_else(|| rewrite(&l.declarations, line, false)) {
            return Some(s);
        }
    }
    None
}

/// 標準の書き方の証明の行を、ロケールでの書き方にする（対応がなければそのまま）
pub fn stmt_from_standard(loc: &Locale, line: &str) -> String {
    rewrite(&loc.statements, line, true).unwrap_or_else(|| line.to_string())
}

/// 宣言の見出し（`thm name :` など）をロケールでの書き方にする
pub fn decl_from_standard(loc: &Locale, line: &str) -> String {
    rewrite(&loc.declarations, line, true).unwrap_or_else(|| line.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_ja() {
        let ja = locale("ja").unwrap();
        for std in [
            "Fix ε | hε : ε > 0",
            "Fix x",
            "assume h : P",
            "by_contra h",
            "Obtain N, hN : h(ε, hε)",
            "cases h",
            "Case left h1",
            "induction n",
            "Case zero",
            "Case succ k, IH : P(k)",
            "choose left",
            "choose N",
            "let N := max(a, b)",
            "k : x > 0 by linarith",
            "k : x > 0",
            "≤ |a| + |b| by triangle(a, b)",
            "Q ∧ P by q, p",
            "sorry",
        ] {
            let loc = stmt_from_standard(ja, std);
            assert_ne!(loc, std, "{std} に日本語の読みがない");
            assert_eq!(to_standard(&loc).as_deref(), Some(std), "{std} → {loc} → 戻らない");
        }
        assert_eq!(decl_from_standard(ja, "thm a.b :"), "定理 a.b :");
        assert_eq!(to_standard("定理 a.b :").as_deref(), Some("thm a.b :"));
    }

    #[test]
    fn roundtrip_en() {
        let en = locale("en").unwrap();
        for std in ["Fix ε | hε : ε > 0", "Fix x", "assume h : P", "Obtain N, hN : h(ε, hε)", "choose N", "k : x > 0 by linarith", "Q ∧ P by q, p"] {
            let loc = stmt_from_standard(en, std);
            assert_ne!(loc, std, "{std} に英語の読みがない");
            assert_eq!(to_standard(&loc).as_deref(), Some(std), "{std} → {loc} → 戻らない");
        }
    }

    #[test]
    fn standard_lines_are_left_alone() {
        for s in ["Fix x", "assume h : P", "h(a)", "x ≤ y by h", "thm t :", "P : Prop, h : P"] {
            assert_eq!(to_standard(s), None, "{s} が読み替えられてしまう");
        }
    }
}
