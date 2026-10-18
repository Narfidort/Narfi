//! 字句解析と構文解析。ファイル → 宣言の列。
//!
//! 行指向で読む。字下げでスコープ（ブロック）を作り、各行を再帰下降でパースする。

use crate::syntax::{Formula, RELS, Term, not};

// ================================================================ 宣言・文

#[derive(Debug, Clone)]
pub enum CtxItem {
    Var(String, String),
    Hyp(String, Formula),
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub is_axiom: bool,
    pub name: String,
    pub line: usize,
    pub ctx: Vec<CtxItem>,
    pub concl: Formula,
    pub body: Vec<Stmt>,
}

/// 根拠。カンマ区切りの列（2個以上なら ∧導入）。各要素は項の形で持ち、検査時に証拠として解釈する。
pub type Just = Vec<Term>;

#[derive(Debug, Clone)]
pub struct Stmt {
    pub line: usize,
    pub src: String,
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum Choice {
    Term(Term),
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub struct ChainStep {
    pub line: usize,
    pub rel: String,
    pub term: Term,
    pub just: Just,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Fix {
        vars: Vec<(String, Option<String>)>,
        hyp: Option<(String, Option<Formula>)>,
        body: Vec<Stmt>,
    },
    Assume {
        name: String,
        ty: Option<Formula>,
        body: Vec<Stmt>,
    },
    ByContra {
        name: String,
        body: Vec<Stmt>,
    },
    Obtain {
        var: String,
        deps: Option<Vec<String>>,
        hyps: Vec<String>,
        just: Just,
    },
    Have {
        name: String,
        ty: Formula,
        just: Just,
    },
    Suffices {
        ty: Formula,
        just: Just,
    },
    Choose {
        choice: Choice,
        just: Option<Just>,
    },
    Contradiction(String, String),
    Cases {
        hyp: String,
        left: (String, Vec<Stmt>),
        right: (String, Vec<Stmt>),
    },
    Induction {
        var: String,
        zero: Vec<Stmt>,
        succ: (String, String, Option<Formula>, Vec<Stmt>),
        succ_line: usize,
    },
    Let {
        name: String,
        term: Term,
    },
    Therefore(Formula),
    Close(Just),
    Chain {
        start: Term,
        steps: Vec<ChainStep>,
    },
}

#[derive(Debug)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

type PResult<T> = Result<T, ParseError>;

// ================================================================ 日本語シュガーの正規化

/// 日本語シュガーで書かれた1行の構文を標準の Narfi 行へ展開する。
pub fn normalize_japanese_sugar(raw: &str) -> String {
    let s = raw.trim();
    if s.is_empty() {
        return String::new();
    }

    // 1. 連鎖の根拠: `(∵ j)` または `∵ j` または `理由 j` → `by j`
    let s = if let Some((lhs, rhs)) = s.rsplit_once("(∵") {
        if let Some(j) = rhs.strip_suffix(')') {
            format!("{} by {}", lhs.trim_end(), j.trim())
        } else {
            s.to_string()
        }
    } else if let Some((lhs, rhs)) = s.rsplit_once('∵') {
        format!("{} by {}", lhs.trim_end(), rhs.trim())
    } else {
        s.to_string()
    };
    let s = s.trim();

    // 2. 単体のキーワード
    if s == "未完" || s == "後で" {
        return "sorry".to_string();
    }
    if s == "左を選ぶ" || s == "左を選べばよい" {
        return "choose left".to_string();
    }
    if s == "右を選ぶ" || s == "右を選べばよい" {
        return "choose right".to_string();
    }
    if s == "基底段階" || s == "基底段階:" {
        return "Case zero".to_string();
    }

    // 3. 語尾型の日本語シュガー
    // Fix: `h : P を満たす x を任意にとって固定する` / `h : P を満たす x を任意にとる`
    for suffix in [
        "を任意にとって固定する",
        "を任意にとって固定",
        "を任意にとる",
        "を固定する",
    ] {
        if let Some(body) = s.strip_suffix(suffix) {
            let body = body.trim();
            if let Some((cond, vars)) = body.split_once("を満たす") {
                return format!("Fix {} | {}", vars.trim(), cond.trim());
            }
            let vars = body
                .strip_prefix("任意の")
                .unwrap_or(body)
                .strip_prefix("任意に")
                .unwrap_or(body)
                .trim();
            return format!("Fix {vars}");
        }
    }

    // Obtain: `j より x, h が存在する` / `j より N(ε), hN を得る` / `j より h : P を満たす x が存在する`
    for suffix in ["が存在する", "を得る", "をとる"] {
        if let Some(body) = s.strip_suffix(suffix) {
            if let Some((just, targets)) = body.split_once("より") {
                let just = just.trim();
                let targets = targets.trim();
                if let Some((cond, var)) = targets.split_once("を満たす") {
                    let h = cond.split(':').next().unwrap_or(cond).trim();
                    return format!("Obtain {}, {} : {}", var.trim(), h, just);
                }
                return format!("Obtain {} : {}", targets, just);
            }
        }
    }

    // Assume: `h : P と仮定する` / `背理法により h と仮定する`
    if let Some(body) = s
        .strip_suffix("と仮定する")
        .or_else(|| s.strip_suffix("を仮定する"))
    {
        let body = body.trim();
        if let Some(rest) = body
            .strip_prefix("背理法により")
            .or_else(|| body.strip_prefix("背理法で"))
        {
            let h = rest.split(':').next().unwrap_or(rest).trim();
            return format!("by_contra {h}");
        }
        return format!("assume {body}");
    }

    // Let: `x := t とする` / `x := t とおく`
    for suffix in ["とする", "とおく", "と定義する"] {
        if let Some(body) = s.strip_suffix(suffix) {
            let body = body
                .trim()
                .strip_prefix("ここで")
                .map(|x| x.trim())
                .unwrap_or(body.trim());
            if body.contains(":=") {
                return format!("let {body}");
            }
        }
    }

    // Choose: `t をうまく選べばよい` / `t を選べばよい` / `t を選ぶ` / `t と選ぶ`
    for suffix in [
        "をうまく選べばよい",
        "を選べばよい",
        "をうまく選ぶ",
        "を選ぶ",
        "と選ぶ",
    ] {
        if let Some(body) = s.strip_suffix(suffix) {
            return format!("choose {}", body.trim());
        }
    }

    // Suffices: `j より ψ を示せば十分である` / `ψ を示せば十分 := j`
    for suffix in ["を示せば十分である", "を示せば十分", "を示せばよい"] {
        if let Some(body) = s.strip_suffix(suffix) {
            if let Some((just, f)) = body.split_once("より") {
                return format!("suffices {} := {}", f.trim(), just.trim());
            }
        }
    }
    if s.contains("を示せば十分") && s.contains(":=") {
        if let Some((f, j)) = s.split_once("を示せば十分") {
            let j = j.trim().strip_prefix(":=").unwrap_or(j.trim()).trim();
            return format!("suffices {} := {}", f.trim(), j);
        }
    }

    // Have: `j より h : φ が成り立つ`
    for suffix in ["が成り立つ", "を得る"] {
        if let Some(body) = s.strip_suffix(suffix) {
            if let Some((just, rest)) = body.split_once("より") {
                let rest = rest.trim();
                if rest.contains(':') {
                    return format!("have {} := {}", rest, just.trim());
                }
            }
        }
    }

    // Cases / Induction: `h で場合分けする` / `n に関する帰納法` / `n で帰納法を行う`
    for suffix in ["で場合分けする", "について場合分けする", "で場合分け"] {
        if let Some(h) = s.strip_suffix(suffix) {
            return format!("cases {}", h.trim());
        }
    }
    for suffix in [
        "に関する数学的帰納法",
        "に関する帰納法",
        "についての帰納法",
        "で帰納法を行う",
        "で帰納法",
    ] {
        if let Some(v) = s.strip_suffix(suffix) {
            return format!("induction {}", v.trim());
        }
    }

    // Contradiction: `h1 と h2 は矛盾`
    for suffix in ["は矛盾する", "は矛盾", "より矛盾"] {
        if let Some(body) = s.strip_suffix(suffix) {
            if let Some((a, b)) = body.split_once("と") {
                return format!("contradiction {} {}", a.trim(), b.trim());
            }
        }
    }

    // 4. 語頭型の日本語キーワード
    let prefixes = [
        ("定理 ", "thm "),
        ("補題 ", "thm "),
        ("命題 ", "thm "),
        ("公理 ", "axiom "),
        ("固定 ", "Fix "),
        ("任意に ", "Fix "),
        ("仮定 ", "assume "),
        ("背理法 ", "by_contra "),
        ("取得 ", "Obtain "),
        ("主張 ", "have "),
        ("示す ", "have "),
        ("十分 ", "suffices "),
        ("選ぶ ", "choose "),
        ("とおく ", "let "),
        ("場合分け ", "cases "),
        ("帰納法 ", "induction "),
        ("帰納段階 ", "Case succ "),
        ("場合 左 ", "Case left "),
        ("場合 右 ", "Case right "),
        ("場合 ", "Case "),
        ("矛盾 ", "contradiction "),
        ("したがって ", "∴ "),
        ("よって ", "∴ "),
        ("ゆえに ", "∴ "),
    ];
    for (jp, en) in prefixes {
        if let Some(rest) = s.strip_prefix(jp) {
            return format!("{en}{}", rest.trim());
        }
    }

    s.to_string()
}

// ================================================================ 字句解析

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Ident(String),
    Num(i64),
    Sym(String),
}

const TYPE_NAMES: [&str; 8] = ["ℕ", "ℤ", "ℚ", "ℝ", "ℂ", "𝔽", "ℙ", "Prop"];

fn is_type_char(c: char) -> bool {
    matches!(c, 'ℕ' | 'ℤ' | 'ℚ' | 'ℝ' | 'ℂ' | '𝔽' | 'ℙ')
}

fn is_ident_start(c: char) -> bool {
    (c.is_alphabetic() || c == '_') && !is_type_char(c)
}

fn is_ident_cont(c: char) -> bool {
    (c.is_alphanumeric() || c == '_' || c == '\'' || ('₀'..='₉').contains(&c))
        && !is_type_char(c)
        && !matches!(c, '²' | '³')
}

fn greek_word_to_char(w: &str) -> Option<&'static str> {
    Some(match w {
        "alpha" => "α",
        "beta" => "β",
        "gamma" => "γ",
        "delta" => "δ",
        "eps" | "epsilon" | "varepsilon" => "ε",
        "zeta" => "ζ",
        "eta" => "η",
        "theta" | "vartheta" => "θ",
        "iota" => "ι",
        "kappa" => "κ",
        "lambda" => "λ",
        "mu" => "μ",
        "nu" => "ν",
        "xi" => "ξ",
        "pi" => "π",
        "rho" => "ρ",
        "sigma" => "σ",
        "tau" => "τ",
        "upsilon" => "υ",
        "phi" | "varphi" => "φ",
        "chi" => "χ",
        "psi" => "ψ",
        "omega" => "ω",
        "Gamma" => "Γ",
        "Delta" => "Δ",
        "Theta" => "Θ",
        "Lambda" => "Λ",
        "Xi" => "Ξ",
        "Pi" => "Π",
        "Sigma" => "Σ",
        "Upsilon" => "Υ",
        "Phi" => "Φ",
        "Psi" => "Ψ",
        "Omega" => "Ω",
        "infty" => "∞",
        "emptyset" | "varnothing" => "∅",
        "partial" => "∂",
        "nabla" => "∇",
        _ => return None,
    })
}

fn tex_macro_replacement(cmd: &str) -> Option<&'static str> {
    if let Some(g) = greek_word_to_char(cmd) {
        return Some(g);
    }
    Some(match cmd {
        "all" | "forall" => "∀",
        "ex" | "exists" => "∃",
        "to" | "imp" | "rightarrow" | "implies" | "Rightarrow" => "→",
        "iff" | "leftrightarrow" | "Leftrightarrow" => "↔",
        "and" | "land" | "wedge" => "∧",
        "or" | "lor" | "vee" => "∨",
        "not" | "neg" | "lnot" => "¬",
        "bot" | "false" | "perp" => "⊥",
        "vdash" | "proves" => "⊢",
        "tf" | "therefore" => "∴",
        "because" => "by",
        "impby" | "Leftarrow" | "impliedby" => "⇐",
        "le" | "leq" => "≤",
        "ge" | "geq" => "≥",
        "ne" | "neq" => "≠",
        "in" => "∈",
        "notin" => "∉",
        "subset" => "⊂",
        "subseteq" => "⊆",
        "supset" => "⊃",
        "supseteq" => "⊇",
        "equiv" => "≡",
        "approx" => "≈",
        "sim" => "∼",
        "cong" => "≅",
        "mid" | "divides" => "∣",
        "cup" | "union" => "∪",
        "cap" | "inter" => "∩",
        "setminus" => "\\",
        "cdot" | "times" => "·",
        "sq" => "²",
        "cube" => "³",
        "N" | "nat" | "Nat" => "ℕ",
        "Z" | "int_set" | "Int" => "ℤ",
        "Q" | "rat" | "Rat" => "ℚ",
        "R" | "real" | "Real" => "ℝ",
        "C" | "complex" | "Complex" => "ℂ",
        "F" | "Field" => "𝔽",
        "P" | "Primes" => "ℙ",
        "a" => "α",
        "b" => "β",
        "g" => "γ",
        "d" => "δ",
        "e" => "ε",
        "l" => "λ",
        "0" | "_0" => "₀",
        "1" | "_1" => "₁",
        "2" | "_2" => "₂",
        "3" | "_3" => "₃",
        "4" | "_4" => "₄",
        "5" | "_5" => "₅",
        "6" | "_6" => "₆",
        "7" | "_7" => "₇",
        "8" | "_8" => "₈",
        "9" | "_9" => "₉",
        _ => return None,
    })
}

/// 文字列中の `\forall` や `\frac{a}{b}` などの TeX 表記を展開する前処理
pub fn expand_tex_macros(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < cs.len() {
        // \frac{a}{b} -> ((a)/(b)), \binom{n}{k} -> binom(n, k), \sqrt{x} -> sqrt(x)
        if cs[i] == '\\' {
            let st = i + 1;
            let mut j = st;
            while j < cs.len() && (cs[j].is_ascii_alphanumeric() || cs[j] == '_') {
                j += 1;
            }
            if j > st {
                let cmd: String = cs[st..j].iter().collect();
                if cmd == "frac" || cmd == "binom" {
                    let mut k = j;
                    while k < cs.len() && cs[k].is_whitespace() {
                        k += 1;
                    }
                    if let Some((num, next_k)) = extract_braced(&cs, k) {
                        let mut m = next_k;
                        while m < cs.len() && cs[m].is_whitespace() {
                            m += 1;
                        }
                        if let Some((den, end_k)) = extract_braced(&cs, m) {
                            let num_exp = expand_tex_macros(&num);
                            let den_exp = expand_tex_macros(&den);
                            if cmd == "frac" {
                                out.push_str(&format!("(({num_exp})/({den_exp}))"));
                            } else {
                                out.push_str(&format!("binom({num_exp}, {den_exp})"));
                            }
                            i = end_k;
                            continue;
                        }
                    }
                } else if matches!(
                    cmd.as_str(),
                    "sqrt" | "abs" | "norm" | "floor" | "ceil" | "set" | "inner" | "vec" | "hat" | "bar" | "tilde"
                ) {
                    let mut k = j;
                    while k < cs.len() && cs[k].is_whitespace() {
                        k += 1;
                    }
                    if let Some((body, end_k)) = extract_braced(&cs, k) {
                        let body_exp = expand_tex_macros(&body);
                        out.push_str(&format!("{cmd}({body_exp})"));
                        i = end_k;
                        continue;
                    }
                } else if let Some(rep) = tex_macro_replacement(&cmd) {
                    out.push_str(rep);
                    i = j;
                    continue;
                }
            }
        }
        // 下付き _{...} または _0 .. _9
        if cs[i] == '_' && i + 1 < cs.len() {
            if cs[i + 1] == '{' {
                if let Some((inner, end_k)) = extract_braced(&cs, i + 1) {
                    let inner_trimmed = inner.trim();
                    let all_digits =
                        !inner_trimmed.is_empty() && inner_trimmed.chars().all(|c| c.is_ascii_digit());
                    if all_digits {
                        for ch in inner_trimmed.chars() {
                            let d = ch as u32 - '0' as u32;
                            if let Some(sub) = char::from_u32('₀' as u32 + d) {
                                out.push(sub);
                            }
                        }
                    } else if let Some(g) = greek_word_to_char(inner_trimmed) {
                        // h_{eps} -> hε (元の Unicode 識別子 hε と完全一致させる)
                        out.push_str(g);
                    } else {
                        out.push('_');
                        out.push_str(&expand_tex_macros(inner_trimmed));
                    }
                    i = end_k;
                    continue;
                }
            } else if cs[i + 1].is_ascii_digit() {
                let d = cs[i + 1] as u32 - '0' as u32;
                if let Some(sub) = char::from_u32('₀' as u32 + d) {
                    out.push(sub);
                    i += 2;
                    continue;
                }
            }
        }
        // 上付き ^{...}
        if cs[i] == '^' && i + 1 < cs.len() && cs[i + 1] == '{' {
            if let Some((inner, end_k)) = extract_braced(&cs, i + 1) {
                let inner_exp = expand_tex_macros(inner.trim());
                out.push_str(&format!("^({inner_exp})"));
                i = end_k;
                continue;
            }
        }
        out.push(cs[i]);
        i += 1;
    }
    out
}

fn extract_braced(cs: &[char], start: usize) -> Option<(String, usize)> {
    if start >= cs.len() || cs[start] != '{' {
        return None;
    }
    let mut depth = 0i32;
    for i in start..cs.len() {
        if cs[i] == '{' {
            depth += 1;
        } else if cs[i] == '}' {
            depth -= 1;
            if depth == 0 {
                let inner: String = cs[(start + 1)..i].iter().collect();
                return Some((inner, i + 1));
            }
        }
    }
    None
}

pub fn lex(s: &str, line: usize) -> PResult<Vec<Tok>> {
    let norm = expand_tex_macros(&normalize_japanese_sugar(s));
    let cs: Vec<char> = norm.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if is_type_char(c) {
            out.push(Tok::Ident(c.to_string()));
            i += 1;
            continue;
        }
        if is_ident_start(c) || matches!(c, '∞' | '∅' | '∂' | '∇') {
            let st = i;
            i += 1;
            loop {
                if i < cs.len() && is_ident_cont(cs[i]) {
                    i += 1;
                } else if i + 1 < cs.len() && cs[i] == '.' && is_ident_start(cs[i + 1]) {
                    // eq.symm, hq.right, x.prop のような名前の中の「.」
                    i += 2;
                } else {
                    break;
                }
            }
            let word: String = cs[st..i].iter().collect();
            let mapped = if let Some(g) = greek_word_to_char(&word) {
                Tok::Ident(g.into())
            } else {
                match word.as_str() {
                    "forall" => Tok::Sym("∀".into()),
                    "exists" => Tok::Sym("∃".into()),
                    "and" => Tok::Sym("∧".into()),
                    "or" => Tok::Sym("∨".into()),
                    "not" => Tok::Sym("¬".into()),
                    "false" | "bot" => Tok::Sym("⊥".into()),
                    "in" => Tok::Sym("∈".into()),
                    "notin" => Tok::Sym("∉".into()),
                    "subset" => Tok::Sym("⊂".into()),
                    "subseteq" => Tok::Sym("⊆".into()),
                    "supset" => Tok::Sym("⊃".into()),
                    "supseteq" => Tok::Sym("⊇".into()),
                    "equiv" => Tok::Sym("≡".into()),
                    "approx" => Tok::Sym("≈".into()),
                    "sim" => Tok::Sym("∼".into()),
                    "cong" => Tok::Sym("≅".into()),
                    "divides" => Tok::Sym("∣".into()),
                    "union" => Tok::Sym("∪".into()),
                    "inter" => Tok::Sym("∩".into()),
                    "setminus" => Tok::Sym("\\".into()),
                    "therefore" => Tok::Sym("∴".into()),
                    "Nat" => Tok::Ident("ℕ".into()),
                    "Int" => Tok::Ident("ℤ".into()),
                    "Rat" => Tok::Ident("ℚ".into()),
                    "Real" => Tok::Ident("ℝ".into()),
                    "Complex" => Tok::Ident("ℂ".into()),
                    "Field" => Tok::Ident("𝔽".into()),
                    "Primes" => Tok::Ident("ℙ".into()),
                    _ => Tok::Ident(word),
                }
            };
            out.push(mapped);
            continue;
        }
        if c.is_ascii_digit() {
            let st = i;
            while i < cs.len() && cs[i].is_ascii_digit() {
                i += 1;
            }
            let txt: String = cs[st..i].iter().collect();
            let n = txt.parse().map_err(|_| ParseError {
                line,
                msg: format!("数が大きすぎる: {txt}"),
            })?;
            out.push(Tok::Num(n));
            continue;
        }
        let three: String = cs[i..(i + 3).min(cs.len())].iter().collect();
        if three == "<->" {
            out.push(Tok::Sym("↔".to_string()));
            i += 3;
            continue;
        }
        let two: String = cs[i..(i + 2).min(cs.len())].iter().collect();
        let sym2 = match two.as_str() {
            ":=" => Some(":="),
            "->" => Some("→"),
            "<-" => Some("⇐"),
            "<=" | "=<" => Some("≤"),
            ">=" => Some("≥"),
            "!=" => Some("≠"),
            "|-" => Some("⊢"),
            "/\\" => Some("∧"),
            "\\/" => Some("∨"),
            _ => None,
        };
        if let Some(s2) = sym2 {
            out.push(Tok::Sym(s2.to_string()));
            i += 2;
            continue;
        }
        let sym = match c {
            '*' => "·".to_string(),
            '²' | '³' | '(' | ')' | ',' | ':' | '|' | '.' | '∀' | '∃' | '→' | '↔' | '∧' | '∨'
            | '¬' | '⊥' | '⊢' | '=' | '≠' | '<' | '≤' | '>' | '≥' | '∈' | '∉' | '⊂' | '⊆'
            | '⊃' | '⊇' | '≡' | '≈' | '∼' | '≅' | '∣' | '∪' | '∩' | '\\' | '+' | '-' | '−'
            | '·' | '/' | '^' | '⇐' | '∴' => {
                if c == '−' {
                    "-".to_string()
                } else {
                    c.to_string()
                }
            }
            _ => {
                return Err(ParseError {
                    line,
                    msg: format!("読めない文字: '{c}'"),
                });
            }
        };
        out.push(Tok::Sym(sym));
        i += 1;
    }
    Ok(out)
}

// ================================================================ 1行のパーサ

pub struct P {
    toks: Vec<Tok>,
    pos: usize,
    line: usize,
    /// 範囲付き量化子の型推論に使う：(変数名, 型)
    tyenv: Vec<(String, String)>,
}

impl P {
    pub fn new(toks: Vec<Tok>, line: usize, tyenv: Vec<(String, String)>) -> P {
        P {
            toks,
            pos: 0,
            line,
            tyenv,
        }
    }
    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError {
            line: self.line,
            msg: msg.into(),
        })
    }
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn peek_at(&self, k: usize) -> Option<&Tok> {
        self.toks.get(self.pos + k)
    }
    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Sym(x)) if x == s)
    }
    fn is_ident(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(x)) if x == s)
    }
    fn eat_sym(&mut self, s: &str) -> bool {
        if self.is_sym(s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect_sym(&mut self, s: &str) -> PResult<()> {
        if self.eat_sym(s) {
            Ok(())
        } else {
            self.err(format!("'{}' が必要（{} の位置）", s, self.here()))
        }
    }
    fn here(&self) -> String {
        match self.peek() {
            None => "行末".into(),
            Some(Tok::Ident(x)) => format!("'{x}'"),
            Some(Tok::Num(n)) => format!("'{n}'"),
            Some(Tok::Sym(s)) => format!("'{s}'"),
        }
    }
    pub fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }
    fn expect_end(&self) -> PResult<()> {
        if self.at_end() {
            Ok(())
        } else {
            self.err(format!("余分なトークン: {}", self.here()))
        }
    }
    pub fn ident(&mut self) -> PResult<String> {
        match self.peek().cloned() {
            Some(Tok::Ident(x)) => {
                self.pos += 1;
                Ok(x)
            }
            _ => self.err(format!("名前が必要（{} の位置）", self.here())),
        }
    }
    fn peek_rel(&self) -> Option<String> {
        match self.peek() {
            Some(Tok::Sym(s)) if RELS.contains(&s.as_str()) => Some(s.clone()),
            _ => None,
        }
    }

    // ------------------------------------------------ 型
    fn ty(&mut self) -> PResult<String> {
        let t = self.ident()?;
        Ok(t)
    }

    // ------------------------------------------------ 論理式
    pub fn formula(&mut self) -> PResult<Formula> {
        let a = self.imp()?;
        if self.eat_sym("↔") {
            let b = self.formula()?;
            return Ok(Formula::And(
                Box::new(Formula::Imp(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(Formula::Imp(Box::new(b), Box::new(a))),
            ));
        }
        Ok(a)
    }
    fn imp(&mut self) -> PResult<Formula> {
        let a = self.disj()?;
        if self.eat_sym("→") {
            let b = self.imp()?;
            return Ok(Formula::Imp(Box::new(a), Box::new(b)));
        }
        Ok(a)
    }
    fn disj(&mut self) -> PResult<Formula> {
        let mut a = self.conj()?;
        while self.eat_sym("∨") {
            let b = self.conj()?;
            a = Formula::Or(Box::new(a), Box::new(b));
        }
        Ok(a)
    }
    fn conj(&mut self) -> PResult<Formula> {
        let a = self.unary()?;
        if self.eat_sym("∧") {
            // 右結合：A ∧ B ∧ C = A ∧ (B ∧ C)
            let b = self.conj()?;
            return Ok(Formula::And(Box::new(a), Box::new(b)));
        }
        Ok(a)
    }
    fn unary(&mut self) -> PResult<Formula> {
        if self.eat_sym("¬") {
            return Ok(not(self.unary()?));
        }
        if self.is_sym("∀") || self.is_sym("∃") {
            let all = self.is_sym("∀");
            self.pos += 1;
            let x = self.ident()?;
            let mut ty = if self.eat_sym(":") {
                Some(self.ty()?)
            } else {
                None
            };
            let guard = match self.peek_rel() {
                Some(r) if r != "=" && r != "≠" => {
                    self.pos += 1;
                    let t = self.term()?;
                    if ty.is_none() {
                        // 範囲付き量化子 ∀n≥N の型は N の型から推論する
                        if let Term::Var(v) = &t {
                            ty = self
                                .tyenv
                                .iter()
                                .rev()
                                .find(|(n, _)| n == v)
                                .map(|(_, t)| t.clone());
                        }
                    }
                    Some(Formula::Atom(r, vec![Term::Var(x.clone()), t]))
                }
                _ => None,
            };
            let ty = ty.unwrap_or_else(|| "?".into());
            self.expect_sym(".")?;
            self.tyenv.push((x.clone(), ty.clone()));
            let body = self.formula();
            self.tyenv.pop();
            let body = body?;
            return Ok(match (all, guard) {
                (true, None) => Formula::Forall(x, ty, Box::new(body)),
                (false, None) => Formula::Exists(x, ty, Box::new(body)),
                (true, Some(g)) => {
                    Formula::Forall(x, ty, Box::new(Formula::Imp(Box::new(g), Box::new(body))))
                }
                (false, Some(g)) => {
                    Formula::Exists(x, ty, Box::new(Formula::And(Box::new(g), Box::new(body))))
                }
            });
        }
        self.primary()
    }
    fn primary(&mut self) -> PResult<Formula> {
        if self.eat_sym("⊥") {
            return Ok(Formula::Bot);
        }
        if self.is_sym("(") {
            // 「(論理式)」か「(項) rel 項」かを、試してから決める
            let save = self.pos;
            self.pos += 1;
            if let Ok(f) = self.formula() {
                if self.eat_sym(")") && self.peek_rel().is_none() && !self.is_term_op() {
                    return Ok(f);
                }
            }
            self.pos = save;
        }
        let t = self.term()?;
        if let Some(r) = self.peek_rel() {
            self.pos += 1;
            let u = self.term()?;
            return Ok(if r == "≠" {
                not(Formula::Atom("=".into(), vec![t, u]))
            } else {
                Formula::Atom(r, vec![t, u])
            });
        }
        match t {
            Term::Var(p) => Ok(Formula::Atom(p, vec![])),
            Term::App(p, args) if p.chars().next().is_some_and(is_ident_start) => {
                Ok(Formula::Atom(p, args))
            }
            _ => self.err(format!("論理式が必要（{} の位置）", self.here())),
        }
    }
    fn is_term_op(&self) -> bool {
        ["+", "-", "·", "/", "^", "²", "³", "∪", "∩", "\\"]
            .iter()
            .any(|s| self.is_sym(s))
    }

    // ------------------------------------------------ 項
    pub fn term(&mut self) -> PResult<Term> {
        let mut a = self.term_mul()?;
        loop {
            let op = if self.is_sym("+") {
                "+"
            } else if self.is_sym("-") {
                "-"
            } else if self.is_sym("∪") {
                "∪"
            } else {
                break;
            };
            self.pos += 1;
            let b = self.term_mul()?;
            a = Term::App(op.into(), vec![a, b]);
        }
        Ok(a)
    }
    fn term_mul(&mut self) -> PResult<Term> {
        let mut a = self.term_unary()?;
        loop {
            let op = if self.is_sym("·") {
                "·"
            } else if self.is_sym("/") {
                "/"
            } else if self.is_sym("∩") {
                "∩"
            } else if self.is_sym("\\") {
                "\\"
            } else {
                break;
            };
            self.pos += 1;
            let b = self.term_unary()?;
            a = Term::App(op.into(), vec![a, b]);
        }
        Ok(a)
    }
    fn term_unary(&mut self) -> PResult<Term> {
        if self.eat_sym("-") {
            return Ok(Term::App("neg".into(), vec![self.term_unary()?]));
        }
        let mut a = self.term_atom()?;
        loop {
            if self.eat_sym("²") {
                a = Term::App("^".into(), vec![a, Term::Num(2)]);
            } else if self.eat_sym("³") {
                a = Term::App("^".into(), vec![a, Term::Num(3)]);
            } else if self.eat_sym("^") {
                let e = self.term_atom()?;
                a = Term::App("^".into(), vec![a, e]);
            } else {
                break;
            }
        }
        Ok(a)
    }
    fn term_atom(&mut self) -> PResult<Term> {
        match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.pos += 1;
                Ok(Term::Num(n))
            }
            Some(Tok::Ident(x)) => {
                self.pos += 1;
                if self.eat_sym("(") {
                    let mut args = Vec::new();
                    if !self.eat_sym(")") {
                        loop {
                            args.push(self.term()?);
                            if self.eat_sym(")") {
                                break;
                            }
                            self.expect_sym(",")?;
                        }
                    }
                    Ok(Term::App(x, args))
                } else {
                    Ok(Term::Var(x))
                }
            }
            Some(Tok::Sym(s)) if s == "(" => {
                self.pos += 1;
                let t = self.term()?;
                self.expect_sym(")")?;
                Ok(t)
            }
            Some(Tok::Sym(s)) if s == "|" => {
                self.pos += 1;
                let t = self.term()?;
                self.expect_sym("|")?;
                Ok(Term::App("abs".into(), vec![t]))
            }
            _ => self.err(format!("項が必要（{} の位置）", self.here())),
        }
    }

    // ------------------------------------------------ 根拠
    pub fn just(&mut self) -> PResult<Just> {
        let mut v = vec![self.term()?];
        while self.eat_sym(",") {
            v.push(self.term()?);
        }
        Ok(v)
    }

    /// トップレベル（括弧の外）の `by` の位置
    fn find_by(&self) -> Option<usize> {
        let mut depth = 0i32;
        for (k, t) in self.toks.iter().enumerate().skip(self.pos) {
            match t {
                Tok::Sym(s) if s == "(" => depth += 1,
                Tok::Sym(s) if s == ")" => depth -= 1,
                Tok::Ident(x) if x == "by" && depth == 0 => return Some(k),
                _ => {}
            }
        }
        None
    }
}

// ================================================================ ファイル全体

struct Line {
    no: usize,
    indent: usize,
    text: String,
}

struct Node {
    no: usize,
    text: String,
    children: Vec<Node>,
}

/// `--` および `//` のコメントを取り除く
pub fn strip_comment(s: &str) -> &str {
    let a = s.find("--");
    let b = s.find("//");
    match (a, b) {
        (Some(x), Some(y)) => &s[..x.min(y)],
        (Some(x), None) => &s[..x],
        (None, Some(y)) => &s[..y],
        (None, None) => s,
    }
}

fn indent_of(s: &str) -> usize {
    s.chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .map(|c| if c == '\t' { 4 } else { 1 })
        .sum()
}

fn starts_decl(text: &str) -> bool {
    let norm = normalize_japanese_sugar(text);
    let w = norm.split_whitespace().next().unwrap_or("");
    w == "thm" || w == "axiom"
}

fn is_axiom_decl(text: &str) -> bool {
    let norm = normalize_japanese_sugar(text);
    norm.starts_with("axiom")
}

pub fn parse_file(src: &str) -> PResult<Vec<Decl>> {
    let mut lines: Vec<Line> = Vec::new();
    let mut in_fence = false;
    for (i, raw) in src.lines().enumerate() {
        let trimmed = raw.trim();
        if trimmed.starts_with("```") {
            in_fence = !in_fence;
            continue;
        }
        if in_fence || trimmed.starts_with('#') {
            continue;
        }
        let s = strip_comment(raw);
        if !s.trim().is_empty() {
            lines.push(Line {
                no: i + 1,
                indent: indent_of(s),
                text: s.trim().to_string(),
            });
        }
    }

    let mut decls = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let l = &lines[i];
        if l.indent != 0 || !starts_decl(&l.text) {
            return Err(ParseError {
                line: l.no,
                msg: "トップレベルには thm か axiom を書く".into(),
            });
        }
        let is_axiom = is_axiom_decl(&l.text);
        // 見出し：thm は ⊢ を含む行まで、axiom は字下げされた続きの行まで
        let mut header = vec![i];
        if is_axiom {
            while i + 1 < lines.len() && lines[i + 1].indent > 0 {
                i += 1;
                header.push(i);
            }
        } else {
            while !lines[i].text.contains('⊢')
                && !lines[i].text.contains("|-")
                && !lines[i].text.contains("\\vdash")
            {
                i += 1;
                if i >= lines.len() || starts_decl(&lines[i].text) && lines[i].indent == 0 {
                    return Err(ParseError {
                        line: l.no,
                        msg: "thm の見出しに ⊢ がない".into(),
                    });
                }
                header.push(i);
            }
        }
        i += 1;
        let htext: Vec<&str> = header.iter().map(|&k| lines[k].text.as_str()).collect();
        let mut decl = parse_header(&htext.join(" "), l.no, is_axiom)?;
        if !is_axiom {
            let st = i;
            while i < lines.len() && !(lines[i].indent == 0 && starts_decl(&lines[i].text)) {
                i += 1;
            }
            let body = join_continuations(&lines[st..i]);
            let tree = build_tree(&body);
            let tyenv: Vec<(String, String)> = decl
                .ctx
                .iter()
                .filter_map(|c| match c {
                    CtxItem::Var(x, t) => Some((x.clone(), t.clone())),
                    _ => None,
                })
                .collect();
            decl.body = parse_block(&tree, &tyenv)?;
        }
        decls.push(decl);
    }
    Ok(decls)
}

fn parse_header(text: &str, line: usize, is_axiom: bool) -> PResult<Decl> {
    let toks = lex(text, line)?;
    let mut p = P::new(toks, line, vec![]);
    p.ident()?; // thm / axiom
    let name = p.ident()?;
    p.expect_sym(":")?;
    let has_turnstile = p.toks.iter().any(|t| *t == Tok::Sym("⊢".into()));
    let mut ctx = Vec::new();
    if has_turnstile {
        while !p.eat_sym("⊢") {
            let x = p.ident()?;
            p.expect_sym(":")?;
            // `x : ℕ` は変数の宣言、それ以外は仮定
            let is_type = matches!(p.peek(), Some(Tok::Ident(t)) if TYPE_NAMES.contains(&t.as_str()))
                && matches!(p.peek_at(1), Some(Tok::Sym(s)) if s == "," || s == "⊢");
            if is_type {
                let t = p.ident()?;
                p.tyenv.push((x.clone(), t.clone()));
                ctx.push(CtxItem::Var(x, t));
            } else {
                ctx.push(CtxItem::Hyp(x, p.formula()?));
            }
            if !p.is_sym("⊢") {
                p.expect_sym(",")?;
            }
        }
    }
    let concl = p.formula()?;
    p.expect_end()?;
    Ok(Decl {
        is_axiom,
        name,
        line,
        ctx,
        concl,
        body: vec![],
    })
}

/// 行末が「,」か括弧が閉じていない行は、次の行とつなげる
fn join_continuations(lines: &[Line]) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    let mut open = false;
    for l in lines {
        if open {
            let last = out.last_mut().unwrap();
            last.text.push(' ');
            last.text.push_str(&l.text);
        } else {
            out.push(Line {
                no: l.no,
                indent: l.indent,
                text: l.text.clone(),
            });
        }
        let t = &out.last().unwrap().text;
        let depth = t.matches('(').count() as i32 - t.matches(')').count() as i32;
        open = t.ends_with(',') || depth > 0;
    }
    out
}

fn build_tree(lines: &[Line]) -> Vec<Node> {
    fn go(lines: &[Line], i: &mut usize, base: usize) -> Vec<Node> {
        let mut out = Vec::new();
        while *i < lines.len() && lines[*i].indent >= base {
            let l = &lines[*i];
            *i += 1;
            let children = if *i < lines.len() && lines[*i].indent > l.indent {
                let ci = lines[*i].indent;
                go(lines, i, ci)
            } else {
                vec![]
            };
            out.push(Node {
                no: l.no,
                text: l.text.clone(),
                children,
            });
        }
        out
    }
    let mut i = 0;
    let base = lines.iter().map(|l| l.indent).min().unwrap_or(0);
    go(lines, &mut i, base)
}

fn parse_block(nodes: &[Node], tyenv: &[(String, String)]) -> PResult<Vec<Stmt>> {
    nodes.iter().map(|n| parse_stmt(n, tyenv)).collect()
}

fn no_children(n: &Node) -> PResult<()> {
    if n.children.is_empty() {
        Ok(())
    } else {
        Err(ParseError {
            line: n.children[0].no,
            msg: "この行の下に字下げされたブロックは置けない".into(),
        })
    }
}

fn parse_stmt(n: &Node, tyenv: &[(String, String)]) -> PResult<Stmt> {
    let toks = lex(&n.text, n.no)?;
    let mut p = P::new(toks, n.no, tyenv.to_vec());
    let first = match p.peek() {
        Some(Tok::Ident(x)) => x.clone(),
        Some(Tok::Sym(s)) => s.clone(),
        _ => String::new(),
    };
    let block = |p: &P| parse_block(&n.children, &p.tyenv);
    let kind = match first.as_str() {
        "Fix" => {
            p.pos += 1;
            let mut vars = Vec::new();
            loop {
                let x = p.ident()?;
                let t = if p.eat_sym(":") {
                    Some(p.ident()?)
                } else {
                    None
                };
                vars.push((x, t));
                if !p.eat_sym(",") {
                    break;
                }
            }
            let hyp = if p.eat_sym("|") {
                let h = p.ident()?;
                let f = if p.eat_sym(":") {
                    Some(p.formula()?)
                } else {
                    None
                };
                Some((h, f))
            } else {
                None
            };
            p.expect_end()?;
            StmtKind::Fix {
                vars,
                hyp,
                body: block(&p)?,
            }
        }
        "assume" => {
            p.pos += 1;
            let name = p.ident()?;
            let ty = if p.eat_sym(":") {
                Some(p.formula()?)
            } else {
                None
            };
            p.expect_end()?;
            StmtKind::Assume {
                name,
                ty,
                body: block(&p)?,
            }
        }
        "by_contra" => {
            p.pos += 1;
            let name = p.ident()?;
            p.expect_end()?;
            StmtKind::ByContra {
                name,
                body: block(&p)?,
            }
        }
        "Obtain" => {
            p.pos += 1;
            let var = p.ident()?;
            let deps = if p.eat_sym("(") {
                let mut d = Vec::new();
                if !p.eat_sym(")") {
                    loop {
                        d.push(p.ident()?);
                        if p.eat_sym(")") {
                            break;
                        }
                        p.expect_sym(",")?;
                    }
                }
                Some(d)
            } else {
                None
            };
            let mut hyps = Vec::new();
            while p.eat_sym(",") {
                hyps.push(p.ident()?);
            }
            if hyps.is_empty() {
                hyps.push(format!("{var}.prop"));
            }
            p.expect_sym(":")?;
            let just = p.just()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Obtain {
                var,
                deps,
                hyps,
                just,
            }
        }
        "have" => {
            p.pos += 1;
            let name = p.ident()?;
            p.expect_sym(":")?;
            let ty = p.formula()?;
            p.expect_sym(":=")?;
            let just = p.just()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Have { name, ty, just }
        }
        "suffices" | "⇐" => {
            p.pos += 1;
            let ty = p.formula()?;
            p.expect_sym(":=")?;
            let just = p.just()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Suffices { ty, just }
        }
        "choose" => {
            p.pos += 1;
            let choice = if p.is_ident("left") {
                p.pos += 1;
                Choice::Left
            } else if p.is_ident("right") {
                p.pos += 1;
                Choice::Right
            } else {
                Choice::Term(p.term()?)
            };
            let just = if p.eat_sym(",") {
                Some(p.just()?)
            } else {
                None
            };
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Choose { choice, just }
        }
        "contradiction" => {
            p.pos += 1;
            let a = p.ident()?;
            let b = p.ident()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Contradiction(a, b)
        }
        "let" => {
            p.pos += 1;
            let name = p.ident()?;
            p.expect_sym(":=")?;
            let term = p.term()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Let { name, term }
        }
        "∴" => {
            p.pos += 1;
            let f = p.formula()?;
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Therefore(f)
        }
        "cases" => {
            p.pos += 1;
            let hyp = p.ident()?;
            p.expect_end()?;
            let (mut left, mut right) = (None, None);
            for c in &n.children {
                let mut q = P::new(lex(&c.text, c.no)?, c.no, tyenv.to_vec());
                if !q.is_ident("Case") {
                    return Err(ParseError {
                        line: c.no,
                        msg: "cases の下には Case left / Case right を書く".into(),
                    });
                }
                q.pos += 1;
                let side = q.ident()?;
                let h = q.ident()?;
                q.eat_sym(":");
                q.expect_end()?;
                let body = parse_block(&c.children, tyenv)?;
                match side.as_str() {
                    "left" => left = Some((h, body)),
                    "right" => right = Some((h, body)),
                    _ => {
                        return Err(ParseError {
                            line: c.no,
                            msg: "Case left か Case right".into(),
                        });
                    }
                }
            }
            match (left, right) {
                (Some(l), Some(r)) => StmtKind::Cases {
                    hyp,
                    left: l,
                    right: r,
                },
                _ => {
                    return Err(ParseError {
                        line: n.no,
                        msg: "Case left と Case right の両方が必要".into(),
                    });
                }
            }
        }
        "induction" => {
            p.pos += 1;
            let var = p.ident()?;
            p.expect_end()?;
            let (mut zero, mut succ, mut succ_line) = (None, None, n.no);
            for c in &n.children {
                let mut q = P::new(lex(&c.text, c.no)?, c.no, tyenv.to_vec());
                if !q.is_ident("Case") {
                    return Err(ParseError {
                        line: c.no,
                        msg: "induction の下には Case zero / Case succ を書く".into(),
                    });
                }
                q.pos += 1;
                let which = q.ident()?;
                let body = parse_block(&c.children, tyenv)?;
                match which.as_str() {
                    "zero" => {
                        q.eat_sym(":");
                        q.expect_end()?;
                        zero = Some(body);
                    }
                    "succ" => {
                        let k = q.ident()?;
                        q.expect_sym(",")?;
                        let ih = q.ident()?;
                        // `Case succ k, IH : φ` の末尾の「:」はあってもなくてもよい
                        let f = if q.eat_sym(":") && !q.at_end() {
                            Some(q.formula()?)
                        } else {
                            None
                        };
                        q.eat_sym(":");
                        q.expect_end()?;
                        succ = Some((k, ih, f, body));
                        succ_line = c.no;
                    }
                    _ => {
                        return Err(ParseError {
                            line: c.no,
                            msg: "Case zero か Case succ".into(),
                        });
                    }
                }
            }
            match (zero, succ) {
                (Some(z), Some(s)) => StmtKind::Induction {
                    var,
                    zero: z,
                    succ: s,
                    succ_line,
                },
                _ => {
                    return Err(ParseError {
                        line: n.no,
                        msg: "Case zero と Case succ の両方が必要".into(),
                    });
                }
            }
        }
        _ => {
            let starts_chain = n.children.first().is_some_and(|c| {
                lex(&c.text, c.no)
                    .ok()
                    .and_then(|t| t.first().cloned())
                    .is_some_and(|t| matches!(t, Tok::Sym(s) if RELS.contains(&s.as_str())))
            });
            if starts_chain || p.find_by().is_some() {
                let start = p.term()?;
                let mut steps = Vec::new();
                if !p.at_end() {
                    steps.push(chain_step(&mut p, n.no)?);
                }
                for c in &n.children {
                    let mut q = P::new(lex(&c.text, c.no)?, c.no, tyenv.to_vec());
                    no_children(c)?;
                    steps.push(chain_step(&mut q, c.no)?);
                }
                StmtKind::Chain { start, steps }
            } else {
                let j = p.just()?;
                p.expect_end()?;
                no_children(n)?;
                StmtKind::Close(j)
            }
        }
    };
    Ok(Stmt {
        line: n.no,
        src: n.text.clone(),
        kind,
    })
}

fn chain_step(p: &mut P, line: usize) -> PResult<ChainStep> {
    let rel = match p.peek_rel() {
        Some(r) if r != "≠" && r != "∈" => r,
        _ => {
            return Err(ParseError {
                line,
                msg: "連鎖の各行は = < ≤ > ≥ のどれかで始める".into(),
            });
        }
    };
    p.pos += 1;
    let term = p.term()?;
    if !p.is_ident("by") {
        return Err(ParseError {
            line,
            msg: "連鎖の各行には `by 根拠` が必要".into(),
        });
    }
    p.pos += 1;
    let just = p.just()?;
    p.expect_end()?;
    Ok(ChainStep {
        line,
        rel,
        term,
        just,
    })
}
