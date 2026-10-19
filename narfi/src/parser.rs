//! 字句解析と構文解析。ファイル → 宣言の列。
//!
//! 行指向で読む。字下げでスコープ（ブロック）を作り、各行を再帰下降でパースする。

use crate::syntax::{
    Formula, Notation, RELS, Term, holds, not, notation_for_sym, with_syntax,
};
use crate::types::Ty;
use std::collections::BTreeSet;

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
    /// `typedef T := {x : σ | φ}` なら Some。concl は ∃x:σ. φ（空でないことの証明が body）
    pub typedef: Option<TypeDef>,
    /// `rec` の定義から自動で作った定理（f.zero・f.succ）。ソースの変換では書き戻さない
    pub generated: bool,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    /// 作る型の名前
    pub name: String,
}

/// `def name(params) := body`。body は引数が関数の位置に現れる所を `@` 形にしたもの。
#[derive(Debug, Clone)]
pub struct Def {
    pub name: String,
    pub line: usize,
    /// (引数名, 型)。型は書かれていなければ "?"（いまは検査に使わない）
    pub params: Vec<(String, String)>,
    /// 述語の定義の本体（項の定義では使わない）
    pub body: Formula,
    /// 項の定義 `def f(x : ℕ) : ℕ := t` の (値の型, 本体)
    pub term: Option<(String, Term)>,
    pub src: String,
}

#[derive(Debug, Clone)]
pub enum Item {
    Decl(Decl),
    Def(Def),
    /// notation 宣言（読み込み時に記法の表へ登録済み）。src は元の行
    Notation { src: String },
    Import { path: String },
}

/// 1ファイル分。宣言を書かれた順に持つ。
#[derive(Debug, Clone, Default)]
pub struct Module {
    pub items: Vec<Item>,
}

impl Module {
    pub fn decls(&self) -> impl Iterator<Item = &Decl> {
        self.items.iter().filter_map(|i| match i {
            Item::Decl(d) => Some(d),
            _ => None,
        })
    }
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
    /// `unfold is_lim` / `unfold is_lim at h₁, h₂`
    Unfold {
        names: Vec<String>,
        at: Vec<String>,
    },
    Close(Just),
    /// `φ by j`：φ を j から示す（goal なら閉じる。後ろに続けば this として使える）
    Show {
        ty: Formula,
        just: Just,
    },
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

    // Choose: `t をとればよい` / `t とすればよい`（古い書き方の `t をうまく選べばよい` / `t を選ぶ` なども読む）
    for suffix in [
        "をとればよい",
        "とすればよい",
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

    // Unfold: `is_lim を展開する` / `h の is_lim を展開する`
    for suffix in ["の定義を展開する", "を展開する"] {
        if let Some(body) = s.strip_suffix(suffix) {
            if let Some((hs, names)) = body.split_once('の') {
                return format!("unfold {} at {}", names.trim(), hs.trim());
            }
            return format!("unfold {}", body.trim());
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
        ("定義 ", "def "),
        ("記法 ", "notation "),
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
        "longrightarrow" | "lto" => "⟶",
        "mapsto" => "↦",
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
                    } else if is_plain_name(inner_trimmed) {
                        out.push('_');
                        out.push_str(&expand_tex_macros(inner_trimmed));
                    } else {
                        // 式の添字 a_{n+1} は a_(n+1) にする（数列の添字なら a(n+1) と読む。subscript_apps）
                        out.push_str("_(");
                        out.push_str(&expand_tex_macros(inner_trimmed));
                        out.push(')');
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

fn is_plain_name(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || ('₀'..='₉').contains(&c))
}

/// 数のあとに来ても積にしない語（2 by ring・1 and … など）
const IMPLICIT_STOP: [&str; 14] =
    ["by", "and", "or", "not", "iff", "in", "notin", "then", "because", "since", "with", "at", "to", "mod"];

// ================================================================ 数列の添字：a_n は a(n)
//
// `a : ℕ → σ` と宣言された a について、`a_n`・`a_{n+1}`・`a_1`（a₁）を a(n)・a(n+1)・a(1) と読む。
// その名前そのもの（a_n など）が宣言されているときは読み替えない。

struct SubScope {
    seqs: BTreeSet<String>,
    declared: BTreeSet<String>,
}

impl SubScope {
    fn new(vars: &[(String, String)]) -> SubScope {
        let is_seq = |t: &str| t.strip_prefix("ℕ →").is_some_and(|r| !r.contains('→') && !r.contains('×'));
        SubScope {
            seqs: vars.iter().filter(|(_, t)| is_seq(t)).map(|(x, _)| x.clone()).collect(),
            declared: vars.iter().map(|(x, _)| x.clone()).collect(),
        }
    }

    /// x が数列の添字の形なら (数列, 添字)
    fn split(&self, x: &str) -> Option<(String, Term)> {
        if self.seqs.is_empty() || self.declared.contains(x) {
            return None;
        }
        if let Some((b, i)) = x.split_once('_') {
            if self.seqs.contains(b) && !i.is_empty() {
                let idx = if let Ok(n) = i.parse::<i64>() { Term::Num(n) } else { Term::Var(i.to_string()) };
                return Some((b.to_string(), idx));
            }
        }
        // a₁₂（a_{12}・a_12 は字句解析で a₁₂ になる）
        let digits: String = x.chars().rev().take_while(|c| ('₀'..='₉').contains(c)).collect();
        if !digits.is_empty() {
            let b: String = x.chars().take(x.chars().count() - digits.chars().count()).collect();
            if self.seqs.contains(&b) {
                let n: String = digits.chars().rev().map(|c| char::from_u32(c as u32 - '₀' as u32 + '0' as u32).unwrap()).collect();
                return Some((b, Term::Num(n.parse().ok()?)));
            }
        }
        None
    }

    fn term(&self, t: &Term) -> Term {
        match t {
            Term::Var(x) => match self.split(x) {
                Some((b, i)) => Term::App(b, vec![i]),
                None => t.clone(),
            },
            Term::App(f, args) => {
                let args: Vec<Term> = args.iter().map(|a| self.term(a)).collect();
                match f.strip_suffix('_') {
                    Some(b) if self.seqs.contains(b) && !self.declared.contains(f) => Term::App(b.to_string(), args),
                    _ => Term::App(f.clone(), args),
                }
            }
            Term::Lam(ps, b) => Term::Lam(ps.clone(), Box::new(self.term(b))),
            Term::Set(ps, phi) => Term::Set(ps.clone(), Box::new(self.formula(phi))),
            Term::Num(_) | Term::Meta(_) => t.clone(),
        }
    }

    fn formula(&self, f: &Formula) -> Formula {
        let bx = |g: &Formula| Box::new(self.formula(g));
        match f {
            Formula::Atom(r, ts) => Formula::Atom(r.clone(), ts.iter().map(|t| self.term(t)).collect()),
            Formula::Imp(a, b) => Formula::Imp(bx(a), bx(b)),
            Formula::And(a, b) => Formula::And(bx(a), bx(b)),
            Formula::Or(a, b) => Formula::Or(bx(a), bx(b)),
            Formula::Forall(x, s, b) => Formula::Forall(x.clone(), s.clone(), bx(b)),
            Formula::Exists(x, s, b) => Formula::Exists(x.clone(), s.clone(), bx(b)),
            Formula::Bot => Formula::Bot,
        }
    }

    fn just(&self, j: &Just) -> Just {
        j.iter().map(|t| self.term(t)).collect()
    }

    fn stmts(&self, ss: &mut [Stmt]) {
        for s in ss {
            self.stmt(&mut s.kind);
        }
    }

    fn stmt(&self, k: &mut StmtKind) {
        match k {
            StmtKind::Fix { hyp, body, .. } => {
                if let Some((_, Some(f))) = hyp {
                    *f = self.formula(f);
                }
                self.stmts(body);
            }
            StmtKind::Assume { ty, body, .. } => {
                if let Some(f) = ty {
                    *f = self.formula(f);
                }
                self.stmts(body);
            }
            StmtKind::ByContra { body, .. } => self.stmts(body),
            StmtKind::Obtain { just, .. } | StmtKind::Close(just) => *just = self.just(just),
            StmtKind::Show { ty, just } => {
                *ty = self.formula(ty);
                *just = self.just(just);
            }
            StmtKind::Have { ty, just, .. } | StmtKind::Suffices { ty, just } => {
                *ty = self.formula(ty);
                *just = self.just(just);
            }
            StmtKind::Choose { choice, just } => {
                if let Choice::Term(t) = choice {
                    *t = self.term(t);
                }
                if let Some(j) = just {
                    *j = self.just(j);
                }
            }
            StmtKind::Contradiction(..) | StmtKind::Unfold { .. } => {}
            StmtKind::Cases { left, right, .. } => {
                self.stmts(&mut left.1);
                self.stmts(&mut right.1);
            }
            StmtKind::Induction { zero, succ, .. } => {
                self.stmts(zero);
                if let Some(f) = &mut succ.2 {
                    *f = self.formula(f);
                }
                self.stmts(&mut succ.3);
            }
            StmtKind::Let { term, .. } => *term = self.term(term),
            StmtKind::Therefore(f) => *f = self.formula(f),
            StmtKind::Chain { start, steps } => {
                *start = self.term(start);
                for st in steps {
                    st.term = self.term(&st.term);
                    st.just = self.just(&st.just);
                }
            }
        }
    }
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
    lex_raw(&norm, line, true)
}

/// 記号の notation（`⟶` など、名前の形でないもの）。長いものから試す。
fn symbolic_notations() -> Vec<Vec<char>> {
    let mut v: Vec<Vec<char>> = with_syntax(|t| {
        t.notations
            .iter()
            .map(|n| n.sym.chars().collect::<Vec<char>>())
            .filter(|cs| !is_ident_start(cs[0]))
            .collect()
    });
    v.sort_by_key(|cs| std::cmp::Reverse(cs.len()));
    v
}

fn lex_raw(norm: &str, line: usize, with_notations: bool) -> PResult<Vec<Tok>> {
    let cs: Vec<char> = norm.chars().collect();
    let nots = if with_notations {
        symbolic_notations()
    } else {
        vec![]
    };
    let mut i = 0;
    let mut out = Vec::new();
    'outer: while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        for n in &nots {
            if cs[i..].starts_with(n) {
                out.push(Tok::Sym(n.iter().collect()));
                i += n.len();
                continue 'outer;
            }
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
        if three == "|->" {
            out.push(Tok::Sym("↦".to_string()));
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
            | '·' | '/' | '^' | '⇐' | '∴' | '×' | '{' | '}' | '↦' => {
                if c == '−' {
                    "-".to_string()
                } else {
                    c.to_string()
                }
            }
            _ => {
                return Err(ParseError {
                    line,
                    msg: format!(
                        "読めない文字: '{c}'（新しい記号は notation で宣言してから使う）"
                    ),
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
    /// notation で宣言した中置記号
    fn peek_notation(&self) -> Option<Notation> {
        match self.peek() {
            Some(Tok::Sym(s)) | Some(Tok::Ident(s)) => notation_for_sym(s),
            _ => None,
        }
    }

    // ------------------------------------------------ 型
    /// 型の式：`ℕ`・`ℕ → ℝ`・`ℕ × ℕ → Prop`・`(ℕ → ℚ) → Prop`
    pub fn ty(&mut self) -> PResult<String> {
        Ok(self.ty_expr()?.show())
    }

    fn ty_expr(&mut self) -> PResult<Ty> {
        let mut args = vec![self.ty_atom()?];
        while self.eat_sym("×") {
            args.push(self.ty_atom()?);
        }
        if self.eat_sym("→") {
            let r = self.ty_expr()?;
            return Ok(Ty::fun(args, r));
        }
        if args.len() > 1 {
            return self.err("積の型（ℕ × ℕ）だけでは値の型にならない（ℕ × ℕ → Prop のように使う）");
        }
        Ok(args.pop().unwrap())
    }

    fn ty_atom(&mut self) -> PResult<Ty> {
        if self.eat_sym("(") {
            let t = self.ty_expr()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        let x = self.ident()?;
        Ok(if x == "Prop" { Ty::Prop } else { Ty::Base(x) })
    }

    /// λ・集合の束縛変数：`x`・`x : ℕ`・`(x, y)`・`(x, y) : ℕ × ℕ`
    fn binders(&mut self) -> PResult<Vec<(String, String)>> {
        if self.eat_sym("(") {
            let mut names = vec![self.ident()?];
            while self.eat_sym(",") {
                names.push(self.ident()?);
            }
            self.expect_sym(")")?;
            let mut tys = vec!["?".to_string(); names.len()];
            if self.eat_sym(":") {
                let mut ts = vec![self.ty_atom()?.show()];
                while self.eat_sym("×") {
                    ts.push(self.ty_atom()?.show());
                }
                if ts.len() != names.len() {
                    return self.err(format!("変数が {} 個あるのに、型が {} 個", names.len(), ts.len()));
                }
                tys = ts;
            }
            return Ok(names.into_iter().zip(tys).collect());
        }
        let x = self.ident()?;
        let t = if self.eat_sym(":") { self.ty()? } else { "?".to_string() };
        Ok(vec![(x, t)])
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
                    if r == "∈" {
                        Some(self.mem(&Term::Var(x.clone()), &t)?)
                    } else {
                        Some(Formula::Atom(r, vec![Term::Var(x.clone()), t]))
                    }
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
                if self.eat_sym(")")
                    && self.peek_rel().is_none()
                    && self.peek_notation().is_none()
                    && !self.is_term_op()
                {
                    return Ok(f);
                }
            }
            self.pos = save;
        }
        let t = self.term()?;
        if let Some(r) = self.peek_rel() {
            self.pos += 1;
            let u = self.term()?;
            match r.as_str() {
                "∈" => return self.mem(&t, &u),
                "∉" => return Ok(not(self.mem(&t, &u)?)),
                "⊆" | "⊂" => return self.subset(&t, &u),
                "⊇" | "⊃" => return self.subset(&u, &t),
                _ => {}
            }
            return Ok(if r == "≠" {
                not(Formula::Atom("=".into(), vec![t, u]))
            } else {
                Formula::Atom(r, vec![t, u])
            });
        }
        if let Some(n) = self.peek_notation() {
            self.pos += 1;
            let u = self.term()?;
            return Ok(n.atom(t, u));
        }
        let (p, args) = match t {
            Term::App(p, args) if p == "@" => return Ok(Formula::Atom(p, args)),
            Term::Var(p) => (p, vec![]),
            Term::App(p, args) if p.chars().next().is_some_and(is_ident_start) => (p, args),
            _ => return self.err(format!("論理式が必要（{} の位置）", self.here())),
        };
        if let Some(k) = with_syntax(|t| t.defs.get(&p).copied()) {
            if k != args.len() {
                return self.err(format!(
                    "`{p}` は引数 {k} 個の定義だが、{} 個渡されている",
                    args.len()
                ));
            }
        }
        Ok(Formula::Atom(p, args))
    }
    /// t ∈ A：A が名前なら述語 A の適用、集合 {x | φ} なら φ[x := t]
    fn mem(&self, t: &Term, a: &Term) -> PResult<Formula> {
        match a {
            Term::Num(_) => self.err(format!("`∈` の右には集合を書く（`{a}`）")),
            _ => Ok(holds(a, std::slice::from_ref(t))),
        }
    }

    /// A ⊆ B は ∀x. x ∈ A → x ∈ B
    fn subset(&self, a: &Term, b: &Term) -> PResult<Formula> {
        let mut used = std::collections::BTreeSet::new();
        a.vars(&mut used);
        b.vars(&mut used);
        let mut x = "x".to_string();
        while used.contains(&x) {
            x.push('\'');
        }
        let v = Term::Var(x.clone());
        let body = Formula::Imp(Box::new(self.mem(&v, a)?), Box::new(self.mem(&v, b)?));
        Ok(Formula::Forall(x, "?".into(), Box::new(body)))
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
            // 数のあとに項が続けば積：2x・2(a + b)・3a_n（数で始まる名前はないので曖昧にならない）
            if matches!(a, Term::Num(_)) && self.starts_implicit_factor() {
                let b = self.term_unary()?;
                a = Term::App("·".into(), vec![a, b]);
                continue;
            }
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
    fn starts_implicit_factor(&self) -> bool {
        match self.peek() {
            Some(Tok::Ident(x)) => !IMPLICIT_STOP.contains(&x.as_str()),
            Some(Tok::Sym(s)) => s == "(",
            _ => false,
        }
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
    /// 項の後ろに続く適用 t(s…)(u…)：関数を返す項を、さらに適用する
    fn term_atom(&mut self) -> PResult<Term> {
        let mut t = self.term_atom0()?;
        while self.is_sym("(") && !matches!(t, Term::Num(_)) {
            self.pos += 1;
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
            t = crate::syntax::apply_term(&t, &args);
        }
        Ok(t)
    }

    fn term_atom0(&mut self) -> PResult<Term> {
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
                // λ：(x ↦ t)・(x : ℕ ↦ t)・((x, y) ↦ t)
                let save = self.pos;
                self.pos += 1;
                if let Ok(ps) = self.binders() {
                    if self.eat_sym("↦") {
                        let body = self.term()?;
                        self.expect_sym(")")?;
                        return Ok(Term::Lam(ps, Box::new(body)));
                    }
                }
                self.pos = save + 1;
                let t = self.term()?;
                self.expect_sym(")")?;
                Ok(t)
            }
            // 集合：{x : ℕ | φ}・{(x, y) : ℕ × ℕ | φ}
            Some(Tok::Sym(s)) if s == "{" => {
                self.pos += 1;
                let ps = self.binders()?;
                self.expect_sym("|")?;
                let phi = self.formula()?;
                self.expect_sym("}")?;
                Ok(Term::Set(ps, Box::new(phi)))
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

fn decl_keyword(text: &str) -> String {
    let norm = normalize_japanese_sugar(text);
    norm.split_whitespace().next().unwrap_or("").to_string()
}

fn starts_decl(text: &str) -> bool {
    matches!(
        decl_keyword(text).as_str(),
        "thm" | "axiom" | "def" | "rec" | "notation" | "import" | "typedef"
    )
}

fn is_axiom_decl(text: &str) -> bool {
    let norm = normalize_japanese_sugar(text);
    norm.starts_with("axiom")
}

/// ファイルを読む。`import` に出会うとその場で on_import を呼ぶ（読み込み側が
/// 先のファイルを検査し、notation を登録する）。notation は宣言した行より後ろで使える。
/// 論理式の中の束縛変数とその型（量化子・λ・集合）
fn binders_f(f: &Formula, out: &mut Vec<(String, String)>) {
    match f {
        Formula::Atom(_, ts) => ts.iter().for_each(|t| binders_t(t, out)),
        Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
            binders_f(a, out);
            binders_f(b, out);
        }
        Formula::Forall(x, s, b) | Formula::Exists(x, s, b) => {
            out.push((x.clone(), s.clone()));
            binders_f(b, out);
        }
        Formula::Bot => {}
    }
}

fn binders_t(t: &Term, out: &mut Vec<(String, String)>) {
    match t {
        Term::App(_, args) => args.iter().for_each(|a| binders_t(a, out)),
        Term::Lam(ps, b) => {
            out.extend(ps.iter().cloned());
            binders_t(b, out);
        }
        Term::Set(ps, phi) => {
            out.extend(ps.iter().cloned());
            binders_f(phi, out);
        }
        _ => {}
    }
}

/// 数列の添字（a_n）を適用（a(n)）に読み替える
fn subscript_apps(decl: &mut Decl) {
    let mut vars: Vec<(String, String)> = decl
        .ctx
        .iter()
        .filter_map(|c| match c {
            CtxItem::Var(x, t) => Some((x.clone(), t.clone())),
            _ => None,
        })
        .collect();
    // ∀a:ℕ → ℝ. … のように量化子・λ・集合で束縛された数列も（その宣言の中では）数列として扱う
    let mut bound = Vec::new();
    for c in &decl.ctx {
        if let CtxItem::Hyp(_, f) = c {
            binders_f(f, &mut bound);
        }
    }
    binders_f(&decl.concl, &mut bound);
    for (x, t) in bound {
        if !vars.iter().any(|(y, _)| *y == x) {
            vars.push((x, t));
        }
    }
    let sc = SubScope::new(&vars);
    if sc.seqs.is_empty() {
        return;
    }
    for c in &mut decl.ctx {
        if let CtxItem::Hyp(_, f) = c {
            *f = sc.formula(f);
        }
    }
    decl.concl = sc.formula(&decl.concl);
    sc.stmts(&mut decl.body);
}

pub fn parse_module(
    src: &str,
    on_import: &mut dyn FnMut(&str, usize) -> PResult<()>,
) -> PResult<Module> {
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

    let mut items = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let l = &lines[i];
        if l.indent != 0 || !starts_decl(&l.text) {
            return Err(ParseError {
                line: l.no,
                msg: "トップレベルには thm・axiom・def・notation・import のどれかを書く".into(),
            });
        }
        match decl_keyword(&l.text).as_str() {
            "import" => {
                let path = parse_import(&l.text, l.no)?;
                on_import(&path, l.no)?;
                items.push(Item::Import { path });
                i += 1;
                continue;
            }
            "notation" => {
                let n = parse_notation(&l.text, l.no)?;
                with_syntax(|t| t.notations.push(n));
                items.push(Item::Notation {
                    src: l.text.clone(),
                });
                i += 1;
                continue;
            }
            "rec" => {
                // 原始再帰の定義：見出しの行と、字下げした 2 つの等式
                let no = l.no;
                let mut text = vec![l.text.clone()];
                while i + 1 < lines.len() && lines[i + 1].indent > 0 {
                    i += 1;
                    text.push(lines[i].text.clone());
                }
                i += 1;
                let generated = expand_rec(&text, no)?;
                // 行番号が rec の行に合うよう、前を空行で埋めて読む
                let padded = format!("{}{}", "\n".repeat(no.saturating_sub(1)), generated);
                let sub = parse_module(&padded, &mut |_, line| {
                    Err(ParseError { line, msg: "rec の中では import は使えない".into() })
                })?;
                let src = format!("{}\n{}", text[0], text[1..].iter().map(|t| format!("  {t}")).collect::<Vec<_>>().join("\n"));
                for it in sub.items {
                    match it {
                        Item::Def(mut d) => {
                            d.src = src.clone();
                            items.push(Item::Def(d));
                        }
                        Item::Decl(mut d) => {
                            d.generated = true;
                            d.line = no;
                            items.push(Item::Decl(d));
                        }
                        other => items.push(other),
                    }
                }
                continue;
            }
            "def" => {
                // 字下げされた続きの行も定義の本体
                let mut text = l.text.clone();
                let no = l.no;
                while i + 1 < lines.len() && lines[i + 1].indent > 0 {
                    i += 1;
                    text.push(' ');
                    text.push_str(&lines[i].text);
                }
                i += 1;
                let d = parse_def(&text, no)?;
                register_def(&d)?;
                items.push(Item::Def(d));
                continue;
            }
            _ => {}
        }
        let is_axiom = is_axiom_decl(&l.text);
        let is_typedef = decl_keyword(&l.text) == "typedef";
        // 見出し：thm は ⊢ を含む行まで、axiom は字下げされた続きの行まで、typedef は1行
        let mut header = vec![i];
        if is_typedef {
            // 1行だけ
        } else if is_axiom {
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
        let mut decl = if is_typedef {
            parse_typedef(&htext.join(" "), l.no)?
        } else {
            parse_header(&htext.join(" "), l.no, is_axiom)?
        };
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
        subscript_apps(&mut decl);
        items.push(Item::Decl(decl));
    }
    Ok(Module { items })
}

/// 論理式か項として読めれば、その LaTeX（エラーメッセージの中の式を数式として表示するため）
pub fn math_latex(s: &str) -> Option<String> {
    let s = s.trim();
    if s.is_empty() || !s.chars().any(|c| !c.is_ascii_alphabetic()) && s.len() > 12 {
        return None;
    }
    let toks = lex(s, 0).ok()?;
    let mut p = P::new(toks.clone(), 0, vec![]);
    if let Ok(f) = p.formula() {
        if p.at_end() {
            return Some(f.to_latex());
        }
    }
    let mut p = P::new(toks, 0, vec![]);
    let t = p.term().ok()?;
    p.at_end().then(|| t.to_latex())
}

/// メッセージの中の式（「…」・`…`・式だけの行）を $…$ にする
pub fn msg_latex(msg: &str) -> String {
    let mut out = Vec::new();
    for line in msg.lines() {
        let body = line.trim_start();
        let indent = &line[..line.len() - body.len()];
        // 「help:」などの見出しのあとの式だけの行、または式だけの行
        if !body.chars().any(|c| ('\u{3040}'..='\u{9fff}').contains(&c) || c == '`' || c == '「') {
            if let Some(l) = math_latex(body) {
                out.push(format!("{indent}${l}$"));
                continue;
            }
        }
        let mut res = String::new();
        let mut rest = body;
        while let Some(k) = rest.find(['「', '`']) {
            let (open, close) = if rest[k..].starts_with('「') { ("「", "」") } else { ("`", "`") };
            res.push_str(&rest[..k]);
            let after = &rest[k + open.len()..];
            match after.find(close) {
                Some(e) => {
                    let inner = &after[..e];
                    match math_latex(inner) {
                        Some(l) => res.push_str(&format!("${l}$")),
                        None => res.push_str(&format!("{open}{inner}{close}")),
                    }
                    rest = &after[e + close.len()..];
                }
                None => {
                    res.push_str(&rest[k..]);
                    rest = "";
                }
            }
        }
        res.push_str(rest);
        out.push(format!("{indent}{res}"));
    }
    out.join("\n")
}

/// import を許さない読み込み（prelude 用）
pub fn parse_standalone(src: &str) -> PResult<Module> {
    parse_module(src, &mut |_, line| {
        Err(ParseError {
            line,
            msg: "ここでは import は使えない".into(),
        })
    })
}

/// `import analysis.limits`
fn parse_import(text: &str, line: usize) -> PResult<String> {
    let mut p = P::new(lex(text, line)?, line, vec![]);
    p.ident()?;
    let path = p.ident()?;
    p.expect_end()?;
    Ok(path)
}

/// `notation a "⟶" α := is_lim(a, α)`
fn parse_notation(text: &str, line: usize) -> PResult<Notation> {
    let err = |msg: String| Err(ParseError { line, msg });
    let norm = normalize_japanese_sugar(text);
    let rest = norm.trim_start().strip_prefix("notation").unwrap_or(&norm);
    let (lhs, rest) = match rest.split_once('"') {
        Some(x) => x,
        None => return err("notation の記号は \"…\" で囲む：notation a \"⟶\" α := is_lim(a, α)".into()),
    };
    let (raw_sym, rest) = match rest.split_once('"') {
        Some(x) => x,
        None => return err("notation の記号の \" が閉じていない".into()),
    };
    let raw_sym = raw_sym.trim();
    let sym = expand_tex_macros(raw_sym).trim().to_string();
    if sym.is_empty() || sym.chars().any(|c| c.is_whitespace() || c == '"') {
        return err(format!("notation の記号「{sym}」には空白を含められない"));
    }
    // 組み込みの記号（→ < + など）と同じなら、式の読み方が変わってしまうので禁止
    if let Ok(toks) = lex_raw(&sym, line, false) {
        if let [Tok::Sym(b)] = toks.as_slice() {
            return err(format!(
                "記号「{raw_sym}」は組み込みの「{b}」と衝突する（例えば \"⟶\"（\\longrightarrow）を使う）"
            ));
        }
    }
    if notation_for_sym(&sym).is_some() {
        return err(format!("記号「{sym}」の notation はすでにある"));
    }
    let mut p = P::new(lex_raw(&expand_tex_macros(lhs), line, false)?, line, vec![]);
    let l = p.ident()?;
    p.expect_end()?;
    let mut p = P::new(lex(rest, line)?, line, vec![]);
    let r = p.ident()?;
    p.expect_sym(":=")?;
    let target = p.formula()?;
    p.expect_end()?;
    let (pred, swap) = match &target {
        Formula::Atom(pred, ts) if l != r => match ts.as_slice() {
            [Term::Var(x), Term::Var(y)] if *x == l && *y == r => (pred.clone(), false),
            [Term::Var(x), Term::Var(y)] if *x == r && *y == l => (pred.clone(), true),
            _ => return err(format!("notation の右辺は {pred}({l}, {r}) の形にする")),
        },
        _ => {
            return err(format!(
                "notation の右辺は述語の適用 P({l}, {r}) の形にする（「{target}」）"
            ));
        }
    };
    let latex = notation_latex(raw_sym, &sym);
    Ok(Notation {
        sym,
        pred,
        swap,
        latex,
    })
}

fn notation_latex(raw: &str, sym: &str) -> String {
    if raw.starts_with('\\') {
        return raw.to_string();
    }
    let known = match sym {
        "⟶" => Some("\\longrightarrow"),
        "⇝" => Some("\\rightsquigarrow"),
        "⇀" => Some("\\rightharpoonup"),
        "↦" => Some("\\mapsto"),
        "≺" => Some("\\prec"),
        "≻" => Some("\\succ"),
        "≼" => Some("\\preceq"),
        "≽" => Some("\\succeq"),
        "⊥⊥" => Some("\\perp\\!\\!\\!\\perp"),
        "~" => Some("\\sim"),
        _ => None,
    };
    match known {
        Some(k) => k.to_string(),
        None if sym.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') => {
            format!("\\mathrel{{\\mathrm{{{}}}}}", sym.replace('_', "\\_"))
        }
        None => format!("\\mathrel{{\\text{{{sym}}}}}"),
    }
}

/// `def is_lim(a : ℕ → ℝ, α : ℝ) := φ`（述語）/ `def sq(x : ℕ) : ℕ := x · x`（項）
fn parse_def(text: &str, line: usize) -> PResult<Def> {
    let mut p = P::new(lex(text, line)?, line, vec![]);
    p.ident()?; // def
    let name = p.ident()?;
    let mut params: Vec<(String, String)> = Vec::new();
    if p.eat_sym("(") && !p.eat_sym(")") {
        loop {
            let x = p.ident()?;
            let ty = if p.eat_sym(":") { p.ty()? } else { "?".to_string() };
            if params.iter().any(|(y, _)| *y == x) {
                return p.err(format!("引数 `{x}` が2回書かれている"));
            }
            params.push((x, ty));
            if p.eat_sym(")") {
                break;
            }
            p.expect_sym(",")?;
        }
    }
    let result = if p.eat_sym(":") { Some(p.ty()?) } else { None };
    p.expect_sym(":=")?;
    p.tyenv = params.iter().filter(|(_, t)| !t.contains('→') && t != "?").cloned().collect();
    let names: Vec<String> = params.iter().map(|(x, _)| x.clone()).collect();
    let is_global = |v: &str| with_syntax(|t| t.defs.contains_key(v) || t.consts.contains(v));
    let (body, term, fv) = match result.as_deref() {
        None | Some("Prop") => {
            let f = p.formula()?;
            let fv = f.free_vars();
            (f, None, fv)
        }
        Some(r) => {
            let t = p.term()?;
            let mut fv = std::collections::BTreeSet::new();
            t.vars(&mut fv);
            (Formula::Bot, Some((r.to_string(), t)), fv)
        }
    };
    p.expect_end()?;
    let sc = SubScope::new(&params);
    let (body, term, fv) = if sc.seqs.is_empty() {
        (body, term, fv)
    } else {
        let body = sc.formula(&body);
        let term = term.map(|(r, t)| (r, sc.term(&t)));
        let mut fv = body.free_vars();
        if let Some((_, t)) = &term {
            fv = std::collections::BTreeSet::new();
            t.vars(&mut fv);
        }
        (body, term, fv)
    };
    if fv.contains(&name) {
        return p.err(format!("`{name}` の定義の中で `{name}` 自身を使っている（再帰的な定義は未対応）"));
    }
    for v in fv {
        if !names.contains(&v) && !is_global(&v) {
            return p.err(format!(
                "定義の本体の `{v}` は引数でも定義済みの記号でもない（引数に加えるか、先に定義する）"
            ));
        }
    }
    Ok(Def { name, line, params, body, term, src: text.to_string() })
}

// ================================================================ 原始再帰の定義（rec）
//
//   rec sum(a : ℕ → ℝ, n : ℕ) : ℝ
//     sum(a, 0) = 0
//     sum(a, n + 1) = sum(a, n) + a_n
//
// を、選択（some）による def と、2 つの等式の定理 sum.zero・sum.succ に展開する。
// 定理の証明は prelude の rec.exists（再帰定理）と choice で、kernel が普通に検算する。

fn contains_app(t: &Term, f: &str) -> bool {
    match t {
        Term::App(g, args) => g == f || args.iter().any(|a| contains_app(a, f)),
        Term::Var(x) => x == f,
        Term::Lam(_, b) => contains_app(b, f),
        Term::Set(_, phi) => {
            let mut v = BTreeSet::new();
            phi.preds(&mut v);
            v.contains(f) || phi.free_vars().contains(f)
        }
        _ => false,
    }
}

/// t の中の app（f(…, m)）を y に置き換える
fn replace_app(t: &Term, app: &Term, y: &Term) -> Term {
    if t == app {
        return y.clone();
    }
    match t {
        Term::App(g, args) => Term::App(g.clone(), args.iter().map(|a| replace_app(a, app, y)).collect()),
        Term::Lam(ps, b) => Term::Lam(ps.clone(), Box::new(replace_app(b, app, y))),
        _ => t.clone(),
    }
}

fn expand_rec(text: &[String], line: usize) -> PResult<String> {
    let err = |msg: String| Err(ParseError { line, msg });
    let mut p = P::new(lex(&text[0], line)?, line, vec![]);
    p.ident()?; // rec
    let name = p.ident()?;
    let mut params: Vec<(String, String)> = Vec::new();
    p.expect_sym("(")?;
    loop {
        let x = p.ident()?;
        p.expect_sym(":")?;
        let ty = p.ty()?;
        params.push((x, ty));
        if p.eat_sym(")") {
            break;
        }
        p.expect_sym(",")?;
    }
    p.expect_sym(":")?;
    let res = p.ty()?;
    p.expect_end()?;
    if res.contains('→') {
        return err(format!("rec の値の型 {res} が関数の型（いまは数・命題などの型だけ）"));
    }
    if text.len() != 3 {
        return err("rec の下には、0 のときと n + 1 のときの 2 つの等式を字下げして書く".into());
    }
    let eq = |k: usize| -> PResult<(Vec<Term>, Term)> {
        let mut q = P::new(lex(&text[k], line + k)?, line + k, vec![]);
        let f = q.formula()?;
        q.expect_end()?;
        match f {
            Formula::Atom(r, ts) if r == "=" => match &ts[0] {
                Term::App(g, args) if *g == name && args.len() == params.len() => Ok((args.clone(), ts[1].clone())),
                _ => Err(ParseError { line: line + k, msg: format!("左辺は {name}(…) の形にする") }),
            },
            _ => Err(ParseError { line: line + k, msg: "等式（左辺 = 右辺）を書く".into() }),
        }
    };
    let (args0, base) = eq(1)?;
    let (args1, step) = eq(2)?;
    // 数列の添字（a_n）を先に a(n) にしておく（n の名前を置き換えるため）
    let sc = SubScope::new(&params);
    let (base, step) = (sc.term(&base), sc.term(&step));
    let Some(r) = args0.iter().position(|a| *a == Term::Num(0)) else {
        return err(format!("1 つ目の等式は、再帰する引数を 0 にした {name}(…, 0, …) = … にする"));
    };
    if params[r].1 != "ℕ" {
        return err(format!("再帰する引数 `{}` の型は ℕ にする", params[r].0));
    }
    let (m, plus_one) = match &args1[r] {
        Term::App(op, xs) if op == "+" && xs.len() == 2 && xs[1] == Term::Num(1) => match &xs[0] {
            Term::Var(m) => (m.clone(), true),
            _ => return err("2 つ目の等式は n + 1 の形にする".into()),
        },
        Term::App(op, xs) if op == "S" && xs.len() == 1 => match &xs[0] {
            Term::Var(m) => (m.clone(), false),
            _ => return err("2 つ目の等式は S(n) の形にする".into()),
        },
        _ => return err("2 つ目の等式は、再帰する引数を n + 1（または S(n)）にする".into()),
    };
    for (j, (x, _)) in params.iter().enumerate() {
        if j != r && (args0[j] != Term::Var(x.clone()) || args1[j] != Term::Var(x.clone())) {
            return err(format!("再帰しない引数は、見出しと同じ名前 `{x}` のまま書く"));
        }
    }
    if contains_app(&base, &name) {
        return err(format!("0 のときの右辺に {name} は使えない"));
    }
    // 1 つ前の値 f(…, n) を y に置き換えると、f が残らないこと（原始再帰）
    let fresh = |base: &str| {
        let mut x = base.to_string();
        while params.iter().any(|(p, _)| *p == x) || x == m {
            x.push('_');
        }
        x
    };
    let (fv, kv, yv) = (fresh("rec_F"), fresh("rec_k"), fresh("rec_y"));
    let prev = Term::App(name.clone(), params.iter().enumerate().map(|(j, (x, _))| if j == r { Term::Var(m.clone()) } else { Term::Var(x.clone()) }).collect());
    let g0 = replace_app(&step, &prev, &Term::Var(yv.clone()));
    if contains_app(&g0, &name) {
        return err(format!("n + 1 のときの右辺では、{name} は 1 つ前の値 {prev} としてだけ使える（原始再帰）"));
    }
    let g_lam = g0.subst(&m, &Term::Var(kv.clone()));
    let g_set = g_lam.subst(&yv, &Term::App(fv.clone(), vec![Term::Var(kv.clone())]));
    let set = format!("{{{fv} : ℕ → {res} | {fv}(0) = {base} ∧ ∀{kv}:ℕ. {fv}(S({kv})) = {g_set}}}");
    let lam = format!("(({kv}, {yv}) : ℕ × {res} ↦ {g_lam})");
    let rn = &params[r].0;
    let ps: Vec<String> = params.iter().map(|(x, t)| format!("{x} : {t}")).collect();
    let others: Vec<&(String, String)> = params.iter().enumerate().filter(|(j, _)| *j != r).map(|(_, p)| p).collect();
    let call = |at: &str| -> String {
        let a: Vec<String> = params.iter().enumerate().map(|(j, (x, _))| if j == r { at.to_string() } else { x.clone() }).collect();
        format!("{name}({})", a.join(", "))
    };
    let foralls = |extra: Option<&str>| -> String {
        let mut s: String = others.iter().map(|(x, t)| format!("∀{x}:{t}. ")).collect();
        if let Some(m) = extra {
            s.push_str(&format!("∀{m}:ℕ. "));
        }
        s
    };
    let fixes = |extra: Option<&str>| -> Vec<String> {
        let mut v: Vec<String> = others.iter().map(|(x, _)| x.clone()).collect();
        if let Some(m) = extra {
            v.push(m.to_string());
        }
        v
    };
    let ex = format!("choice({set}, rec.exists({base}, {lam}))");
    let mut out = format!("def {name}({}) : {res} := some({set})({rn})\n\n", ps.join(", "));
    // name.zero
    out.push_str(&format!("thm {name}.zero :\n  ⊢ {}{} = {base}\n\n", foralls(None), call("0")));
    let fx = fixes(None);
    if fx.is_empty() {
        out.push_str(&format!("and.left({ex})\n\n"));
    } else {
        out.push_str(&format!("Fix {}\n  and.left({ex})\n\n", fx.join(", ")));
    }
    // name.succ
    let lhs = if plus_one { call(&format!("{m} + 1")) } else { call(&format!("S({m})")) };
    out.push_str(&format!("thm {name}.succ :\n  ⊢ {}{lhs} = {step}\n\n", foralls(Some(&m))));
    out.push_str(&format!("Fix {}\n", fixes(Some(&m)).join(", ")));
    let core = format!("all.elim(and.right({ex}), {m})");
    if plus_one {
        out.push_str(&format!("  have rec_h : {} = {step} := {core}\n", call(&format!("S({m})"))));
        out.push_str(&format!("  have rec_e : S({m}) = {m} + 1 := ring\n"));
        out.push_str("  EQ2(rec_e, rec_h)\n");
    } else {
        out.push_str(&format!("  {core}\n"));
    }
    Ok(out)
}

/// 定義の名前を表に登録する。再帰的な定義（展開が止まらなくなる）はここで止める。
fn register_def(d: &Def) -> PResult<()> {
    let mut preds = BTreeSet::new();
    d.body.preds(&mut preds);
    if let Some((_, t)) = &d.term {
        t.vars(&mut preds);
    }
    let err = |msg: String| Err(ParseError { line: d.line, msg });
    if RELS.contains(&d.name.as_str()) {
        return err(format!("`{}` は組み込みの関係なので定義できない", d.name));
    }
    if preds.contains(&d.name) {
        return err(format!("`{}` の定義の中で `{}` 自身を使っている（再帰的な定義は未対応）", d.name, d.name));
    }
    with_syntax(|t| {
        if t.defs.contains_key(&d.name) {
            return err(format!("`{}` はすでに定義されている", d.name));
        }
        if t.def_preds.contains(&d.name) {
            return err(format!(
                "`{}` は前の定義の中で（未定義の述語として）使われているので、あとから定義できない",
                d.name
            ));
        }
        t.defs.insert(d.name.clone(), d.params.len());
        t.def_preds.extend(preds);
        Ok(())
    })
}

/// `typedef T := {x : σ | φ}`。型 T・定数 T.abs・T.rep をこの場で登録する（後ろの行で使えるように）
fn parse_typedef(text: &str, line: usize) -> PResult<Decl> {
    let mut p = P::new(lex(text, line)?, line, vec![]);
    p.ident()?; // typedef
    let name = p.ident()?;
    p.expect_sym(":=")?;
    let set = p.term()?;
    p.expect_end()?;
    let Term::Set(ps, phi) = set else {
        return p.err("typedef の右辺は {x : σ | φ} の形にする");
    };
    let [(x, ty)] = ps.as_slice() else {
        return p.err("typedef の集合の変数は1つ（{x : σ | φ}）");
    };
    if ty == "?" {
        return p.err(format!("typedef では元の型を書く（{{{x} : σ | …}}）"));
    }
    if TYPE_NAMES.contains(&name.as_str()) || name.contains('.') {
        return p.err(format!("`{name}` は型の名前に使えない"));
    }
    with_syntax(|t| {
        t.types.insert(name.clone());
        t.consts.insert(format!("{name}.abs"));
        t.consts.insert(format!("{name}.rep"));
    });
    Ok(Decl {
        is_axiom: false,
        name: name.clone(),
        line,
        ctx: vec![],
        concl: Formula::Exists(x.clone(), ty.clone(), phi),
        body: vec![],
        typedef: Some(TypeDef { name }),
        generated: false,
    })
}

/// 型として読めるもの（数の型・Prop・typedef で作った型からなる）
fn known_type(t: &Ty) -> bool {
    !t.any(&|u| match u {
        Ty::Base(b) => !TYPE_NAMES.contains(&b.as_str()) && !with_syntax(|tb| tb.types.contains(b)),
        _ => false,
    })
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
            // `x : ℕ`・`a : ℕ → ℝ`・`P : ℕ → Prop` は変数の宣言、それ以外は仮定
            let save = p.pos;
            let decl = match p.ty_expr() {
                Ok(t) if known_type(&t) && (p.is_sym(",") || p.is_sym("⊢")) => Some(t),
                _ => None,
            };
            match decl {
                Some(t) => {
                    let t = t.show();
                    if !t.contains('→') {
                        p.tyenv.push((x.clone(), t.clone()));
                    }
                    ctx.push(CtxItem::Var(x, t));
                }
                None => {
                    p.pos = save;
                    ctx.push(CtxItem::Hyp(x, p.formula()?));
                }
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
        typedef: None,
        generated: false,
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
                    Some(p.ty()?)
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
        "unfold" => {
            p.pos += 1;
            let mut names = vec![p.ident()?];
            while p.eat_sym(",") {
                names.push(p.ident()?);
            }
            let mut at = Vec::new();
            if p.is_ident("at") {
                p.pos += 1;
                at.push(p.ident()?);
                while p.eat_sym(",") {
                    at.push(p.ident()?);
                }
            }
            p.expect_end()?;
            no_children(n)?;
            StmtKind::Unfold { names, at }
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
            // `Q ∧ P by j`：関係（= ≤ など）でない命題を根拠で示す。関係なら連鎖として読む（意味は同じ）
            if !starts_chain && p.find_by().is_some() {
                let save = p.pos;
                if let Ok(f) = p.formula() {
                    let is_rel = matches!(&f, Formula::Atom(r, _) if RELS.contains(&r.as_str()));
                    if !is_rel && p.is_ident("by") {
                        p.pos += 1;
                        let just = p.just()?;
                        p.expect_end()?;
                        no_children(n)?;
                        return Ok(Stmt { line: n.no, src: n.text.clone(), kind: StmtKind::Show { ty: f, just } });
                    }
                }
                p.pos = save;
            }
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
