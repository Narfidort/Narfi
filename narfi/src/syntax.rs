//! 項・論理式の AST と、表示・代入・自由変数。

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::fmt;

/// 項。演算子も関数適用として表す（"+", "-", "·", "/", "^", "neg", "abs"）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Num(i64),
    App(String, Vec<Term>),
    /// 単一化用のメタ変数（ソースには現れない）
    Meta(u32),
}

/// 論理式。¬φ は Imp(φ, Bot) で表す。範囲付き量化子は展開して持つ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    /// 関係（"=", "<", "≤", ">", "≥", "∈" 等）または述語の適用
    Atom(String, Vec<Term>),
    Imp(Box<Formula>, Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    /// 束縛変数名・型名（"?" は型が書かれていない）・本体
    Forall(String, String, Box<Formula>),
    Exists(String, String, Box<Formula>),
    Bot,
}

pub const RELS: [&str; 17] = [
    "=", "≠", "<", "≤", ">", "≥", "∈", "∉", "⊂", "⊆", "⊃", "⊇", "≡", "≈", "∼", "≅", "∣",
];
pub const ORDER_RELS: [&str; 9] = ["<", "≤", ">", "≥", "∈", "⊂", "⊆", "⊃", "⊇"];

pub fn not(f: Formula) -> Formula {
    Formula::Imp(Box::new(f), Box::new(Formula::Bot))
}


// ---------------------------------------------------------------- 記法・定義の表
//
// notation は字句解析・構文解析・表示（Display / LaTeX）のすべてに効くので、
// スレッドごとの表に置く。読み込みの最初に reset_syntax() で空にする。

/// `notation a "⟶" α := is_lim(a, α)`。式 `t ⟶ u` は Atom(pred, [t, u]) として持つ。
#[derive(Clone, Debug)]
pub struct Notation {
    pub sym: String,
    pub pred: String,
    /// 述語の引数の順が (右辺, 左辺) のとき true
    pub swap: bool,
    pub latex: String,
}

impl Notation {
    pub fn atom(&self, lhs: Term, rhs: Term) -> Formula {
        let args = if self.swap { vec![rhs, lhs] } else { vec![lhs, rhs] };
        Formula::Atom(self.pred.clone(), args)
    }
    fn sides<'t>(&self, ts: &'t [Term]) -> (&'t Term, &'t Term) {
        if self.swap { (&ts[1], &ts[0]) } else { (&ts[0], &ts[1]) }
    }
}

#[derive(Default)]
pub struct SyntaxTable {
    pub notations: Vec<Notation>,
    /// def で定義した述語の名前 → 引数の数
    pub defs: HashMap<String, usize>,
    /// 定義の本体に現れた述語（あとから同じ名前を def して循環させないため）
    pub def_preds: BTreeSet<String>,
}

thread_local! {
    static SYNTAX: RefCell<SyntaxTable> = RefCell::new(SyntaxTable::default());
}

pub fn reset_syntax() {
    SYNTAX.with(|t| *t.borrow_mut() = SyntaxTable::default());
}

pub fn with_syntax<R>(f: impl FnOnce(&mut SyntaxTable) -> R) -> R {
    SYNTAX.with(|t| f(&mut t.borrow_mut()))
}

pub fn notation_for_sym(sym: &str) -> Option<Notation> {
    with_syntax(|t| t.notations.iter().find(|n| n.sym == sym).cloned())
}

/// 表示に使う記法（同じ述語に複数あるときは最初に宣言したもの）
pub fn notation_for_pred(pred: &str) -> Option<Notation> {
    with_syntax(|t| t.notations.iter().find(|n| n.pred == pred).cloned())
}

// ---------------------------------------------------------------- 定義・図式の具体化

/// 関数型のソート（`ℕ → ℝ`）か
pub fn is_fn_sort(s: &str) -> bool {
    s.contains('→')
}

/// 定義・図式のパラメータ params に args を同時に代入する。
/// 関数型のパラメータには関数記号の名前（`Term::Var(g)`）だけを渡せ、記号の付け替えになる。
pub fn instantiate(params: &[(String, String)], body: &Formula, args: &[Term]) -> Formula {
    let mut f = body.clone();
    let mut subs = Vec::new();
    let mut renames = Vec::new();
    for (i, ((p, sort), a)) in params.iter().zip(args).enumerate() {
        if is_fn_sort(sort) {
            if let Term::Var(g) = a {
                // 同時に付け替えるため、まずソースに現れない名前を経由する（a→b, b→c が混ざらないように）
                let tmp = format!("%f{i}");
                f = f.rename_fn(p, &tmp);
                renames.push((tmp, g.clone()));
            }
        } else {
            subs.push((p.clone(), a.clone()));
        }
    }
    for (tmp, g) in &renames {
        f = f.rename_fn(tmp, g);
    }
    f.subst_many(&subs)
}
// ---------------------------------------------------------------- 自由変数

impl Term {
    pub fn vars(&self, out: &mut BTreeSet<String>) {
        match self {
            Term::Var(x) => {
                out.insert(x.clone());
            }
            Term::App(_, args) => args.iter().for_each(|a| a.vars(out)),
            Term::Num(_) | Term::Meta(_) => {}
        }
    }
    pub fn has_meta(&self) -> bool {
        match self {
            Term::Meta(_) => true,
            Term::App(_, args) => args.iter().any(|a| a.has_meta()),
            _ => false,
        }
    }
    pub fn mentions(&self, x: &str) -> bool {
        match self {
            Term::Var(y) => y == x,
            Term::App(_, args) => args.iter().any(|a| a.mentions(x)),
            _ => false,
        }
    }
    pub fn subst(&self, x: &str, t: &Term) -> Term {
        match self {
            Term::Var(y) if y == x => t.clone(),
            Term::App(f, args) => {
                Term::App(f.clone(), args.iter().map(|a| a.subst(x, t)).collect())
            }
            _ => self.clone(),
        }
    }
    pub fn to_latex(&self) -> String {
        show_term_latex(self, 0)
    }
    /// 関数記号 old を new に付け替える（`old(t…)` と、引数として渡された `old` の両方）
    pub fn rename_fn(&self, old: &str, new: &str) -> Term {
        match self {
            Term::Var(x) if x == old => Term::Var(new.to_string()),
            Term::App(f, args) => {
                let f = if f == old { new.to_string() } else { f.clone() };
                Term::App(f, args.iter().map(|a| a.rename_fn(old, new)).collect())
            }
            _ => self.clone(),
        }
    }
}

impl Formula {
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.fv_into(&mut out, &mut Vec::new());
        out
    }
    fn fv_into(&self, out: &mut BTreeSet<String>, bound: &mut Vec<String>) {
        match self {
            Formula::Atom(_, ts) => {
                let mut s = BTreeSet::new();
                ts.iter().for_each(|t| t.vars(&mut s));
                out.extend(s.into_iter().filter(|v| !bound.contains(v)));
            }
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                a.fv_into(out, bound);
                b.fv_into(out, bound);
            }
            Formula::Forall(x, _, b) | Formula::Exists(x, _, b) => {
                bound.push(x.clone());
                b.fv_into(out, bound);
                bound.pop();
            }
            Formula::Bot => {}
        }
    }
    pub fn has_meta(&self) -> bool {
        match self {
            Formula::Atom(_, ts) => ts.iter().any(|t| t.has_meta()),
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                a.has_meta() || b.has_meta()
            }
            Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => b.has_meta(),
            Formula::Bot => false,
        }
    }

    /// 捕獲を避ける代入 φ[x := t]
    pub fn subst(&self, x: &str, t: &Term) -> Formula {
        match self {
            Formula::Atom(p, ts) => {
                Formula::Atom(p.clone(), ts.iter().map(|s| s.subst(x, t)).collect())
            }
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::And(a, b) => Formula::And(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::Forall(y, ty, b) | Formula::Exists(y, ty, b) => {
                let is_all = matches!(self, Formula::Forall(..));
                let mk = |v: String, body: Formula| {
                    if is_all {
                        Formula::Forall(v, ty.clone(), Box::new(body))
                    } else {
                        Formula::Exists(v, ty.clone(), Box::new(body))
                    }
                };
                if y == x {
                    return self.clone();
                }
                if t.mentions(y) {
                    let mut avoid = b.free_vars();
                    t.vars(&mut avoid);
                    let mut fresh = format!("{y}'");
                    while avoid.contains(&fresh) {
                        fresh.push('\'');
                    }
                    let body = b.subst(y, &Term::Var(fresh.clone()));
                    mk(fresh, body.subst(x, t))
                } else {
                    mk(y.clone(), b.subst(x, t))
                }
            }
            Formula::Bot => Formula::Bot,
        }
    }

    pub fn to_latex(&self) -> String {
        show_formula_latex(self, 0)
    }

    pub fn map_terms(&self, g: &impl Fn(&Term) -> Term) -> Formula {
        match self {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(g).collect()),
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.map_terms(g)), Box::new(b.map_terms(g))),
            Formula::And(a, b) => Formula::And(Box::new(a.map_terms(g)), Box::new(b.map_terms(g))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.map_terms(g)), Box::new(b.map_terms(g))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), t.clone(), Box::new(b.map_terms(g))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), t.clone(), Box::new(b.map_terms(g))),
            Formula::Bot => Formula::Bot,
        }
    }

    pub fn rename_fn(&self, old: &str, new: &str) -> Formula {
        self.map_terms(&|t| t.rename_fn(old, new))
    }

    /// 束縛変数の型を書き換える（図式のソート変数の具体化など）
    pub fn map_sorts(&self, g: &impl Fn(&str) -> String) -> Formula {
        match self {
            Formula::Atom(..) | Formula::Bot => self.clone(),
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::And(a, b) => Formula::And(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), g(t), Box::new(b.map_sorts(g))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), g(t), Box::new(b.map_sorts(g))),
        }
    }

    /// 同時代入 φ[x₁ := t₁, …]（tᵢ の中の変数が xⱼ と同じ名前でも混ざらない）
    pub fn subst_many(&self, subs: &[(String, Term)]) -> Formula {
        let mut f = self.clone();
        for (i, (x, _)) in subs.iter().enumerate() {
            f = f.subst(x, &Term::Var(format!("%{i}")));
        }
        for (i, (_, t)) in subs.iter().enumerate() {
            f = f.subst(&format!("%{i}"), t);
        }
        f
    }

    /// 現れる述語の名前
    pub fn preds(&self, out: &mut BTreeSet<String>) {
        match self {
            Formula::Atom(p, _) => {
                out.insert(p.clone());
            }
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                a.preds(out);
                b.preds(out);
            }
            Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => b.preds(out),
            Formula::Bot => {}
        }
    }
}

// ---------------------------------------------------------------- 表示

pub fn show_term(t: &Term, prec: u8) -> String {
    match t {
        Term::Var(x) => x.clone(),
        Term::Num(n) => n.to_string(),
        Term::Meta(m) => format!("?{m}"),
        Term::App(f, args) => {
            let (s, p) = match (f.as_str(), args.as_slice()) {
                ("+" | "-" | "∪" | "∩" | "\\", [a, b]) => {
                    (format!("{} {} {}", show_term(a, 1), f, show_term(b, 2)), 1)
                }
                ("·", [a, b]) => (format!("{}·{}", show_term(a, 2), show_term(b, 3)), 2),
                ("/", [a, b]) => (format!("{}/{}", show_term(a, 2), show_term(b, 3)), 2),
                ("neg", [a]) => (format!("-{}", show_term(a, 3)), 3),
                ("^", [a, Term::Num(2)]) => (format!("{}²", show_term(a, 5)), 4),
                ("^", [a, b]) => (format!("{}^{}", show_term(a, 5), show_term(b, 5)), 4),
                ("abs", [a]) => (format!("|{}|", show_term(a, 0)), 5),
                _ => {
                    let a: Vec<String> = args.iter().map(|a| show_term(a, 0)).collect();
                    (format!("{}({})", f, a.join(", ")), 5)
                }
            };
            if p < prec { format!("({s})") } else { s }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_term(self, 0))
    }
}

/// 範囲付き量化子の形 ∀x>t. φ / ∃x>t. φ を取り出す
pub fn bounded(x: &str, guard: &Formula) -> Option<(String, Term)> {
    if let Formula::Atom(r, ts) = guard {
        if ORDER_RELS.contains(&r.as_str())
            && ts.len() == 2
            && ts[0] == Term::Var(x.to_string())
            && !ts[1].mentions(x)
        {
            return Some((r.clone(), ts[1].clone()));
        }
    }
    None
}

/// 表示しない型：書かれていない型（?）・ソート変数（'a）・推論途中の型（?σ1）
fn hidden_sort(ty: &str) -> bool {
    ty == "?" || ty.starts_with('\'') || ty.starts_with("?σ")
}

fn binder(q: &str, x: &str, ty: &str) -> String {
    if hidden_sort(ty) {
        format!("{q}{x}")
    } else {
        format!("{q}{x}:{ty}")
    }
}

pub fn show_formula(f: &Formula, prec: u8) -> String {
    let (s, p) = match f {
        Formula::Bot => ("⊥".to_string(), 5),
        Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => (
            format!("{} {} {}", show_term(&ts[0], 0), r, show_term(&ts[1], 0)),
            5,
        ),
        Formula::Atom(p, ts) if ts.is_empty() => (p.clone(), 5),
        Formula::Atom(p, ts) if ts.len() == 2 && notation_for_pred(p).is_some() => {
            let n = notation_for_pred(p).unwrap();
            let (l, r) = n.sides(ts);
            (format!("{} {} {}", show_term(l, 0), n.sym, show_term(r, 0)), 5)
        }
        Formula::Atom(p, ts) => {
            let a: Vec<String> = ts.iter().map(|t| show_term(t, 0)).collect();
            (format!("{}({})", p, a.join(", ")), 5)
        }
        Formula::Imp(a, b) if **b == Formula::Bot => match &**a {
            Formula::Atom(r, ts) if r == "=" && ts.len() == 2 => (
                format!("{} ≠ {}", show_term(&ts[0], 0), show_term(&ts[1], 0)),
                5,
            ),
            _ => (format!("¬{}", show_formula(a, 4)), 4),
        },
        Formula::Imp(a, b) => (
            format!("{} → {}", show_formula(a, 2), show_formula(b, 1)),
            1,
        ),
        Formula::Or(a, b) => (
            format!("{} ∨ {}", show_formula(a, 2), show_formula(b, 3)),
            2,
        ),
        Formula::And(a, b) => (
            format!("{} ∧ {}", show_formula(a, 3), show_formula(b, 4)),
            3,
        ),
        Formula::Forall(x, ty, b) => {
            if let Formula::Imp(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!("∀{}{}{}. {}", x, r, show_term(&t, 0), show_formula(body, 0));
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (format!("{}. {}", binder("∀", x, ty), show_formula(b, 0)), 0)
        }
        Formula::Exists(x, ty, b) => {
            if let Formula::And(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!("∃{}{}{}. {}", x, r, show_term(&t, 0), show_formula(body, 0));
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (format!("{}. {}", binder("∃", x, ty), show_formula(b, 0)), 0)
        }
    };
    if p < prec { format!("({s})") } else { s }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_formula(self, 0))
    }
}

// ---------------------------------------------------------------- LaTeX 表示

fn greek_char_to_latex(c: char) -> Option<&'static str> {
    Some(match c {
        'α' => "\\alpha",
        'β' => "\\beta",
        'γ' => "\\gamma",
        'δ' => "\\delta",
        'ε' => "\\varepsilon",
        'ζ' => "\\zeta",
        'η' => "\\eta",
        'θ' => "\\theta",
        'ι' => "\\iota",
        'κ' => "\\kappa",
        'λ' => "\\lambda",
        'μ' => "\\mu",
        'ν' => "\\nu",
        'ξ' => "\\xi",
        'π' => "\\pi",
        'ρ' => "\\rho",
        'σ' => "\\sigma",
        'τ' => "\\tau",
        'υ' => "\\upsilon",
        'φ' => "\\varphi",
        'χ' => "\\chi",
        'ψ' => "\\psi",
        'ω' => "\\omega",
        'Γ' => "\\Gamma",
        'Δ' => "\\Delta",
        'Θ' => "\\Theta",
        'Λ' => "\\Lambda",
        'Ξ' => "\\Xi",
        'Π' => "\\Pi",
        'Σ' => "\\Sigma",
        'Υ' => "\\Upsilon",
        'Φ' => "\\Phi",
        'Ψ' => "\\Psi",
        'Ω' => "\\Omega",
        '∞' => "\\infty",
        '∅' => "\\emptyset",
        '∂' => "\\partial",
        '∇' => "\\nabla",
        _ => return None,
    })
}

pub fn ident_to_latex(s: &str) -> String {
    match s {
        "ℕ" => "\\mathbb{N}".to_string(),
        "ℤ" => "\\mathbb{Z}".to_string(),
        "ℚ" => "\\mathbb{Q}".to_string(),
        "ℝ" => "\\mathbb{R}".to_string(),
        "ℂ" => "\\mathbb{C}".to_string(),
        "𝔽" => "\\mathbb{F}".to_string(),
        "ℙ" => "\\mathbb{P}".to_string(),
        "Prop" => "\\mathrm{Prop}".to_string(),
        "max" => "\\max".to_string(),
        "min" => "\\min".to_string(),
        "sup" => "\\sup".to_string(),
        "inf" => "\\inf".to_string(),
        "sin" => "\\sin".to_string(),
        "cos" => "\\cos".to_string(),
        "tan" => "\\tan".to_string(),
        "exp" => "\\exp".to_string(),
        "log" => "\\log".to_string(),
        "ln" => "\\ln".to_string(),
        "gcd" => "\\gcd".to_string(),
        "det" => "\\det".to_string(),
        "dim" => "\\dim".to_string(),
        "ker" => "\\ker".to_string(),
        _ => {
            let cs: Vec<char> = s.chars().collect();
            // ギリシャ文字1文字
            if cs.len() == 1 {
                if let Some(gl) = greek_char_to_latex(cs[0]) {
                    return gl.to_string();
                }
                return s.to_string();
            }
            // 1文字英字 + 数字添字 (例: N₁, a₂, x₀)
            if cs.len() == 2 && cs[0].is_ascii_alphabetic() && ('₀'..='₉').contains(&cs[1]) {
                let d = (cs[1] as u32 - '₀' as u32) as u8 + b'0';
                return format!("{}_{{{}}}", cs[0], d as char);
            }
            // h + ギリシャ文字 (例: hε)
            if cs.len() == 2 && cs[0] == 'h' {
                if let Some(gl) = greek_char_to_latex(cs[1]) {
                    return format!("h_{{{gl}}}");
                }
                if cs[1].is_ascii_alphabetic() {
                    return format!("h_{{{}}}", cs[1]);
                }
            }
            // hN₁ -> h_{N_1}
            if cs.len() == 3 && s.starts_with("hN") && ('₀'..='₉').contains(&cs[2]) {
                let d = (cs[2] as u32 - '₀' as u32) as u8 + b'0';
                return format!("h_{{N_{}}}", d as char);
            }
            // ドットを含む識別子 (例: ge.max.left)
            if s.contains('.') {
                return format!("\\mathrm{{{}}}", s);
            }
            // アンダースコアを含む識別子 (例: conv_a -> \mathrm{conv}_{a}, pos_half -> \mathrm{pos\_half})
            if let Some((p, rest)) = s.split_once('_') {
                if p.len() > 1 && p.chars().all(|c| c.is_ascii_alphabetic()) {
                    if rest.len() == 1 {
                        return format!("\\mathrm{{{}}}_{{{}}}", p, rest);
                    } else {
                        return format!("\\mathrm{{{}}}", s.replace('_', "\\_"));
                    }
                }
                return format!("\\mathrm{{{}}}", s.replace('_', "\\_"));
            }
            // 2文字以上の英単語 (例: triangle, pos, etc.)
            if s.len() > 1 && s.chars().all(|c| c.is_ascii_alphabetic()) {
                return format!("\\mathrm{{{}}}", s);
            }

            let mut out = String::new();
            let mut in_sub = false;
            for (idx, &c) in cs.iter().enumerate() {
                if ('₀'..='₉').contains(&c) {
                    if !in_sub {
                        out.push_str("_{");
                        in_sub = true;
                    }
                    let d = (c as u32 - '₀' as u32) as u8 + b'0';
                    out.push(d as char);
                } else if let Some(gl) = greek_char_to_latex(c) {
                    if in_sub {
                        out.push('}');
                        in_sub = false;
                    }
                    if idx > 0 && cs[idx - 1].is_ascii_alphabetic() {
                        out.push_str(&format!("_{{{gl}}}"));
                    } else {
                        out.push_str(gl);
                        out.push(' ');
                    }
                } else {
                    if in_sub {
                        out.push('}');
                        in_sub = false;
                    }
                    match c {
                        '_' => out.push_str("\\_"),
                        _ => out.push(c),
                    }
                }
            }
            if in_sub {
                out.push('}');
            }
            out.trim_end().to_string()
        }
    }
}

pub fn rel_to_latex(r: &str) -> &str {
    match r {
        "=" => "=",
        "≠" => "\\ne",
        "<" => "<",
        "≤" => "\\le",
        ">" => ">",
        "≥" => "\\ge",
        "∈" => "\\in",
        "∉" => "\\notin",
        "⊂" => "\\subset",
        "⊆" => "\\subseteq",
        "⊃" => "\\supset",
        "⊇" => "\\supseteq",
        "≡" => "\\equiv",
        "≈" => "\\approx",
        "∼" => "\\sim",
        "≅" => "\\cong",
        "∣" => "\\mid",
        _ => r,
    }
}

pub fn show_term_latex(t: &Term, prec: u8) -> String {
    match t {
        Term::Var(x) => ident_to_latex(x),
        Term::Num(n) => n.to_string(),
        Term::Meta(m) => format!("?{m}"),
        Term::App(f, args) => {
            let (s, p) = match (f.as_str(), args.as_slice()) {
                ("+" | "-", [a, b]) => (
                    format!("{} {} {}", show_term_latex(a, 1), f, show_term_latex(b, 2)),
                    1,
                ),
                ("∪", [a, b]) => (
                    format!("{} \\cup {}", show_term_latex(a, 1), show_term_latex(b, 2)),
                    1,
                ),
                ("∩", [a, b]) => (
                    format!("{} \\cap {}", show_term_latex(a, 2), show_term_latex(b, 3)),
                    2,
                ),
                ("\\", [a, b]) => (
                    format!(
                        "{} \\setminus {}",
                        show_term_latex(a, 2),
                        show_term_latex(b, 3)
                    ),
                    2,
                ),
                ("·", [a, b]) => (
                    format!("{} \\cdot {}", show_term_latex(a, 2), show_term_latex(b, 3)),
                    2,
                ),
                ("/", [a, b]) => (
                    format!(
                        "\\frac{{{}}}{{{}}}",
                        show_term_latex(a, 0),
                        show_term_latex(b, 0)
                    ),
                    4,
                ),
                ("neg", [a]) => (format!("-{}", show_term_latex(a, 3)), 3),
                ("^", [a, b]) => (
                    format!(
                        "{{{}}}^{{{}}}",
                        show_term_latex(a, 5),
                        show_term_latex(b, 0)
                    ),
                    4,
                ),
                ("abs", [a]) => (format!("\\left| {} \\right|", show_term_latex(a, 0)), 5),
                ("norm", [a]) => (format!("\\left\\| {} \\right\\|", show_term_latex(a, 0)), 5),
                ("floor", [a]) => (
                    format!("\\left\\lfloor {} \\right\\rfloor", show_term_latex(a, 0)),
                    5,
                ),
                ("ceil", [a]) => (
                    format!("\\left\\lceil {} \\right\\rceil", show_term_latex(a, 0)),
                    5,
                ),
                ("set", [a]) => (
                    format!("\\left\\{{ {} \\right\\}}", show_term_latex(a, 0)),
                    5,
                ),
                ("inner", [a]) => (
                    format!("\\left\\langle {} \\right\\rangle", show_term_latex(a, 0)),
                    5,
                ),
                ("sqrt", [a]) => (format!("\\sqrt{{{}}}", show_term_latex(a, 0)), 5),
                ("root", [n, a]) => (
                    format!(
                        "\\sqrt[{}]{{{}}}",
                        show_term_latex(n, 0),
                        show_term_latex(a, 0)
                    ),
                    5,
                ),
                ("binom", [n, k]) => (
                    format!(
                        "\\binom{{{}}}{{{}}}",
                        show_term_latex(n, 0),
                        show_term_latex(k, 0)
                    ),
                    5,
                ),
                ("vec", [a]) => (format!("\\vec{{{}}}", show_term_latex(a, 0)), 5),
                ("hat", [a]) => (format!("\\hat{{{}}}", show_term_latex(a, 0)), 5),
                ("bar", [a]) => (format!("\\overline{{{}}}", show_term_latex(a, 0)), 5),
                ("tilde", [a]) => (format!("\\tilde{{{}}}", show_term_latex(a, 0)), 5),
                ("sum", [sub, sup, body]) => (
                    format!(
                        "\\sum_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("prod", [sub, sup, body]) => (
                    format!(
                        "\\prod_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("int", [sub, sup, body]) => (
                    format!(
                        "\\int_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("lim", [sub, body]) => (
                    format!(
                        "\\lim_{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                _ => {
                    let a: Vec<String> = args.iter().map(|a| show_term_latex(a, 0)).collect();
                    (format!("{}({})", ident_to_latex(f), a.join(", ")), 5)
                }
            };
            if p < prec {
                format!("\\left({s}\\right)")
            } else {
                s
            }
        }
    }
}

fn binder_latex(q: &str, x: &str, ty: &str) -> String {
    let xl = ident_to_latex(x);
    if hidden_sort(ty) {
        format!("{q} {xl}")
    } else {
        format!("{q} {xl} \\in {}", ident_to_latex(ty))
    }
}

pub fn show_formula_latex(f: &Formula, prec: u8) -> String {
    let (s, p) = match f {
        Formula::Bot => ("\\bot".to_string(), 5),
        Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => (
            format!(
                "{} {} {}",
                show_term_latex(&ts[0], 0),
                rel_to_latex(r),
                show_term_latex(&ts[1], 0)
            ),
            5,
        ),
        Formula::Atom(p, ts) if ts.is_empty() => (ident_to_latex(p), 5),
        Formula::Atom(p, ts) if ts.len() == 2 && notation_for_pred(p).is_some() => {
            let n = notation_for_pred(p).unwrap();
            let (l, r) = n.sides(ts);
            (
                format!("{} {} {}", show_term_latex(l, 0), n.latex, show_term_latex(r, 0)),
                5,
            )
        }
        Formula::Atom(p, ts) => {
            let a: Vec<String> = ts.iter().map(|t| show_term_latex(t, 0)).collect();
            (format!("{}({})", ident_to_latex(p), a.join(", ")), 5)
        }
        Formula::Imp(a, b) if **b == Formula::Bot => match &**a {
            Formula::Atom(r, ts) if r == "=" && ts.len() == 2 => (
                format!(
                    "{} \\ne {}",
                    show_term_latex(&ts[0], 0),
                    show_term_latex(&ts[1], 0)
                ),
                5,
            ),
            _ => (format!("\\lnot {}", show_formula_latex(a, 4)), 4),
        },
        Formula::Imp(a, b) => (
            format!(
                "{} \\to {}",
                show_formula_latex(a, 2),
                show_formula_latex(b, 1)
            ),
            1,
        ),
        Formula::Or(a, b) => (
            format!(
                "{} \\lor {}",
                show_formula_latex(a, 2),
                show_formula_latex(b, 3)
            ),
            2,
        ),
        Formula::And(a, b) => (
            format!(
                "{} \\land {}",
                show_formula_latex(a, 3),
                show_formula_latex(b, 4)
            ),
            3,
        ),
        Formula::Forall(x, ty, b) => {
            if let Formula::Imp(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!(
                        "\\forall {} {} {},\\ {}",
                        ident_to_latex(x),
                        rel_to_latex(&r),
                        show_term_latex(&t, 0),
                        show_formula_latex(body, 0)
                    );
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (
                format!(
                    "{},\\ {}",
                    binder_latex("\\forall", x, ty),
                    show_formula_latex(b, 0)
                ),
                0,
            )
        }
        Formula::Exists(x, ty, b) => {
            if let Formula::And(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!(
                        "\\exists {} {} {},\\ {}",
                        ident_to_latex(x),
                        rel_to_latex(&r),
                        show_term_latex(&t, 0),
                        show_formula_latex(body, 0)
                    );
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (
                format!(
                    "{},\\ {}",
                    binder_latex("\\exists", x, ty),
                    show_formula_latex(b, 0)
                ),
                0,
            )
        }
    };
    if p < prec { format!("({s})") } else { s }
}
