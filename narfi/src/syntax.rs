//! 項・論理式の AST と、表示・代入・自由変数。

use std::collections::BTreeSet;
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

pub fn types_compatible(a: &str, b: &str) -> bool {
    a == b || a == "?" || b == "?"
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

    /// A ∧ (B ∧ C) を [A, B, C] に（最大 n 個）
    pub fn split_and(&self, n: usize) -> Option<Vec<Formula>> {
        let mut out = Vec::new();
        let mut cur = self.clone();
        while out.len() + 1 < n {
            match cur {
                Formula::And(a, b) => {
                    out.push(*a);
                    cur = *b;
                }
                _ => return None,
            }
        }
        out.push(cur);
        Some(out)
    }

    pub fn to_latex(&self) -> String {
        show_formula_latex(self, 0)
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

fn binder(q: &str, x: &str, ty: &str) -> String {
    if ty == "?" {
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
    if ty == "?" {
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
