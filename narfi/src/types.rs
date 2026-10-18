//! 型（単純型理論の型）。
//!
//! ```text
//! σ ::= ℕ | ℤ | ℚ | ℝ | T（typedef で作った型）   基本型
//!     | Prop                                         命題の型
//!     | σ₁ × … × σₙ → τ                             関数型（τ が Prop なら述語・集合）
//!     | 'a                                           型変数（定理の図式の中だけ）
//! ```
//!
//! 構文木（Formula・Term）の中では、型を「正規形の文字列」で持つ（`Ty::show` の出力）。
//! 比べるときは文字列のまま比べてよい（正規形なので、同じ型なら同じ文字列になる）。

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Base(String),
    Prop,
    Fun(Vec<Ty>, Box<Ty>),
    /// 型変数 `'a`（図式のパラメータ）
    Param(String),
    /// 推論途中の型 `?σ3`（elab の中だけ）
    Meta(String),
    /// 書かれていない型 `?`
    Unknown,
}

fn atom_str(t: &Ty) -> String {
    match t {
        Ty::Fun(..) => format!("({})", t.show()),
        _ => t.show(),
    }
}

impl Ty {
    pub fn show(&self) -> String {
        match self {
            Ty::Base(s) | Ty::Param(s) | Ty::Meta(s) => s.clone(),
            Ty::Prop => "Prop".into(),
            Ty::Unknown => "?".into(),
            Ty::Fun(args, res) => {
                let a: Vec<String> = args.iter().map(atom_str).collect();
                format!("{} → {}", a.join(" × "), atom_str(res))
            }
        }
    }

    /// 正規形の文字列（と、人が書いた `ℕ→ℝ` のような空白のない形）を読む
    pub fn parse(s: &str) -> Option<Ty> {
        let toks = tokenize(s);
        let mut i = 0;
        let t = parse_ty(&toks, &mut i)?;
        (i == toks.len()).then_some(t)
    }

    pub fn fun(args: Vec<Ty>, res: Ty) -> Ty {
        Ty::Fun(args, Box::new(res))
    }

    /// 部分の型を置き換える（型変数の具体化・推論途中の型の解決など）
    pub fn map(&self, g: &impl Fn(&Ty) -> Option<Ty>) -> Ty {
        if let Some(t) = g(self) {
            return t;
        }
        match self {
            Ty::Fun(args, res) => Ty::Fun(args.iter().map(|a| a.map(g)).collect(), Box::new(res.map(g))),
            _ => self.clone(),
        }
    }

    pub fn any(&self, p: &impl Fn(&Ty) -> bool) -> bool {
        p(self)
            || match self {
                Ty::Fun(args, res) => args.iter().any(|a| a.any(p)) || res.any(p),
                _ => false,
            }
    }
}

/// 型の文字列の中の部分を置き換える（読めなければそのまま）
pub fn map_ty_str(s: &str, g: &impl Fn(&Ty) -> Option<Ty>) -> String {
    match Ty::parse(s) {
        Some(t) => t.map(g).show(),
        None => s.to_string(),
    }
}

fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        if c.is_whitespace() || matches!(c, '(' | ')' | '×' | '→') {
            if !cur.is_empty() {
                out.push(std::mem::take(&mut cur));
            }
            if !c.is_whitespace() {
                out.push(c.to_string());
            }
        } else {
            cur.push(c);
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse_atom(t: &[String], i: &mut usize) -> Option<Ty> {
    let tok = t.get(*i)?;
    *i += 1;
    Some(match tok.as_str() {
        "(" => {
            let ty = parse_ty(t, i)?;
            if t.get(*i)? != ")" {
                return None;
            }
            *i += 1;
            ty
        }
        ")" | "×" | "→" => return None,
        "Prop" => Ty::Prop,
        "?" => Ty::Unknown,
        s if s.starts_with('\'') => Ty::Param(s.into()),
        s if s.starts_with("?σ") => Ty::Meta(s.into()),
        s => Ty::Base(s.into()),
    })
}

fn parse_ty(t: &[String], i: &mut usize) -> Option<Ty> {
    let mut args = vec![parse_atom(t, i)?];
    while t.get(*i).map(|s| s.as_str()) == Some("×") {
        *i += 1;
        args.push(parse_atom(t, i)?);
    }
    if t.get(*i).map(|s| s.as_str()) == Some("→") {
        *i += 1;
        let res = parse_ty(t, i)?;
        return Some(Ty::Fun(args, Box::new(res)));
    }
    // 積の型だけ（`ℕ × ℕ`）は値の型にならない
    if args.len() == 1 { args.pop() } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        for s in ["ℕ", "Prop", "ℕ → ℝ", "ℕ × ℕ → Prop", "(ℕ → ℚ) → Prop", "ℕ → (ℕ → ℕ)", "'a → Prop"] {
            assert_eq!(Ty::parse(s).unwrap().show(), s);
        }
        assert_eq!(Ty::parse("ℕ→ℝ").unwrap().show(), "ℕ → ℝ");
        assert_eq!(Ty::parse("((ℕ → ℚ) → Prop)").unwrap().show(), "(ℕ → ℚ) → Prop");
        assert!(Ty::parse("ℕ × ℕ").is_none());
        assert!(Ty::parse("ℕ →").is_none());
    }
}
