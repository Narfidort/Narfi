//! kernel の環境：ソート・シグネチャ・定義・定理の図式と、型付け（仕様 §1〜§3）・
//! 定義的等しさ（仕様 §6）。

use crate::syntax::{Formula, Term, instantiate, is_fn_sort};
use std::collections::{BTreeMap, BTreeSet, HashMap};

// ================================================================ ソート

pub const NUM_SORTS: [&str; 4] = ["ℕ", "ℤ", "ℚ", "ℝ"];

/// 数のソートの順位（ℕ=0, ℤ=1, ℚ=2, ℝ=3）
pub fn num_rank(s: &str) -> Option<u8> {
    NUM_SORTS.iter().position(|x| *x == s).map(|i| i as u8)
}

/// 組み込みの算術演算が使える最小のソート（仕様 §2.1）。演算でなければ None。
pub fn op_min_rank(f: &str, arity: usize) -> Option<u8> {
    match (f, arity) {
        ("+" | "·" | "max" | "min", 2) => Some(0),
        ("-", 2) | ("neg" | "abs", 1) => Some(1),
        ("/", 2) => Some(2),
        _ => None,
    }
}

pub const ORDER_RELS: [&str; 4] = ["<", "≤", ">", "≥"];

pub fn is_builtin_fn(f: &str) -> bool {
    matches!(f, "+" | "·" | "max" | "min" | "-" | "neg" | "abs" | "/" | "S" | "^")
}

/// 関数記号の型 σ₁ × … × σₙ → σ
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSig {
    pub args: Vec<String>,
    pub res: String,
}

impl FnSig {
    /// `ℕ → ℝ` / `ℕ × ℕ → ℝ`
    pub fn parse(s: &str) -> Option<FnSig> {
        let (a, r) = s.split_once('→')?;
        let args: Vec<String> = a.split('×').map(|x| x.trim().to_string()).collect();
        let res = r.trim().to_string();
        if args.iter().any(|x| x.is_empty()) || res.is_empty() || res.contains('→') {
            return None;
        }
        Some(FnSig { args, res })
    }
    pub fn show(&self) -> String {
        format!("{} → {}", self.args.join(" × "), self.res)
    }
}

/// 定理ごとの局所記号（仕様 §2.2）
#[derive(Clone, Default, Debug)]
pub struct LocalSig {
    pub fns: BTreeMap<String, FnSig>,
    pub preds: BTreeMap<String, Vec<String>>,
}

// ================================================================ 定義・図式・環境

#[derive(Clone, Debug)]
pub struct KDef {
    pub params: Vec<(String, String)>,
    pub body: Formula,
}

/// 定理・公理の図式（仕様 §8）
#[derive(Clone, Debug)]
pub struct Schema {
    pub sort_params: Vec<String>,
    /// 文の自由変数と局所関数記号（型が `ℕ → ℝ` の形なら関数記号）
    pub params: Vec<(String, String)>,
    /// 文の局所述語記号（v2.0 では同じ名前でしか具体化できない）
    pub preds: Vec<(String, Vec<String>)>,
    /// 仮定を → でつないだ文
    pub formula: Formula,
    pub is_axiom: bool,
    /// prelude の公理（等号・ペアノ）
    pub core: bool,
    pub deps: Deps,
}

/// 証明が何に依存したか（kernel が数える）
#[derive(Clone, Debug, Default)]
pub struct Deps {
    /// 利用者の公理（推移的に）
    pub axioms: BTreeSet<String>,
    /// 使った算術の規則（ring・linarith・decide）
    pub arith: BTreeSet<String>,
    pub sorry: bool,
}

impl Deps {
    pub fn extend(&mut self, o: &Deps) {
        self.axioms.extend(o.axioms.iter().cloned());
        self.arith.extend(o.arith.iter().cloned());
        self.sorry |= o.sorry;
    }
}

#[derive(Default)]
pub struct KEnv {
    pub defs: HashMap<String, KDef>,
    pub thms: HashMap<String, Schema>,
}

#[derive(Debug, Clone)]
pub struct KError {
    pub line: Option<usize>,
    pub msg: String,
}

pub type KResult<T> = Result<T, KError>;

pub fn kerr<T>(msg: impl Into<String>) -> KResult<T> {
    Err(KError { line: None, msg: msg.into() })
}

// ================================================================ 文脈と型付け

/// kernel の文脈 Γ（仕様 §4）
pub struct KCtx<'a> {
    pub env: &'a KEnv,
    pub sig: &'a LocalSig,
    pub sort_params: &'a [String],
    pub vars: Vec<(String, String)>,
    pub lets: Vec<(String, String, Term)>,
    pub hyps: Vec<(String, Formula)>,
    fresh: u32,
}

/// 項の型。数字だけの項は型が決まらず、使われた演算の最小の順位だけを持つ（仕様 §3.2）。
#[derive(Clone, Debug, PartialEq)]
enum TSort {
    Known(String),
    Lit(u8),
}

impl<'a> KCtx<'a> {
    pub fn new(env: &'a KEnv, sig: &'a LocalSig, sort_params: &'a [String]) -> KCtx<'a> {
        KCtx { env, sig, sort_params, vars: vec![], lets: vec![], hyps: vec![], fresh: 0 }
    }

    pub fn var_sort(&self, x: &str) -> Option<String> {
        self.vars
            .iter()
            .rev()
            .find(|(y, _)| y == x)
            .map(|(_, s)| s.clone())
            .or_else(|| self.lets.iter().rev().find(|(y, ..)| y == x).map(|(_, s, _)| s.clone()))
    }

    pub fn valid_sort(&self, s: &str) -> bool {
        num_rank(s).is_some() || self.sort_params.iter().any(|p| p == s)
    }

    /// 新しく導入する変数名が使えるか（固有変数条件の半分。残りは各規則で見る）
    pub fn fresh_var(&self, x: &str) -> KResult<()> {
        if self.var_sort(x).is_some() {
            return kerr(format!("変数 `{x}` はすでに文脈にある"));
        }
        if self.sig.fns.contains_key(x) || self.sig.preds.contains_key(x) || self.env.defs.contains_key(x) {
            return kerr(format!("`{x}` は記号の名前なので変数には使えない"));
        }
        Ok(())
    }

    fn infer_t(&self, t: &Term) -> KResult<TSort> {
        match t {
            Term::Meta(_) => kerr("決まっていない項（メタ変数）が残っている"),
            Term::Num(_) => Ok(TSort::Lit(0)),
            Term::Var(x) => match self.var_sort(x) {
                Some(s) => Ok(TSort::Known(s)),
                None if self.sig.fns.contains_key(x) => {
                    kerr(format!("関数記号 `{x}` を値として使うことはできない"))
                }
                None => kerr(format!("変数 `{x}` が文脈にない")),
            },
            Term::App(f, args) => {
                if let Some(min) = op_min_rank(f, args.len()) {
                    return self.infer_op(f, args, min);
                }
                match (f.as_str(), args.as_slice()) {
                    ("S", [a]) => {
                        self.check_t(a, "ℕ")?;
                        Ok(TSort::Known("ℕ".into()))
                    }
                    ("^", [a, e]) => {
                        self.check_t(e, "ℕ")?;
                        self.infer_op("^", std::slice::from_ref(a), 0)
                    }
                    _ => {
                        let Some(sig) = self.sig.fns.get(f) else {
                            return kerr(format!("関数記号 `{f}` が宣言されていない"));
                        };
                        if sig.args.len() != args.len() {
                            return kerr(format!("`{f}` の引数は {} 個", sig.args.len()));
                        }
                        for (a, s) in args.iter().zip(&sig.args) {
                            self.check_t(a, s)?;
                        }
                        Ok(TSort::Known(sig.res.clone()))
                    }
                }
            }
        }
    }

    /// 算術演算：引数はすべて同じソートで、そのソートで演算が使えること
    fn infer_op(&self, f: &str, args: &[Term], min: u8) -> KResult<TSort> {
        let mut known: Option<String> = None;
        let mut lit = min;
        for a in args {
            match self.infer_t(a)? {
                TSort::Known(s) => match &known {
                    Some(k) if *k != s => return kerr(format!("`{f}` の両辺の型が違う（{k} と {s}）")),
                    _ => known = Some(s),
                },
                TSort::Lit(r) => lit = lit.max(r),
            }
        }
        match known {
            None => Ok(TSort::Lit(lit)),
            Some(s) => match num_rank(&s) {
                Some(r) if r >= lit => Ok(TSort::Known(s)),
                _ => kerr(format!("演算 `{f}` は {s} では使えない")),
            },
        }
    }

    pub fn check_t(&self, t: &Term, s: &str) -> KResult<()> {
        match self.infer_t(t)? {
            TSort::Known(k) if k == s => Ok(()),
            TSort::Known(k) => kerr(format!("項 `{t}` の型は {k} だが、{s} が必要")),
            TSort::Lit(r) => match num_rank(s) {
                Some(q) if q >= r => Ok(()),
                _ => kerr(format!("数の項 `{t}` を {s} として読めない")),
            },
        }
    }

    /// 関係の両辺の共通のソート（数字だけなら None）
    pub fn rel_sort(&self, r: &str, a: &Term, b: &Term) -> KResult<Option<String>> {
        let s = match (self.infer_t(a)?, self.infer_t(b)?) {
            (TSort::Known(x), _) => {
                self.check_t(b, &x)?;
                Some(x)
            }
            (_, TSort::Known(y)) => {
                self.check_t(a, &y)?;
                Some(y)
            }
            _ => None,
        };
        if ORDER_RELS.contains(&r) {
            if let Some(x) = &s {
                if num_rank(x).is_none() {
                    return kerr(format!("`{r}` は数のソートにしか使えない（{x}）"));
                }
            }
        }
        Ok(s)
    }

    /// 論理式が型として正しいか（仕様 §3.1）
    pub fn check_f(&mut self, f: &Formula) -> KResult<()> {
        match f {
            Formula::Bot => Ok(()),
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                self.check_f(a)?;
                self.check_f(b)
            }
            Formula::Forall(x, s, b) | Formula::Exists(x, s, b) => {
                if !self.valid_sort(s) {
                    return kerr(format!("束縛変数 `{x}` の型 `{s}` が正しくない"));
                }
                self.vars.push((x.clone(), s.clone()));
                let r = self.check_f(b);
                self.vars.pop();
                r
            }
            Formula::Atom(r, ts) if r == "=" || ORDER_RELS.contains(&r.as_str()) => match ts.as_slice() {
                [a, b] => self.rel_sort(r, a, b).map(|_| ()),
                _ => kerr(format!("`{r}` の引数は2つ")),
            },
            Formula::Atom(p, ts) => {
                if let Some(d) = self.env.defs.get(p) {
                    if d.params.len() != ts.len() {
                        return kerr(format!("`{p}` の引数は {} 個", d.params.len()));
                    }
                    for ((_, s), t) in d.params.iter().zip(ts) {
                        self.check_arg(t, s)?;
                    }
                    return Ok(());
                }
                let Some(sorts) = self.sig.preds.get(p) else {
                    return kerr(format!("述語 `{p}` が宣言されていない"));
                };
                if sorts.len() != ts.len() {
                    return kerr(format!("`{p}` の引数は {} 個", sorts.len()));
                }
                for (t, s) in ts.iter().zip(sorts) {
                    self.check_t(t, s)?;
                }
                Ok(())
            }
        }
    }

    /// 定義・図式の引数：関数型のパラメータには、同じ型の関数記号の名前だけを渡せる
    pub fn check_arg(&self, t: &Term, s: &str) -> KResult<()> {
        if !is_fn_sort(s) {
            return self.check_t(t, s);
        }
        let want = FnSig::parse(s).ok_or_else(|| KError { line: None, msg: format!("型 `{s}` が読めない") })?;
        match t {
            Term::Var(g) => match self.sig.fns.get(g) {
                Some(have) if *have == want => Ok(()),
                Some(have) => kerr(format!("関数記号 `{g}` の型は {} だが、{} が必要", have.show(), want.show())),
                None => kerr(format!("`{g}` は関数記号ではない（{s} の引数には関数記号を渡す）")),
            },
            _ => kerr(format!("{s} の引数には関数記号の名前だけを渡せる（`{t}` は v2.0 では渡せない）")),
        }
    }

    // ------------------------------------------------ 定義的等しさ（仕様 §6）

    /// ζ：let を展開する
    pub fn expand_lets_f(&self, f: &Formula) -> Formula {
        let mut f = f.clone();
        for (x, _, t) in self.lets.iter().rev() {
            f = f.subst(x, t);
        }
        f
    }

    pub fn expand_lets_t(&self, t: &Term) -> Term {
        let mut t = t.clone();
        for (x, _, u) in self.lets.iter().rev() {
            t = t.subst(x, u);
        }
        t
    }

    /// δ：先頭の定義を1段展開する
    pub fn unfold_head(&self, f: &Formula) -> Option<Formula> {
        match f {
            Formula::Atom(p, ts) => {
                let d = self.env.defs.get(p)?;
                (d.params.len() == ts.len()).then(|| instantiate(&d.params, &d.body, ts))
            }
            _ => None,
        }
    }

    /// whnf：先頭が定義である限り展開する
    pub fn whnf(&self, f: &Formula) -> Formula {
        let mut f = f.clone();
        while let Some(g) = self.unfold_head(&f) {
            f = g;
        }
        f
    }

    fn unfold_all(&self, f: &Formula) -> Formula {
        let go = |g: &Formula| self.unfold_all(g);
        match f {
            Formula::Atom(..) => match self.unfold_head(f) {
                Some(g) => go(&g),
                None => f.clone(),
            },
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => Formula::Imp(Box::new(go(a)), Box::new(go(b))),
            Formula::And(a, b) => Formula::And(Box::new(go(a)), Box::new(go(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(go(a)), Box::new(go(b))),
            Formula::Forall(x, s, b) => Formula::Forall(x.clone(), s.clone(), Box::new(go(b))),
            Formula::Exists(x, s, b) => Formula::Exists(x.clone(), s.clone(), Box::new(go(b))),
        }
    }

    fn alpha_eq(&mut self, a: &Formula, b: &Formula) -> bool {
        use Formula::*;
        match (a, b) {
            (Atom(p, ts), Atom(q, us)) => p == q && ts == us,
            (Imp(a1, b1), Imp(a2, b2)) | (And(a1, b1), And(a2, b2)) | (Or(a1, b1), Or(a2, b2)) => {
                self.alpha_eq(a1, a2) && self.alpha_eq(b1, b2)
            }
            (Forall(x, s, b1), Forall(y, t, b2)) | (Exists(x, s, b1), Exists(y, t, b2)) => {
                if s != t {
                    return false;
                }
                self.fresh += 1;
                let v = Term::Var(format!("#{}", self.fresh));
                self.alpha_eq(&b1.subst(x, &v), &b2.subst(y, &v))
            }
            (Bot, Bot) => true,
            _ => false,
        }
    }

    /// φ ≡ ψ（α・δ・ζ）
    pub fn conv(&mut self, a: &Formula, b: &Formula) -> bool {
        let a = self.unfold_all(&self.expand_lets_f(a));
        let b = self.unfold_all(&self.expand_lets_f(b));
        self.alpha_eq(&a, &b)
    }

    /// 項の等しさ（ζ）
    pub fn term_eq(&self, a: &Term, b: &Term) -> bool {
        self.expand_lets_t(a) == self.expand_lets_t(b)
    }
}

// ================================================================ 図式の具体化

impl Schema {
    /// ソート σs・項 ts で具体化した文（型の検査は呼び出し側で行う）
    pub fn instance(&self, sorts: &[String]) -> (Vec<(String, String)>, Vec<(String, Vec<String>)>, Formula) {
        let sub = |s: &str| -> String {
            let mut out = s.to_string();
            for (p, q) in self.sort_params.iter().zip(sorts) {
                // 型の文字列（`'a`、`'a → ℝ` など）の中のソート変数を置き換える
                out = out
                    .split(' ')
                    .map(|w| if w == p { q.as_str() } else { w })
                    .collect::<Vec<_>>()
                    .join(" ");
            }
            out
        };
        let params = self.params.iter().map(|(x, s)| (x.clone(), sub(s))).collect();
        let preds = self.preds.iter().map(|(p, ss)| (p.clone(), ss.iter().map(|s| sub(s)).collect())).collect();
        let formula = self.formula.map_sorts(&|s| sub(s));
        (params, preds, formula)
    }
}
