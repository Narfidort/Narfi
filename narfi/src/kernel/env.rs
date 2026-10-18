//! kernel の環境：型・定義・定理の図式と、型付け（仕様 §1〜§3）・定義的等しさ（仕様 §6）。

use crate::syntax::{Formula, Term, instantiate};
use crate::types::{Ty, map_ty_str};
use std::collections::{BTreeSet, HashMap};

// ================================================================ 型

pub const NUM_SORTS: [&str; 4] = ["ℕ", "ℤ", "ℚ", "ℝ"];

/// 数の型の順位（ℕ=0, ℤ=1, ℚ=2, ℝ=3）
pub fn num_rank(s: &str) -> Option<u8> {
    NUM_SORTS.iter().position(|x| *x == s).map(|i| i as u8)
}

fn ty_rank(t: &Ty) -> Option<u8> {
    match t {
        Ty::Base(s) => num_rank(s),
        _ => None,
    }
}

/// 組み込みの算術演算が使える最小の型（仕様 §2.1）。演算でなければ None。
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
    matches!(f, "+" | "·" | "max" | "min" | "-" | "neg" | "abs" | "/" | "S" | "^" | "some")
}

// ================================================================ 定義・図式・環境

#[derive(Clone, Debug)]
pub enum DefBody {
    /// 述語の定義 P(x…) := φ
    Pred(Formula),
    /// 項の定義 f(x…) : τ := t
    Term(String, Term),
}

#[derive(Clone, Debug)]
pub struct KDef {
    pub params: Vec<(String, String)>,
    pub body: DefBody,
}

/// 定理・公理の図式（仕様 §8）
#[derive(Clone, Debug)]
pub struct Schema {
    pub type_params: Vec<String>,
    /// 文の自由変数（関数型・述語型の変数も含む）
    pub params: Vec<(String, String)>,
    /// 仮定を → でつないだ文
    pub formula: Formula,
    pub is_axiom: bool,
    /// prelude の公理（等号・ペアノ・外延性・選択）
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
    /// typedef で作った型
    pub types: BTreeSet<String>,
    /// typedef で作った定数（名前 → 型）
    pub consts: HashMap<String, String>,
}

impl KEnv {
    /// 大域的な名前（定義・typedef の定数）か
    pub fn is_global(&self, n: &str) -> bool {
        self.defs.contains_key(n) || self.consts.contains_key(n) || is_builtin_fn(n)
    }
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
    pub type_params: &'a [String],
    pub vars: Vec<(String, String)>,
    pub lets: Vec<(String, String, Term)>,
    pub hyps: Vec<(String, Formula)>,
    fresh: u32,
}

/// 項の型。数字だけの項は型が決まらず、使われた演算の最小の順位だけを持つ（仕様 §3.2）。
#[derive(Clone, Debug, PartialEq)]
enum TSort {
    Known(Ty),
    Lit(u8),
}

fn parse_ty(s: &str) -> KResult<Ty> {
    Ty::parse(s).ok_or_else(|| KError { line: None, msg: format!("型 `{s}` が読めない") })
}

impl<'a> KCtx<'a> {
    pub fn new(env: &'a KEnv, type_params: &'a [String]) -> KCtx<'a> {
        KCtx { env, type_params, vars: vec![], lets: vec![], hyps: vec![], fresh: 0 }
    }

    pub fn var_sort(&self, x: &str) -> Option<String> {
        self.vars
            .iter()
            .rev()
            .find(|(y, _)| y == x)
            .map(|(_, s)| s.clone())
            .or_else(|| self.lets.iter().rev().find(|(y, ..)| y == x).map(|(_, s, _)| s.clone()))
    }

    pub fn valid_ty(&self, t: &Ty) -> bool {
        match t {
            Ty::Base(s) => num_rank(s).is_some() || self.env.types.contains(s),
            Ty::Prop => true,
            Ty::Param(p) => self.type_params.iter().any(|q| q == p),
            Ty::Fun(args, res) => args.iter().all(|a| self.valid_ty(a)) && self.valid_ty(res),
            Ty::Meta(_) | Ty::Unknown => false,
        }
    }

    pub fn valid_sort(&self, s: &str) -> bool {
        Ty::parse(s).is_some_and(|t| self.valid_ty(&t))
    }

    /// 新しく導入する変数名が使えるか（固有変数条件の半分。残りは各規則で見る）
    pub fn fresh_var(&self, x: &str) -> KResult<()> {
        if self.var_sort(x).is_some() {
            return kerr(format!("変数 `{x}` はすでに文脈にある"));
        }
        if self.env.is_global(x) {
            return kerr(format!("`{x}` は定義・定数の名前なので変数には使えない"));
        }
        Ok(())
    }

    fn infer_t(&mut self, t: &Term) -> KResult<TSort> {
        match t {
            Term::Meta(_) => kerr("決まっていない項（メタ変数）が残っている"),
            Term::Num(_) => Ok(TSort::Lit(0)),
            Term::Var(x) => {
                if let Some(s) = self.var_sort(x) {
                    return Ok(TSort::Known(parse_ty(&s)?));
                }
                if let Some(s) = self.env.consts.get(x) {
                    return Ok(TSort::Known(parse_ty(s)?));
                }
                if let Some(KDef { params, body: DefBody::Term(s, _) }) = self.env.defs.get(x) {
                    if params.is_empty() {
                        return Ok(TSort::Known(parse_ty(s)?));
                    }
                }
                kerr(format!("変数 `{x}` が文脈にない"))
            }
            Term::App(f, args) => {
                if let Some(min) = op_min_rank(f, args.len()) {
                    return self.infer_op(f, args, min);
                }
                match (f.as_str(), args.as_slice()) {
                    ("S", [a]) => {
                        self.check_t(a, &Ty::Base("ℕ".into()))?;
                        Ok(TSort::Known(Ty::Base("ℕ".into())))
                    }
                    ("^", [a, e]) => {
                        self.check_t(e, &Ty::Base("ℕ".into()))?;
                        self.infer_op("^", std::slice::from_ref(a), 0)
                    }
                    // 選択：some(P) は P を満たすものがあれば、その1つ（仕様 §8 の choice）
                    ("some", [p]) => match self.infer_t(p)? {
                        TSort::Known(Ty::Fun(a, r)) if a.len() == 1 && *r == Ty::Prop => Ok(TSort::Known(a[0].clone())),
                        other => kerr(format!("some の引数は述語（σ → Prop）でなければならない（{other:?}）")),
                    },
                    // 一般の適用 @(f, s…)：f の型が σ₁ × … → τ（τ ≠ Prop）
                    ("@", [h, rest @ ..]) => match self.infer_t(h)? {
                        TSort::Known(Ty::Fun(ps, r)) if *r != Ty::Prop && ps.len() == rest.len() => {
                            for (a, s) in rest.iter().zip(&ps) {
                                self.check_t(a, s)?;
                            }
                            Ok(TSort::Known(*r))
                        }
                        _ => kerr(format!("`{t}` は適用できない形をしている")),
                    },
                    _ => {
                        let fty = if let Some(s) = self.var_sort(f) {
                            parse_ty(&s)?
                        } else if let Some(s) = self.env.consts.get(f) {
                            parse_ty(s)?
                        } else if let Some(KDef { params, body: DefBody::Term(r, _) }) = self.env.defs.get(f) {
                            let ps: KResult<Vec<Ty>> = params.iter().map(|(_, s)| parse_ty(s)).collect();
                            Ty::fun(ps?, parse_ty(r)?)
                        } else {
                            return kerr(format!("関数 `{f}` が文脈にない"));
                        };
                        let Ty::Fun(ps, r) = fty else {
                            return kerr(format!("`{f}` は関数ではない"));
                        };
                        if *r == Ty::Prop {
                            return kerr(format!("`{f}` は述語なので、項の中では使えない"));
                        }
                        if ps.len() != args.len() {
                            return kerr(format!("`{f}` の引数は {} 個", ps.len()));
                        }
                        for (a, s) in args.iter().zip(&ps) {
                            self.check_t(a, s)?;
                        }
                        Ok(TSort::Known(*r))
                    }
                }
            }
            Term::Lam(ps, body) => {
                let tys = self.push_binders(ps)?;
                let r = self.infer_t(body);
                self.vars.truncate(self.vars.len() - ps.len());
                match r? {
                    TSort::Known(res) => Ok(TSort::Known(Ty::fun(tys, res))),
                    TSort::Lit(_) => kerr(format!("λ `{t}` の値の型が決まらない")),
                }
            }
            Term::Set(ps, phi) => {
                let tys = self.push_binders(ps)?;
                let r = self.check_f(phi);
                self.vars.truncate(self.vars.len() - ps.len());
                r?;
                Ok(TSort::Known(Ty::fun(tys, Ty::Prop)))
            }
        }
    }

    fn push_binders(&mut self, ps: &[(String, String)]) -> KResult<Vec<Ty>> {
        let mut tys = Vec::new();
        for (p, s) in ps {
            let t = parse_ty(s)?;
            if !self.valid_ty(&t) {
                return kerr(format!("束縛変数 `{p}` の型 `{s}` が正しくない"));
            }
            tys.push(t);
        }
        for (p, s) in ps {
            self.vars.push((p.clone(), s.clone()));
        }
        Ok(tys)
    }

    /// 算術演算：引数はすべて同じ型で、その型で演算が使えること
    fn infer_op(&mut self, f: &str, args: &[Term], min: u8) -> KResult<TSort> {
        let mut known: Option<Ty> = None;
        let mut lit = min;
        for a in args {
            match self.infer_t(a)? {
                TSort::Known(s) => match &known {
                    Some(k) if *k != s => {
                        return kerr(format!("`{f}` の両辺の型が違う（{} と {}）", k.show(), s.show()));
                    }
                    _ => known = Some(s),
                },
                TSort::Lit(r) => lit = lit.max(r),
            }
        }
        match known {
            None => Ok(TSort::Lit(lit)),
            Some(s) => match ty_rank(&s) {
                Some(r) if r >= lit => Ok(TSort::Known(s)),
                _ => kerr(format!("演算 `{f}` は {} では使えない", s.show())),
            },
        }
    }

    pub fn check_t(&mut self, t: &Term, s: &Ty) -> KResult<()> {
        // λ は期待される型から引数・値の型を受け取る（値が数字だけでもよい）
        if let (Term::Lam(ps, body), Ty::Fun(args, res)) = (t, s) {
            if ps.len() != args.len() || ps.iter().zip(args).any(|((_, p), a)| *p != a.show()) {
                return kerr(format!("λ `{t}` の引数の型が {} と合わない", s.show()));
            }
            self.push_binders(ps)?;
            let r = self.check_t(body, res);
            self.vars.truncate(self.vars.len() - ps.len());
            return r;
        }
        match self.infer_t(t)? {
            TSort::Known(k) if k == *s => Ok(()),
            TSort::Known(k) => kerr(format!("項 `{t}` の型は {} だが、{} が必要", k.show(), s.show())),
            TSort::Lit(r) => match ty_rank(s) {
                Some(q) if q >= r => Ok(()),
                _ => kerr(format!("数の項 `{t}` を {} として読めない", s.show())),
            },
        }
    }

    pub fn check_sort(&mut self, t: &Term, s: &str) -> KResult<()> {
        let ty = parse_ty(s)?;
        self.check_t(t, &ty)
    }

    /// 項の型（数字だけなら None）
    pub fn sort_of(&mut self, t: &Term) -> KResult<Option<Ty>> {
        Ok(match self.infer_t(t)? {
            TSort::Known(k) => Some(k),
            TSort::Lit(_) => None,
        })
    }

    /// 関係の両辺の共通の型（数字だけなら None）
    pub fn rel_sort(&mut self, r: &str, a: &Term, b: &Term) -> KResult<Option<Ty>> {
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
                if ty_rank(x).is_none() {
                    return kerr(format!("`{r}` は数の型にしか使えない（{}）", x.show()));
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
            Formula::Atom(p, ts) if p == "@" && !ts.is_empty() => match self.infer_t(&ts[0])? {
                TSort::Known(Ty::Fun(ps, r)) if *r == Ty::Prop && ps.len() + 1 == ts.len() => {
                    for (t, s) in ts[1..].iter().zip(&ps) {
                        self.check_t(t, s)?;
                    }
                    Ok(())
                }
                _ => kerr(format!("`{f}` は述語の適用になっていない")),
            },
            Formula::Atom(p, ts) => {
                if let Some(d) = self.env.defs.get(p) {
                    if !matches!(d.body, DefBody::Pred(_)) {
                        return kerr(format!("`{p}` は項の定義なので、命題としては使えない"));
                    }
                    if d.params.len() != ts.len() {
                        return kerr(format!("`{p}` の引数は {} 個", d.params.len()));
                    }
                    let params = d.params.clone();
                    for ((_, s), t) in params.iter().zip(ts) {
                        self.check_sort(t, s)?;
                    }
                    return Ok(());
                }
                let Some(s) = self.var_sort(p) else {
                    return kerr(format!("述語 `{p}` が文脈にない"));
                };
                match parse_ty(&s)? {
                    Ty::Prop if ts.is_empty() => Ok(()),
                    Ty::Fun(args, r) if *r == Ty::Prop && args.len() == ts.len() => {
                        for (t, a) in ts.iter().zip(&args) {
                            self.check_t(t, a)?;
                        }
                        Ok(())
                    }
                    other => kerr(format!("`{p}`（型 {}）は {} 個の引数をとる述語ではない", other.show(), ts.len())),
                }
            }
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

    /// δ：項の定義をすべて展開する
    pub fn unfold_terms(&self, t: &Term) -> Term {
        match t {
            Term::App(f, args) => {
                let args: Vec<Term> = args.iter().map(|a| self.unfold_terms(a)).collect();
                match self.env.defs.get(f) {
                    Some(KDef { params, body: DefBody::Term(_, b) }) if params.len() == args.len() => {
                        let subs: Vec<(String, Term)> =
                            params.iter().map(|(p, _)| p.clone()).zip(args).collect();
                        self.unfold_terms(&b.subst_many(&subs))
                    }
                    _ => Term::App(f.clone(), args),
                }
            }
            Term::Var(x) => match self.env.defs.get(x) {
                Some(KDef { params, body: DefBody::Term(_, b) }) if params.is_empty() => self.unfold_terms(b),
                _ => t.clone(),
            },
            Term::Lam(ps, b) => Term::Lam(ps.clone(), Box::new(self.unfold_terms(b))),
            Term::Set(ps, phi) => Term::Set(ps.clone(), Box::new(self.unfold_all(phi))),
            _ => t.clone(),
        }
    }

    /// 算術の検算に渡す形：let と項の定義を展開する
    pub fn arith_form(&self, t: &Term) -> Term {
        self.unfold_terms(&self.expand_lets_t(t))
    }

    /// decide に渡す形：let と項の定義を展開する（述語の定義は展開しない）
    pub fn arith_form_f(&self, f: &Formula) -> Formula {
        fn go(c: &KCtx, f: &Formula) -> Formula {
            match f {
                Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| c.unfold_terms(t)).collect()),
                Formula::Bot => Formula::Bot,
                Formula::Imp(a, b) => Formula::Imp(Box::new(go(c, a)), Box::new(go(c, b))),
                Formula::And(a, b) => Formula::And(Box::new(go(c, a)), Box::new(go(c, b))),
                Formula::Or(a, b) => Formula::Or(Box::new(go(c, a)), Box::new(go(c, b))),
                Formula::Forall(x, s, b) => Formula::Forall(x.clone(), s.clone(), Box::new(go(c, b))),
                Formula::Exists(x, s, b) => Formula::Exists(x.clone(), s.clone(), Box::new(go(c, b))),
            }
        }
        go(self, &self.expand_lets_f(f))
    }

    /// δ：先頭の述語の定義を1段展開する
    pub fn unfold_head(&self, f: &Formula) -> Option<Formula> {
        match f {
            Formula::Atom(p, ts) => match self.env.defs.get(p)? {
                KDef { params, body: DefBody::Pred(b) } if params.len() == ts.len() => Some(instantiate(params, b, ts)),
                _ => None,
            },
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
            Formula::Atom(p, ts) => match self.unfold_head(f) {
                Some(g) => go(&g),
                None => Formula::Atom(p.clone(), ts.iter().map(|t| self.unfold_terms(t)).collect()),
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
            (Atom(p, ts), Atom(q, us)) => {
                p == q && ts.len() == us.len() && ts.iter().zip(us).all(|(t, u)| t.canonical() == u.canonical())
            }
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

    /// φ ≡ ψ（α・β・δ・ζ。β は代入のたびに済んでいる）
    pub fn conv(&mut self, a: &Formula, b: &Formula) -> bool {
        let a = self.unfold_all(&self.expand_lets_f(a));
        let b = self.unfold_all(&self.expand_lets_f(b));
        self.alpha_eq(&a, &b)
    }

    /// 項の等しさ（α・δ・ζ）
    pub fn term_eq(&self, a: &Term, b: &Term) -> bool {
        self.arith_form(a).canonical() == self.arith_form(b).canonical()
    }
}

// ================================================================ 図式の具体化

impl Schema {
    /// 型変数を tys で具体化したパラメータと文（項の型検査は呼び出し側で行う）
    pub fn instance(&self, tys: &[String]) -> (Vec<(String, String)>, Formula) {
        let sub = |s: &str| -> String {
            map_ty_str(s, &|t| match t {
                Ty::Param(p) => self.type_params.iter().position(|q| q == p).map(|i| Ty::parse(&tys[i]).unwrap_or(Ty::Unknown)),
                _ => None,
            })
        };
        let params = self.params.iter().map(|(x, s)| (x.clone(), sub(s))).collect();
        (params, self.formula.map_sorts(&|s| sub(s)))
    }
}
