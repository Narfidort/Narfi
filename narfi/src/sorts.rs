//! 型の推論（仕様 §3.3）。elab の一部で、kernel はこの結果を信じない（検算する）。
//!
//! 変数・数字・演算の結果ごとに「型の穴」を作り、同じ型であるべきものを単一化する
//! （Hindley–Milner 型推論と同じ考え方。型が `ℕ → ℝ` のように構造を持つので、構造ごと比べる）。
//! 最後に、残った穴の型を決める：
//!   - 数字だけからなる穴は、使われた演算が意味を持つ最小の数の型（§3.2）
//!   - 数の演算に使われた変数なのに決まらなければエラー（`x : ℝ` と書いてもらう）
//!   - 何の制約もなければ、定理の文では型変数 `'a`、それ以外ではエラー

use crate::kernel::env::{DefBody, KEnv, NUM_SORTS, num_rank, op_min_rank};
use crate::syntax::{Formula, RELS, Term};
use crate::types::Ty;

pub type SResult<T> = Result<T, String>;

/// 推論途中の型
#[derive(Clone, Debug, PartialEq)]
pub enum IT {
    V(usize),
    Base(String),
    Param(String),
    Prop,
    Fun(Vec<IT>, Box<IT>),
}

#[derive(Clone, Debug)]
struct Hole {
    bind: Option<IT>,
    /// 数の型でなければならない
    numeric: bool,
    /// 必要な最小の順位（`-` があれば ℤ 以上、`/` があれば ℚ 以上）
    rank: u8,
    /// 数字だけからなる
    lit: bool,
    /// エラーメッセージ用の名前
    name: Option<String>,
}

pub struct Infer<'a> {
    kenv: &'a KEnv,
    /// 文脈の変数（名前・型）
    ctx: Vec<(String, String)>,
    /// 文の自由変数を作ってよいか（定理の文のとき）
    statement: bool,
    holes: Vec<Hole>,
    scope: Vec<(String, IT)>,
    free: Vec<(String, IT)>,
    /// 束縛変数（∀・∃・λ・集合）の型。走査の順に並ぶ
    binders: Vec<IT>,
}

pub struct Inferred {
    pub free: Vec<(String, String)>,
    pub type_params: Vec<String>,
    binders: Vec<String>,
}

const OP_NAME: [(&str, &str); 6] =
    [("-", "引き算"), ("neg", "符号の反転"), ("abs", "絶対値"), ("/", "割り算"), ("+", "足し算"), ("·", "掛け算")];

fn op_label(f: &str) -> &str {
    OP_NAME.iter().find(|(k, _)| *k == f).map(|(_, v)| *v).unwrap_or(f)
}

fn from_ty(t: &Ty, fresh: &mut impl FnMut() -> IT) -> IT {
    match t {
        Ty::Base(s) | Ty::Meta(s) => IT::Base(s.clone()),
        Ty::Param(p) => IT::Param(p.clone()),
        Ty::Prop => IT::Prop,
        Ty::Fun(a, r) => IT::Fun(a.iter().map(|x| from_ty(x, fresh)).collect(), Box::new(from_ty(r, fresh))),
        Ty::Unknown => fresh(),
    }
}

impl<'a> Infer<'a> {
    pub fn new(kenv: &'a KEnv, ctx: Vec<(String, String)>, statement: bool) -> Self {
        Infer { kenv, ctx, statement, holes: vec![], scope: vec![], free: vec![], binders: vec![] }
    }

    fn hole(&mut self, lit: bool, name: Option<String>) -> IT {
        self.holes.push(Hole { bind: None, numeric: false, rank: 0, lit, name });
        IT::V(self.holes.len() - 1)
    }

    fn parse(&mut self, s: &str) -> SResult<IT> {
        let t = Ty::parse(s).ok_or(format!("型 `{s}` が読めない"))?;
        let mut holes = std::mem::take(&mut self.holes);
        let r = from_ty(&t, &mut || {
            holes.push(Hole { bind: None, numeric: false, rank: 0, lit: false, name: None });
            IT::V(holes.len() - 1)
        });
        self.holes = holes;
        Ok(r)
    }

    fn resolve(&self, t: &IT) -> IT {
        match t {
            IT::V(i) => match &self.holes[*i].bind {
                Some(u) => self.resolve(u),
                None => t.clone(),
            },
            _ => t.clone(),
        }
    }

    fn occurs(&self, i: usize, t: &IT) -> bool {
        match self.resolve(t) {
            IT::V(j) => i == j,
            IT::Fun(a, r) => a.iter().any(|x| self.occurs(i, x)) || self.occurs(i, &r),
            _ => false,
        }
    }

    /// 型を表示用の文字列に（決まっていない部分は ?）
    fn show(&self, t: &IT) -> String {
        match self.resolve(t) {
            IT::V(_) => "?".into(),
            IT::Base(s) | IT::Param(s) => s,
            IT::Prop => "Prop".into(),
            IT::Fun(a, r) => {
                let a: Vec<String> = a
                    .iter()
                    .map(|x| {
                        let s = self.show(x);
                        if matches!(self.resolve(x), IT::Fun(..)) { format!("({s})") } else { s }
                    })
                    .collect();
                format!("{} → {}", a.join(" × "), self.show(&r))
            }
        }
    }

    fn check_hole(&self, i: usize, t: &IT) -> SResult<()> {
        let h = &self.holes[i];
        if !h.numeric {
            return Ok(());
        }
        match t {
            IT::Base(s) => match num_rank(s) {
                Some(k) if k >= h.rank => Ok(()),
                Some(_) => Err(format!("{s} では使えない演算がある（{} 以上が必要）", NUM_SORTS[h.rank as usize])),
                None => Err(format!("{s} に数の演算・大小関係を使っている")),
            },
            IT::V(_) => Ok(()),
            other => Err(format!("{} に数の演算・大小関係を使っている", self.show(other))),
        }
    }

    fn label(&self, i: usize) -> String {
        match &self.holes[i].name {
            Some(n) => format!("`{n}` の"),
            None => String::new(),
        }
    }

    fn unify(&mut self, a: &IT, b: &IT) -> SResult<()> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (IT::V(i), IT::V(j)) if i == j => Ok(()),
            (IT::V(i), IT::V(j)) => {
                let hi = self.holes[*i].clone();
                self.holes[*i].bind = Some(b.clone());
                let hj = &mut self.holes[*j];
                hj.numeric |= hi.numeric;
                hj.rank = hj.rank.max(hi.rank);
                hj.lit &= hi.lit;
                if hj.name.is_none() {
                    hj.name = hi.name;
                }
                Ok(())
            }
            (IT::V(i), t) | (t, IT::V(i)) => {
                if self.occurs(*i, t) {
                    return Err(format!("{}型が無限に入れ子になる", self.label(*i)));
                }
                self.check_hole(*i, t).map_err(|e| format!("{}{e}", self.label(*i)))?;
                self.holes[*i].bind = Some(t.clone());
                Ok(())
            }
            (IT::Fun(a1, r1), IT::Fun(a2, r2)) if a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    self.unify(x, y)?;
                }
                self.unify(r1, r2)
            }
            _ if a == b => Ok(()),
            _ => Err(format!("型が合わない：{} と {}", self.show(&a), self.show(&b))),
        }
    }

    /// 数字だけからなる項の型（まだ決まっていない穴）
    fn is_lit_hole(&self, t: &IT) -> bool {
        match self.resolve(t) {
            IT::V(i) => self.holes[i].lit && self.holes[i].numeric,
            _ => false,
        }
    }

    /// 型が数の型（ℕ・ℤ・ℚ・ℝ）に決まっていれば、その順位
    fn num_base(&self, t: &IT) -> Option<u8> {
        match self.resolve(t) {
            IT::Base(s) => num_rank(&s),
            _ => None,
        }
    }

    /// 関数 fty を、型 args の引数に適用した値の型を res にする。
    /// 数の引数は、引数の型以上の順位なら埋め込まれる（ℕ の項を ℝ の引数に渡してよい。逆はだめ）
    fn apply(&mut self, fty: &IT, args: Vec<IT>, res: &IT) -> SResult<()> {
        if let IT::Fun(ps, r) = self.resolve(fty) {
            if ps.len() == args.len() {
                for (p, a) in ps.iter().zip(&args) {
                    match (self.num_base(a), self.num_base(p)) {
                        (Some(ka), Some(kp)) if ka <= kp => {}
                        _ => self.unify(p, a)?,
                    }
                }
                return self.unify(&r, res);
            }
        }
        self.unify(fty, &IT::Fun(args, Box::new(res.clone())))
    }

    fn constrain_num(&mut self, t: &IT, rank: u8, what: &str) -> SResult<()> {
        match self.resolve(t) {
            IT::V(i) => {
                self.holes[i].numeric = true;
                self.holes[i].rank = self.holes[i].rank.max(rank);
                Ok(())
            }
            IT::Base(s) => match num_rank(&s) {
                Some(k) if k >= rank => Ok(()),
                Some(_) => Err(format!("{what}：{s} では使えない演算がある（{} 以上が必要）", NUM_SORTS[rank as usize])),
                None => Err(format!("{what}：{s} は数の型ではない")),
            },
            other => Err(format!("{what}：{} は数の型ではない", self.show(&other))),
        }
    }

    fn lookup_var(&mut self, x: &str) -> SResult<IT> {
        if let Some((_, t)) = self.scope.iter().rev().find(|(y, _)| y == x) {
            return Ok(t.clone());
        }
        if let Some((_, s)) = self.ctx.iter().rev().find(|(y, _)| y == x) {
            let s = s.clone();
            return self.parse(&s);
        }
        if let Some(s) = self.kenv.consts.get(x) {
            let s = s.clone();
            return self.parse(&s);
        }
        if self.statement {
            if let Some((_, t)) = self.free.iter().find(|(y, _)| y == x) {
                return Ok(t.clone());
            }
            let t = self.hole(false, Some(x.to_string()));
            self.free.push((x.to_string(), t.clone()));
            return Ok(t);
        }
        Err(format!("`{x}` は文脈にない"))
    }

    fn binder_types(&mut self, ps: &[(String, String)]) -> SResult<Vec<IT>> {
        let mut out = Vec::new();
        for (p, s) in ps {
            let t = if s == "?" {
                self.hole(false, Some(p.clone()))
            } else {
                let t = self.parse(s)?;
                if let IT::V(i) = t {
                    self.holes[i].name = Some(p.clone());
                }
                t
            };
            self.binders.push(t.clone());
            out.push(t);
        }
        Ok(out)
    }

    pub fn term(&mut self, t: &Term) -> SResult<IT> {
        match t {
            Term::Meta(_) => Ok(self.hole(false, None)),
            Term::Num(_) => {
                let h = self.hole(true, None);
                self.constrain_num(&h, 0, "数")?;
                Ok(h)
            }
            Term::Var(x) => {
                if let Some(d) = self.kenv.defs.get(x) {
                    if let DefBody::Term(s, _) = &d.body {
                        if d.params.is_empty() {
                            let s = s.clone();
                            return self.parse(&s);
                        }
                    }
                }
                self.lookup_var(x)
            }
            Term::App(f, args) => {
                if let Some(min) = op_min_rank(f, args.len()) {
                    // 型の分かった数の引数は、結果の型に埋め込む（ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ）：結果はそれ以上の順位の数
                    // 引数の型がすべて分かっていて、その最大の型で演算が使えるなら、結果はその型。
                    // それ以外（型の分からない引数がある・ℕ の n で 1/(n+1) のように順位を上げる）は、順位の下限つきの穴
                    let r = self.hole(true, None);
                    let mut known: Option<u8> = None;
                    let mut unknown = false;
                    let mut nums = Vec::new();
                    for a in args {
                        let n = self.term(a)?;
                        match self.num_base(&n) {
                            Some(k) => known = Some(known.map_or(k, |q| q.max(k))),
                            // 数字だけの項はどの型にも合わせられるので、結果の型に合わせる（型の分からない引数とは数えない）
                            None if self.is_lit_hole(&n) => nums.push(n),
                            None => {
                                unknown = true;
                                self.unify(&r, &n).map_err(|e| format!("{}の両辺：{e}", op_label(f)))?
                            }
                        }
                    }
                    let out = match known {
                        Some(k) if !unknown && k >= min => {
                            let b = IT::Base(NUM_SORTS[k as usize].into());
                            self.unify(&r, &b)?;
                            b
                        }
                        _ => {
                            self.constrain_num(&r, known.unwrap_or(0).max(min), op_label(f))?;
                            r
                        }
                    };
                    for n in nums {
                        self.unify(&out, &n).map_err(|e| format!("{}の両辺：{e}", op_label(f)))?;
                    }
                    return Ok(out);
                }
                let nat = IT::Base("ℕ".into());
                match (f.as_str(), args.as_slice()) {
                    ("S", [a]) => {
                        let n = self.term(a)?;
                        self.unify(&n, &nat).map_err(|e| format!("S の引数：{e}"))?;
                        Ok(nat)
                    }
                    ("^", [a, e]) => {
                        let n = self.term(a)?;
                        let ne = self.term(e)?;
                        self.unify(&ne, &nat).map_err(|e| format!("指数：{e}"))?;
                        self.constrain_num(&n, 0, "累乗")?;
                        Ok(n)
                    }
                    // 一般の適用 @(f, s…)：f は関数を値とする項
                    ("@", [h, rest @ ..]) => {
                        let fty = self.term(h)?;
                        let mut ns = Vec::new();
                        for a in rest {
                            ns.push(self.term(a)?);
                        }
                        let res = self.hole(false, None);
                        self.apply(&fty, ns, &res).map_err(|e| format!("`{t}` の適用：{e}"))?;
                        Ok(res)
                    }
                    ("some", [p]) => {
                        let np = self.term(p)?;
                        let a = self.hole(false, None);
                        self.unify(&np, &IT::Fun(vec![a.clone()], Box::new(IT::Prop)))
                            .map_err(|e| format!("some の引数：{e}"))?;
                        Ok(a)
                    }
                    _ => {
                        let fty = match self.kenv.defs.get(f) {
                            Some(d) => match &d.body {
                                DefBody::Term(r, _) => {
                                    let ps: Vec<String> = d.params.iter().map(|(_, s)| s.clone()).collect();
                                    let r = r.clone();
                                    let mut args = Vec::new();
                                    for s in ps {
                                        args.push(self.parse(&s)?);
                                    }
                                    IT::Fun(args, Box::new(self.parse(&r)?))
                                }
                                DefBody::Pred(_) => return Err(format!("`{f}` は述語なので、項の中では使えない")),
                            },
                            None => self.lookup_var(f)?,
                        };
                        let mut ns = Vec::new();
                        for a in args {
                            ns.push(self.term(a)?);
                        }
                        let res = self.hole(false, Some(format!("{f}(…)")));
                        let curried = ns.len() > 1 && matches!(&fty, IT::Fun(ps, r) if ps.len() == 1 && matches!(**r, IT::Fun(..)));
                        self.apply(&fty, ns, &res).map_err(|e| {
                            let hint = if curried { "。複数の引数をまとめて渡す関数の型は A × B → C と書く（A → B → C は 1 つずつ渡す形で、f(a)(b) と書く）" } else { "" };
                            format!("`{f}` の適用：{e}{hint}")
                        })?;
                        Ok(res)
                    }
                }
            }
            Term::Lam(ps, body) => {
                let tys = self.binder_types(ps)?;
                for (p, t) in ps.iter().zip(&tys) {
                    self.scope.push((p.0.clone(), t.clone()));
                }
                let r = self.term(body);
                self.scope.truncate(self.scope.len() - ps.len());
                Ok(IT::Fun(tys, Box::new(r?)))
            }
            Term::Set(ps, phi) => {
                let tys = self.binder_types(ps)?;
                for (p, t) in ps.iter().zip(&tys) {
                    self.scope.push((p.0.clone(), t.clone()));
                }
                let r = self.formula(phi);
                self.scope.truncate(self.scope.len() - ps.len());
                r?;
                Ok(IT::Fun(tys, Box::new(IT::Prop)))
            }
        }
    }

    pub fn formula(&mut self, f: &Formula) -> SResult<()> {
        match f {
            Formula::Bot => Ok(()),
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                self.formula(a)?;
                self.formula(b)
            }
            Formula::Forall(x, s, b) | Formula::Exists(x, s, b) => {
                let t = self.binder_types(&[(x.clone(), s.clone())])?.pop().unwrap();
                self.scope.push((x.clone(), t));
                let r = self.formula(b);
                self.scope.pop();
                r
            }
            Formula::Atom(r, ts) if r == "=" || ["<", "≤", ">", "≥"].contains(&r.as_str()) => {
                let [a, b] = ts.as_slice() else {
                    return Err(format!("`{r}` の引数は2つ"));
                };
                let (na, nb) = (self.term(a)?, self.term(b)?);
                if self.num_base(&na).is_none() || self.num_base(&nb).is_none() {
                    self.unify(&na, &nb).map_err(|e| format!("`{a} {r} {b}`：{e}"))?;
                }
                if r != "=" {
                    self.constrain_num(&na, 0, &format!("`{r}`"))?;
                }
                Ok(())
            }
            Formula::Atom(r, _) if RELS.contains(&r.as_str()) => {
                Err(format!("関係 `{r}` はこの形では使えない（集合は x ∈ A・{{x | φ}} で書く）"))
            }
            Formula::Atom(p, ts) if p == "@" && !ts.is_empty() => {
                let pty = self.term(&ts[0])?;
                let mut ns = Vec::new();
                for t in &ts[1..] {
                    ns.push(self.term(t)?);
                }
                self.unify(&pty, &IT::Fun(ns, Box::new(IT::Prop))).map_err(|e| format!("`{f}`：{e}"))
            }
            Formula::Atom(p, ts) => {
                let pty = match self.kenv.defs.get(p) {
                    Some(d) => match &d.body {
                        DefBody::Pred(_) => {
                            let ps: Vec<String> = d.params.iter().map(|(_, s)| s.clone()).collect();
                            let mut args = Vec::new();
                            for s in ps {
                                args.push(self.parse(&s)?);
                            }
                            if args.is_empty() { IT::Prop } else { IT::Fun(args, Box::new(IT::Prop)) }
                        }
                        DefBody::Term(..) => return Err(format!("`{p}` は項の定義なので、命題としては使えない")),
                    },
                    None => self.lookup_var(p)?,
                };
                let mut ns = Vec::new();
                for t in ts {
                    ns.push(self.term(t)?);
                }
                let want = if ns.is_empty() { IT::Prop } else { IT::Fun(ns, Box::new(IT::Prop)) };
                self.unify(&pty, &want).map_err(|e| format!("述語 `{p}`：{e}"))
            }
        }
    }

    fn final_ty(&self, t: &IT, decided: &[Option<Ty>]) -> Ty {
        match self.resolve(t) {
            IT::V(i) => decided[i].clone().unwrap_or(Ty::Unknown),
            IT::Base(s) => Ty::Base(s),
            IT::Param(p) => Ty::Param(p),
            IT::Prop => Ty::Prop,
            IT::Fun(a, r) => {
                Ty::Fun(a.iter().map(|x| self.final_ty(x, decided)).collect(), Box::new(self.final_ty(&r, decided)))
            }
        }
    }

    /// 項 t の型が ty であること
    pub fn term_expect(&mut self, t: &Term, ty: &str) -> SResult<()> {
        let n = self.term(t)?;
        let want = self.parse(ty)?;
        self.unify(&n, &want)
    }

    /// 型を決める
    pub fn finish(self) -> SResult<Inferred> {
        let n = self.holes.len();
        let mut decided: Vec<Option<Ty>> = vec![None; n];
        let mut params: Vec<String> = Vec::new();
        for i in 0..n {
            let h = &self.holes[i];
            if h.bind.is_some() {
                continue;
            }
            // 数字だけの穴、または ℝ と決まるしかない穴（ℝ の項との演算の結果）は、その順位の型にする
            decided[i] = Some(if h.numeric && (h.lit || h.rank as usize == NUM_SORTS.len() - 1) {
                Ty::Base(NUM_SORTS[h.rank as usize].to_string())
            } else if h.numeric {
                let cand = NUM_SORTS[h.rank as usize..].join("・");
                return Err(match h.name.as_deref() {
                    Some(n) if n.ends_with("(…)") => {
                        let f = n.trim_end_matches("(…)");
                        format!("関数 `{f}` の値の型が決まらない（{cand} のどれか）。`{f} : ℕ → ℝ` のように宣言する")
                    }
                    Some(n) => format!("`{n}` の型が決まらない（{cand} のどれか）。`{n} : ℝ` のように型を書く"),
                    None => format!("項の型が決まらない（{cand} のどれか）。変数の型を書く"),
                });
            } else if self.statement {
                let p = format!("'{}", (b'a' + params.len() as u8) as char);
                params.push(p.clone());
                Ty::Param(p)
            } else {
                let who = h.name.clone().unwrap_or("項".into());
                return Err(format!("`{who}` の型が決まらない。型を書く"));
            });
        }
        let binders = self.binders.iter().map(|t| self.final_ty(t, &decided).show()).collect();
        let free = self.free.iter().map(|(x, t)| (x.clone(), self.final_ty(t, &decided).show())).collect();
        Ok(Inferred { free, type_params: params, binders })
    }
}

impl Inferred {
    /// 推論した型を、論理式の束縛変数（∀・∃・λ・集合）に書き込む（formula に渡したのと同じ順で呼ぶ）
    pub fn annotate(&self, f: &Formula, k: &mut usize) -> Formula {
        match f {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| self.annotate_t(t, k)).collect()),
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => {
                let a = self.annotate(a, k);
                Formula::Imp(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::And(a, b) => {
                let a = self.annotate(a, k);
                Formula::And(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::Or(a, b) => {
                let a = self.annotate(a, k);
                Formula::Or(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::Forall(x, _, b) | Formula::Exists(x, _, b) => {
                let s = self.binders[*k].clone();
                *k += 1;
                let b = Box::new(self.annotate(b, k));
                if matches!(f, Formula::Forall(..)) {
                    Formula::Forall(x.clone(), s, b)
                } else {
                    Formula::Exists(x.clone(), s, b)
                }
            }
        }
    }

    pub fn annotate_t(&self, t: &Term, k: &mut usize) -> Term {
        match t {
            Term::App(f, args) => Term::App(f.clone(), args.iter().map(|a| self.annotate_t(a, k)).collect()),
            Term::Lam(ps, b) => {
                let ps2 = self.params(ps, k);
                Term::Lam(ps2, Box::new(self.annotate_t(b, k)))
            }
            Term::Set(ps, phi) => {
                let ps2 = self.params(ps, k);
                Term::Set(ps2, Box::new(self.annotate(phi, k)))
            }
            _ => t.clone(),
        }
    }

    fn params(&self, ps: &[(String, String)], k: &mut usize) -> Vec<(String, String)> {
        ps.iter()
            .map(|(p, _)| {
                let s = self.binders[*k].clone();
                *k += 1;
                (p.clone(), s)
            })
            .collect()
    }
}

/// 文脈の中の論理式 1 つの束縛変数の型を埋める（証明の中の have・assume など）
pub fn infer_formula(kenv: &KEnv, ctx: &[(String, String)], f: &Formula) -> SResult<Formula> {
    let mut inf = Infer::new(kenv, ctx.to_vec(), false);
    inf.formula(f)?;
    let r = inf.finish()?;
    Ok(r.annotate(f, &mut 0))
}

/// 文脈の中の項の λ・集合の型を埋める。expected があればその型に合わせる。
pub fn infer_term(kenv: &KEnv, ctx: &[(String, String)], t: &Term, expected: Option<&str>) -> SResult<Term> {
    let mut inf = Infer::new(kenv, ctx.to_vec(), false);
    let n = inf.term(t)?;
    if let Some(e) = expected {
        let want = inf.parse(e)?;
        inf.unify(&n, &want)?;
    }
    let r = inf.finish()?;
    Ok(r.annotate_t(t, &mut 0))
}

/// 項の型（数字だけ・決まらないなら None）。elab が型の具体化を決めるのに使う。
pub fn term_sort(kenv: &KEnv, ctx: &[(String, String)], t: &Term) -> Option<String> {
    let mut inf = Infer::new(kenv, ctx.to_vec(), false);
    let n = inf.term(t).ok()?;
    if let IT::V(i) = inf.resolve(&n) {
        // ℝ の項との演算の結果（順位の下限が ℝ）は ℝ
        let h = &inf.holes[i];
        return (h.numeric && !h.lit && h.rank as usize == NUM_SORTS.len() - 1).then(|| "ℝ".to_string());
    }
    let s = inf.show(&n);
    (!s.contains('?')).then_some(s)
}
