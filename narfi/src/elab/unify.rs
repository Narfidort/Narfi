//! メタ変数と単一化。
//!
//! 「まだ決まっていないもの」を穴（メタ変数）として置き、式どうしを見比べて穴を埋める。
//! - 項のメタ変数 `Term::Meta(n)`：定理を使うときの暗黙の引数など
//! - 型のメタ変数 `?σn`：型変数を持つ定理（`eq.symm` など）を使うとき
//! - 関数・述語のメタ変数 `?Fn`：関数型・述語型のパラメータを持つ定理を使うとき。
//!   中身は名前・λ・集合のどれでもよく、`?F(x) =?= x > 0` のように、穴が異なる変数に
//!   適用されている形（Miller のパターン）なら `?F := {x | x > 0}` と一意に決まる。
//!
//! 最後に zonk（穴を中身で置き換える）してから kernel に渡す。

use super::{CResult, Checker, Ctx};
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term, apply_term, holds};
use crate::types::{Ty, map_ty_str};
use std::collections::BTreeSet;

type Saved = (Vec<Option<Term>>, Vec<Option<String>>, Vec<(Option<Term>, String)>);

impl<'a> Checker<'a> {
    // ------------------------------------------------ メタ変数を作る

    pub(super) fn new_meta(&mut self) -> Term {
        self.metas.push(None);
        Term::Meta(self.metas.len() as u32 - 1)
    }

    pub(super) fn new_sort_meta(&mut self) -> String {
        self.sort_metas.push(None);
        format!("?σ{}", self.sort_metas.len() - 1)
    }

    /// 関数型・述語型の穴（型 ty）
    pub(super) fn new_fn_meta(&mut self, ty: &str) -> String {
        self.fn_metas.push((None, ty.to_string()));
        format!("?F{}", self.fn_metas.len() - 1)
    }

    fn sort_meta_index(s: &str) -> Option<usize> {
        s.strip_prefix("?σ")?.parse().ok()
    }

    fn fn_meta_index(s: &str) -> Option<usize> {
        s.strip_prefix("?F")?.parse().ok()
    }

    fn fn_binding(&self, name: &str) -> Option<Term> {
        self.fn_metas.get(Self::fn_meta_index(name)?)?.0.clone()
    }

    fn is_open_fn_meta(&self, name: &str) -> bool {
        Self::fn_meta_index(name).is_some_and(|i| self.fn_metas[i].0.is_none())
    }

    // ------------------------------------------------ zonk（穴を中身で置き換える）

    pub(super) fn zonk_sort(&self, s: &str) -> String {
        if !s.contains("?σ") {
            return s.to_string();
        }
        map_ty_str(s, &|t| match t {
            Ty::Meta(m) => {
                let i = Self::sort_meta_index(m)?;
                let b = self.sort_metas.get(i)?.as_ref()?;
                Ty::parse(&self.zonk_sort(b))
            }
            _ => None,
        })
    }

    pub(super) fn zonk_t(&self, t: &Term) -> Term {
        match t {
            Term::Meta(m) => match &self.metas[*m as usize] {
                Some(u) => self.zonk_t(u),
                None => t.clone(),
            },
            Term::Var(x) => match self.fn_binding(x) {
                Some(b) => self.zonk_t(&b),
                None => t.clone(),
            },
            Term::App(f, a) => {
                let a: Vec<Term> = a.iter().map(|x| self.zonk_t(x)).collect();
                match self.fn_binding(f) {
                    Some(b) => self.zonk_t(&apply_term(&self.zonk_t(&b), &a)),
                    None if f == "@" && !a.is_empty() => apply_term(&a[0], &a[1..]),
                    None => Term::App(f.clone(), a),
                }
            }
            Term::Lam(ps, b) => Term::Lam(ps.iter().map(|(p, s)| (p.clone(), self.zonk_sort(s))).collect(), Box::new(self.zonk_t(b))),
            Term::Set(ps, phi) => Term::Set(ps.iter().map(|(p, s)| (p.clone(), self.zonk_sort(s))).collect(), Box::new(self.zonk_f(phi))),
            Term::Num(_) => t.clone(),
        }
    }

    pub(super) fn zonk_f(&self, f: &Formula) -> Formula {
        match f {
            Formula::Atom(p, ts) => {
                let ts: Vec<Term> = ts.iter().map(|t| self.zonk_t(t)).collect();
                match self.fn_binding(p) {
                    Some(b) => self.zonk_f(&holds(&self.zonk_t(&b), &ts)),
                    None if p == "@" && !ts.is_empty() => holds(&ts[0], &ts[1..]),
                    None => Formula::Atom(p.clone(), ts),
                }
            }
            Formula::Imp(a, b) => Formula::Imp(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::And(a, b) => Formula::And(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), self.zonk_sort(t), Box::new(self.zonk_f(b))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), self.zonk_sort(t), Box::new(self.zonk_f(b))),
            Formula::Bot => Formula::Bot,
        }
    }

    fn open_holes_f(&self, f: &Formula) -> bool {
        f.has_meta() || f.free_vars().iter().any(|v| v.starts_with("?F")) || sort_holes_f(f)
    }

    fn open_holes_t(&self, t: &Term) -> bool {
        let mut vs = BTreeSet::new();
        t.vars(&mut vs);
        t.has_meta() || vs.iter().any(|v| v.starts_with("?F")) || sort_holes_t(t)
    }

    /// 証明項の穴をすべて埋める。埋まらない穴が残ればエラー。
    pub(super) fn zonk_proof(&self, p: &Proof) -> CResult<Proof> {
        let zf = |f: &Formula| -> CResult<Formula> {
            let g = self.zonk_f(f);
            if self.open_holes_f(&g) {
                return self.err(format!("決まらない項・型が残っている：{g}（引数や型を明示する）"));
            }
            Ok(g)
        };
        let zt = |t: &Term| -> CResult<Term> {
            let u = self.zonk_t(t);
            if self.open_holes_t(&u) {
                return self.err(format!("決まらない項が残っている：{u}（引数を明示する）"));
            }
            Ok(u)
        };
        let zs = |s: &str| -> CResult<String> {
            let t = self.zonk_sort(s);
            if t.contains("?σ") {
                return self.err("型が決まらない箇所がある（変数に型を書く）");
            }
            Ok(t)
        };
        let b = |q: &Proof| -> CResult<Box<Proof>> { Ok(Box::new(self.zonk_proof(q)?)) };
        Ok(match p {
            Proof::Hyp(h) => Proof::Hyp(h.clone()),
            Proof::Thm { name, sorts, args } => Proof::Thm {
                name: name.clone(),
                sorts: sorts.iter().map(|s| zs(s)).collect::<CResult<_>>()?,
                args: args.iter().map(&zt).collect::<CResult<_>>()?,
            },
            Proof::ImpI { h, phi, body } => Proof::ImpI { h: h.clone(), phi: zf(phi)?, body: b(body)? },
            Proof::ImpE(p, q) => Proof::ImpE(b(p)?, b(q)?),
            Proof::AndI(p, q) => Proof::AndI(b(p)?, b(q)?),
            Proof::AndE { right, p } => Proof::AndE { right: *right, p: b(p)? },
            Proof::OrI { right, other, p } => Proof::OrI { right: *right, other: zf(other)?, p: b(p)? },
            Proof::OrE { p, h1, q1, h2, q2 } => Proof::OrE { p: b(p)?, h1: h1.clone(), q1: b(q1)?, h2: h2.clone(), q2: b(q2)? },
            Proof::AllI { x, sort, body } => Proof::AllI { x: x.clone(), sort: zs(sort)?, body: b(body)? },
            Proof::AllE(p, t) => Proof::AllE(b(p)?, zt(t)?),
            Proof::ExI { target, witness, p } => Proof::ExI { target: zf(target)?, witness: zt(witness)?, p: b(p)? },
            Proof::ExE { p, x, h, body } => Proof::ExE { p: b(p)?, x: x.clone(), h: h.clone(), body: b(body)? },
            Proof::BotE(f, p) => Proof::BotE(zf(f)?, b(p)?),
            Proof::Raa { h, phi, body } => Proof::Raa { h: h.clone(), phi: zf(phi)?, body: b(body)? },
            Proof::Cut { h, phi, p, body } => Proof::Cut { h: h.clone(), phi: zf(phi)?, p: b(p)?, body: b(body)? },
            Proof::Let { x, sort, t, body } => Proof::Let { x: x.clone(), sort: zs(sort)?, t: zt(t)?, body: b(body)? },
            Proof::Refl(t) => Proof::Refl(zt(t)?),
            Proof::Subst { eq, z, motive, p } => Proof::Subst { eq: b(eq)?, z: z.clone(), motive: zf(motive)?, p: b(p)? },
            Proof::Ind { x, phi, base, k, ih, step } => {
                Proof::Ind { x: x.clone(), phi: zf(phi)?, base: b(base)?, k: k.clone(), ih: ih.clone(), step: b(step)? }
            }
            Proof::Trans(p, q) => Proof::Trans(b(p)?, b(q)?),
            Proof::Antisymm(p, q) => Proof::Antisymm(b(p)?, b(q)?),
            Proof::NatNonneg(t) => Proof::NatNonneg(zt(t)?),
            Proof::Ring { lhs, rhs } => Proof::Ring { lhs: zt(lhs)?, rhs: zt(rhs)? },
            Proof::LinArith { goal, facts, coeffs } => Proof::LinArith {
                goal: zf(goal)?,
                facts: facts.iter().map(|q| self.zonk_proof(q)).collect::<CResult<_>>()?,
                coeffs: coeffs.clone(),
            },
            Proof::Decide(f) => Proof::Decide(zf(f)?),
            Proof::Sorry(f) => Proof::Sorry(zf(f)?),
            Proof::Line(l, p) => Proof::Line(*l, b(p)?),
        })
    }

    // ------------------------------------------------ 正規化

    /// let を展開し、穴を埋める
    pub(super) fn norm(&self, ctx: &Ctx, f: &Formula) -> Formula {
        ctx.expand_f(&self.zonk_f(f))
    }

    /// 先頭が def の述語である限り展開する（透過的な定義展開）。let は展開しない。
    pub(super) fn whnf(&self, f: &Formula) -> Formula {
        let mut f = self.zonk_f(f);
        while let Some(g) = self.unfold_head(&f) {
            f = g;
        }
        f
    }

    pub(super) fn unfold_head(&self, f: &Formula) -> Option<Formula> {
        match f {
            // 集合への所属 S(x)：S が（項の定義を開くと）内包表記 {y | φ} なら φ[x/y]（kernel の unfold_head と同じ）
            Formula::Atom(p, ts) if p == "@" && !ts.is_empty() => match self.unfold_terms(&ts[0]) {
                Term::Set(ps, phi) if ps.len() == ts.len() - 1 => Some(crate::syntax::instantiate(&ps, &phi, &ts[1..])),
                _ => None,
            },
            Formula::Atom(p, ts) => {
                let d = self.env.kernel.defs.get(p)?;
                match &d.body {
                    crate::kernel::env::DefBody::Pred(b) if d.params.len() == ts.len() => {
                        Some(crate::syntax::instantiate(&d.params, b, ts))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// 項の定義をすべて展開する（算術に渡す前。kernel の unfold_terms と同じ）
    pub(super) fn unfold_terms(&self, t: &Term) -> Term {
        use crate::kernel::env::{DefBody, KDef};
        match t {
            Term::App(f, args) => {
                let args: Vec<Term> = args.iter().map(|a| self.unfold_terms(a)).collect();
                // β：開いて λ になった頭を、残りの引数に当てる（kernel の unfold_terms と同じ）
                if f == "@" && matches!(args.first(), Some(Term::Lam(..))) {
                    return self.unfold_terms(&crate::syntax::apply_term(&args[0], &args[1..]));
                }
                match self.env.kernel.defs.get(f) {
                    Some(KDef { params, body: DefBody::Term(_, b) }) if params.len() == args.len() => {
                        let subs: Vec<(String, Term)> = params.iter().map(|(p, _)| p.clone()).zip(args).collect();
                        self.unfold_terms(&b.subst_many(&subs))
                    }
                    _ => Term::App(f.clone(), args),
                }
            }
            Term::Var(x) => match self.env.kernel.defs.get(x) {
                Some(KDef { params, body: DefBody::Term(_, b) }) if params.is_empty() => self.unfold_terms(b),
                _ => t.clone(),
            },
            _ => t.clone(),
        }
    }

    /// 論理式の中の項の定義を展開する
    pub(super) fn unfold_terms_f(&self, f: &Formula) -> Formula {
        match f {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| self.unfold_terms(t)).collect()),
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => Formula::Imp(Box::new(self.unfold_terms_f(a)), Box::new(self.unfold_terms_f(b))),
            Formula::And(a, b) => Formula::And(Box::new(self.unfold_terms_f(a)), Box::new(self.unfold_terms_f(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(self.unfold_terms_f(a)), Box::new(self.unfold_terms_f(b))),
            Formula::Forall(x, s, b) => Formula::Forall(x.clone(), s.clone(), Box::new(self.unfold_terms_f(b))),
            Formula::Exists(x, s, b) => Formula::Exists(x.clone(), s.clone(), Box::new(self.unfold_terms_f(b))),
        }
    }

    /// A ∧ (B ∧ C) を [A, B, C] に。途中の定義も展開する。
    pub(super) fn split_and_w(&self, f: &Formula, n: usize) -> Option<Vec<Formula>> {
        let mut out = Vec::new();
        let mut cur = f.clone();
        while out.len() + 1 < n {
            match self.whnf(&cur) {
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

    // ------------------------------------------------ 型の単一化

    pub(super) fn unify_sort(&mut self, a: &str, b: &str) -> bool {
        let (a, b) = (self.zonk_sort(a), self.zonk_sort(b));
        if a == b {
            return true;
        }
        match (Ty::parse(&a), Ty::parse(&b)) {
            (Some(x), Some(y)) => self.unify_ty(&x, &y),
            _ => false,
        }
    }

    fn unify_ty(&mut self, x: &Ty, y: &Ty) -> bool {
        match (x, y) {
            (Ty::Meta(m), t) | (t, Ty::Meta(m)) => {
                if let Ty::Meta(n) = t
                    && n == m
                {
                    return true;
                }
                let Some(i) = Self::sort_meta_index(m) else { return false };
                if let Some(b) = self.sort_metas[i].clone() {
                    return self.unify_sort(&b, &t.show());
                }
                if t.any(&|u| matches!(u, Ty::Meta(n) if n == m)) {
                    return false;
                }
                self.sort_metas[i] = Some(t.show());
                true
            }
            (Ty::Fun(a1, r1), Ty::Fun(a2, r2)) if a1.len() == a2.len() => {
                a1.iter().zip(a2).all(|(p, q)| self.unify_ty(p, q)) && self.unify_ty(r1, r2)
            }
            _ => x == y,
        }
    }

    // ------------------------------------------------ 単一化

    fn save(&self) -> Saved {
        (self.metas.clone(), self.sort_metas.clone(), self.fn_metas.clone())
    }

    fn restore(&mut self, s: Saved) {
        self.metas = s.0;
        self.sort_metas = s.1;
        self.fn_metas = s.2;
    }

    /// let の展開・定義の展開・束縛変数の名前の違いを無視して、a と b を単一化する。失敗したら元に戻す。
    pub(super) fn unify(&mut self, ctx: &Ctx, a: &Formula, b: &Formula) -> bool {
        let save = self.save();
        let (a, b) = (self.norm(ctx, a), self.norm(ctx, b));
        let ok = self.uf(&a, &b);
        if !ok {
            self.restore(save);
            return false;
        }
        // 型が決まっていない関数の穴（funext の f など）が、型の分かる項に決まったら、その項の型に合わせる
        for i in 0..self.fn_metas.len() {
            let Some(t) = self.fn_metas[i].0.clone() else { continue };
            let sort = self.zonk_sort(&self.fn_metas[i].1);
            if !sort.contains("?σ") {
                continue;
            }
            if let Some(ts) = self.term_sort(ctx, &t) {
                self.unify_sort(&sort, &ts);
            }
        }
        true
    }

    fn fresh_var(&mut self) -> Term {
        self.fresh += 1;
        Term::Var(format!("#{}", self.fresh))
    }

    fn uf(&mut self, a: &Formula, b: &Formula) -> bool {
        use Formula::*;
        let (a, b) = (self.zonk_f(a), self.zonk_f(b));
        match (&a, &b) {
            (Atom(p, ts), other) | (other, Atom(p, ts)) if self.is_open_fn_meta(p) => {
                let (p, ts, other) = (p.clone(), ts.clone(), other.clone());
                self.solve_pred(&p, &ts, &other)
            }
            (Atom(p, ts), Atom(q, us)) if p == q && ts.len() == us.len() => {
                let save = self.save();
                if ts.iter().zip(us).all(|(t, u)| self.ut(t, u)) {
                    return true;
                }
                // 後ろの引数から決まるメタ変数もある（?F(0) = sum(?F, 1) の ?F は右辺から決まる）
                self.restore(save.clone());
                if ts.iter().zip(us).rev().all(|(t, u)| self.ut(t, u)) {
                    return true;
                }
                // 引数が合わなくても、展開すれば一致することがある
                self.restore(save);
                match (self.unfold_head(&a), self.unfold_head(&b)) {
                    (Some(x), Some(y)) => self.uf(&x, &y),
                    _ => false,
                }
            }
            (Imp(a1, b1), Imp(a2, b2)) | (And(a1, b1), And(a2, b2)) | (Or(a1, b1), Or(a2, b2)) => self.uf(a1, a2) && self.uf(b1, b2),
            (Forall(x, t1, b1), Forall(y, t2, b2)) | (Exists(x, t1, b1), Exists(y, t2, b2)) => {
                if !self.unify_sort(t1, t2) {
                    return false;
                }
                let v = self.fresh_var();
                self.uf(&b1.subst(x, &v), &b2.subst(y, &v))
            }
            (Bot, Bot) => true,
            // 形が違っても、片方が定義された述語なら展開して比べる
            _ => {
                if let Some(x) = self.unfold_head(&a) {
                    self.uf(&x, &b)
                } else if let Some(y) = self.unfold_head(&b) {
                    self.uf(&a, &y)
                } else {
                    false
                }
            }
        }
    }

    pub(super) fn ut(&mut self, a: &Term, b: &Term) -> bool {
        // η：(x ↦ F(x)) と F は同じ（関数の変数 f と (x ↦ f(x)) も）
        let (a, b) = (self.zonk_t(a).eta_top(false), self.zonk_t(b).eta_top(false));
        let eta_var = |l: &Term, v: &Term| match (l, v) {
            (Term::Lam(ps, body), Term::Var(f)) => matches!(&**body, Term::App(g, args) if g == f && args.len() == ps.len()
                && args.iter().zip(ps).all(|(x, (p, _))| matches!(x, Term::Var(y) if y == p)) && !ps.iter().any(|(p, _)| p == f)),
            _ => false,
        };
        if eta_var(&a, &b) || eta_var(&b, &a) {
            return true;
        }
        match (&a, &b) {
            (Term::Meta(m), Term::Meta(n)) if m == n => true,
            (Term::Meta(m), t) | (t, Term::Meta(m)) => {
                let mut vs = BTreeSet::new();
                t.vars(&mut vs);
                if occurs(*m, t) || vs.iter().any(|v| v.starts_with('#')) {
                    return false;
                }
                self.metas[*m as usize] = Some(t.clone());
                true
            }
            (Term::Var(x), t) | (t, Term::Var(x)) if self.is_open_fn_meta(x) => {
                if matches!(t, Term::Var(y) if y == x) {
                    return true;
                }
                let mut vs = BTreeSet::new();
                t.vars(&mut vs);
                if vs.contains(x) || vs.iter().any(|v| v.starts_with('#')) {
                    return false;
                }
                let i = Self::fn_meta_index(x).unwrap();
                self.fn_metas[i].0 = Some(t.clone());
                true
            }
            (Term::App(f, xs), u) | (u, Term::App(f, xs)) if self.is_open_fn_meta(f) => {
                let (f, xs, u) = (f.clone(), xs.clone(), u.clone());
                self.solve_app(&f, &xs, &u)
            }
            // ?F(i)(x)（関数を返す関数の適用）
            (Term::App(at, xs), u) | (u, Term::App(at, xs))
                if at == "@"
                    && xs.len() >= 2
                    && matches!(&xs[0], Term::App(f, _) if self.is_open_fn_meta(f))
                    && !matches!(u, Term::App(at2, ys) if at2 == "@" && ys.len() == xs.len()) =>
            {
                let Term::App(f, ys) = &xs[0] else { unreachable!() };
                let mut all = ys.clone();
                all.extend(xs[1..].iter().cloned());
                let (f, u) = (f.clone(), u.clone());
                self.solve_app(&f, &all, &u)
            }
            (Term::Num(x), Term::Num(y)) => x == y,
            (Term::App(f, xs), Term::App(g, ys)) if f == g && xs.len() == ys.len() => {
                let save = self.save();
                if xs.iter().zip(ys).all(|(x, y)| self.ut(x, y)) {
                    return true;
                }
                self.restore(save);
                self.ut_unfold(&a, &b)
            }
            (Term::Lam(p1, b1), Term::Lam(p2, b2)) if p1.len() == p2.len() => {
                if !p1.iter().zip(p2).all(|((_, s), (_, t))| self.unify_sort(s, t)) {
                    return false;
                }
                let vs: Vec<Term> = p1.iter().map(|_| self.fresh_var()).collect();
                let s1: Vec<(String, Term)> = p1.iter().map(|(p, _)| p.clone()).zip(vs.iter().cloned()).collect();
                let s2: Vec<(String, Term)> = p2.iter().map(|(p, _)| p.clone()).zip(vs.iter().cloned()).collect();
                self.ut(&b1.subst_many(&s1), &b2.subst_many(&s2))
            }
            (Term::Set(p1, f1), Term::Set(p2, f2)) if p1.len() == p2.len() => {
                if !p1.iter().zip(p2).all(|((_, s), (_, t))| self.unify_sort(s, t)) {
                    return false;
                }
                let vs: Vec<Term> = p1.iter().map(|_| self.fresh_var()).collect();
                let s1: Vec<(String, Term)> = p1.iter().map(|(p, _)| p.clone()).zip(vs.iter().cloned()).collect();
                let s2: Vec<(String, Term)> = p2.iter().map(|(p, _)| p.clone()).zip(vs.iter().cloned()).collect();
                self.uf(&f1.subst_many(&s1), &f2.subst_many(&s2))
            }
            (Term::Var(x), Term::Var(y)) if x == y => true,
            _ => self.ut_unfold(&a, &b),
        }
    }

    /// 項の定義を1段展開して比べ直す（δ）
    fn ut_unfold(&mut self, a: &Term, b: &Term) -> bool {
        fn one(c: &Checker, t: &Term) -> Option<Term> {
            use crate::kernel::env::{DefBody, KDef};
            // 値が関数の定義を、さらに適用したもの：mmul(A, B, n)(i, j)
            if let Term::App(at, xs) = t
                && at == "@"
                && !xs.is_empty()
            {
                let head = one(c, &xs[0])?;
                return Some(crate::syntax::apply_term(&head, &xs[1..]));
            }
            let (f, args) = match t {
                Term::App(f, args) => (f, args.clone()),
                Term::Var(f) => (f, vec![]),
                _ => return None,
            };
            match c.env.kernel.defs.get(f) {
                Some(KDef { params, body: DefBody::Term(_, body) }) if params.len() == args.len() => {
                    let subs: Vec<(String, Term)> = params.iter().map(|(p, _)| p.clone()).zip(args).collect();
                    Some(body.subst_many(&subs))
                }
                _ => None,
            }
        }
        if let Some(x) = one(self, a) {
            return self.ut(&x, b);
        }
        if let Some(y) = one(self, b) {
            return self.ut(a, &y);
        }
        false
    }

    /// パターンの引数（相異なる変数）なら、そのパラメータの名前と型を返す
    fn pattern_params(&self, f: &str, xs: &[Term], body_vars: &BTreeSet<String>) -> Option<Vec<(String, String)>> {
        let i = Self::fn_meta_index(f)?;
        let ty = Ty::parse(&self.zonk_sort(&self.fn_metas[i].1))?;
        // 関数を返す関数 ℕ → (σ → τ) は、引数を続けて受ける（?F(i)(x) を ?F(i, x) と見る）
        let arg_tys: Vec<Ty> = match ty {
            Ty::Fun(mut a, mut r) => {
                while a.len() < xs.len() {
                    match *r {
                        Ty::Fun(a2, r2) => {
                            a.extend(a2);
                            r = r2;
                        }
                        _ => break,
                    }
                }
                a
            }
            Ty::Prop => vec![],
            _ => return None,
        };
        if arg_tys.len() != xs.len() {
            return None;
        }
        let mut names = Vec::new();
        for (k, x) in xs.iter().enumerate() {
            let Term::Var(v) = x else { return None };
            if names.iter().any(|(n, _): &(String, String)| n == v) || v.starts_with("?F") {
                return None;
            }
            // 束縛変数の仮の名前（#3）は読みやすい名前にする
            let name = if v.starts_with('#') {
                let mut n = ["x", "y", "z", "w"].get(k).copied().unwrap_or("v").to_string();
                while body_vars.contains(&n) || names.iter().any(|(m, _)| *m == n) {
                    n.push('\'');
                }
                n
            } else {
                v.clone()
            };
            names.push((name, arg_tys[k].show()));
        }
        Some(names)
    }

    /// ?F(xs) =?= u を解く
    fn solve_app(&mut self, f: &str, xs: &[Term], u: &Term) -> bool {
        let i = Self::fn_meta_index(f).unwrap();
        // 1. 頭が同じ形なら名前を入れる：?F(a) =?= g(b) なら ?F := g, a =?= b
        if let Term::App(g, ys) = u
            && ys.len() == xs.len()
            && !self.is_open_fn_meta(g)
        {
            let save = self.save();
            // 定義の名前は値として渡せないので、λ で包む（f ↦ (i ↦ f(i))）
            let head = match self.env.kernel.defs.get(g) {
                Some(d) if d.params.len() == ys.len() => {
                    let ps: Vec<(String, String)> = d.params.iter().enumerate().map(|(k, (_, t))| (format!("v{k}'"), t.clone())).collect();
                    let args: Vec<Term> = ps.iter().map(|(p, _)| Term::Var(p.clone())).collect();
                    self.curried_lam(i, ps, Term::App(g.clone(), args))
                }
                _ => Term::Var(g.clone()),
            };
            self.fn_metas[i].0 = Some(head);
            if xs.iter().zip(ys).all(|(x, y)| self.ut(x, y)) {
                return true;
            }
            self.restore(save);
        }
        // 2. パターン：?F(x, y) =?= u なら ?F := ((x, y) ↦ u)
        let mut vs = BTreeSet::new();
        u.vars(&mut vs);
        if vs.contains(f) {
            return false;
        }
        let Some(ps) = self.pattern_params(f, xs, &vs) else { return false };
        let xnames: Vec<String> = xs.iter().filter_map(|x| if let Term::Var(v) = x { Some(v.clone()) } else { None }).collect();
        if vs.iter().any(|v| v.starts_with('#') && !xnames.contains(v)) {
            return false;
        }
        let subs: Vec<(String, Term)> = xnames.iter().cloned().zip(ps.iter().map(|(p, _)| Term::Var(p.clone()))).collect();
        let body = u.subst_many(&subs);
        self.fn_metas[i].0 = Some(self.curried_lam(i, ps, body));
        true
    }

    /// メタ変数 i の型に合わせて λ を入れ子にする（ℕ → (σ → τ) なら (i ↦ (x ↦ …))）
    fn curried_lam(&self, i: usize, ps: Vec<(String, String)>, mut body: Term) -> Term {
        let mut chunks: Vec<usize> = vec![];
        let mut t = Ty::parse(&self.zonk_sort(&self.fn_metas[i].1));
        while let Some(Ty::Fun(a, r)) = t {
            chunks.push(a.len());
            t = Some(*r);
        }
        let mut groups: Vec<Vec<(String, String)>> = vec![];
        let mut start = 0;
        for c in &chunks {
            if start >= ps.len() {
                break;
            }
            let end = (start + c).min(ps.len());
            groups.push(ps[start..end].to_vec());
            start = end;
        }
        if start < ps.len() {
            groups.push(ps[start..].to_vec());
        }
        for g in groups.into_iter().rev() {
            body = Term::Lam(g, Box::new(body));
        }
        body
    }

    /// ?P(xs) =?= φ を解く
    fn solve_pred(&mut self, p: &str, xs: &[Term], phi: &Formula) -> bool {
        let i = Self::fn_meta_index(p).unwrap();
        if let Formula::Atom(q, ys) = phi
            && ys.len() == xs.len()
            && !self.is_open_fn_meta(q)
            && !["=", "<", "≤", ">", "≥"].contains(&q.as_str())
        {
            let save = self.save();
            self.fn_metas[i].0 = Some(Term::Var(q.clone()));
            if xs.iter().zip(ys).all(|(x, y)| self.ut(x, y)) {
                return true;
            }
            self.restore(save);
        }
        let vs = phi.free_vars();
        if vs.contains(p) {
            return false;
        }
        let Some(ps) = self.pattern_params(p, xs, &vs) else { return false };
        let xnames: Vec<String> = xs.iter().filter_map(|x| if let Term::Var(v) = x { Some(v.clone()) } else { None }).collect();
        if vs.iter().any(|v| v.starts_with('#') && !xnames.contains(v)) {
            return false;
        }
        let subs: Vec<(String, Term)> = xnames.iter().cloned().zip(ps.iter().map(|(p, _)| Term::Var(p.clone()))).collect();
        self.fn_metas[i].0 = Some(Term::Set(ps, Box::new(phi.subst_many(&subs))));
        true
    }
}

/// 束縛変数・λ・集合の型に、決まっていない型 ?σ が残っているか
fn sort_holes_t(t: &Term) -> bool {
    match t {
        Term::App(_, a) => a.iter().any(sort_holes_t),
        Term::Lam(ps, b) => ps.iter().any(|(_, s)| s.contains("?σ")) || sort_holes_t(b),
        Term::Set(ps, phi) => ps.iter().any(|(_, s)| s.contains("?σ")) || sort_holes_f(phi),
        _ => false,
    }
}

fn sort_holes_f(f: &Formula) -> bool {
    match f {
        Formula::Atom(_, ts) => ts.iter().any(sort_holes_t),
        Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => sort_holes_f(a) || sort_holes_f(b),
        Formula::Forall(_, s, b) | Formula::Exists(_, s, b) => s.contains("?σ") || sort_holes_f(b),
        Formula::Bot => false,
    }
}

fn occurs(m: u32, t: &Term) -> bool {
    match t {
        Term::Meta(n) => *n == m,
        Term::App(_, a) => a.iter().any(|x| occurs(m, x)),
        Term::Lam(_, b) => occurs(m, b),
        Term::Set(_, phi) => phi.has_meta(),
        _ => false,
    }
}
