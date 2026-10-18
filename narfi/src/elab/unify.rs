//! メタ変数と単一化。
//!
//! 「まだ決まっていないもの」を穴（メタ変数）として置き、式どうしを見比べて穴を埋める。
//! - 項のメタ変数 `Term::Meta(n)`：定理を使うときの暗黙の引数など
//! - ソートのメタ変数 `?σn`：ソート変数を持つ定理（`eq.symm` など）を使うとき
//! - 関数記号のメタ変数 `?Fn`：局所関数記号を持つ定理を使うとき
//! 最後に zonk（穴を中身で置き換える）してから kernel に渡す。

use super::{CResult, Checker, Ctx};
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term};
use std::collections::BTreeSet;

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

    pub(super) fn new_fn_meta(&mut self) -> String {
        self.fn_metas.push(None);
        format!("?F{}", self.fn_metas.len() - 1)
    }

    fn sort_meta_index(s: &str) -> Option<usize> {
        s.strip_prefix("?σ")?.parse().ok()
    }

    fn fn_meta_index(s: &str) -> Option<usize> {
        s.strip_prefix("?F")?.parse().ok()
    }

    // ------------------------------------------------ zonk（穴を中身で置き換える）

    pub(super) fn zonk_sort(&self, s: &str) -> String {
        // 関数型（`?σ1 → ℝ`）の中も置き換える
        if s.contains(' ') {
            return s.split(' ').map(|w| self.zonk_sort(w)).collect::<Vec<_>>().join(" ");
        }
        match Self::sort_meta_index(s) {
            Some(i) => match &self.sort_metas[i] {
                Some(t) => self.zonk_sort(t),
                None => s.to_string(),
            },
            None => s.to_string(),
        }
    }

    fn zonk_fn(&self, f: &str) -> String {
        match Self::fn_meta_index(f) {
            Some(i) => match &self.fn_metas[i] {
                Some(g) => self.zonk_fn(g),
                None => f.to_string(),
            },
            None => f.to_string(),
        }
    }

    pub(super) fn zonk_t(&self, t: &Term) -> Term {
        match t {
            Term::Meta(m) => match &self.metas[*m as usize] {
                Some(u) => self.zonk_t(u),
                None => t.clone(),
            },
            Term::App(f, a) => Term::App(self.zonk_fn(f), a.iter().map(|x| self.zonk_t(x)).collect()),
            Term::Var(x) if Self::fn_meta_index(x).is_some() => Term::Var(self.zonk_fn(x)),
            _ => t.clone(),
        }
    }

    pub(super) fn zonk_f(&self, f: &Formula) -> Formula {
        match f {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| self.zonk_t(t)).collect()),
            Formula::Imp(a, b) => Formula::Imp(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::And(a, b) => Formula::And(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), self.zonk_sort(t), Box::new(self.zonk_f(b))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), self.zonk_sort(t), Box::new(self.zonk_f(b))),
            Formula::Bot => Formula::Bot,
        }
    }

    /// 証明項の穴をすべて埋める。埋まらない穴が残ればエラー。
    pub(super) fn zonk_proof(&self, p: &Proof) -> CResult<Proof> {
        let zf = |f: &Formula| -> CResult<Formula> {
            let g = self.zonk_f(f);
            if g.has_meta() {
                return self.err(format!("決まらない項が残っている：{g}（引数を明示する）"));
            }
            Ok(g)
        };
        let zt = |t: &Term| -> CResult<Term> {
            let u = self.zonk_t(t);
            if u.has_meta() {
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
                args: args.iter().map(|t| zt(t)).collect::<CResult<_>>()?,
            },
            Proof::ImpI { h, phi, body } => Proof::ImpI { h: h.clone(), phi: zf(phi)?, body: b(body)? },
            Proof::ImpE(p, q) => Proof::ImpE(b(p)?, b(q)?),
            Proof::AndI(p, q) => Proof::AndI(b(p)?, b(q)?),
            Proof::AndE { right, p } => Proof::AndE { right: *right, p: b(p)? },
            Proof::OrI { right, other, p } => Proof::OrI { right: *right, other: zf(other)?, p: b(p)? },
            Proof::OrE { p, h1, q1, h2, q2 } => {
                Proof::OrE { p: b(p)?, h1: h1.clone(), q1: b(q1)?, h2: h2.clone(), q2: b(q2)? }
            }
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
            Proof::Ind { x, phi, base, k, ih, step } => Proof::Ind {
                x: x.clone(),
                phi: zf(phi)?,
                base: b(base)?,
                k: k.clone(),
                ih: ih.clone(),
                step: b(step)?,
            },
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
            Formula::Atom(p, ts) => {
                let d = self.env.kernel.defs.get(p)?;
                (d.params.len() == ts.len()).then(|| crate::syntax::instantiate(&d.params, &d.body, ts))
            }
            _ => None,
        }
    }

    /// names に挙げた定義を、式の中のすべての位置で展開する
    pub(super) fn unfold_named(&self, f: &Formula, names: &[String]) -> Formula {
        let go = |g: &Formula| self.unfold_named(g, names);
        match f {
            Formula::Atom(p, _) if names.contains(p) => match self.unfold_head(f) {
                Some(g) => go(&g),
                None => f.clone(),
            },
            Formula::Atom(..) | Formula::Bot => f.clone(),
            Formula::Imp(a, b) => Formula::Imp(Box::new(go(a)), Box::new(go(b))),
            Formula::And(a, b) => Formula::And(Box::new(go(a)), Box::new(go(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(go(a)), Box::new(go(b))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), t.clone(), Box::new(go(b))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), t.clone(), Box::new(go(b))),
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

    // ------------------------------------------------ 単一化

    pub(super) fn unify_sort(&mut self, a: &str, b: &str) -> bool {
        let (a, b) = (self.zonk_sort(a), self.zonk_sort(b));
        if a == b {
            return true;
        }
        if let Some(i) = Self::sort_meta_index(&a) {
            self.sort_metas[i] = Some(b);
            return true;
        }
        if let Some(i) = Self::sort_meta_index(&b) {
            self.sort_metas[i] = Some(a);
            return true;
        }
        // 関数型どうし：語ごとに
        let (wa, wb): (Vec<&str>, Vec<&str>) = (a.split(' ').collect(), b.split(' ').collect());
        if wa.len() > 1 && wa.len() == wb.len() {
            let (wa, wb): (Vec<String>, Vec<String>) =
                (wa.iter().map(|s| s.to_string()).collect(), wb.iter().map(|s| s.to_string()).collect());
            return wa.iter().zip(&wb).all(|(x, y)| self.unify_sort(x, y));
        }
        false
    }

    fn save(&self) -> (Vec<Option<Term>>, Vec<Option<String>>, Vec<Option<String>>) {
        (self.metas.clone(), self.sort_metas.clone(), self.fn_metas.clone())
    }

    fn restore(&mut self, s: (Vec<Option<Term>>, Vec<Option<String>>, Vec<Option<String>>)) {
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
        }
        ok
    }

    fn uf(&mut self, a: &Formula, b: &Formula) -> bool {
        use Formula::*;
        match (a, b) {
            (Atom(p, ts), Atom(q, us)) if p == q && ts.len() == us.len() => {
                let save = self.save();
                if ts.iter().zip(us).all(|(t, u)| self.ut(t, u)) {
                    return true;
                }
                // 引数が合わなくても、展開すれば一致することがある
                self.restore(save);
                match (self.unfold_head(a), self.unfold_head(b)) {
                    (Some(x), Some(y)) => {
                        let (x, y) = (self.zonk_f(&x), self.zonk_f(&y));
                        self.uf(&x, &y)
                    }
                    _ => false,
                }
            }
            (Imp(a1, b1), Imp(a2, b2)) | (And(a1, b1), And(a2, b2)) | (Or(a1, b1), Or(a2, b2)) => {
                self.uf(a1, a2) && self.uf(b1, b2)
            }
            (Forall(x, t1, b1), Forall(y, t2, b2)) | (Exists(x, t1, b1), Exists(y, t2, b2)) => {
                if !self.unify_sort(t1, t2) {
                    return false;
                }
                self.fresh += 1;
                let v = Term::Var(format!("#{}", self.fresh));
                self.uf(&b1.subst(x, &v), &b2.subst(y, &v))
            }
            (Bot, Bot) => true,
            // 形が違っても、片方が定義された述語なら展開して比べる
            _ => {
                if let Some(x) = self.unfold_head(a) {
                    let x = self.zonk_f(&x);
                    self.uf(&x, b)
                } else if let Some(y) = self.unfold_head(b) {
                    let y = self.zonk_f(&y);
                    self.uf(a, &y)
                } else {
                    false
                }
            }
        }
    }

    pub(super) fn ut(&mut self, a: &Term, b: &Term) -> bool {
        let (a, b) = (self.zonk_t(a), self.zonk_t(b));
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
            (Term::Var(x), Term::Var(y)) => self.unify_fn_name(x, y),
            (Term::Num(x), Term::Num(y)) => x == y,
            (Term::App(f, xs), Term::App(g, ys)) => {
                xs.len() == ys.len() && self.unify_fn_name(f, g) && xs.iter().zip(ys).all(|(x, y)| self.ut(x, y))
            }
            _ => false,
        }
    }

    /// 関数記号の名前どうし（関数記号のメタ変数があれば埋める）
    fn unify_fn_name(&mut self, f: &str, g: &str) -> bool {
        let (f, g) = (self.zonk_fn(f), self.zonk_fn(g));
        if f == g {
            return true;
        }
        if let Some(i) = Self::fn_meta_index(&f) {
            self.fn_metas[i] = Some(g);
            return true;
        }
        if let Some(i) = Self::fn_meta_index(&g) {
            self.fn_metas[i] = Some(f);
            return true;
        }
        false
    }
}

fn occurs(m: u32, t: &Term) -> bool {
    match t {
        Term::Meta(n) => *n == m,
        Term::App(_, a) => a.iter().any(|x| occurs(m, x)),
        _ => false,
    }
}
