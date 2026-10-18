//! 根拠の解釈：`h(a, b)`・`thm(…)`・`h.left`・`refl`・`ring`・`linarith`・`EQ2` など。
//! どれも (示す命題, 証明項) を返す。

use super::{BUILTINS, CResult, Checker, Ctx, Entry};
use crate::kernel::arith::{decide, ring_eq};
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term, instantiate, is_fn_sort};
use std::collections::BTreeSet;

impl<'a> Checker<'a> {
    // ------------------------------------------------ 名前

    /// 名前が示す命題と、その証明項
    pub(super) fn resolve(&mut self, ctx: &Ctx, name: &str) -> CResult<(Formula, Proof)> {
        if let Some(f) = ctx.hyp(name) {
            return Ok((f.clone(), Proof::Hyp(name.to_string())));
        }
        if ctx.is_term_var(name) {
            return self.err(format!("`{name}` は項（対象）であって、証拠ではない"));
        }
        if self.env.failed.contains(name) {
            return self.err(format!("`{name}` は検証に失敗した定理なので使えない"));
        }
        if let Some(sc) = self.env.kernel.thms.get(name).cloned() {
            // ソート変数・パラメータを穴にして具体化する
            let sorts: Vec<String> = sc.sort_params.iter().map(|_| self.new_sort_meta()).collect();
            let (params, preds, formula) = sc.instance(&sorts);
            let mut args = Vec::new();
            for (_, s) in &params {
                args.push(if is_fn_sort(s) { Term::Var(self.new_fn_meta()) } else { self.new_meta() });
            }
            // 図式の局所述語は、この定理でも同じ名前・同じ型で使う
            for (p, ss) in preds {
                match self.sig.preds.get(&p).cloned() {
                    Some(have) => {
                        if have.len() != ss.len() || !have.iter().zip(&ss).all(|(a, b)| self.unify_sort(a, b)) {
                            return self.err(format!("`{name}` の述語 `{p}` の型が、この定理の `{p}` と違う"));
                        }
                    }
                    None => {
                        self.sig.preds.insert(p, ss);
                    }
                }
            }
            let vs = self.var_sorts(ctx);
            for ((_, s), a) in params.iter().zip(&args) {
                if !is_fn_sort(s) {
                    self.pending.push((vs.clone(), s.clone(), a.clone()));
                }
            }
            let f = instantiate(&params, &formula, &args);
            return Ok((f, Proof::Thm { name: name.to_string(), sorts, args }));
        }
        if let Some(base) = name.strip_suffix(".def") {
            if let Some(d) = self.env.kernel.defs.get(base).cloned() {
                // 定義の同値 P(x) ↔ φ(x)：kernel は δ で両辺を同一視するので、どちら向きも恒等写像で示せる
                let mut args = Vec::new();
                for (_, s) in &d.params {
                    args.push(if is_fn_sort(s) { Term::Var(self.new_fn_meta()) } else { self.new_meta() });
                }
                let atom = Formula::Atom(base.to_string(), args.clone());
                let body = instantiate(&d.params, &d.body, &args);
                let id = |a: &Formula| Proof::ImpI { h: "#d".into(), phi: a.clone(), body: Proof::Hyp("#d".into()).b() };
                let f = Formula::And(
                    Box::new(Formula::Imp(Box::new(atom.clone()), Box::new(body.clone()))),
                    Box::new(Formula::Imp(Box::new(body.clone()), Box::new(atom.clone()))),
                );
                return Ok((f, Proof::AndI(id(&atom).b(), id(&body).b())));
            }
        }
        if let Some((base, field)) = name.rsplit_once('.') {
            if field == "left" || field == "right" {
                let (f, p) = self.resolve(ctx, base)?;
                return match self.whnf(&self.norm(ctx, &f)) {
                    Formula::And(a, b) => {
                        let right = field == "right";
                        Ok((if right { *b } else { *a }, Proof::AndE { right, p: p.b() }))
                    }
                    g => self.err(format!("`{base}` は「{g}」で ∧ の形ではないので、.{field} は使えない")),
                };
            }
        }
        self.err(format!("`{name}` が見つからない（文脈にも定理にもない）"))
    }

    pub(super) fn names_proof(&self, ctx: &Ctx, n: &str) -> bool {
        if ctx.hyp(n).is_some() {
            return true;
        }
        if ctx.is_term_var(n) {
            return false;
        }
        if self.env.kernel.thms.contains_key(n) || self.env.failed.contains(n) || BUILTINS.contains(&n) {
            return true;
        }
        if let Some(base) = n.strip_suffix(".def") {
            if self.env.kernel.defs.contains_key(base) {
                return true;
            }
        }
        match n.rsplit_once('.') {
            Some((base, "left" | "right")) => self.names_proof(ctx, base),
            _ => false,
        }
    }

    pub(super) fn is_proof(&self, ctx: &Ctx, t: &Term) -> bool {
        match t {
            Term::Var(n) | Term::App(n, _) => self.names_proof(ctx, n),
            _ => false,
        }
    }

    pub(super) fn check_term_scope(&self, ctx: &Ctx, t: &Term) -> CResult<()> {
        let mut vs = BTreeSet::new();
        t.vars(&mut vs);
        for v in vs {
            if !ctx.is_term_var(&v) {
                return self.err(format!("`{v}` は文脈にない（スコープの外か、まだ導入されていない）"));
            }
        }
        Ok(())
    }

    // ------------------------------------------------ 根拠

    /// 根拠 p が示す命題と証明項
    pub(super) fn infer(&mut self, ctx: &Ctx, p: &Term) -> CResult<(Formula, Proof)> {
        match p {
            Term::Var(n) | Term::App(n, _) if BUILTINS.contains(&n.as_str()) => self.err(format!(
                "`{n}` は、示すべき命題が決まっている場所（goal・have・連鎖）でしか使えない"
            )),
            Term::Var(n) => self.resolve(ctx, n),
            Term::App(n, args) => {
                let (f, pf) = self.resolve(ctx, n)?;
                self.apply(ctx, f, pf, args)
            }
            _ => self.err(format!("`{p}` は根拠として読めない")),
        }
    }

    /// ∀除去（項を渡す）と →除去（証拠を渡す）を引数の順に行う
    fn apply(&mut self, ctx: &Ctx, f: Formula, pf: Proof, args: &[Term]) -> CResult<(Formula, Proof)> {
        let (mut f, mut pf) = (f, pf);
        for arg in args {
            loop {
                match self.whnf(&f) {
                    Formula::Forall(x, s, body) => {
                        if self.is_proof(ctx, arg) {
                            // 証拠が来たら、∀ の変数は単一化で決める
                            let m = self.new_meta();
                            f = body.subst(&x, &m);
                            pf = Proof::AllE(pf.b(), m);
                            continue;
                        }
                        self.check_term_scope(ctx, arg)?;
                        if let Some(t) = self.term_sort(ctx, arg) {
                            if !self.unify_sort(&s, &t) {
                                let s = self.zonk_sort(&s);
                                return self.err(format!("型が違う：`{arg}` は {t} だが、ここには {s} の項が必要"));
                            }
                        }
                        f = body.subst(&x, arg);
                        pf = Proof::AllE(pf.b(), arg.clone());
                    }
                    Formula::Imp(a, b) => {
                        if !self.is_proof(ctx, arg) {
                            let a = self.zonk_f(&a);
                            return self.err(format!("ここには「{a}」の証拠が必要だが、項 `{arg}` が渡された"));
                        }
                        let q = self.check(ctx, arg, &a)?;
                        pf = Proof::ImpE(pf.b(), q.b());
                        f = *b;
                    }
                    g => return self.err(format!("引数が多すぎる（「{g}」にはもう `{arg}` を渡せない）")),
                }
                break;
            }
        }
        Ok((f, pf))
    }

    pub(super) fn check_just(&mut self, ctx: &Ctx, j: &[Term], expected: &Formula) -> CResult<Proof> {
        if j.len() == 1 {
            return self.check(ctx, &j[0], expected);
        }
        // j₁, j₂, … は ∧導入
        let e = self.norm(ctx, expected);
        let Some(parts) = self.split_and_w(&e, j.len()) else {
            return self.err(format!(
                "根拠が {} 個あるが、示すべき「{e}」は {} 個の ∧ ではない",
                j.len(),
                j.len()
            ));
        };
        let mut proofs = Vec::new();
        for (p, f) in j.iter().zip(parts) {
            proofs.push(self.check(ctx, p, &f)?);
        }
        let mut acc = proofs.pop().unwrap();
        while let Some(p) = proofs.pop() {
            acc = Proof::AndI(p.b(), acc.b());
        }
        Ok(acc)
    }

    /// 根拠 p が命題 expected を示す証明項
    pub(super) fn check(&mut self, ctx: &Ctx, p: &Term, expected: &Formula) -> CResult<Proof> {
        let e = self.norm(ctx, expected);
        let is_builtin = matches!(p, Term::Var(n) | Term::App(n, _) if BUILTINS.contains(&n.as_str()));
        let e = if is_builtin { self.whnf(&e) } else { e };
        match p {
            Term::Var(n) if n == "refl" => match &e {
                Formula::Atom(r, ts) if r == "=" && self.ut(&ts[0], &ts[1]) => Ok(Proof::Refl(ts[0].clone())),
                _ => self.err(format!("refl で示せるのは t = t の形だけ（必要なのは「{e}」）")),
            },
            Term::Var(n) if n == "ring" => {
                if e.has_meta() {
                    return self.err("ring に渡す命題がまだ決まっていない");
                }
                match &e {
                    Formula::Atom(r, ts) if r == "=" && ring_eq(&ts[0], &ts[1]) => {
                        Ok(Proof::Ring { lhs: ts[0].clone(), rhs: ts[1].clone() })
                    }
                    _ => self.err(format!("ring では「{e}」を示せない")),
                }
            }
            Term::Var(n) if n == "sorry" => {
                self.sorries.push((self.line, self.snapshot.0.show(), e.clone()));
                Ok(Proof::Sorry(e))
            }
            Term::Var(n) if n == "linarith" => self.linarith(ctx, vec![], &e),
            Term::App(n, hints) if n == "linarith" => {
                let mut extra = Vec::new();
                for h in hints {
                    extra.push(self.infer(ctx, h)?);
                }
                self.linarith(ctx, extra, &e)
            }
            Term::Var(n) if n == "decide" => {
                if !e.free_vars().is_empty() || e.has_meta() {
                    return self.err(format!("decide は変数を含まない命題にしか使えない（「{e}」）"));
                }
                match decide(&e) {
                    Some(true) => Ok(Proof::Decide(e)),
                    Some(false) => self.err(format!("decide：「{e}」は偽")),
                    None => self.err(format!("decide では「{e}」を計算できない")),
                }
            }
            Term::App(n, args) if n == "EQ2" => self.eq2(ctx, args, &e),
            Term::App(n, args) if (n == "or.left" || n == "or.right") && args.len() == 1 => match &e {
                Formula::Or(l, r) => {
                    let right = n == "or.right";
                    let q = self.check(ctx, &args[0], if right { r } else { l })?;
                    let other = if right { (**l).clone() } else { (**r).clone() };
                    Ok(Proof::OrI { right, other, p: q.b() })
                }
                _ => self.err(format!("{n} で示せるのは ∨ の形だけ（必要なのは「{e}」）")),
            },
            _ => {
                let (f, pf) = self.infer(ctx, p)?;
                if self.unify(ctx, &f, &e) {
                    return Ok(pf);
                }
                let f = self.norm(ctx, &f);
                if f == Formula::Bot {
                    return Ok(Proof::BotE(e, pf.b())); // ⊥除去
                }
                let e = self.norm(ctx, &e);
                self.err(format!("根拠 `{p}` が示すのは\n      {f}\n    だが、必要なのは\n      {e}"))
            }
        }
    }

    // ------------------------------------------------ linarith（証明書を探す）

    /// 命題 f を (関係, 左, 右, 証明項) の事実に分解する（∧ は分ける）
    fn facts_of(&self, f: &Formula, p: Proof, out: &mut Vec<(String, Term, Term, Proof)>) {
        match f {
            Formula::Atom(r, ts) if ["=", "<", "≤", ">", "≥"].contains(&r.as_str()) && ts.len() == 2 && !f.has_meta() => {
                out.push((r.clone(), ts[0].clone(), ts[1].clone(), p))
            }
            Formula::And(a, b) => {
                self.facts_of(a, Proof::AndE { right: false, p: p.clone().b() }, out);
                self.facts_of(b, Proof::AndE { right: true, p: p.b() }, out);
            }
            _ => {}
        }
    }

    /// 文脈の仮定と extra から、線形算術で e を示す証明項（kernel が検算する証明書つき）
    pub(super) fn linarith(&mut self, ctx: &Ctx, extra: Vec<(Formula, Proof)>, e: &Formula) -> CResult<Proof> {
        let e = self.norm(ctx, e);
        let (rel, l, r) = match &e {
            Formula::Atom(rel, ts) if ts.len() == 2 && !e.has_meta() => (rel.clone(), ts[0].clone(), ts[1].clone()),
            _ => return self.err(format!("linarith では「{e}」を示せない（等式・不等式ではない）")),
        };
        if rel == "=" {
            let le = Formula::Atom("≤".into(), vec![l.clone(), r.clone()]);
            let ge = Formula::Atom("≥".into(), vec![l, r]);
            let p1 = self.linarith(ctx, extra.clone(), &le)?;
            let p2 = self.linarith(ctx, extra, &ge)?;
            return Ok(Proof::Antisymm(p1.b(), p2.b()));
        }
        let goal_sort = self.term_sort(ctx, &l).or_else(|| self.term_sort(ctx, &r));
        let mut facts = Vec::new();
        for (f, p) in extra {
            let f = self.norm(ctx, &f);
            self.facts_of(&f, p, &mut facts);
        }
        for en in &ctx.entries {
            match en {
                Entry::Hyp(h, f) => {
                    let f = self.norm(ctx, f);
                    self.facts_of(&f, Proof::Hyp(h.clone()), &mut facts);
                }
                Entry::Var(x, s, _) if self.zonk_sort(s) == "ℕ" && goal_sort.as_deref() == Some("ℕ") => {
                    let v = Term::Var(x.clone());
                    facts.push(("≥".into(), v.clone(), Term::Num(0), Proof::NatNonneg(v)));
                }
                _ => {}
            }
        }
        // 目標と同じソートの事実だけを使う（kernel は型の混ざった証明書を受け付けない）
        facts.retain(|(_, a, b, _)| {
            let s = self.term_sort(ctx, a).or_else(|| self.term_sort(ctx, b));
            s.is_none() || goal_sort.is_none() || s == goal_sort
        });
        let fs: Vec<(String, Term, Term)> = facts.iter().map(|(r, a, b, _)| (r.clone(), a.clone(), b.clone())).collect();
        let Some(cert) = crate::arith::find_certificate(&fs, (&rel, &l, &r)) else {
            return self.err(format!("linarith では「{e}」を示せない"));
        };
        let mut used = Vec::new();
        let mut coeffs = Vec::new();
        for ((_, _, _, p), c) in facts.into_iter().zip(&cert) {
            if !c.is_zero() {
                used.push(p);
                coeffs.push(*c);
            }
        }
        coeffs.push(*cert.last().unwrap());
        Ok(Proof::LinArith { goal: e, facts: used, coeffs })
    }

    // ------------------------------------------------ EQ2（等号による書き換え）

    /// EQ2(h, hφ)：h : x = y、hφ : φ(x) から φ(y)。φ は goal と hφ を見比べて決める。
    fn eq2(&mut self, ctx: &Ctx, args: &[Term], g: &Formula) -> CResult<Proof> {
        if args.len() != 2 {
            return self.err("EQ2 は EQ2(h, hφ) の形で書く");
        }
        let (h, hp) = self.infer(ctx, &args[0])?;
        let h = self.norm(ctx, &h);
        let (x, y) = match &h {
            Formula::Atom(r, ts) if r == "=" && !h.has_meta() => (ts[0].clone(), ts[1].clone()),
            _ => return self.err(format!("EQ2 の第1引数は等式の証拠（「{h}」は等式ではない）")),
        };
        if g.has_meta() {
            return self.err("EQ2 の結論がまだ決まっていない");
        }
        let refl = |t: &Term| Formula::Atom("=".into(), vec![t.clone(), t.clone()]);
        let cands: Vec<(Formula, Proof)> = if args[1] == Term::Var("refl".into()) {
            let mut c = vec![];
            if let Formula::Atom(r, ts) = g {
                if r == "=" {
                    c.push((refl(&ts[0]), Proof::Refl(ts[0].clone())));
                    c.push((refl(&ts[1]), Proof::Refl(ts[1].clone())));
                }
            }
            c.push((refl(&x), Proof::Refl(x.clone())));
            c.push((refl(&y), Proof::Refl(y.clone())));
            c
        } else {
            let (f, p) = self.infer(ctx, &args[1])?;
            vec![(self.norm(ctx, &f), p)]
        };
        for (pf, pp) in cands {
            if repl_f(&pf, g, &x, &y) {
                self.fresh += 1;
                let z = format!("#z{}", self.fresh);
                let motive = motive_f(&pf, g, &x, &y, &z);
                return Ok(Proof::Subst { eq: hp.b(), z, motive, p: pp.b() });
            }
        }
        self.err(format!("EQ2：{x} の一部を {y} に置き換えても「{g}」にならない"))
    }
}

fn repl_t(p: &Term, g: &Term, x: &Term, y: &Term) -> bool {
    if p == g || (p == x && g == y) {
        return true;
    }
    match (p, g) {
        (Term::App(f, ps), Term::App(h, gs)) => {
            f == h && ps.len() == gs.len() && ps.iter().zip(gs).all(|(a, b)| repl_t(a, b, x, y))
        }
        _ => false,
    }
}

/// g が p の中の x のいくつかを y に置き換えたものか
fn repl_f(p: &Formula, g: &Formula, x: &Term, y: &Term) -> bool {
    use Formula::*;
    match (p, g) {
        (Atom(a, ps), Atom(b, gs)) => a == b && ps.len() == gs.len() && ps.iter().zip(gs).all(|(s, t)| repl_t(s, t, x, y)),
        (Imp(a1, b1), Imp(a2, b2)) | (And(a1, b1), And(a2, b2)) | (Or(a1, b1), Or(a2, b2)) => {
            repl_f(a1, a2, x, y) && repl_f(b1, b2, x, y)
        }
        (Forall(v, t, b1), Forall(w, s, b2)) | (Exists(v, t, b1), Exists(w, s, b2)) => {
            v == w && t == s && repl_f(b1, b2, x, y)
        }
        (Bot, Bot) => true,
        _ => false,
    }
}

/// 置き換えた位置を z にした「動機」φ(z)：φ(x) が p、φ(y) が g になる
fn motive_t(p: &Term, g: &Term, x: &Term, y: &Term, z: &str) -> Term {
    if p == g {
        return p.clone();
    }
    if p == x && g == y {
        return Term::Var(z.to_string());
    }
    match (p, g) {
        (Term::App(f, ps), Term::App(_, gs)) => {
            Term::App(f.clone(), ps.iter().zip(gs).map(|(a, b)| motive_t(a, b, x, y, z)).collect())
        }
        _ => p.clone(),
    }
}

fn motive_f(p: &Formula, g: &Formula, x: &Term, y: &Term, z: &str) -> Formula {
    use Formula::*;
    let go = |a: &Formula, b: &Formula| Box::new(motive_f(a, b, x, y, z));
    match (p, g) {
        (Atom(a, ps), Atom(_, gs)) => Atom(a.clone(), ps.iter().zip(gs).map(|(s, t)| motive_t(s, t, x, y, z)).collect()),
        (Imp(a1, b1), Imp(a2, b2)) => Imp(go(a1, a2), go(b1, b2)),
        (And(a1, b1), And(a2, b2)) => And(go(a1, a2), go(b1, b2)),
        (Or(a1, b1), Or(a2, b2)) => Or(go(a1, a2), go(b1, b2)),
        (Forall(v, t, b1), Forall(_, _, b2)) => Forall(v.clone(), t.clone(), go(b1, b2)),
        (Exists(v, t, b1), Exists(_, _, b2)) => Exists(v.clone(), t.clone(), go(b1, b2)),
        _ => p.clone(),
    }
}
