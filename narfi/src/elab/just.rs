//! 根拠の解釈：`h(a, b)`・`thm(…)`・`h.left`・`refl`・`ring`・`linarith`・`EQ2` など。
//! どれも (示す命題, 証明項) を返す。

use super::{BUILTINS, CResult, Checker, Ctx, Entry, RULES};
use crate::kernel::arith::{decide, ring_eq};
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term, instantiate};
use crate::types::Ty;
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
            // 型変数・パラメータを穴にして具体化する
            let tys: Vec<String> = sc.type_params.iter().map(|_| self.new_sort_meta()).collect();
            let (params, formula) = sc.instance(&tys);
            let args = self.holes_for(&params);
            let vs = self.var_sorts(ctx);
            for ((_, s), a) in params.iter().zip(&args) {
                if !is_higher(s) {
                    self.pending.push((vs.clone(), s.clone(), a.clone()));
                }
            }
            let f = instantiate(&params, &formula, &args);
            return Ok((f, Proof::Thm { name: name.to_string(), sorts: tys, args }));
        }
        if let Some(base) = name.strip_suffix(".def") {
            if let Some(d) = self.env.kernel.defs.get(base).cloned() {
                if let crate::kernel::env::DefBody::Pred(body) = &d.body {
                    // 定義の同値 P(x) ↔ φ(x)：kernel は δ で両辺を同一視するので、どちら向きも恒等写像で示せる
                    let args = self.holes_for(&d.params);
                    let atom = Formula::Atom(base.to_string(), args.clone());
                    let body = instantiate(&d.params, body, &args);
                    let id = |a: &Formula| Proof::ImpI { h: "#d".into(), phi: a.clone(), body: Proof::Hyp("#d".into()).b() };
                    let f = Formula::And(
                        Box::new(Formula::Imp(Box::new(atom.clone()), Box::new(body.clone()))),
                        Box::new(Formula::Imp(Box::new(body.clone()), Box::new(atom.clone()))),
                    );
                    return Ok((f, Proof::AndI(id(&atom).b(), id(&body).b())));
                }
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

    /// パラメータごとの穴：関数型・述語型・命題型なら関数の穴（λ や集合が入りうる）、それ以外は項の穴
    fn holes_for(&mut self, params: &[(String, String)]) -> Vec<Term> {
        params
            .iter()
            .map(|(_, s)| if is_higher(s) { Term::Var(self.new_fn_meta(s)) } else { self.new_meta() })
            .collect()
    }

    pub(super) fn names_proof(&self, ctx: &Ctx, n: &str) -> bool {
        if ctx.hyp(n).is_some() {
            return true;
        }
        if ctx.is_term_var(n) {
            return false;
        }
        if self.env.kernel.thms.contains_key(n) || self.env.failed.contains(n) || BUILTINS.contains(&n) || RULES.contains(&n) {
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
            if !ctx.is_term_var(&v) && !self.env.kernel.is_global(&v) {
                return self.err(format!("`{v}` は文脈にない（スコープの外か、まだ導入されていない）"));
            }
        }
        Ok(())
    }

    // ------------------------------------------------ 根拠

    /// 根拠 p が示す命題と証明項
    pub(super) fn infer(&mut self, ctx: &Ctx, p: &Term) -> CResult<(Formula, Proof)> {
        // h(a)(b) は h(a, b)（順に当てる）
        if let Term::App(at, args) = p {
            if at == "@" {
                if let Some(Term::App(g, a0)) = args.first() {
                    let mut all = a0.clone();
                    all.extend(args[1..].iter().cloned());
                    return self.infer(ctx, &Term::App(g.clone(), all));
                }
            }
        }
        match p {
            Term::Var(n) | Term::App(n, _) if BUILTINS.contains(&n.as_str()) => self.err(format!(
                "`{n}` は、示すべき命題が決まっている場所（goal・have・連鎖）でしか使えない"
            )),
            // 規則の名前（∧除去・→除去・∀除去）
            Term::App(n, args) if (n == "and.left" || n == "and.right") && args.len() == 1 => {
                let (f, pf) = self.infer(ctx, &args[0])?;
                match self.whnf(&self.norm(ctx, &f)) {
                    Formula::And(a, b) => {
                        let right = n == "and.right";
                        Ok((if right { *b } else { *a }, Proof::AndE { right, p: pf.b() }))
                    }
                    g => self.err(format!("{n} に渡せるのは ∧ の形の根拠だけ（「{g}」）")),
                }
            }
            Term::App(n, args) if (n == "imp.elim" || n == "all.elim") && !args.is_empty() => {
                let (f, pf) = self.infer(ctx, &args[0])?;
                self.apply(ctx, f, pf, &args[1..])
            }
            Term::Var(n) | Term::App(n, _) if n == "and.intro" || n == "bot.elim" => {
                self.err(format!("`{n}` は、示すべき命題が決まっている場所（goal・have・連鎖）でしか使えない"))
            }
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
                            // 証拠が来たら、∀ の変数は単一化で決める（関数型・述語型なら関数の穴）
                            let m = if is_higher(&self.zonk_sort(&s)) { Term::Var(self.new_fn_meta(&s)) } else { self.new_meta() };
                            f = body.subst(&x, &m);
                            pf = Proof::AllE(pf.b(), m);
                            continue;
                        }
                        self.check_term_scope(ctx, arg)?;
                        let arg = &self.annotate_term(ctx, arg, Some(&s))?;
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
                    Formula::Atom(r, ts) if r == "=" && ring_eq(&self.unfold_terms(&ts[0]), &self.unfold_terms(&ts[1])) => {
                        Ok(Proof::Ring { lhs: ts[0].clone(), rhs: ts[1].clone() })
                    }
                    // 関数どうしの等式 (x ↦ s) = (x ↦ t)：各点で ring、funext で包む
                    Formula::Atom(r, ts) if r == "=" && matches!((&ts[0], &ts[1]), (Term::Lam(..), Term::Lam(..))) => {
                        let before = self.sort_metas.len();
                        let (f, pf) = self.infer(ctx, &Term::App("funext".into(), vec![ts[0].clone(), ts[1].clone()]))?;
                        // 値が数字だけの λ（(n ↦ 0 + 0)）は値の型が決まらない。数字だけの等式は
                        // どの数の型でも同じ真偽（埋め込みで保たれる）なので、決まらなければ ℝ で検査する
                        // 定義域は λ に書いた型で決める
                        if let (Term::Lam(ps, _), Formula::Imp(prem, _)) = (&ts[0], &self.zonk_f(&f)) {
                            if let (Formula::Forall(_, sx, _), [(_, dom)]) = (&**prem, ps.as_slice()) {
                                if let Some(k) = sx.strip_prefix("?σ").and_then(|k| k.parse::<usize>().ok()) {
                                    if k < self.sort_metas.len() && self.sort_metas[k].is_none() {
                                        self.sort_metas[k] = Some(dom.clone());
                                    }
                                }
                            }
                        }
                        for m in before..self.sort_metas.len() {
                            if self.sort_metas[m].is_none() {
                                self.sort_metas[m] = Some("ℝ".into());
                            }
                        }
                        let f = self.norm(ctx, &f);
                        match &f {
                            Formula::Imp(prem, _) => match &**prem {
                                Formula::Forall(x, sort, body) => match &**body {
                                    Formula::Atom(q, us) if q == "=" && ring_eq(&self.unfold_terms(&us[0]), &self.unfold_terms(&us[1])) => {
                                        let each = Proof::AllI { x: x.clone(), sort: sort.clone(), body: Proof::Ring { lhs: us[0].clone(), rhs: us[1].clone() }.b() };
                                        Ok(Proof::ImpE(pf.b(), each.b()))
                                    }
                                    _ => self.err(format!("ring では「{e}」を示せない（各点の等式「{body}」が ring で示せない）")),
                                },
                                _ => self.err(format!("ring では「{e}」を示せない")),
                            },
                            _ => self.err(format!("ring では「{e}」を示せない")),
                        }
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
                match decide(&self.unfold_terms_f(&e)) {
                    Some(true) => Ok(Proof::Decide(e)),
                    Some(false) => self.err(format!("decide：「{e}」は偽")),
                    None => self.err(format!("decide では「{e}」を計算できない")),
                }
            }
            Term::App(n, args) if n == "EQ2" => self.eq2(ctx, args, &e),
            Term::App(n, args) if n == "and.intro" && args.len() == 2 => match self.whnf(&e) {
                Formula::And(l, r) => {
                    let a = self.check(ctx, &args[0], &l)?;
                    let b = self.check(ctx, &args[1], &r)?;
                    Ok(Proof::AndI(a.b(), b.b()))
                }
                g => self.err(format!("and.intro で示せるのは ∧ の形だけ（必要なのは「{g}」）")),
            },
            Term::App(n, args) if n == "bot.elim" && args.len() == 1 => {
                let q = self.check(ctx, &args[0], &Formula::Bot)?;
                Ok(Proof::BotE(e, q.b()))
            }
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
                // 根拠が等式 x = y で、示すのも等式なら、代入として使う（EQ2(h, refl)。逆向きも）
                let is_eq = |g: &Formula| matches!(g, Formula::Atom(r, ts) if r == "=" && ts.len() == 2);
                if is_eq(&f) && is_eq(&e) && !e.has_meta() {
                    let refl = Term::Var("refl".into());
                    if let Ok(q) = self.eq2(ctx, &[p.clone(), refl.clone()], &e) {
                        return Ok(q);
                    }
                    if let Ok(q) = self.eq2(ctx, &[Term::App("eq.symm".into(), vec![p.clone()]), refl], &e) {
                        return Ok(q);
                    }
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
        self.linarith_in(ctx, extra, e, None)
    }

    /// `sort` は目標の型を外から決めるとき（⊥ を示すとき）
    fn linarith_in(&mut self, ctx: &Ctx, extra: Vec<(Formula, Proof)>, e: &Formula, sort: Option<&str>) -> CResult<Proof> {
        let e = self.norm(ctx, e);
        // 矛盾：どちらかの型の事実から 0 < 0 を導き、¬(0 < 0)（計算）に当てる
        if e == Formula::Bot {
            let zz = Formula::Atom("<".into(), vec![Term::Num(0), Term::Num(0)]);
            for s in ["ℝ", "ℕ"] {
                if let Ok(p) = self.linarith_in(ctx, extra.clone(), &zz, Some(s)) {
                    let not = Formula::Imp(Box::new(zz.clone()), Box::new(Formula::Bot));
                    return Ok(Proof::ImpE(Proof::Decide(not).b(), p.b()));
                }
            }
            return self.err("linarith では矛盾を導けない（仮定の不等式から 0 < 0 が出ない）");
        }
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
        let goal_sort = sort.map(String::from).or_else(|| self.term_sort(ctx, &l)).or_else(|| self.term_sort(ctx, &r));
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
        let fs: Vec<(String, Term, Term)> =
            facts.iter().map(|(r, a, b, _)| (r.clone(), self.unfold_terms(a), self.unfold_terms(b))).collect();
        let (ul, ur) = (self.unfold_terms(&l), self.unfold_terms(&r));
        let Some(cert) = crate::arith::find_certificate(&fs, (&rel, &ul, &ur)) else {
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

/// 頭の名前 f を g に置き換えてよいか（x・y が関数・述語の変数の名前のとき）
fn head_repl(f: &str, g: &str, x: &Term, y: &Term) -> bool {
    f == g || (*x == Term::Var(f.to_string()) && *y == Term::Var(g.to_string()))
}

fn repl_t(p: &Term, g: &Term, x: &Term, y: &Term) -> bool {
    if p == g || (p == x && g == y) {
        return true;
    }
    // x(t…) を y に置き換えると、y が λ なら β 簡約される（(n ↦ 0)(n) は 0）
    if let Term::App(f, ps) = p {
        if f == "@" && ps.first() == Some(x) && crate::syntax::apply_term(y, &ps[1..]) == *g {
            return true;
        }
    }
    match (p, g) {
        (Term::Lam(b1, t1), Term::Lam(b2, t2)) => b1 == b2 && repl_t(t1, t2, x, y),
        (Term::App(f, ps), Term::App(h, gs)) => {
            head_repl(f, h, x, y) && ps.len() == gs.len() && ps.iter().zip(gs).all(|(a, b)| repl_t(a, b, x, y))
        }
        _ => false,
    }
}

/// g が p の中の x のいくつかを y に置き換えたものか
fn repl_f(p: &Formula, g: &Formula, x: &Term, y: &Term) -> bool {
    use Formula::*;
    match (p, g) {
        (Atom(a, ps), Atom(b, gs)) => {
            head_repl(a, b, x, y) && ps.len() == gs.len() && ps.iter().zip(gs).all(|(s, t)| repl_t(s, t, x, y))
        }
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
    if let Term::App(f, ps) = p {
        if f == "@" && ps.first() == Some(x) && crate::syntax::apply_term(y, &ps[1..]) == *g {
            let mut args = vec![Term::Var(z.to_string())];
            args.extend(ps[1..].iter().cloned());
            return Term::App("@".into(), args);
        }
    }
    match (p, g) {
        (Term::Lam(b1, t1), Term::Lam(b2, t2)) if b1 == b2 => Term::Lam(b1.clone(), Box::new(motive_t(t1, t2, x, y, z))),
        (Term::App(f, ps), Term::App(h, gs)) => {
            let head = if f != h { z.to_string() } else { f.clone() };
            Term::App(head, ps.iter().zip(gs).map(|(a, b)| motive_t(a, b, x, y, z)).collect())
        }
        _ => p.clone(),
    }
}

fn motive_f(p: &Formula, g: &Formula, x: &Term, y: &Term, z: &str) -> Formula {
    use Formula::*;
    let go = |a: &Formula, b: &Formula| Box::new(motive_f(a, b, x, y, z));
    match (p, g) {
        (Atom(a, ps), Atom(b, gs)) => {
            let head = if a != b { z.to_string() } else { a.clone() };
            Atom(head, ps.iter().zip(gs).map(|(s, t)| motive_t(s, t, x, y, z)).collect())
        }
        (Imp(a1, b1), Imp(a2, b2)) => Imp(go(a1, a2), go(b1, b2)),
        (And(a1, b1), And(a2, b2)) => And(go(a1, a2), go(b1, b2)),
        (Or(a1, b1), Or(a2, b2)) => Or(go(a1, a2), go(b1, b2)),
        (Forall(v, t, b1), Forall(_, _, b2)) => Forall(v.clone(), t.clone(), go(b1, b2)),
        (Exists(v, t, b1), Exists(_, _, b2)) => Exists(v.clone(), t.clone(), go(b1, b2)),
        _ => p.clone(),
    }
}

/// 関数型・命題型（穴に λ・集合・論理式が入りうる型）か
fn is_higher(s: &str) -> bool {
    matches!(Ty::parse(s), Some(Ty::Fun(..)) | Some(Ty::Prop))
}

// ================================================================ 根拠の探索（書かれていない根拠の候補）
//
// 根拠を省いた行はエラーにし、ここで見つけた根拠を直し方（Tab で入る）として示す。
// 勝手に補うことはしない：使われた根拠は、必ずソースに書かれる。

thread_local! {
    static SEARCH_CACHE: std::cell::RefCell<std::collections::HashMap<String, Vec<String>>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// 1 回の探索で試す根拠の数の上限（重くならないように）
const SEARCH_BUDGET: usize = 2000;
const SEARCH_WANT: usize = 4;

type SearchSaved = (Vec<Option<Term>>, Vec<Option<String>>, Vec<(Option<Term>, String)>, Vec<(Vec<(String, String)>, String, Term)>, u32, usize, (Ctx, Option<Formula>), usize);

impl Checker<'_> {
    fn save_all(&self) -> SearchSaved {
        (
            self.metas.clone(),
            self.sort_metas.clone(),
            self.fn_metas.clone(),
            self.pending.clone(),
            self.fresh,
            self.line,
            self.snapshot.clone(),
            self.sorries.len(),
        )
    }

    fn restore_all(&mut self, s: SearchSaved) {
        self.metas = s.0;
        self.sort_metas = s.1;
        self.fn_metas = s.2;
        self.pending = s.3;
        self.fresh = s.4;
        self.line = s.5;
        self.set_snapshot(s.6 .0, s.6 .1);
        self.sorries.truncate(s.7);
    }

    /// 根拠 j で f が示せるか（状態は元に戻す）
    fn try_just(&mut self, ctx: &Ctx, j: &Term, f: &Formula) -> bool {
        let saved = self.save_all();
        let ok = self.check_just(ctx, std::slice::from_ref(j), f).is_ok();
        self.restore_all(saved);
        ok
    }

    /// f を示せる根拠の候補（見つかった順）
    pub(super) fn search_just(&mut self, ctx: &Ctx, f: &Formula) -> Vec<String> {
        let key = format!("{}|{}", self.zonk_f(f), ctx.show().join(";"));
        if let Some(v) = SEARCH_CACHE.with(|c| c.borrow().get(&key).cloned()) {
            return v;
        }
        let hyps: Vec<(String, Formula)> = ctx
            .entries
            .iter()
            .rev()
            .filter_map(|e| match e {
                Entry::Hyp(h, phi) if !h.starts_with('#') => Some((h.clone(), phi.clone())),
                _ => None,
            })
            .collect();
        let mut cands: Vec<Term> = Vec::new();
        for (h, _) in &hyps {
            cands.push(Term::Var(h.clone()));
        }
        for (h, phi) in &hyps {
            if let Formula::And(..) = self.whnf(phi) {
                cands.push(Term::Var(format!("{h}.left")));
                cands.push(Term::Var(format!("{h}.right")));
            }
        }
        cands.push(Term::Var("refl".into()));
        // 仮定（∀・→）を、ほかの仮定に当てる
        for (h, phi) in &hyps {
            if matches!(self.whnf(phi), Formula::Forall(..) | Formula::Imp(..)) {
                for (k, _) in &hyps {
                    if k != h {
                        cands.push(Term::App(h.clone(), vec![Term::Var(k.clone())]));
                    }
                }
            }
        }
        for b in ["linarith", "ring", "decide"] {
            cands.push(Term::Var(b.into()));
        }
        // 定理（そのまま・仮定に当てる）
        let mut thms: Vec<String> = self.env.kernel.thms.keys().cloned().collect();
        thms.sort();
        for t in &thms {
            cands.push(Term::Var(t.clone()));
        }
        for t in &thms {
            for (k, _) in &hyps {
                cands.push(Term::App(t.clone(), vec![Term::Var(k.clone())]));
            }
        }
        let mut found = Vec::new();
        for c in cands.into_iter().take(SEARCH_BUDGET) {
            if self.try_just(ctx, &c, f) {
                found.push(c.to_string());
                if found.len() >= SEARCH_WANT {
                    break;
                }
            }
        }
        SEARCH_CACHE.with(|c| c.borrow_mut().insert(key, found.clone()));
        found
    }

    /// 根拠のない事実の行：エラーにして、見つかった根拠を直し方として示す
    pub(super) fn missing_just<T>(&mut self, ctx: &Ctx, f: &Formula) -> CResult<T> {
        self.snapshot.0 = ctx.clone();
        let found = self.search_just(ctx, f);
        let fz = self.zonk_f(f);
        let msg = if found.is_empty() {
            format!("「{fz}」の根拠が書かれていない\n  help: 自動では見つからなかった。`by 根拠` を書くか、下に字下げして証明を書く")
        } else {
            let list: Vec<String> = found.iter().map(|j| format!("`by {j}`")).collect();
            format!("「{fz}」の根拠が書かれていない\n  help: 見つかった根拠：{}（エディタでは行末で Tab）", list.join("、"))
        };
        let mut err = self.err::<T>(msg).err().unwrap();
        err.fix = found.first().map(|j| format!(" by {j}"));
        err.alts = found.iter().skip(1).map(|j| format!(" by {j}")).collect();
        Err(err)
    }
}
