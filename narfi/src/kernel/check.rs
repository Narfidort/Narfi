//! kernel の推論規則（仕様 §5）。証明項を根から検算し、示している命題を返す。

use crate::kernel::arith;
use crate::kernel::env::{Deps, KCtx, KError, KResult, ORDER_RELS, Schema, kerr, num_rank};
use crate::types::Ty;
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term, not};

pub struct Checker<'a, 'c> {
    pub ctx: &'c mut KCtx<'a>,
    pub deps: Deps,
    /// 表示用（証明木）：部分証明（のアドレス）→ その結論。検査の判断には使わない
    pub record: Option<std::collections::HashMap<usize, Formula>>,
}

fn rel_parts(f: &Formula) -> Option<(&str, &Term, &Term)> {
    match f {
        Formula::Atom(r, ts) if ts.len() == 2 && (r == "=" || ORDER_RELS.contains(&r.as_str())) => {
            Some((r.as_str(), &ts[0], &ts[1]))
        }
        _ => None,
    }
}

/// 推移律で組める向きか（仕様 §5.1）
fn compose(a: &str, b: &str) -> Option<&'static str> {
    let dir = |r: &str| match r {
        "=" => 0,
        "<" | "≤" => 1,
        _ => -1,
    };
    let st = |r: &str| -> &'static str {
        match r {
            "=" => "=",
            "<" => "<",
            "≤" => "≤",
            ">" => ">",
            _ => "≥",
        }
    };
    if a == "=" {
        return Some(st(b));
    }
    if b == "=" {
        return Some(st(a));
    }
    if dir(a) != dir(b) {
        return None;
    }
    let strict = a == "<" || a == ">" || b == "<" || b == ">";
    Some(match (dir(a), strict) {
        (1, true) => "<",
        (1, false) => "≤",
        (_, true) => ">",
        (_, false) => "≥",
    })
}

impl<'a, 'c> Checker<'a, 'c> {
    pub fn new(ctx: &'c mut KCtx<'a>) -> Self {
        Checker { ctx, deps: Deps::default(), record: None }
    }

    fn want_conv(&mut self, have: &Formula, want: &Formula, what: &str) -> KResult<()> {
        if self.ctx.conv(have, want) {
            Ok(())
        } else {
            kerr(format!("{what}：示されているのは「{have}」だが、必要なのは「{want}」"))
        }
    }

    fn with_var<T>(&mut self, x: &str, s: &str, f: impl FnOnce(&mut Self) -> KResult<T>) -> KResult<T> {
        self.ctx.fresh_var(x)?;
        if !self.ctx.valid_sort(s) {
            return kerr(format!("変数 `{x}` の型 `{s}` が正しくない"));
        }
        self.ctx.vars.push((x.to_string(), s.to_string()));
        let r = f(self);
        self.ctx.vars.pop();
        r
    }

    fn with_hyp<T>(&mut self, h: &str, phi: &Formula, f: impl FnOnce(&mut Self) -> KResult<T>) -> KResult<T> {
        self.ctx.check_f(phi)?;
        self.ctx.hyps.push((h.to_string(), phi.clone()));
        let r = f(self);
        self.ctx.hyps.pop();
        r
    }

    fn infer_whnf(&mut self, p: &Proof) -> KResult<Formula> {
        let f = self.infer(p)?;
        Ok(self.ctx.whnf(&f))
    }

    /// 証明項 p が示す命題
    pub fn infer(&mut self, p: &Proof) -> KResult<Formula> {
        let f = self.infer0(p)?;
        if let Some(r) = &mut self.record {
            r.insert(p as *const Proof as usize, f.clone());
        }
        Ok(f)
    }

    fn infer0(&mut self, p: &Proof) -> KResult<Formula> {
        match p {
            Proof::Line(line, q) => self.infer(q).map_err(|mut e| {
                e.line.get_or_insert(*line);
                e
            }),
            Proof::Hyp(h) => match self.ctx.hyps.iter().rev().find(|(x, _)| x == h) {
                Some((_, f)) => Ok(f.clone()),
                None => kerr(format!("仮定 `{h}` が文脈にない")),
            },
            Proof::Thm { name, sorts, args } => self.thm(name, sorts, args),
            Proof::ImpI { h, phi, body } => {
                let psi = self.with_hyp(h, phi, |c| c.infer(body))?;
                Ok(Formula::Imp(Box::new(phi.clone()), Box::new(psi)))
            }
            Proof::ImpE(p, q) => match self.infer_whnf(p)? {
                Formula::Imp(a, b) => {
                    let qa = self.infer(q)?;
                    self.want_conv(&qa, &a, "→除去の前提")?;
                    Ok(*b)
                }
                f => kerr(format!("→除去：「{f}」は → の形ではない")),
            },
            Proof::AndI(p, q) => Ok(Formula::And(Box::new(self.infer(p)?), Box::new(self.infer(q)?))),
            Proof::AndE { right, p } => match self.infer_whnf(p)? {
                Formula::And(a, b) => Ok(if *right { *b } else { *a }),
                f => kerr(format!("∧除去：「{f}」は ∧ の形ではない")),
            },
            Proof::OrI { right, other, p } => {
                self.ctx.check_f(other)?;
                let a = self.infer(p)?;
                let (l, r) = if *right { (other.clone(), a) } else { (a, other.clone()) };
                Ok(Formula::Or(Box::new(l), Box::new(r)))
            }
            Proof::OrE { p, h1, q1, h2, q2 } => match self.infer_whnf(p)? {
                Formula::Or(a, b) => {
                    let c1 = self.with_hyp(h1, &a, |c| c.infer(q1))?;
                    let c2 = self.with_hyp(h2, &b, |c| c.infer(q2))?;
                    self.want_conv(&c2, &c1, "∨除去の2つの場合の結論")?;
                    Ok(c1)
                }
                f => kerr(format!("∨除去：「{f}」は ∨ の形ではない")),
            },
            Proof::AllI { x, sort, body } => {
                let phi = self.with_var(x, sort, |c| c.infer(body))?;
                Ok(Formula::Forall(x.clone(), sort.clone(), Box::new(phi)))
            }
            Proof::AllE(p, t) => match self.infer_whnf(p)? {
                Formula::Forall(x, s, body) => {
                    self.ctx.check_sort(t, &s)?;
                    Ok(body.subst(&x, t))
                }
                f => kerr(format!("∀除去：「{f}」は ∀ の形ではない")),
            },
            Proof::ExI { target, witness, p } => {
                self.ctx.check_f(target)?;
                match self.ctx.whnf(target) {
                    Formula::Exists(x, s, body) => {
                        self.ctx.check_sort(witness, &s)?;
                        let have = self.infer(p)?;
                        self.want_conv(&have, &body.subst(&x, witness), "∃導入")?;
                        Ok(target.clone())
                    }
                    f => kerr(format!("∃導入：「{f}」は ∃ の形ではない")),
                }
            }
            Proof::ExE { p, x, h, body } => match self.infer_whnf(p)? {
                Formula::Exists(y, s, phi) => {
                    let phi = phi.subst(&y, &Term::Var(x.clone()));
                    let chi = self.with_var(x, &s, |c| c.with_hyp(h, &phi, |c| c.infer(body)))?;
                    // 固有変数条件：取り出した x は結論に現れてはならない
                    if self.ctx.expand_lets_f(&chi).free_vars().contains(x) {
                        return kerr(format!("∃除去：取り出した `{x}` が結論「{chi}」に残っている"));
                    }
                    Ok(chi)
                }
                f => kerr(format!("∃除去：「{f}」は ∃ の形ではない")),
            },
            Proof::BotE(phi, p) => {
                self.ctx.check_f(phi)?;
                let f = self.infer(p)?;
                self.want_conv(&f, &Formula::Bot, "⊥除去")?;
                Ok(phi.clone())
            }
            Proof::Raa { h, phi, body } => {
                self.ctx.check_f(phi)?;
                let f = self.with_hyp(h, &not(phi.clone()), |c| c.infer(body))?;
                self.want_conv(&f, &Formula::Bot, "背理法")?;
                Ok(phi.clone())
            }
            Proof::Cut { h, phi, p, body } => {
                self.ctx.check_f(phi)?;
                let have = self.infer(p)?;
                self.want_conv(&have, phi, "have")?;
                self.with_hyp(h, phi, |c| c.infer(body))
            }
            Proof::Let { x, sort, t, body } => {
                self.ctx.fresh_var(x)?;
                if !self.ctx.valid_sort(sort) {
                    return kerr(format!("let の型 `{sort}` が正しくない"));
                }
                self.ctx.check_sort(t, sort)?;
                self.ctx.lets.push((x.clone(), sort.clone(), t.clone()));
                let r = self.infer(body);
                self.ctx.lets.pop();
                Ok(r?.subst(x, t))
            }
            Proof::Refl(t) => {
                self.ctx.rel_sort("=", t, t)?;
                Ok(Formula::Atom("=".into(), vec![t.clone(), t.clone()]))
            }
            Proof::Subst { eq, z, motive, p } => {
                let e = self.infer(eq)?;
                let (s, t) = match rel_parts(&self.ctx.whnf(&e)) {
                    Some(("=", s, t)) => (s.clone(), t.clone()),
                    _ => return kerr(format!("書き換え：「{e}」は等式ではない")),
                };
                let sort = self.term_sort(&s)?;
                self.with_var(z, &sort, |c| c.ctx.check_f(motive))?;
                let have = self.infer(p)?;
                self.want_conv(&have, &motive.subst(z, &s), "書き換えの前提")?;
                Ok(motive.subst(z, &t))
            }
            Proof::Ind { x, phi, base, k, ih, step } => {
                self.with_var(x, "ℕ", |c| c.ctx.check_f(phi))?;
                let b = self.infer(base)?;
                self.want_conv(&b, &phi.subst(x, &Term::Num(0)), "帰納法の基底")?;
                let kv = Term::Var(k.clone());
                let ih_f = phi.subst(x, &kv);
                let st = self.with_var(k, "ℕ", |c| c.with_hyp(ih, &ih_f, |c| c.infer(step)))?;
                let want = phi.subst(x, &Term::App("S".into(), vec![kv]));
                self.want_conv(&st, &want, "帰納法の帰納段階")?;
                Ok(Formula::Forall(x.clone(), "ℕ".into(), Box::new(phi.clone())))
            }
            Proof::Trans(p, q) => {
                let (f1, f2) = (self.infer(p)?, self.infer(q)?);
                let (Some((r1, a, b)), Some((r2, b2, c))) = (rel_parts(&f1), rel_parts(&f2)) else {
                    return kerr(format!("推移律：「{f1}」「{f2}」は関係ではない"));
                };
                if !self.ctx.term_eq(b, b2) {
                    return kerr(format!("推移律：中央の項 `{b}` と `{b2}` が違う"));
                }
                let Some(r) = compose(r1, r2) else {
                    return kerr(format!("推移律：{r1} と {r2} は向きが逆なので組めない"));
                };
                let f = Formula::Atom(r.into(), vec![a.clone(), c.clone()]);
                self.ctx.check_f(&f)?;
                Ok(f)
            }
            Proof::Antisymm(p, q) => {
                let (f1, f2) = (self.infer(p)?, self.infer(q)?);
                // a ≥ b は b ≤ a と読む
                let le = |f: &Formula| -> Option<(Term, Term)> {
                    match rel_parts(f)? {
                        ("≤", a, b) => Some((a.clone(), b.clone())),
                        ("≥", a, b) => Some((b.clone(), a.clone())),
                        _ => None,
                    }
                };
                match (le(&f1), le(&f2)) {
                    (Some((a, b)), Some((b2, a2))) if self.ctx.term_eq(&a, &a2) && self.ctx.term_eq(&b, &b2) => {
                        let f = Formula::Atom("=".into(), vec![a, b]);
                        self.ctx.check_f(&f)?;
                        Ok(f)
                    }
                    _ => kerr(format!("反対称律：「{f1}」「{f2}」から等式は出ない")),
                }
            }
            Proof::NatNonneg(t) => {
                self.ctx.check_sort(t, "ℕ")?;
                Ok(Formula::Atom("≥".into(), vec![t.clone(), Term::Num(0)]))
            }
            Proof::Ring { lhs, rhs } => {
                let f = Formula::Atom("=".into(), vec![lhs.clone(), rhs.clone()]);
                let s = self.ctx.rel_sort("=", lhs, rhs)?;
                if let Some(s) = &s {
                    if num_rank(&s.show()).is_none() {
                        return kerr(format!("ring は数の型にしか使えない（{}）", s.show()));
                    }
                }
                let (l, r) = (self.ctx.arith_form(lhs), self.ctx.arith_form(rhs));
                if !arith::ring_eq(&l, &r) {
                    return kerr(format!("ring：「{f}」は環の等式ではない"));
                }
                self.deps.arith.insert("ring".into());
                Ok(f)
            }
            Proof::LinArith { goal, facts, coeffs } => self.linarith(goal, facts, coeffs),
            Proof::Decide(phi) => {
                self.ctx.check_f(phi)?;
                let f = self.ctx.arith_form_f(phi);
                if !f.free_vars().is_empty() {
                    return kerr(format!("decide：「{phi}」には変数がある"));
                }
                match arith::decide(&f) {
                    Some(true) => {
                        self.deps.arith.insert("decide".into());
                        Ok(phi.clone())
                    }
                    Some(false) => kerr(format!("decide：「{phi}」は偽")),
                    None => kerr(format!("decide：「{phi}」は計算できない")),
                }
            }
            Proof::Sorry(phi) => {
                self.ctx.check_f(phi)?;
                self.deps.sorry = true;
                Ok(phi.clone())
            }
        }
    }

    fn term_sort(&mut self, t: &Term) -> KResult<String> {
        match self.ctx.sort_of(t)? {
            Some(s) => Ok(s.show()),
            // 数字だけの項：§3.2 の規則で ℚ として扱えば十分（埋め込みで真偽は変わらない）
            None => Ok("ℚ".into()),
        }
    }

    /// 線形算術の証明書（仕様 §7.2）
    fn linarith(&mut self, goal: &Formula, facts: &[Proof], coeffs: &[arith::Q]) -> KResult<Formula> {
        self.ctx.check_f(goal)?;
        let g = self.ctx.whnf(goal);
        let Some((gr, gl, grr)) = rel_parts(&g) else {
            return kerr(format!("linarith：目標「{goal}」は不等式ではない"));
        };
        let mut sort = self.ctx.rel_sort(gr, gl, grr)?;
        let mut fs = Vec::new();
        for p in facts {
            let f = self.infer_whnf(p)?;
            let Some((r, l, rr)) = rel_parts(&f) else {
                return kerr(format!("linarith：事実「{f}」は等式・不等式ではない"));
            };
            match (self.ctx.rel_sort(r, l, rr)?, &sort) {
                (Some(s), Some(t)) if s != *t => {
                    return kerr(format!("linarith：型が混ざっている（{} と {}）", s.show(), t.show()));
                }
                (Some(s), None) => sort = Some(s),
                _ => {}
            }
            fs.push((r.to_string(), self.ctx.arith_form(l), self.ctx.arith_form(rr)));
        }
        if let Some(s) = &sort {
            if !matches!(s, Ty::Base(b) if num_rank(b).is_some()) {
                return kerr(format!("linarith は数の型にしか使えない（{}）", s.show()));
            }
        }
        let (gl, grr) = (self.ctx.arith_form(gl), self.ctx.arith_form(grr));
        let mut forms = Vec::new();
        for (r, l, rr) in &fs {
            forms.push(arith::fact_form(r, l, rr).expect("関係は確認済み"));
        }
        let Some(neg) = arith::negated_goal_form(gr, &gl, &grr) else {
            return kerr(format!("linarith：目標「{goal}」は < ≤ > ≥ のどれかでなければならない"));
        };
        forms.push(neg);
        if let Err(m) = arith::farkas_check(&forms, coeffs) {
            return kerr(format!("linarith の証明書が正しくない：{m}"));
        }
        self.deps.arith.insert("linarith".into());
        Ok(goal.clone())
    }

    /// 図式の具体化（仕様 §8）
    fn thm(&mut self, name: &str, tys: &[String], args: &[Term]) -> KResult<Formula> {
        let Some(sc) = self.ctx.env.thms.get(name) else {
            return kerr(format!("定理・公理 `{name}` がない"));
        };
        let sc: Schema = sc.clone();
        if tys.len() != sc.type_params.len() || args.len() != sc.params.len() {
            return kerr(format!("`{name}` の具体化の引数の数が合わない"));
        }
        for s in tys {
            if !self.ctx.valid_sort(s) {
                return kerr(format!("`{name}` の型の引数 `{s}` が正しくない"));
            }
        }
        let (params, formula) = sc.instance(tys);
        for ((_, s), t) in params.iter().zip(args) {
            self.ctx.check_sort(t, s)?;
        }
        if sc.is_axiom && !sc.core {
            self.deps.axioms.insert(name.to_string());
        }
        self.deps.extend(&sc.deps);
        Ok(crate::syntax::instantiate(&params, &formula, args))
    }
}

/// 定理の検査結果
pub fn check_theorem_proof(ctx: &mut KCtx, proof: &Proof, concl: &Formula) -> Result<Deps, KError> {
    let mut c = Checker::new(ctx);
    let have = c.infer(proof)?;
    if !c.ctx.conv(&have, concl) {
        return kerr(format!("証明が示すのは「{have}」で、定理の結論「{concl}」と違う"));
    }
    Ok(c.deps)
}
