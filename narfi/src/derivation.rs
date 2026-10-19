//! 証明木（表示用）：kernel が検算した証明項を、Gentzen 式の自然演繹の木にする。
//!
//! 各部分証明の結論は、kernel に検算させながら記録したもの（Checker::record）を使う。
//! ここは表示のためだけのもので、検査の判断には関わらない（信じなくてよい部分）。

use crate::kernel::env::KEnv;
use crate::kernel::Statement;
use crate::kernel::check::Checker;
use crate::kernel::env::KCtx;
use crate::kernel::proof::Proof;
use crate::syntax::{Formula, Term, not};
use std::collections::HashMap;

/// 証明木の節
pub struct Node {
    /// 規則の名前（LaTeX）。葉では空
    pub rule: String,
    /// 結論（LaTeX）
    pub concl: String,
    pub premises: Vec<Node>,
    /// 葉の仮定の名前（文脈の仮定 h、または打ち消される仮定）
    pub hyp: String,
    /// 打ち消された仮定の葉（[φ]^h と描く）
    pub discharged: bool,
    /// この規則が打ち消す仮定：(前提の番号, 名前, 式の LaTeX)
    pub discharges: Vec<(usize, String, String)>,
    /// ソースの行（その文から作られた部分証明なら）
    pub line: usize,
}

fn leaf(concl: String, rule: &str, hyp: &str) -> Node {
    Node { rule: rule.into(), concl, premises: vec![], hyp: hyp.into(), discharged: false, discharges: vec![], line: 0 }
}

struct Builder {
    rec: HashMap<usize, Formula>,
    /// いま打ち消し待ちの仮定（名前 → 式）
    open: Vec<(String, Formula)>,
    /// have（Cut）で入った仮定 → その証明（使われた所に木を差し込む）
    cuts: Vec<(String, usize)>,
    size: usize,
}

const MAX_NODES: usize = 400;

impl Builder {
    fn concl(&self, p: &Proof) -> Formula {
        self.rec.get(&(p as *const Proof as usize)).cloned().unwrap_or(Formula::Bot)
    }

    fn node(&mut self, rule: &str, p: &Proof, premises: Vec<Node>) -> Node {
        Node {
            rule: rule.into(),
            concl: self.concl(p).to_latex(),
            premises,
            hyp: String::new(),
            discharged: false,
            discharges: vec![],
            line: 0,
        }
    }

    fn with_open<T>(&mut self, h: &str, phi: Formula, f: impl FnOnce(&mut Self) -> T) -> T {
        self.open.push((h.to_string(), phi));
        let r = f(self);
        self.open.pop();
        r
    }

    fn build(&mut self, p: &Proof, cut_proofs: &HashMap<usize, &Proof>) -> Node {
        self.size += 1;
        if self.size > MAX_NODES {
            return leaf(self.concl(p).to_latex(), "\\cdots", "");
        }
        let c = |b: &Self, q: &Proof| b.concl(q);
        match p {
            Proof::Line(l, q) => {
                let mut n = self.build(q, cut_proofs);
                if n.line == 0 {
                    n.line = *l;
                }
                n
            }
            Proof::Hyp(h) => {
                // have で入れた仮定なら、その証明の木を差し込む
                if let Some((_, addr)) = self.cuts.iter().rev().find(|(x, _)| x == h) {
                    if let Some(q) = cut_proofs.get(addr) {
                        let q: &Proof = q;
                        return self.build(q, cut_proofs);
                    }
                }
                let discharged = self.open.iter().any(|(x, _)| x == h);
                let mut n = leaf(c(self, p).to_latex(), "", h);
                n.discharged = discharged;
                n
            }
            Proof::Thm { name, .. } => leaf(c(self, p).to_latex(), &format!("\\mathrm{{{}}}", name.replace('_', "\\_")), ""),
            Proof::ImpI { h, phi, body } => {
                let b = self.with_open(h, phi.clone(), |s| s.build(body, cut_proofs));
                let mut n = self.node("{\\to}\\mathrm{I}", p, vec![b]);
                n.discharges.push((0, h.clone(), phi.to_latex()));
                n
            }
            Proof::ImpE(a, b) => {
                let (x, y) = (self.build(a, cut_proofs), self.build(b, cut_proofs));
                self.node("{\\to}\\mathrm{E}", p, vec![x, y])
            }
            Proof::AndI(a, b) => {
                let (x, y) = (self.build(a, cut_proofs), self.build(b, cut_proofs));
                self.node("{\\land}\\mathrm{I}", p, vec![x, y])
            }
            Proof::AndE { right, p: q } => {
                let x = self.build(q, cut_proofs);
                self.node(if *right { "{\\land}\\mathrm{E}_2" } else { "{\\land}\\mathrm{E}_1" }, p, vec![x])
            }
            Proof::OrI { right, p: q, .. } => {
                let x = self.build(q, cut_proofs);
                self.node(if *right { "{\\lor}\\mathrm{I}_2" } else { "{\\lor}\\mathrm{I}_1" }, p, vec![x])
            }
            Proof::OrE { p: q, h1, q1, h2, q2 } => {
                let (l, r) = match c(self, q) {
                    Formula::Or(l, r) => (*l, *r),
                    _ => (Formula::Bot, Formula::Bot),
                };
                let x = self.build(q, cut_proofs);
                let y = self.with_open(h1, l.clone(), |s| s.build(q1, cut_proofs));
                let z = self.with_open(h2, r.clone(), |s| s.build(q2, cut_proofs));
                let mut n = self.node("{\\lor}\\mathrm{E}", p, vec![x, y, z]);
                n.discharges.push((1, h1.clone(), l.to_latex()));
                n.discharges.push((2, h2.clone(), r.to_latex()));
                n
            }
            Proof::AllI { body, .. } => {
                let x = self.build(body, cut_proofs);
                self.node("{\\forall}\\mathrm{I}", p, vec![x])
            }
            Proof::AllE(q, _) => {
                let x = self.build(q, cut_proofs);
                self.node("{\\forall}\\mathrm{E}", p, vec![x])
            }
            Proof::ExI { p: q, .. } => {
                let x = self.build(q, cut_proofs);
                self.node("{\\exists}\\mathrm{I}", p, vec![x])
            }
            Proof::ExE { p: q, x, h, body } => {
                let phi = match c(self, q) {
                    Formula::Exists(y, _, b) => b.subst(&y, &Term::Var(x.clone())),
                    other => other,
                };
                let a = self.build(q, cut_proofs);
                let b = self.with_open(h, phi.clone(), |s| s.build(body, cut_proofs));
                let mut n = self.node("{\\exists}\\mathrm{E}", p, vec![a, b]);
                n.discharges.push((1, h.clone(), phi.to_latex()));
                n
            }
            Proof::BotE(_, q) => {
                let x = self.build(q, cut_proofs);
                self.node("{\\bot}\\mathrm{E}", p, vec![x])
            }
            Proof::Raa { h, phi, body } => {
                let nphi = not(phi.clone());
                let b = self.with_open(h, nphi.clone(), |s| s.build(body, cut_proofs));
                let mut n = self.node("\\mathrm{RAA}", p, vec![b]);
                n.discharges.push((0, h.clone(), nphi.to_latex()));
                n
            }
            // have：使われた所に証明の木を差し込む（Gentzen の木には「補題」の箱がないため）
            Proof::Cut { h, body, p: q, .. } => {
                self.cuts.push((h.clone(), &**q as *const Proof as usize));
                let n = self.build(body, cut_proofs);
                self.cuts.pop();
                n
            }
            Proof::Let { body, .. } => self.build(body, cut_proofs),
            Proof::Refl(_) => leaf(c(self, p).to_latex(), "\\mathrm{refl}", ""),
            Proof::Subst { eq, p: q, .. } => {
                let (x, y) = (self.build(eq, cut_proofs), self.build(q, cut_proofs));
                self.node("{=}\\mathrm{E}", p, vec![x, y])
            }
            Proof::Ind { ih, k, x, phi, base, step } => {
                let ihf = phi.subst(x, &Term::Var(k.clone()));
                let a = self.build(base, cut_proofs);
                let b = self.with_open(ih, ihf.clone(), |s| s.build(step, cut_proofs));
                let mut n = self.node("\\mathrm{Ind}", p, vec![a, b]);
                n.discharges.push((1, ih.clone(), ihf.to_latex()));
                n
            }
            Proof::Trans(a, b) => {
                let (x, y) = (self.build(a, cut_proofs), self.build(b, cut_proofs));
                self.node("\\mathrm{trans}", p, vec![x, y])
            }
            Proof::Antisymm(a, b) => {
                let (x, y) = (self.build(a, cut_proofs), self.build(b, cut_proofs));
                self.node("\\mathrm{antisymm}", p, vec![x, y])
            }
            Proof::NatNonneg(_) => leaf(c(self, p).to_latex(), "\\mathbb{N}_{\\geq 0}", ""),
            Proof::Ring { .. } => leaf(c(self, p).to_latex(), "\\mathrm{ring}", ""),
            Proof::LinArith { facts, .. } => {
                let xs: Vec<Node> = facts.iter().map(|f| self.build(f, cut_proofs)).collect();
                self.node("\\mathrm{linarith}", p, xs)
            }
            Proof::Decide(_) => leaf(c(self, p).to_latex(), "\\mathrm{decide}", ""),
            Proof::Sorry(_) => leaf(c(self, p).to_latex(), "\\mathrm{sorry}", ""),
        }
    }
}

/// have の証明（Cut の p）をアドレスで引けるように集める
fn collect_cuts<'p>(p: &'p Proof, out: &mut HashMap<usize, &'p Proof>) {
    use Proof::*;
    match p {
        Cut { p: q, body, .. } => {
            out.insert(&**q as *const Proof as usize, &**q);
            collect_cuts(q, out);
            collect_cuts(body, out);
        }
        Line(_, q) | AndE { p: q, .. } | OrI { p: q, .. } | AllI { body: q, .. } | AllE(q, _) | ExI { p: q, .. }
        | BotE(_, q) | Raa { body: q, .. } | ImpI { body: q, .. } | Let { body: q, .. } => collect_cuts(q, out),
        ImpE(a, b) | AndI(a, b) | Trans(a, b) | Antisymm(a, b) | Subst { eq: a, p: b, .. } | ExE { p: a, body: b, .. }
        | Ind { base: a, step: b, .. } => {
            collect_cuts(a, out);
            collect_cuts(b, out);
        }
        OrE { p: a, q1, q2, .. } => {
            collect_cuts(a, out);
            collect_cuts(q1, out);
            collect_cuts(q2, out);
        }
        LinArith { facts, .. } => facts.iter().for_each(|f| collect_cuts(f, out)),
        Hyp(_) | Thm { .. } | Refl(_) | NatNonneg(_) | Ring { .. } | Decide(_) | Sorry(_) => {}
    }
}

/// 定理の証明木。kernel にもう一度検算させ、その途中の結論を記録して組み立てる
pub fn derivation(env: &KEnv, st: &Statement, proof: &Proof) -> Option<Node> {
    let mut ctx = KCtx::new(env, &st.type_params);
    for (x, s) in &st.vars {
        ctx.vars.push((x.clone(), s.clone()));
    }
    for (h, f) in &st.hyps {
        ctx.hyps.push((h.clone(), f.clone()));
    }
    let mut c = Checker::new(&mut ctx);
    c.record = Some(HashMap::new());
    c.infer(proof).ok()?;
    let rec = c.record.take()?;
    let mut cuts = HashMap::new();
    collect_cuts(proof, &mut cuts);
    let mut b = Builder { rec, open: vec![], cuts: vec![], size: 0 };
    Some(b.build(proof, &cuts))
}

fn js(s: &str) -> String {
    crate::api::json_str(s)
}

impl Node {
    pub fn to_json(&self) -> String {
        let ps: Vec<String> = self.premises.iter().map(|n| n.to_json()).collect();
        let ds: Vec<String> =
            self.discharges.iter().map(|(i, h, f)| format!("[{i},{},{}]", js(h), js(f))).collect();
        format!(
            "{{\"r\":{},\"c\":{},\"h\":{},\"o\":{},\"l\":{},\"d\":[{}],\"p\":[{}]}}",
            js(&self.rule),
            js(&self.concl),
            js(&self.hyp),
            self.discharged,
            self.line,
            ds.join(","),
            ps.join(",")
        )
    }
}
