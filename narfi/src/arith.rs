//! linarith の証明書探し（elab の一部。kernel はこの結果を信じず、kernel/arith.rs で検算する）。
//!
//! Fourier–Motzkin の消去法で矛盾を探す。各制約が「元の事実を何倍して足したものか」（由来）を
//! 持ち歩くので、矛盾が見つかったとき、その由来がそのまま Farkas の証明書（係数）になる。

use crate::kernel::arith::{Cmp, Mono, Normalizer, Q, fact_form, negated_goal_form};
use crate::syntax::Term;
use std::collections::BTreeMap;

/// Σ coef·mono + c ⋈ 0（strict なら >、そうでなければ ≥）と、その由来（元の式ごとの係数）
#[derive(Clone, Debug)]
struct Lin {
    coef: BTreeMap<Mono, Q>,
    c: Q,
    strict: bool,
    origin: Vec<Q>,
}

fn contradictory(l: &Lin) -> bool {
    l.coef.is_empty() && (l.c.sign() < 0 || (l.strict && l.c.sign() <= 0))
}

fn unit(n: usize, i: usize, c: Q) -> Vec<Q> {
    let mut v = vec![Q::zero(); n];
    v[i] = c;
    v
}

/// 消去法で矛盾を探し、矛盾した制約の由来を返す
fn infeasible(mut cs: Vec<Lin>) -> Option<Vec<Q>> {
    const LIMIT: usize = 20000;
    loop {
        if let Some(l) = cs.iter().find(|l| contradictory(l)) {
            return Some(l.origin.clone());
        }
        let var = cs.iter().find_map(|l| l.coef.keys().next().cloned())?;
        let (mut pos, mut neg, mut rest) = (vec![], vec![], vec![]);
        for l in cs {
            match l.coef.get(&var).map(|q| q.sign()) {
                Some(1) => pos.push(l),
                Some(-1) => neg.push(l),
                _ => rest.push(l),
            }
        }
        for p in &pos {
            for n in &neg {
                let a = p.coef[&var];
                let b = n.coef[&var].neg();
                // b·p + a·n で var を消す（a, b > 0）
                let mut coef = BTreeMap::new();
                for (k, v) in p.coef.iter() {
                    coef.insert(k.clone(), v.mul(b));
                }
                for (k, v) in n.coef.iter() {
                    let e = coef.entry(k.clone()).or_insert(Q::zero());
                    *e = e.add(v.mul(a));
                }
                coef.retain(|_, v| !v.is_zero());
                let origin = p.origin.iter().zip(&n.origin).map(|(x, y)| x.mul(b).add(y.mul(a))).collect();
                rest.push(Lin { coef, c: p.c.mul(b).add(n.c.mul(a)), strict: p.strict || n.strict, origin });
                if rest.len() > LIMIT {
                    return None;
                }
            }
        }
        cs = rest;
    }
}

/// facts から goal（l rel r、rel は < ≤ > ≥）を示す証明書。
/// 返り値は facts の各々と目標の否定（最後）に掛ける係数（kernel::arith::farkas_check の形）。
pub fn find_certificate(facts: &[(String, Term, Term)], goal: (&str, &Term, &Term)) -> Option<Vec<Q>> {
    let n = facts.len() + 1;
    let mut forms = Vec::new();
    for (r, l, rr) in facts {
        forms.push(fact_form(r, l, rr)?);
    }
    forms.push(negated_goal_form(goal.0, goal.1, goal.2)?);
    let mut a = Normalizer::new();
    let mut cs = Vec::new();
    for (i, (l, r, cmp)) in forms.iter().enumerate() {
        let e = a.poly(l)?.sub(&a.poly(r)?); // e ⋈ 0
        let mut coef = e.0.clone();
        let c = coef.remove(&vec![]).unwrap_or(Q::zero());
        match cmp {
            Cmp::Gt | Cmp::Ge => {
                cs.push(Lin { coef, c, strict: *cmp == Cmp::Gt, origin: unit(n, i, Q::int(1)) });
            }
            // 等式は e ≥ 0 と -e ≥ 0 の2つ（係数の符号は自由）
            Cmp::Eq => {
                let neg: BTreeMap<Mono, Q> = coef.iter().map(|(k, v)| (k.clone(), v.neg())).collect();
                cs.push(Lin { coef, c, strict: false, origin: unit(n, i, Q::int(1)) });
                cs.push(Lin { coef: neg, c: c.neg(), strict: false, origin: unit(n, i, Q::int(-1)) });
            }
        }
    }
    infeasible(cs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::arith::{farkas_check, ring_eq};
    use crate::parser::{P, lex};

    fn t(s: &str) -> Term {
        P::new(lex(s, 0).unwrap(), 0, vec![]).term().unwrap()
    }

    /// 見つけた証明書を kernel の検算に通す
    fn proves(facts: &[(&str, &str, &str)], goal: (&str, &str, &str)) -> bool {
        let fs: Vec<(String, Term, Term)> = facts.iter().map(|(r, a, b)| (r.to_string(), t(a), t(b))).collect();
        let (gl, gr) = (t(goal.1), t(goal.2));
        let Some(cert) = find_certificate(&fs, (goal.0, &gl, &gr)) else {
            return false;
        };
        let mut forms: Vec<_> = fs.iter().map(|(r, a, b)| fact_form(r, a, b).unwrap()).collect();
        forms.push(negated_goal_form(goal.0, &gl, &gr).unwrap());
        farkas_check(&forms, &cert).is_ok()
    }

    #[test]
    fn ring_basic() {
        assert!(ring_eq(&t("ε/2 + ε/2"), &t("ε")));
        assert!(ring_eq(&t("(a + b)²"), &t("a² + 2·a·b + b²")));
        assert!(!ring_eq(&t("(a + b)²"), &t("a² + b²")));
    }

    #[test]
    fn linarith_certificates() {
        assert!(proves(&[("<", "x", "3"), ("≤", "y", "x")], ("<", "y", "3")));
        assert!(!proves(&[("<", "x", "3"), ("≤", "y", "x")], ("<", "y", "2")));
        assert!(proves(&[("<", "|a - c|", "e/2"), ("<", "|b - d|", "e/2")], ("<", "|a - c| + |b - d|", "e")));
        assert!(proves(&[("=", "x", "y + 1")], (">", "x", "y")));
        assert!(proves(&[(">", "e", "0")], (">", "e/2", "0")));
    }

    /// 間違った証明書は kernel が拒否する
    #[test]
    fn kernel_rejects_bad_certificate() {
        let (x, three, two) = (t("x"), t("3"), t("2"));
        let forms = vec![fact_form("<", &x, &three).unwrap(), negated_goal_form("<", &x, &two).unwrap()];
        assert!(farkas_check(&forms, &[Q::int(1), Q::int(1)]).is_err());
        assert!(farkas_check(&forms, &[Q::int(-1), Q::int(1)]).is_err());
    }
}
