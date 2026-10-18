//! kernel 単体のテスト。elab を通さず、証明項を手で組み立てて kernel に渡す。
//! 「elab がどんな証明項を作っても、kernel は誤りを通さない」ことを確かめる。

use super::Statement;
use super::arith::Q;
use super::env::{KEnv, LocalSig};
use super::proof::Proof;
use crate::parser::{P, lex};
use crate::syntax::{Formula, Term};

fn f(s: &str) -> Formula {
    P::new(lex(s, 0).unwrap(), 0, vec![]).formula().unwrap()
}

fn t(s: &str) -> Term {
    P::new(lex(s, 0).unwrap(), 0, vec![]).term().unwrap()
}

fn b(p: Proof) -> Box<Proof> {
    Box::new(p)
}

/// 拒否され、その理由に want が含まれること
fn rejected(r: Result<(), String>, want: &str) {
    match r {
        Err(m) => assert!(m.contains(want), "拒否の理由が違う：{m}（期待：{want}）"),
        Ok(()) => panic!("通ってしまった（期待：{want}）"),
    }
}

fn hyp(h: &str) -> Proof {
    Proof::Hyp(h.into())
}

/// 局所述語 P : ℕ、R : ℕ × ℕ を持つ定理を kernel に検査させる
fn thm(vars: &[(&str, &str)], hyps: &[(&str, &str)], concl: &str, proof: Proof) -> Result<(), String> {
    let mut env = KEnv::default();
    let mut sig = LocalSig::default();
    sig.preds.insert("P".into(), vec!["ℕ".into()]);
    sig.preds.insert("R".into(), vec!["ℕ".into(), "ℕ".into()]);
    let st = Statement {
        name: "t".into(),
        sig,
        sort_params: vec![],
        vars: vars.iter().map(|(x, s)| (x.to_string(), s.to_string())).collect(),
        hyps: hyps.iter().map(|(h, s)| (h.to_string(), f(s))).collect(),
        concl: f(concl),
        is_axiom: false,
        core: false,
    };
    env.add_statement(&st, Some(&proof)).map(|_| ()).map_err(|e| e.msg)
}

#[test]
fn accepts_modus_ponens() {
    let p = Proof::ImpE(b(hyp("k")), b(hyp("h")));
    assert_eq!(thm(&[("x", "ℕ")], &[("h", "P(x)"), ("k", "P(x) → P(0)")], "P(0)", p), Ok(()));
}

#[test]
fn rejects_wrong_conclusion() {
    let p = hyp("h");
    rejected(thm(&[("x", "ℕ")], &[("h", "P(x)")], "P(0)", p), "定理の結論");
}

/// ∀導入の固有変数条件：仮定に現れる x について一般化してはならない
#[test]
fn rejects_generalizing_a_variable_in_a_hypothesis() {
    // h : P(x) から ∀x. P(x) を出そうとする
    let p = Proof::AllI { x: "x".into(), sort: "ℕ".into(), body: b(hyp("h")) };
    rejected(thm(&[("x", "ℕ")], &[("h", "P(x)")], "∀y:ℕ. P(y)", p), "すでに文脈にある");
    // 別名 z にしても、結論は ∀z. P(x) なので一致しない
    let p = Proof::AllI { x: "z".into(), sort: "ℕ".into(), body: b(hyp("h")) };
    rejected(thm(&[("x", "ℕ")], &[("h", "P(x)")], "∀y:ℕ. P(y)", p), "定理の結論");
}

/// ∃除去で取り出した対象は、結論に現れてはならない
#[test]
fn rejects_escaping_witness() {
    let p = Proof::AllI {
        x: "y".into(),
        sort: "ℕ".into(),
        body: b(Proof::ExE { p: b(hyp("e")), x: "w".into(), h: "hw".into(), body: b(hyp("hw")) }),
    };
    rejected(thm(&[], &[("e", "∃x:ℕ. P(x)")], "∀y:ℕ. P(y)", p), "結論「P(w)」に残っている");
}

/// ∀∃ の入れ替え：∃x∀y から ∀y∃x は正しいが、逆は通らない
#[test]
fn quantifier_swap() {
    let ok = Proof::AllI {
        x: "y".into(),
        sort: "ℕ".into(),
        body: b(Proof::ExE {
            p: b(hyp("h")),
            x: "a".into(),
            h: "ha".into(),
            body: b(Proof::ExI {
                target: f("∃x:ℕ. R(x, y)"),
                witness: t("a"),
                p: b(Proof::AllE(b(hyp("ha")), t("y"))),
            }),
        }),
    };
    assert_eq!(thm(&[], &[("h", "∃x:ℕ. ∀y:ℕ. R(x, y)")], "∀y:ℕ. ∃x:ℕ. R(x, y)", ok), Ok(()));
    // 逆向き：y を固定して取り出した x を、∀y の外で使おうとする
    let bad = Proof::ExE {
        p: b(Proof::AllE(b(hyp("h")), t("0"))),
        x: "a".into(),
        h: "ha".into(),
        body: b(Proof::ExI {
            target: f("∃x:ℕ. ∀y:ℕ. R(x, y)"),
            witness: t("a"),
            p: b(Proof::AllI { x: "y".into(), sort: "ℕ".into(), body: b(hyp("ha")) }),
        }),
    };
    rejected(thm(&[], &[("h", "∀y:ℕ. ∃x:ℕ. R(x, y)")], "∃x:ℕ. ∀y:ℕ. R(x, y)", bad), "∃導入");
}

/// 型の違う項を ∀ に渡すことはできない
#[test]
fn rejects_wrong_sort_instantiation() {
    let p = Proof::AllE(b(hyp("h")), t("x"));
    rejected(thm(&[("x", "ℝ")], &[("h", "∀n:ℕ. P(n)")], "P(x)", p), "型は ℝ だが、ℕ が必要");
    // ℕ に引き算はない
    let p = Proof::Ring { lhs: t("n - n"), rhs: t("0") };
    rejected(thm(&[("n", "ℕ")], &[], "n - n = 0", p), "ℕ では使えない");
    // NatNonneg は ℕ の項にだけ使える
    let p = Proof::NatNonneg(t("x"));
    rejected(thm(&[("x", "ℝ")], &[], "x ≥ 0", p), "ℕ が必要");
}

#[test]
fn ring_and_decide() {
    let ok = Proof::Ring { lhs: t("(a + b)²"), rhs: t("a² + 2·a·b + b²") };
    assert_eq!(thm(&[("a", "ℝ"), ("b", "ℝ")], &[], "(a + b)² = a² + 2·a·b + b²", ok), Ok(()));
    let bad = Proof::Ring { lhs: t("(a + b)²"), rhs: t("a² + b²") };
    rejected(thm(&[("a", "ℝ"), ("b", "ℝ")], &[], "(a + b)² = a² + b²", bad), "環の等式ではない");
    rejected(thm(&[], &[], "2 + 2 = 5", Proof::Decide(f("2 + 2 = 5"))), "偽");
    assert_eq!(thm(&[], &[], "1/2 + 1/2 = 1", Proof::Decide(f("1/2 + 1/2 = 1"))), Ok(()));
}

/// linarith の証明書：正しい係数なら通り、間違った係数・型の混ざった事実は通らない
#[test]
fn linarith_certificate() {
    let goal = f("y < 3");
    let ok = Proof::LinArith { goal: goal.clone(), facts: vec![hyp("h1"), hyp("h2")], coeffs: vec![Q::int(1), Q::int(1), Q::int(1)] };
    let hyps = [("h1", "x < 3"), ("h2", "y ≤ x")];
    assert_eq!(thm(&[("x", "ℝ"), ("y", "ℝ")], &hyps, "y < 3", ok), Ok(()));
    // 1つ足りない（h2 を使わない）
    let bad = Proof::LinArith { goal: goal.clone(), facts: vec![hyp("h1")], coeffs: vec![Q::int(1), Q::int(1)] };
    rejected(thm(&[("x", "ℝ"), ("y", "ℝ")], &hyps, "y < 3", bad), "定数にならない");
    // 負の係数で不等式の向きを逆にする
    let bad = Proof::LinArith { goal: f("x < 2"), facts: vec![hyp("h1")], coeffs: vec![Q::int(-1), Q::int(1)] };
    rejected(thm(&[("x", "ℝ"), ("y", "ℝ")], &hyps, "x < 2", bad), "負の係数");
    // 係数は正しい形でも、x < 3 から x < 2 は出ない（和が 1 > 0 で矛盾にならない）
    let bad = Proof::LinArith { goal: f("x < 2"), facts: vec![hyp("h1")], coeffs: vec![Q::int(1), Q::int(1)] };
    rejected(thm(&[("x", "ℝ"), ("y", "ℝ")], &hyps, "x < 2", bad), "矛盾にならない");
    // ℕ の事実と ℝ の目標を混ぜる
    let bad = Proof::LinArith { goal: f("x < 3"), facts: vec![hyp("h")], coeffs: vec![Q::int(1), Q::int(1)] };
    rejected(thm(&[("x", "ℝ"), ("n", "ℕ")], &[("h", "n < 3")], "x < 3", bad), "型が混ざっている");
}

#[test]
fn transitivity_direction() {
    // a < b と b > c からは何も出ない（向きが逆）
    let p = Proof::Trans(b(hyp("h1")), b(hyp("h2")));
    let hyps = [("h1", "a < b"), ("h2", "b > c")];
    rejected(thm(&[("a", "ℝ"), ("b", "ℝ"), ("c", "ℝ")], &hyps, "a < c", p), "向きが逆");
    // 中央の項が違うものはつなげない
    let p = Proof::Trans(b(hyp("h1")), b(hyp("h2")));
    let hyps = [("h1", "a < b"), ("h2", "c < b")];
    rejected(thm(&[("a", "ℝ"), ("b", "ℝ"), ("c", "ℝ")], &hyps, "a < c", p), "中央の項");
    let p = Proof::Trans(b(hyp("h1")), b(hyp("h2")));
    let hyps = [("h1", "a < b"), ("h2", "b ≤ c")];
    assert_eq!(thm(&[("a", "ℝ"), ("b", "ℝ"), ("c", "ℝ")], &hyps, "a < c", p), Ok(()));
}

/// 帰納法：帰納段階で示したものが φ(S(k)) でなければ通らない
#[test]
fn induction_step_must_match() {
    // ∀n. n = 0 を「基底 0 = 0、帰納段階で IH をそのまま使う」で示そうとする
    let p = Proof::Ind {
        x: "n".into(),
        phi: f("n = 0"),
        base: b(Proof::Refl(t("0"))),
        k: "k".into(),
        ih: "ih".into(),
        step: b(hyp("ih")),
    };
    rejected(thm(&[], &[], "∀n:ℕ. n = 0", p), "帰納段階");
    // 基底が違う
    let p = Proof::Ind {
        x: "n".into(),
        phi: f("n = n"),
        base: b(Proof::Refl(t("1"))),
        k: "k".into(),
        ih: "ih".into(),
        step: b(Proof::Refl(t("S(k)"))),
    };
    rejected(thm(&[], &[], "∀n:ℕ. n = n", p), "帰納法の基底");
}

/// 定義：自分自身を使う定義・未宣言の述語を使う定義は登録できない
#[test]
fn definitions() {
    let mut env = KEnv::default();
    assert!(env.add_def("loop", &[("x".into(), "ℕ".into())], &f("loop(x)")).is_err());
    assert!(env.add_def("q", &[("x".into(), "ℕ".into())], &f("undeclared(x)")).is_err());
    assert!(env.add_def("pos", &[("x".into(), "ℝ".into())], &f("x > 0")).is_ok());
    // 定義の展開（δ）で同一視される
    let mut sig = LocalSig::default();
    sig.preds.insert("P".into(), vec![]);
    let st = Statement {
        name: "t".into(),
        sig,
        sort_params: vec![],
        vars: vec![("y".into(), "ℝ".into())],
        hyps: vec![("h".into(), f("y > 0"))],
        concl: f("pos(y)"),
        is_axiom: false,
        core: false,
    };
    assert!(env.add_statement(&st, Some(&hyp("h"))).is_ok());
}
