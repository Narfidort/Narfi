//! 核（kernel）。Narfi v2 で「正しい」と判断するのはこのモジュールだけ。
//!
//! - `env`   ：型・型付け・定義的等しさ（仕様 §1〜§4, §6）
//! - `check` ：推論規則（仕様 §5）
//! - `arith` ：算術の検算（仕様 §7）
//! - `proof` ：証明項
//!
//! elab（src/elab/）にバグがあっても、ここが通さなければ定理は環境に入らない。
//! 逆に言えば、このモジュールと src/syntax.rs の代入・自由変数・src/types.rs の型だけを読めば、
//! 検査結果を信じてよいかを判断できる。

pub mod arith;
pub mod check;
pub mod env;
pub mod proof;
#[cfg(test)]
mod tests;

use crate::syntax::{Formula, Term};
use env::{DefBody, Deps, KCtx, KDef, KEnv, KResult, Schema, kerr, num_rank};
use proof::Proof;

/// 定理・公理の文
pub struct Statement {
    pub name: String,
    pub type_params: Vec<String>,
    /// 文の自由変数と型（関数型・述語型の変数も含む）
    pub vars: Vec<(String, String)>,
    pub hyps: Vec<(String, Formula)>,
    pub concl: Formula,
    pub is_axiom: bool,
    pub core: bool,
}

impl KEnv {
    fn name_free(&self, name: &str) -> KResult<()> {
        if self.thms.contains_key(name) || self.is_global(name) || name == "=" || num_rank(name).is_some() {
            return kerr(format!("名前 `{name}` はすでに使われている"));
        }
        Ok(())
    }

    /// 定理（proof あり）・公理（proof なし）を検査して環境に入れる。返り値は依存。
    pub fn add_statement(&mut self, st: &Statement, proof: Option<&Proof>) -> KResult<Deps> {
        if self.thms.contains_key(&st.name) {
            return kerr(format!("名前 `{}` はすでに使われている", st.name));
        }
        let deps = {
            let mut ctx = KCtx::new(self, &st.type_params);
            for (x, s) in &st.vars {
                ctx.fresh_var(x)?;
                if !ctx.valid_sort(s) {
                    return kerr(format!("変数 `{x}` の型 `{s}` が正しくない"));
                }
                ctx.vars.push((x.clone(), s.clone()));
            }
            for (h, f) in &st.hyps {
                ctx.check_f(f)?;
                ctx.hyps.push((h.clone(), f.clone()));
            }
            ctx.check_f(&st.concl)?;
            match proof {
                Some(p) => check::check_theorem_proof(&mut ctx, p, &st.concl)?,
                None if st.is_axiom => Deps::default(),
                None => return kerr("定理に証明がない"),
            }
        };
        // 図式：仮定を → でつなぎ、文の自由変数をパラメータにする
        let mut formula = st.concl.clone();
        for (_, h) in st.hyps.iter().rev() {
            formula = Formula::Imp(Box::new(h.clone()), Box::new(formula));
        }
        self.thms.insert(
            st.name.clone(),
            Schema {
                type_params: st.type_params.clone(),
                params: st.vars.clone(),
                formula,
                is_axiom: st.is_axiom,
                core: st.core,
                deps: deps.clone(),
            },
        );
        Ok(deps)
    }

    /// 型の定義 `typedef T := {x : σ | φ}`（仕様 §8.3）。
    /// proof が ∃x:σ. φ を示せば、型 T・定数 T.abs : σ → T・T.rep : T → σ と、
    /// T と {x : σ | φ} が1対1に対応することを表す3つの公理を置く。
    pub fn add_typedef(&mut self, name: &str, x: &str, carrier: &str, phi: &Formula, proof: &Proof) -> KResult<Deps> {
        if num_rank(name).is_some() || self.types.contains(name) || name == "Prop" {
            return kerr(format!("型の名前 `{name}` はすでに使われている"));
        }
        let (abs, rep) = (format!("{name}.abs"), format!("{name}.rep"));
        let names = [abs.clone(), rep.clone(), format!("{name}.rep_prop"), format!("{name}.abs_rep"), format!("{name}.rep_abs")];
        for n in &names {
            self.name_free(n)?;
        }
        let nonempty = Formula::Exists(x.to_string(), carrier.to_string(), Box::new(phi.clone()));
        let deps = {
            let mut ctx = KCtx::new(self, &[]);
            if !ctx.valid_sort(carrier) {
                return kerr(format!("typedef の元の型 `{carrier}` が正しくない"));
            }
            // 述語は閉じていなければならない（x 以外の自由変数を持たない）
            ctx.check_f(&nonempty)?;
            check::check_theorem_proof(&mut ctx, proof, &nonempty)?
        };
        let ty = crate::types::Ty::Base(name.to_string());
        let car = crate::types::Ty::parse(carrier).ok_or_else(|| env::KError { line: None, msg: format!("型 `{carrier}` が読めない") })?;
        self.types.insert(name.to_string());
        self.consts.insert(abs.clone(), crate::types::Ty::fun(vec![car.clone()], ty.clone()).show());
        self.consts.insert(rep.clone(), crate::types::Ty::fun(vec![ty], car).show());
        let t = Term::Var("t".into());
        let rep_t = Term::App(rep.clone(), vec![t.clone()]);
        let xv = Term::Var(x.to_string());
        let eq = |a: Term, b: Term| Formula::Atom("=".into(), vec![a, b]);
        let all = |v: &str, s: &str, f: Formula| Formula::Forall(v.into(), s.into(), Box::new(f));
        let axioms = [
            // rep(t) は φ を満たす
            (names[2].clone(), all("t", name, phi.subst(x, &rep_t))),
            // abs(rep(t)) = t
            (names[3].clone(), all("t", name, eq(Term::App(abs.clone(), vec![rep_t.clone()]), t.clone()))),
            // φ(x) なら rep(abs(x)) = x
            (
                names[4].clone(),
                all(
                    x,
                    carrier,
                    Formula::Imp(
                        Box::new(phi.clone()),
                        Box::new(eq(Term::App(rep.clone(), vec![Term::App(abs.clone(), vec![xv.clone()])]), xv)),
                    ),
                ),
            ),
        ];
        for (n, f) in axioms {
            self.thms.insert(
                n,
                Schema { type_params: vec![], params: vec![], formula: f, is_axiom: true, core: true, deps: deps.clone() },
            );
        }
        Ok(deps)
    }

    /// 定義 `def P(params) := φ` / `def f(params) : τ := t`（仕様 §8）
    pub fn add_def(&mut self, name: &str, params: &[(String, String)], body: &DefBody) -> KResult<()> {
        self.name_free(name)?;
        {
            let mut ctx = KCtx::new(self, &[]);
            for (x, s) in params {
                ctx.fresh_var(x)?;
                if !ctx.valid_sort(s) {
                    return kerr(format!("引数 `{x}` の型 `{s}` が正しくない"));
                }
                ctx.vars.push((x.clone(), s.clone()));
            }
            // 本体の型付け。未宣言の記号や、引数にない変数があればここで止まる。
            // 自分自身はまだ環境にないので、再帰的な定義もここで止まる。
            match body {
                DefBody::Pred(f) => ctx.check_f(f)?,
                DefBody::Term(s, t) => {
                    // 値が関数の定義（行列の積など）も、閉じた項に名前を付けるだけなので保守的（矛盾を持ち込まない）
                    if !ctx.valid_sort(s) || s == "Prop" {
                        return kerr(format!("項の定義の値の型 `{s}` は使えない（命題を値にするなら述語の def を使う）"));
                    }
                    ctx.check_sort(t, s)?;
                }
            }
        }
        self.defs.insert(name.to_string(), KDef { params: params.to_vec(), body: body.clone() });
        Ok(())
    }
}
