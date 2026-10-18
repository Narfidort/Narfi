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

use crate::syntax::Formula;
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
                    if !ctx.valid_sort(s) || s.contains('→') || s == "Prop" {
                        return kerr(format!("項の定義の値の型 `{s}` は使えない（関数・命題を値にする定義はまだ書けない）"));
                    }
                    ctx.check_sort(t, s)?;
                }
            }
        }
        self.defs.insert(name.to_string(), KDef { params: params.to_vec(), body: body.clone() });
        Ok(())
    }
}
