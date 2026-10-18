//! 核（kernel）。Narfi v2 で「正しい」と判断するのはこのモジュールだけ。
//!
//! - `env`   ：ソート・シグネチャ・型付け・定義的等しさ（仕様 §1〜§4, §6）
//! - `check` ：推論規則（仕様 §5）
//! - `arith` ：算術の検算（仕様 §7）
//! - `proof` ：証明項
//!
//! elab（src/elab.rs）にバグがあっても、ここが通さなければ定理は環境に入らない。
//! 逆に言えば、このモジュール（と syntax.rs の代入・自由変数）だけを読めば、
//! 検査結果を信じてよいかを判断できる。

pub mod arith;
pub mod check;
pub mod env;
pub mod proof;
#[cfg(test)]
mod tests;

use crate::syntax::{Formula, is_fn_sort};
use env::{Deps, FnSig, KCtx, KDef, KEnv, KResult, LocalSig, Schema, is_builtin_fn, kerr, num_rank};
use proof::Proof;
use std::collections::BTreeSet;

/// 定理・公理の文
pub struct Statement {
    pub name: String,
    pub sig: LocalSig,
    pub sort_params: Vec<String>,
    /// 文の自由変数と型
    pub vars: Vec<(String, String)>,
    pub hyps: Vec<(String, Formula)>,
    pub concl: Formula,
    pub is_axiom: bool,
    pub core: bool,
}

fn atoms_of(f: &Formula, preds: &mut BTreeSet<String>, fns: &mut BTreeSet<String>) {
    fn t_go(t: &crate::syntax::Term, fns: &mut BTreeSet<String>) {
        match t {
            crate::syntax::Term::App(f, a) => {
                fns.insert(f.clone());
                a.iter().for_each(|x| t_go(x, fns));
            }
            crate::syntax::Term::Var(x) => {
                fns.insert(x.clone());
            }
            _ => {}
        }
    }
    match f {
        Formula::Atom(p, ts) => {
            preds.insert(p.clone());
            ts.iter().for_each(|t| t_go(t, fns));
        }
        Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
            atoms_of(a, preds, fns);
            atoms_of(b, preds, fns);
        }
        Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => atoms_of(b, preds, fns),
        Formula::Bot => {}
    }
}

impl KEnv {
    fn sort_ok(s: &str, sort_params: &[String]) -> bool {
        num_rank(s).is_some() || sort_params.iter().any(|p| p == s)
    }

    fn check_sig(&self, sig: &LocalSig, sort_params: &[String]) -> KResult<()> {
        for (f, fs) in &sig.fns {
            if is_builtin_fn(f) || self.defs.contains_key(f) {
                return kerr(format!("`{f}` は組み込みか定義済みの名前なので、局所記号にできない"));
            }
            if !fs.args.iter().chain(std::iter::once(&fs.res)).all(|s| Self::sort_ok(s, sort_params)) {
                return kerr(format!("関数記号 `{f}` の型 {} が正しくない", fs.show()));
            }
        }
        for (p, ss) in &sig.preds {
            if self.defs.contains_key(p) || p == "=" {
                return kerr(format!("`{p}` は定義済みの名前なので、局所記号にできない"));
            }
            if !ss.iter().all(|s| Self::sort_ok(s, sort_params)) {
                return kerr(format!("述語 `{p}` の型が正しくない"));
            }
        }
        Ok(())
    }

    /// 定理（proof あり）・公理（proof なし）を検査して環境に入れる。返り値は依存。
    pub fn add_statement(&mut self, st: &Statement, proof: Option<&Proof>) -> KResult<Deps> {
        if self.thms.contains_key(&st.name) {
            return kerr(format!("名前 `{}` はすでに使われている", st.name));
        }
        self.check_sig(&st.sig, &st.sort_params)?;
        let deps = {
            let mut ctx = KCtx::new(self, &st.sig, &st.sort_params);
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
        // 図式：仮定を → でつなぎ、文に現れる局所記号をパラメータにする
        let mut formula = st.concl.clone();
        for (_, h) in st.hyps.iter().rev() {
            formula = Formula::Imp(Box::new(h.clone()), Box::new(formula));
        }
        let (mut preds, mut syms) = (BTreeSet::new(), BTreeSet::new());
        atoms_of(&formula, &mut preds, &mut syms);
        let mut params = st.vars.clone();
        for (f, fs) in &st.sig.fns {
            if syms.contains(f) {
                params.push((f.clone(), fs.show()));
            }
        }
        let preds = st
            .sig
            .preds
            .iter()
            .filter(|(p, _)| preds.contains(*p))
            .map(|(p, ss)| (p.clone(), ss.clone()))
            .collect();
        self.thms.insert(
            st.name.clone(),
            Schema {
                sort_params: st.sort_params.clone(),
                params,
                preds,
                formula,
                is_axiom: st.is_axiom,
                core: st.core,
                deps: deps.clone(),
            },
        );
        Ok(deps)
    }

    /// 定義 `def name(params) := body`（仕様 §8）
    pub fn add_def(&mut self, name: &str, params: &[(String, String)], body: &Formula) -> KResult<()> {
        if self.defs.contains_key(name) || self.thms.contains_key(name) || is_builtin_fn(name) || name == "=" {
            return kerr(format!("名前 `{name}` はすでに使われている"));
        }
        let mut sig = LocalSig::default();
        let mut vars = Vec::new();
        for (x, s) in params {
            if is_fn_sort(s) {
                let Some(fs) = FnSig::parse(s) else {
                    return kerr(format!("引数 `{x}` の型 `{s}` が読めない"));
                };
                sig.fns.insert(x.clone(), fs);
            } else {
                vars.push((x.clone(), s.clone()));
            }
        }
        self.check_sig(&sig, &[])?;
        {
            let mut ctx = KCtx::new(self, &sig, &[]);
            for (x, s) in &vars {
                ctx.fresh_var(x)?;
                if !ctx.valid_sort(s) {
                    return kerr(format!("引数 `{x}` の型 `{s}` が正しくない（数のソートか関数型）"));
                }
                ctx.vars.push((x.clone(), s.clone()));
            }
            // 本体の型付け。未宣言の述語や、引数にない変数があればここで止まる。
            // 自分自身はまだ環境にないので、再帰的な定義もここで止まる。
            ctx.check_f(body)?;
        }
        self.defs.insert(name.to_string(), KDef { params: params.to_vec(), body: body.clone() });
        Ok(())
    }
}
