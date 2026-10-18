//! 証明検査器。各行で文脈 Γ と goal を追跡し、推論規則に合うかを確かめる。

use crate::arith;
use crate::parser::{ChainStep, Choice, CtxItem, Decl, Just, Stmt, StmtKind};
use crate::syntax::{Formula, Term, ident_to_latex, not, types_compatible};
use std::collections::{BTreeSet, HashMap};

// ================================================================ 環境・文脈

/// 定理・公理の型。仮定は → の連鎖として formula に入れ、自由変数は implicit として使うたびに単一化する。
pub struct Scheme {
    pub formula: Formula,
    pub implicit: Vec<String>,
    pub core: bool,
    pub is_axiom: bool,
    pub ok: bool,
    pub axioms: BTreeSet<String>,
    pub oracles: BTreeSet<String>,
}

#[derive(Default)]
pub struct Env {
    pub schemes: HashMap<String, Scheme>,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum VarKind {
    /// 定理の文に現れる定数
    Const,
    /// Fix で導入した任意の対象
    Fixed,
    /// Obtain で取り出した対象
    Obtained,
}

#[derive(Clone, Debug)]
pub enum Entry {
    Var(String, String, VarKind),
    Hyp(String, Formula),
    Def(String, Term),
}

#[derive(Clone, Default, Debug)]
pub struct Ctx {
    pub entries: Vec<Entry>,
}

impl Ctx {
    fn has_name(&self, n: &str) -> bool {
        self.entries.iter().any(|e| match e {
            Entry::Var(x, ..) | Entry::Hyp(x, _) | Entry::Def(x, _) => x == n,
        })
    }
    pub fn hyp(&self, n: &str) -> Option<&Formula> {
        self.entries.iter().rev().find_map(|e| match e {
            Entry::Hyp(x, f) if x == n => Some(f),
            _ => None,
        })
    }
    fn is_term_var(&self, n: &str) -> bool {
        self.entries
            .iter()
            .any(|e| matches!(e, Entry::Var(x, ..) | Entry::Def(x, _) if x == n))
    }
    fn fixed_vars(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter_map(|e| match e {
                Entry::Var(x, _, VarKind::Fixed) => Some(x.clone()),
                _ => None,
            })
            .collect()
    }
    /// let で定義した名前を中身に置き換える
    fn expand_f(&self, f: &Formula) -> Formula {
        let mut f = f.clone();
        for e in self.entries.iter().rev() {
            if let Entry::Def(x, t) = e {
                f = f.subst(x, t);
            }
        }
        f
    }
    pub fn show(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter_map(|e| match e {
                Entry::Var(x, t, k) => {
                    let kind = match k {
                        VarKind::Const => "",
                        VarKind::Fixed => "  (Fix)",
                        VarKind::Obtained => "  (Obtain)",
                    };
                    Some(if t == "?" {
                        format!("{x}{kind}")
                    } else {
                        format!("{x} : {t}{kind}")
                    })
                }
                Entry::Hyp(h, _) if h.ends_with(".def") => None,
                Entry::Hyp(h, f) => Some(format!("{h} : {f}")),
                Entry::Def(x, t) => Some(format!("{x} := {t}")),
            })
            .collect()
    }
    pub fn show_latex(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter_map(|e| match e {
                Entry::Var(x, t, k) => {
                    let kind = match k {
                        VarKind::Const => "",
                        VarKind::Fixed => " \\;(\\text{Fix})",
                        VarKind::Obtained => " \\;(\\text{Obtain})",
                    };
                    let xl = ident_to_latex(x);
                    Some(if t == "?" {
                        format!("{xl}{kind}")
                    } else {
                        format!("{xl} \\in {}{kind}", ident_to_latex(t))
                    })
                }
                Entry::Hyp(h, _) if h.ends_with(".def") => None,
                Entry::Hyp(h, f) => Some(format!("{} : {}", ident_to_latex(h), f.to_latex())),
                Entry::Def(x, t) => Some(format!("{} := {}", ident_to_latex(x), t.to_latex())),
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct StepTrace {
    pub line: usize,
    pub depth: usize,
    pub src: String,
    pub ctx: Vec<String>,
    pub ctx_latex: Vec<String>,
    pub goal: Option<String>,
    pub goal_latex: Option<String>,
}

#[derive(Debug)]
pub struct CheckError {
    pub line: usize,
    pub msg: String,
    pub goal: Option<Formula>,
    pub ctx: Vec<String>,
    pub ctx_latex: Vec<String>,
}

type CResult<T> = Result<T, CheckError>;

const BUILTINS: [&str; 8] = [
    "sorry", "refl", "ring", "linarith", "decide", "EQ2", "or.left", "or.right",
];

// ================================================================ 検査器

pub struct Checker<'a> {
    env: &'a Env,
    metas: Vec<Option<Term>>,
    fresh: u32,
    line: usize,
    snapshot: (Ctx, Option<Formula>),
    pub axioms: BTreeSet<String>,
    pub oracles: BTreeSet<String>,
    /// sorry で飛ばした箇所：(行, 文脈, 残っている goal)
    pub sorries: Vec<(usize, Vec<String>, Formula)>,
    pub steps: Vec<StepTrace>,
    trace: bool,
    depth: usize,
}

impl<'a> Checker<'a> {
    pub fn new(env: &'a Env, trace: bool) -> Self {
        Checker {
            env,
            metas: vec![],
            fresh: 0,
            line: 0,
            snapshot: (Ctx::default(), None),
            axioms: BTreeSet::new(),
            oracles: BTreeSet::new(),
            sorries: vec![],
            steps: vec![],
            trace,
            depth: 0,
        }
    }

    fn err<T>(&self, msg: impl Into<String>) -> CResult<T> {
        Err(CheckError {
            line: self.line,
            msg: msg.into(),
            goal: self.snapshot.1.clone(),
            ctx: self.snapshot.0.show(),
            ctx_latex: self.snapshot.0.show_latex(),
        })
    }

    // ------------------------------------------------ メタ変数と単一化

    fn new_meta(&mut self) -> Term {
        self.metas.push(None);
        Term::Meta(self.metas.len() as u32 - 1)
    }

    fn zonk_t(&self, t: &Term) -> Term {
        match t {
            Term::Meta(m) => match &self.metas[*m as usize] {
                Some(u) => self.zonk_t(u),
                None => t.clone(),
            },
            Term::App(f, a) => Term::App(f.clone(), a.iter().map(|x| self.zonk_t(x)).collect()),
            _ => t.clone(),
        }
    }

    fn zonk_f(&self, f: &Formula) -> Formula {
        match f {
            Formula::Atom(p, ts) => {
                Formula::Atom(p.clone(), ts.iter().map(|t| self.zonk_t(t)).collect())
            }
            Formula::Imp(a, b) => Formula::Imp(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::And(a, b) => Formula::And(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(self.zonk_f(a)), Box::new(self.zonk_f(b))),
            Formula::Forall(x, t, b) => {
                Formula::Forall(x.clone(), t.clone(), Box::new(self.zonk_f(b)))
            }
            Formula::Exists(x, t, b) => {
                Formula::Exists(x.clone(), t.clone(), Box::new(self.zonk_f(b)))
            }
            Formula::Bot => Formula::Bot,
        }
    }

    fn norm(&self, ctx: &Ctx, f: &Formula) -> Formula {
        ctx.expand_f(&self.zonk_f(f))
    }

    /// let の展開と束縛変数の名前の違いを無視して、a と b を単一化する。失敗したら元に戻す。
    fn unify(&mut self, ctx: &Ctx, a: &Formula, b: &Formula) -> bool {
        let save = self.metas.clone();
        let (a, b) = (self.norm(ctx, a), self.norm(ctx, b));
        let ok = self.uf(&a, &b);
        if !ok {
            self.metas = save;
        }
        ok
    }

    fn uf(&mut self, a: &Formula, b: &Formula) -> bool {
        use Formula::*;
        match (a, b) {
            (Atom(p, ts), Atom(q, us)) => {
                p == q && ts.len() == us.len() && ts.iter().zip(us).all(|(t, u)| self.ut(t, u))
            }
            (Imp(a1, b1), Imp(a2, b2)) | (And(a1, b1), And(a2, b2)) | (Or(a1, b1), Or(a2, b2)) => {
                self.uf(a1, a2) && self.uf(b1, b2)
            }
            (Forall(x, t1, b1), Forall(y, t2, b2)) | (Exists(x, t1, b1), Exists(y, t2, b2)) => {
                if !types_compatible(t1, t2) {
                    return false;
                }
                self.fresh += 1;
                let v = Term::Var(format!("#{}", self.fresh));
                self.uf(&b1.subst(x, &v), &b2.subst(y, &v))
            }
            (Bot, Bot) => true,
            _ => false,
        }
    }

    fn ut(&mut self, a: &Term, b: &Term) -> bool {
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
            (Term::Var(x), Term::Var(y)) => x == y,
            (Term::Num(x), Term::Num(y)) => x == y,
            (Term::App(f, xs), Term::App(g, ys)) => {
                f == g && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.ut(x, y))
            }
            _ => false,
        }
    }

    // ------------------------------------------------ 名前と根拠

    fn record(&mut self, name: &str) {
        let s = &self.env.schemes[name];
        if !s.core && s.is_axiom {
            self.axioms.insert(name.to_string());
        }
        self.axioms.extend(s.axioms.iter().cloned());
        self.oracles.extend(s.oracles.iter().cloned());
    }

    fn resolve(&mut self, ctx: &Ctx, name: &str) -> CResult<Formula> {
        if let Some(f) = ctx.hyp(name) {
            return Ok(f.clone());
        }
        if ctx.is_term_var(name) {
            return self.err(format!("`{name}` は項（対象）であって、証拠ではない"));
        }
        if let Some(s) = self.env.schemes.get(name) {
            if !s.ok {
                return self.err(format!("`{name}` は検証に失敗した定理なので使えない"));
            }
            let mut f = s.formula.clone();
            for v in s.implicit.clone() {
                let m = self.new_meta();
                f = f.subst(&v, &m);
            }
            self.record(name);
            return Ok(f);
        }
        if let Some((base, field)) = name.rsplit_once('.') {
            if field == "left" || field == "right" {
                let f = self.resolve(ctx, base)?;
                return match self.norm(ctx, &f) {
                    Formula::And(a, b) => Ok(if field == "left" { *a } else { *b }),
                    g => self.err(format!(
                        "`{base}` は「{g}」で ∧ の形ではないので、.{field} は使えない"
                    )),
                };
            }
        }
        self.err(format!("`{name}` が見つからない（文脈にも定理にもない）"))
    }

    fn names_proof(&self, ctx: &Ctx, n: &str) -> bool {
        if ctx.hyp(n).is_some() {
            return true;
        }
        if ctx.is_term_var(n) {
            return false;
        }
        if self.env.schemes.contains_key(n) || BUILTINS.contains(&n) {
            return true;
        }
        match n.rsplit_once('.') {
            Some((base, "left" | "right")) => self.names_proof(ctx, base),
            _ => false,
        }
    }

    fn is_proof(&self, ctx: &Ctx, t: &Term) -> bool {
        match t {
            Term::Var(n) | Term::App(n, _) => self.names_proof(ctx, n),
            _ => false,
        }
    }

    fn check_term_scope(&self, ctx: &Ctx, t: &Term) -> CResult<()> {
        let mut vs = BTreeSet::new();
        t.vars(&mut vs);
        for v in vs {
            if !ctx.is_term_var(&v) {
                return self.err(format!(
                    "`{v}` は文脈にない（スコープの外か、まだ導入されていない）"
                ));
            }
        }
        Ok(())
    }

    fn check_formula_scope(&self, ctx: &Ctx, f: &Formula) -> CResult<()> {
        for v in f.free_vars() {
            if !ctx.is_term_var(&v) {
                return self.err(format!(
                    "`{v}` は文脈にない（スコープの外か、まだ導入されていない）"
                ));
            }
        }
        Ok(())
    }

    /// 根拠 p が示す命題を求める
    fn infer(&mut self, ctx: &Ctx, p: &Term) -> CResult<Formula> {
        match p {
            Term::Var(n) | Term::App(n, _) if BUILTINS.contains(&n.as_str()) => self.err(format!(
                "`{n}` は、示すべき命題が決まっている場所（goal・have・連鎖）でしか使えない"
            )),
            Term::Var(n) => self.resolve(ctx, n),
            Term::App(n, args) => {
                let f = self.resolve(ctx, n)?;
                self.apply(ctx, f, args)
            }
            _ => self.err(format!("`{p}` は根拠として読めない")),
        }
    }

    /// ∀除去（項を渡す）と →除去（証拠を渡す）を引数の順に行う
    fn apply(&mut self, ctx: &Ctx, f: Formula, args: &[Term]) -> CResult<Formula> {
        let mut f = f;
        for arg in args {
            loop {
                match self.zonk_f(&f) {
                    Formula::Forall(x, _, body) => {
                        if self.is_proof(ctx, arg) {
                            // 証拠が来たら、∀ の変数は単一化で決める
                            let m = self.new_meta();
                            f = body.subst(&x, &m);
                            continue;
                        }
                        self.check_term_scope(ctx, arg)?;
                        f = body.subst(&x, arg);
                    }
                    Formula::Imp(a, b) => {
                        if !self.is_proof(ctx, arg) {
                            let a = self.zonk_f(&a);
                            return self.err(format!(
                                "ここには「{a}」の証拠が必要だが、項 `{arg}` が渡された"
                            ));
                        }
                        self.check(ctx, arg, &a)?;
                        f = *b;
                    }
                    g => {
                        return self.err(format!(
                            "引数が多すぎる（「{g}」にはもう `{arg}` を渡せない）"
                        ));
                    }
                }
                break;
            }
        }
        Ok(f)
    }

    fn check_just(&mut self, ctx: &Ctx, j: &Just, expected: &Formula) -> CResult<()> {
        if j.len() == 1 {
            return self.check(ctx, &j[0], expected);
        }
        // j₁, j₂, … は ∧導入
        let e = self.norm(ctx, expected);
        match e.split_and(j.len()) {
            Some(parts) => {
                for (p, f) in j.iter().zip(parts) {
                    self.check(ctx, p, &f)?;
                }
                Ok(())
            }
            None => self.err(format!(
                "根拠が {} 個あるが、示すべき「{e}」は {} 個の ∧ ではない",
                j.len(),
                j.len()
            )),
        }
    }

    /// 根拠 p が命題 expected を示すか
    fn check(&mut self, ctx: &Ctx, p: &Term, expected: &Formula) -> CResult<()> {
        let e = self.norm(ctx, expected);
        match p {
            Term::Var(n) if n == "refl" => match &e {
                Formula::Atom(r, ts) if r == "=" && self.ut(&ts[0], &ts[1]) => Ok(()),
                _ => self.err(format!(
                    "refl で示せるのは t = t の形だけ（必要なのは「{e}」）"
                )),
            },
            Term::Var(n) if n == "ring" => {
                if e.has_meta() {
                    return self.err("ring に渡す命題がまだ決まっていない");
                }
                match &e {
                    Formula::Atom(r, ts) if r == "=" && arith::ring(&ts[0], &ts[1]) => {
                        self.oracles.insert("ring".into());
                        Ok(())
                    }
                    _ => self.err(format!("ring では「{e}」を示せない")),
                }
            }
            Term::Var(n) if n == "sorry" => {
                self.oracles.insert("sorry".into());
                self.sorries.push((self.line, self.snapshot.0.show(), e));
                Ok(())
            }
            Term::Var(n) if n == "linarith" => self.linarith(ctx, &[], &e, "linarith"),
            Term::App(n, hints) if n == "linarith" => self.linarith(ctx, hints, &e, "linarith"),
            Term::Var(n) if n == "decide" => {
                if !e.free_vars().is_empty() || e.has_meta() {
                    return self.err(format!(
                        "decide は変数を含まない命題にしか使えない（「{e}」）"
                    ));
                }
                match arith::decide(&e) {
                    Some(true) => {
                        self.oracles.insert("decide".into());
                        Ok(())
                    }
                    Some(false) => self.err(format!("decide：「{e}」は偽")),
                    None => self.err(format!("decide では「{e}」を計算できない")),
                }
            }
            Term::App(n, args) if n == "EQ2" => self.eq2(ctx, args, &e),
            Term::App(n, args) if (n == "or.left" || n == "or.right") && args.len() == 1 => {
                match &e {
                    Formula::Or(l, r) => {
                        self.check(ctx, &args[0], if n == "or.left" { l } else { r })
                    }
                    _ => self.err(format!("{n} で示せるのは ∨ の形だけ（必要なのは「{e}」）")),
                }
            }
            _ => {
                let f = self.infer(ctx, p)?;
                if self.unify(ctx, &f, &e) {
                    return Ok(());
                }
                let f = self.norm(ctx, &f);
                if f == Formula::Bot {
                    return Ok(()); // ⊥除去
                }
                let e = self.norm(ctx, &e);
                self.err(format!(
                    "根拠 `{p}` が示すのは\n      {f}\n    だが、必要なのは\n      {e}"
                ))
            }
        }
    }

    fn rel_facts(f: &Formula, out: &mut Vec<(String, Term, Term)>) {
        match f {
            Formula::Atom(r, ts)
                if ["=", "<", "≤", ">", "≥"].contains(&r.as_str())
                    && ts.len() == 2
                    && !f.has_meta() =>
            {
                out.push((r.clone(), ts[0].clone(), ts[1].clone()))
            }
            Formula::And(a, b) => {
                Self::rel_facts(a, out);
                Self::rel_facts(b, out);
            }
            _ => {}
        }
    }

    /// 文脈の仮定（と hints）から、線形算術で e を示す
    fn linarith(&mut self, ctx: &Ctx, hints: &[Term], e: &Formula, tag: &str) -> CResult<()> {
        let mut extra = Vec::new();
        for h in hints {
            let f = self.infer(ctx, h)?;
            extra.push(self.norm(ctx, &f));
        }
        if self.linarith_facts(ctx, &extra, e) {
            self.oracles.insert(tag.into());
            Ok(())
        } else {
            self.err(format!("linarith では「{e}」を示せない"))
        }
    }

    fn linarith_facts(&self, ctx: &Ctx, extra: &[Formula], e: &Formula) -> bool {
        let e = self.norm(ctx, e);
        let (rel, l, r) = match &e {
            Formula::Atom(r, ts) if ts.len() == 2 && !e.has_meta() => (r.as_str(), &ts[0], &ts[1]),
            _ => return false,
        };
        let mut facts = Vec::new();
        for f in extra {
            Self::rel_facts(f, &mut facts);
        }
        for en in &ctx.entries {
            match en {
                Entry::Hyp(_, f) => Self::rel_facts(&self.norm(ctx, f), &mut facts),
                Entry::Var(x, t, _) if t == "ℕ" => {
                    facts.push(("≥".into(), Term::Var(x.clone()), Term::Num(0)))
                }
                _ => {}
            }
        }
        arith::linarith(&facts, (rel, l, r))
    }

    /// EQ2(h, hφ)：h : x = y、hφ : φ(x) から φ(y)。φ は goal と hφ を見比べて決める。
    fn eq2(&mut self, ctx: &Ctx, args: &[Term], g: &Formula) -> CResult<()> {
        if args.len() != 2 {
            return self.err("EQ2 は EQ2(h, hφ) の形で書く");
        }
        let h = self.infer(ctx, &args[0])?;
        let h = self.norm(ctx, &h);
        let (x, y) = match &h {
            Formula::Atom(r, ts) if r == "=" && !h.has_meta() => (ts[0].clone(), ts[1].clone()),
            _ => {
                return self.err(format!(
                    "EQ2 の第1引数は等式の証拠（「{h}」は等式ではない）"
                ));
            }
        };
        if g.has_meta() {
            return self.err("EQ2 の結論がまだ決まっていない");
        }
        let refl = |t: &Term| Formula::Atom("=".into(), vec![t.clone(), t.clone()]);
        let cands: Vec<Formula> = if args[1] == Term::Var("refl".into()) {
            let mut c = vec![];
            if let Formula::Atom(r, ts) = g {
                if r == "=" {
                    c.push(refl(&ts[0]));
                    c.push(refl(&ts[1]));
                }
            }
            c.push(refl(&x));
            c.push(refl(&y));
            c
        } else {
            let f = self.infer(ctx, &args[1])?;
            vec![self.norm(ctx, &f)]
        };
        if cands.iter().any(|p| repl_f(p, g, &x, &y)) {
            Ok(())
        } else {
            self.err(format!(
                "EQ2：{x} の一部を {y} に置き換えても「{g}」にならない"
            ))
        }
    }

    // ------------------------------------------------ 文

    fn fresh_name(&self, ctx: &Ctx, x: &str) -> CResult<()> {
        if ctx.has_name(x) {
            return self.err(format!("名前 `{x}` はすでに使われている"));
        }
        Ok(())
    }

    fn push(&self, ctx: &mut Ctx, e: Entry) {
        if self.trace {
            let pad = "  ".repeat(self.depth);
            let s = match &e {
                Entry::Var(x, t, _) if t == "?" => x.clone(),
                Entry::Var(x, t, _) => format!("{x} : {t}"),
                Entry::Hyp(h, f) => format!("{h} : {f}"),
                Entry::Def(x, t) => format!("{x} := {t}"),
            };
            if !matches!(&e, Entry::Hyp(h, _) if h.ends_with(".def")) {
                println!("       │ {pad}    + {s}");
            }
        }
        ctx.entries.push(e);
    }

    fn record_step(
        &mut self,
        line: usize,
        depth: usize,
        src: &str,
        ctx: &Ctx,
        goal: &Option<Formula>,
    ) {
        self.steps.push(StepTrace {
            line,
            depth,
            src: src.to_string(),
            ctx: ctx.show(),
            ctx_latex: ctx.show_latex(),
            goal: goal.as_ref().map(|g| g.to_string()),
            goal_latex: goal.as_ref().map(|g| g.to_latex()),
        });
    }

    pub fn check_decl(&mut self, d: &Decl) -> CResult<()> {
        let mut ctx = Ctx::default();
        let declared: BTreeSet<String> = d
            .ctx
            .iter()
            .filter_map(|c| match c {
                CtxItem::Var(x, _) => Some(x.clone()),
                _ => None,
            })
            .collect();
        for v in statement_vars(d) {
            if !declared.contains(&v) {
                ctx.entries.push(Entry::Var(v, "?".into(), VarKind::Const));
            }
        }
        for c in &d.ctx {
            ctx.entries.push(match c {
                CtxItem::Var(x, t) => Entry::Var(x.clone(), t.clone(), VarKind::Const),
                CtxItem::Hyp(h, f) => Entry::Hyp(h.clone(), f.clone()),
            });
        }
        self.line = d.line;
        self.record_step(
            d.line,
            0,
            &format!("thm {}", d.name),
            &ctx,
            &Some(d.concl.clone()),
        );
        if d.body.is_empty() {
            self.snapshot = (ctx, Some(d.concl.clone()));
            return self.err("証明が書かれていない");
        }
        self.block(ctx, &d.body, d.concl.clone(), d.line)
    }

    fn block(
        &mut self,
        ctx: Ctx,
        stmts: &[Stmt],
        goal: Formula,
        parent_line: usize,
    ) -> CResult<()> {
        let mut ctx = ctx;
        let mut goal = Some(goal);
        let mut last: Option<Formula> = None;
        self.depth += 1;
        for (i, s) in stmts.iter().enumerate() {
            self.line = s.line;
            self.snapshot = (ctx.clone(), goal.clone());
            self.record_step(s.line, self.depth, &s.src, &ctx, &goal);
            if self.trace {
                let pad = "  ".repeat(self.depth - 1);
                println!("  {:>4} │ {pad}{}", s.line, s.src);
                if let Some(g) = &goal {
                    println!("       │ {pad}    ⊢ {g}");
                }
            }
            let is_last = i + 1 == stmts.len();
            if goal.is_none() && !matches!(s.kind, StmtKind::Therefore(_)) {
                return self.err("goal はもう示し終わっている。この行は不要");
            }
            self.stmt(&mut ctx, &mut goal, &mut last, s, is_last)?;
        }
        self.depth -= 1;
        if let Some(g) = goal {
            self.line = stmts.last().map(|s| s.line).unwrap_or(parent_line);
            self.snapshot = (ctx, Some(g.clone()));
            return self.err(format!(
                "ブロックが終わったが、goal「{g}」がまだ示されていない"
            ));
        }
        Ok(())
    }

    fn stmt(
        &mut self,
        ctx: &mut Ctx,
        goal: &mut Option<Formula>,
        last: &mut Option<Formula>,
        s: &Stmt,
        is_last: bool,
    ) -> CResult<()> {
        let g = goal.clone().unwrap_or(Formula::Bot);
        match &s.kind {
            StmtKind::Fix { vars, hyp, body } => {
                let mut c2 = ctx.clone();
                let mut cur = g.clone();
                for (x, ty) in vars {
                    match cur {
                        Formula::Forall(y, t, b) => {
                            if let Some(ty) = ty {
                                if !types_compatible(ty, &t) {
                                    return self.err(format!(
                                        "型が違う：goal の変数は {t} だが、{ty} と書かれている"
                                    ));
                                }
                            }
                            self.fresh_name(&c2, x)?;
                            let t = if t == "?" { ty.clone().unwrap_or(t) } else { t };
                            self.push(&mut c2, Entry::Var(x.clone(), t, VarKind::Fixed));
                            cur = b.subst(&y, &Term::Var(x.clone()));
                        }
                        other => {
                            return self
                                .err(format!("Fix できない：goal「{other}」は ∀ の形ではない"));
                        }
                    }
                }
                if let Some((h, f)) = hyp {
                    match cur {
                        Formula::Imp(a, b) => {
                            let a = self.assumed(&c2, f.as_ref(), &a)?;
                            self.fresh_name(&c2, h)?;
                            self.push(&mut c2, Entry::Hyp(h.clone(), a));
                            cur = *b;
                        }
                        other => {
                            return self.err(format!(
                                "`| {h}` は使えない：goal「{other}」は「… → …」の形ではない"
                            ));
                        }
                    }
                }
                self.block(c2, body, cur, s.line)?;
                *last = goal.take();
            }
            StmtKind::Assume { name, ty, body } => match g.clone() {
                Formula::Imp(a, b) => {
                    let mut c2 = ctx.clone();
                    let a = self.assumed(&c2, ty.as_ref(), &a)?;
                    self.fresh_name(&c2, name)?;
                    self.push(&mut c2, Entry::Hyp(name.clone(), a));
                    self.block(c2, body, *b, s.line)?;
                    *last = goal.take();
                }
                other => {
                    return self.err(format!(
                        "assume できない：goal「{other}」は「… → …」の形ではない"
                    ));
                }
            },
            StmtKind::ByContra { name, body } => {
                if matches!(&g, Formula::Imp(_, b) if **b == Formula::Bot) {
                    return self.err("goal が否定（¬φ）なので、by_contra ではなく assume を使う");
                }
                let mut c2 = ctx.clone();
                self.fresh_name(&c2, name)?;
                self.push(&mut c2, Entry::Hyp(name.clone(), not(g.clone())));
                self.block(c2, body, Formula::Bot, s.line)?;
                *last = goal.take();
            }
            StmtKind::Obtain {
                var,
                deps,
                hyps,
                just,
            } => {
                if just.len() != 1 {
                    return self.err("Obtain の根拠は1つ");
                }
                let f = self.infer(ctx, &just[0])?;
                let f = self.norm(ctx, &f);
                if f.has_meta() {
                    return self.err(format!("根拠の引数が足りず、命題が決まらない：{f}"));
                }
                match f {
                    Formula::Exists(y, ty, body) => {
                        self.fresh_name(ctx, var)?;
                        if let Some(deps) = deps {
                            let actual = ctx.fixed_vars();
                            let a: BTreeSet<&String> = actual.iter().collect();
                            let d: BTreeSet<&String> = deps.iter().collect();
                            if a != d {
                                return self.err(format!(
                                    "依存関係の宣言が合わない：{var} は ({}) のスコープの中で取り出しているので ({}) に依存するが、宣言は {var}({})",
                                    actual.join(", "),
                                    actual.join(", "),
                                    deps.join(", ")
                                ));
                            }
                        }
                        self.push(ctx, Entry::Var(var.clone(), ty, VarKind::Obtained));
                        let body = body.subst(&y, &Term::Var(var.clone()));
                        let parts = match body.split_and(hyps.len()) {
                            Some(p) => p,
                            None => {
                                return self.err(format!(
                                    "「{body}」を {} 個の ∧ に分けられない",
                                    hyps.len()
                                ));
                            }
                        };
                        for (h, p) in hyps.iter().zip(parts) {
                            self.fresh_name(ctx, h)?;
                            self.push(ctx, Entry::Hyp(h.clone(), p));
                        }
                        *last = Some(body);
                    }
                    other => {
                        return self.err(format!(
                            "Obtain できない：根拠が示すのは ∃ ではなく「{other}」"
                        ));
                    }
                }
            }
            StmtKind::Have { name, ty, just } => {
                self.check_formula_scope(ctx, ty)?;
                self.check_just(ctx, just, ty)?;
                self.fresh_name(ctx, name)?;
                self.push(ctx, Entry::Hyp(name.clone(), ty.clone()));
                *last = Some(ty.clone());
            }
            StmtKind::Suffices { ty, just } => {
                self.check_formula_scope(ctx, ty)?;
                let need = Formula::Imp(Box::new(ty.clone()), Box::new(g.clone()));
                self.check_just(ctx, just, &need)?;
                *goal = Some(ty.clone());
            }
            StmtKind::Choose { choice, just } => {
                let next = match (choice, g.clone()) {
                    (Choice::Term(t), Formula::Exists(y, _, b)) => {
                        self.check_term_scope(ctx, t)?;
                        b.subst(&y, t)
                    }
                    (Choice::Left, Formula::Or(a, _)) => *a,
                    (Choice::Right, Formula::Or(_, b)) => *b,
                    (Choice::Term(_), other) => {
                        return self
                            .err(format!("choose できない：goal「{other}」は ∃ の形ではない"));
                    }
                    (_, other) => {
                        return self.err(format!(
                            "choose left/right できない：goal「{other}」は ∨ の形ではない"
                        ));
                    }
                };
                *goal = Some(match just {
                    None => next,
                    // choose t, j：範囲付き ∃ の条件 t > 0 などを j で示す
                    Some(j) => match next {
                        Formula::And(a, b) => {
                            self.check_just(ctx, j, &a)?;
                            *b
                        }
                        other => {
                            return self.err(format!(
                                "`choose t, 根拠` は条件付きの ∃ にだけ使える（「{other}」）"
                            ));
                        }
                    },
                });
            }
            StmtKind::Contradiction(a, b) => {
                let fa = self.resolve(ctx, a)?;
                let fb = self.resolve(ctx, b)?;
                if !(self.unify(ctx, &fb, &not(fa.clone()))
                    || self.unify(ctx, &fa, &not(fb.clone())))
                {
                    let (fa, fb) = (self.norm(ctx, &fa), self.norm(ctx, &fb));
                    return self.err(format!(
                        "`{a}` : {fa} と `{b}` : {fb} は互いの否定になっていない"
                    ));
                }
                *last = goal.take();
            }
            StmtKind::Cases { hyp, left, right } => {
                let f = self.resolve(ctx, hyp)?;
                match self.norm(ctx, &f) {
                    Formula::Or(a, b) => {
                        for ((h, body), side) in [(left, *a), (right, *b)] {
                            let mut c2 = ctx.clone();
                            self.fresh_name(&c2, h)?;
                            self.push(&mut c2, Entry::Hyp(h.clone(), side));
                            self.block(c2, body, g.clone(), s.line)?;
                        }
                        *last = goal.take();
                    }
                    other => {
                        return self.err(format!(
                            "cases できない：`{hyp}` は「{other}」で ∨ の形ではない"
                        ));
                    }
                }
            }
            StmtKind::Induction {
                var,
                zero,
                succ,
                succ_line,
            } => {
                let (pv, pred) = if ctx.is_term_var(var) {
                    (var.clone(), g.clone())
                } else {
                    match g.clone() {
                        Formula::Forall(y, _, b) => (y, *b),
                        other => return self.err(format!(
                            "induction できない：`{var}` は文脈になく、goal「{other}」も ∀ ではない"
                        )),
                    }
                };
                self.block(ctx.clone(), zero, pred.subst(&pv, &Term::Num(0)), s.line)?;
                let (k, ih, ih_ty, body) = succ;
                let mut c2 = ctx.clone();
                self.line = *succ_line;
                self.fresh_name(&c2, k)?;
                self.push(&mut c2, Entry::Var(k.clone(), "ℕ".into(), VarKind::Fixed));
                let ih_f = pred.subst(&pv, &Term::Var(k.clone()));
                let ih_f = self.assumed(&c2, ih_ty.as_ref(), &ih_f)?;
                self.fresh_name(&c2, ih)?;
                self.push(&mut c2, Entry::Hyp(ih.clone(), ih_f));
                let sg = pred.subst(&pv, &Term::App("S".into(), vec![Term::Var(k.clone())]));
                self.record_step(
                    *succ_line,
                    self.depth + 1,
                    &format!("Case succ {k}, {ih}"),
                    &c2,
                    &Some(sg.clone()),
                );
                self.block(c2, body, sg, *succ_line)?;
                *last = goal.take();
            }
            StmtKind::Let { name, term } => {
                self.check_term_scope(ctx, term)?;
                self.fresh_name(ctx, name)?;
                self.push(ctx, Entry::Def(name.clone(), term.clone()));
                ctx.entries.push(Entry::Hyp(
                    format!("{name}.def"),
                    Formula::Atom("=".into(), vec![Term::Var(name.clone()), term.clone()]),
                ));
            }
            StmtKind::Therefore(f) => {
                self.check_formula_scope(ctx, f)?;
                match last.clone() {
                    Some(l) if self.unify(ctx, f, &l) => {}
                    Some(l) => {
                        return self.err(format!("∴ の命題が、直前に示したもの「{l}」と一致しない"));
                    }
                    None => return self.err("∴ の前に、示し終わったものがない"),
                }
            }
            StmtKind::Close(j) => {
                self.check_just(ctx, j, &g)?;
                *last = goal.take();
            }
            StmtKind::Chain { start, steps } => {
                let result = self.chain(ctx, start, steps)?;
                if is_last {
                    if !self.unify(ctx, &result, &g) {
                        if self.linarith_facts(ctx, std::slice::from_ref(&result), &g) {
                            self.oracles.insert("linarith".into());
                        } else {
                            return self
                                .err(format!("連鎖の結論「{result}」が goal「{g}」と一致しない"));
                        }
                    }
                    *last = goal.take();
                } else {
                    self.push(ctx, Entry::Hyp("this".into(), result.clone()));
                    *last = Some(result);
                }
            }
        }
        Ok(())
    }

    /// assume / Fix | h / Case succ で書かれた仮定の型を、goal から決まるものと照合する
    fn assumed(
        &mut self,
        ctx: &Ctx,
        written: Option<&Formula>,
        expected: &Formula,
    ) -> CResult<Formula> {
        match written {
            None => Ok(expected.clone()),
            Some(f) => {
                self.check_formula_scope(ctx, f)?;
                if self.unify(ctx, f, expected) {
                    Ok(f.clone())
                } else {
                    self.err(format!("仮定の型が違う：goal から決まるのは「{expected}」だが、「{f}」と書かれている"))
                }
            }
        }
    }

    fn chain(&mut self, ctx: &Ctx, start: &Term, steps: &[ChainStep]) -> CResult<Formula> {
        self.check_term_scope(ctx, start)?;
        let mut cur = start.clone();
        let mut acc: Option<String> = None;
        for st in steps {
            self.line = st.line;
            let f = Formula::Atom(st.rel.clone(), vec![cur.clone(), st.term.clone()]);
            self.record_step(
                st.line,
                self.depth + 1,
                &format!("{} {} by ...", st.rel, st.term),
                ctx,
                &Some(f.clone()),
            );
            self.check_term_scope(ctx, &st.term)?;
            self.chain_step(ctx, &st.just, &f)?;
            acc = Some(match compose(acc.as_deref(), &st.rel) {
                Some(r) => r,
                None => return self.err("連鎖の中で不等号の向きが混ざっている"),
            });
            cur = st.term.clone();
        }
        Ok(Formula::Atom(
            acc.unwrap_or_else(|| "=".into()),
            vec![start.clone(), cur],
        ))
    }

    /// 連鎖の1段。根拠がそのまま当てはまらなければ、根拠の命題を事実として linarith で補う。
    fn chain_step(&mut self, ctx: &Ctx, j: &Just, f: &Formula) -> CResult<()> {
        match self.check_just(ctx, j, f) {
            Ok(()) => Ok(()),
            Err(e) => {
                let mut facts = Vec::new();
                for p in j {
                    match self.infer(ctx, p) {
                        Ok(x) => facts.push(self.norm(ctx, &x)),
                        Err(_) => return Err(e),
                    }
                }
                if self.linarith_facts(ctx, &facts, f) {
                    self.oracles.insert("linarith".into());
                    Ok(())
                } else {
                    Err(e)
                }
            }
        }
    }
}

fn occurs(m: u32, t: &Term) -> bool {
    match t {
        Term::Meta(n) => *n == m,
        Term::App(_, a) => a.iter().any(|x| occurs(m, x)),
        _ => false,
    }
}

fn compose(a: Option<&str>, b: &str) -> Option<String> {
    let dir = |r: &str| match r {
        "=" => 0,
        "<" | "≤" => 1,
        _ => -1,
    };
    let a = match a {
        None => return Some(b.into()),
        Some(a) => a,
    };
    if a == "=" {
        return Some(b.into());
    }
    if b == "=" {
        return Some(a.into());
    }
    if dir(a) != dir(b) {
        return None;
    }
    let strict = a == "<" || a == ">" || b == "<" || b == ">";
    Some(
        match (dir(a), strict) {
            (1, true) => "<",
            (1, false) => "≤",
            (_, true) => ">",
            (_, false) => "≥",
        }
        .into(),
    )
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
        (Atom(a, ps), Atom(b, gs)) => {
            a == b && ps.len() == gs.len() && ps.iter().zip(gs).all(|(s, t)| repl_t(s, t, x, y))
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

pub fn statement_vars(d: &Decl) -> BTreeSet<String> {
    let mut vs = d.concl.free_vars();
    for c in &d.ctx {
        if let CtxItem::Hyp(_, f) = c {
            vs.extend(f.free_vars());
        }
    }
    vs
}

// ================================================================ ファイルの検査

pub struct Report {
    pub name: String,
    pub line: usize,
    pub is_axiom: bool,
    pub err: Option<CheckError>,
    pub axioms: BTreeSet<String>,
    pub oracles: BTreeSet<String>,
    pub sorries: Vec<(usize, Vec<String>, Formula)>,
    pub steps: Vec<StepTrace>,
}

pub fn check_decls(env: &mut Env, decls: &[Decl], trace: bool, core: bool) -> Vec<Report> {
    let mut reports = Vec::new();
    for d in decls {
        // 定理の型：仮定を → でつなぎ、自由変数は使うたびに単一化で決める
        let mut formula = d.concl.clone();
        for c in d.ctx.iter().rev() {
            if let CtxItem::Hyp(_, f) = c {
                formula = Formula::Imp(Box::new(f.clone()), Box::new(formula));
            }
        }
        let implicit: Vec<String> = statement_vars(d).into_iter().collect();
        let (err, axioms, oracles, sorries, steps) = if env.schemes.contains_key(&d.name) {
            let msg = format!(
                "名前 `{}` はすでに使われている（組み込みの定理か、前に書いた定理）",
                d.name
            );
            (
                Some(CheckError {
                    line: d.line,
                    msg,
                    goal: None,
                    ctx: vec![],
                    ctx_latex: vec![],
                }),
                BTreeSet::new(),
                BTreeSet::new(),
                vec![],
                vec![],
            )
        } else if d.is_axiom {
            (None, BTreeSet::new(), BTreeSet::new(), vec![], vec![])
        } else {
            if trace {
                println!("\n── thm {} ──", d.name);
            }
            let mut ch = Checker::new(env, trace);
            let r = ch.check_decl(d).err();
            (r, ch.axioms, ch.oracles, ch.sorries, ch.steps)
        };
        if env.schemes.contains_key(&d.name) {
            reports.push(Report {
                name: d.name.clone(),
                line: d.line,
                is_axiom: false,
                err,
                axioms,
                oracles,
                sorries,
                steps,
            });
            continue;
        }
        let ok = err.is_none();
        env.schemes.insert(
            d.name.clone(),
            Scheme {
                formula,
                implicit,
                core,
                is_axiom: d.is_axiom,
                ok,
                axioms: axioms.clone(),
                oracles: oracles.clone(),
            },
        );
        reports.push(Report {
            name: d.name.clone(),
            line: d.line,
            is_axiom: d.is_axiom,
            err,
            axioms,
            oracles,
            sorries,
            steps,
        });
    }
    reports
}
