//! elab（推敲器）。表層の証明（Fix・Obtain・連鎖…）を読み、kernel の証明項を組み立てる。
//!
//! ここは **信じなくてよい** 部分。単一化・定義の展開・自動証明の探索をして証明項を作るが、
//! 最後に kernel（src/kernel/）が証明項を検算する。ここにバグがあっても、誤った定理は
//! kernel で止まる（逆に、正しい証明が通らないことはありうる）。
//!
//! - `unify.rs`：メタ変数（項・ソート・関数記号）と単一化
//! - `just.rs` ：根拠（`h(a, b)`・`ring`・`linarith` など）の解釈
//! - `stmt.rs` ：文（Fix・Obtain・have・連鎖など）

mod just;
mod stmt;
mod unify;

use crate::kernel::env::{DefBody, KEnv};
use crate::kernel::Statement;
use crate::parser::{CtxItem, Decl, Def, Item, Module, ParseError};
use crate::sorts::Infer;
use crate::syntax::{Formula, Term, ident_to_latex};
use std::collections::{BTreeSet, HashSet};

// ================================================================ 環境

#[derive(Default)]
pub struct Env {
    pub kernel: KEnv,
    /// 検証に失敗した定理（使おうとしたときに分かりやすく伝えるため）
    pub failed: HashSet<String>,
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
    /// let で置いた名前（名前・型・中身）
    Def(String, String, Term),
}

#[derive(Clone, Default, Debug)]
pub struct Ctx {
    pub entries: Vec<Entry>,
}

impl Ctx {
    fn has_name(&self, n: &str) -> bool {
        self.entries.iter().any(|e| match e {
            Entry::Var(x, ..) | Entry::Hyp(x, _) | Entry::Def(x, ..) => x == n,
        })
    }
    pub fn hyp(&self, n: &str) -> Option<&Formula> {
        self.entries.iter().rev().find_map(|e| match e {
            Entry::Hyp(x, f) if x == n => Some(f),
            _ => None,
        })
    }
    fn is_term_var(&self, n: &str) -> bool {
        self.entries.iter().any(|e| matches!(e, Entry::Var(x, ..) | Entry::Def(x, ..) if x == n))
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
            if let Entry::Def(x, _, t) = e {
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
                    Some(if t.starts_with('\'') { format!("{x}{kind}") } else { format!("{x} : {t}{kind}") })
                }
                Entry::Hyp(h, _) if h.ends_with(".def") => None,
                Entry::Hyp(h, f) => Some(format!("{h} : {f}")),
                Entry::Def(x, _, t) => Some(format!("{x} := {t}")),
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
                    Some(if t.starts_with('\'') {
                        format!("{xl}{kind}")
                    } else {
                        format!("{xl} \\in {}{kind}", ident_to_latex(t))
                    })
                }
                Entry::Hyp(h, _) if h.ends_with(".def") => None,
                Entry::Hyp(h, f) => Some(format!("{} : {}", ident_to_latex(h), f.to_latex())),
                Entry::Def(x, _, t) => Some(format!("{} := {}", ident_to_latex(x), t.to_latex())),
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
    /// 次の一手の候補（goal と仮定の形から。src は書くもの、why は理由）
    pub hints: Vec<(String, String)>,
    /// 文脈（goal と仮定、定義を展開した形も）に現れる式。エディタの記法の補完に使う（docs/system/editor.md）
    pub terms: Vec<String>,
    /// 数列（ℕ → 何か）の変数の名前
    pub seqs: Vec<String>,
}

#[derive(Debug)]
pub struct CheckError {
    pub line: usize,
    pub msg: String,
    pub goal: Option<Formula>,
    pub ctx: Vec<String>,
    pub ctx_latex: Vec<String>,
    /// 直し方：この行の末尾に足せばよい文字列（エディタの Tab で入る）
    pub fix: Option<String>,
    /// ほかの直し方の候補（同じく行末に足す）
    pub alts: Vec<String>,
    /// 文脈の数列（goal を添字 a_n で表示するため）
    pub seqs: BTreeSet<String>,
}

impl CheckError {
    /// goal の表示（ふつうの形・LaTeX）
    pub fn goal_show(&self) -> Option<(String, String)> {
        let g = self.goal.as_ref()?;
        Some(crate::syntax::with_sub_seqs(&self.seqs, || (g.to_string(), g.to_latex())))
    }
}

type CResult<T> = Result<T, CheckError>;

const BUILTINS: [&str; 8] = ["sorry", "refl", "ring", "linarith", "decide", "EQ2", "or.left", "or.right"];
/// 自然演繹の規則の名前（短い書き方の別名。docs/language/syntax.md）。
/// and.intro(p, q) = `p, q`、and.left(h) = `h.left`、imp.elim(f, a) = `f(a)`、all.elim(h, t) = `h(t)`、bot.elim(h)
const RULES: [&str; 6] = ["and.intro", "and.left", "and.right", "imp.elim", "all.elim", "bot.elim"];

// ================================================================ 検査器の状態

pub struct Checker<'a> {
    env: &'a Env,
    /// 項のメタ変数
    metas: Vec<Option<Term>>,
    /// ソートのメタ変数（`?σ3`）
    sort_metas: Vec<Option<String>>,
    /// 関数型・述語型のメタ変数（`?F2`）：中身（名前・λ・集合）と型
    fn_metas: Vec<(Option<Term>, String)>,
    /// 定理を使ったときの「パラメータの型 = 引数の項の型」という約束。
    /// 引数が穴のうちは型が分からないので、最後（穴が埋まったあと）に解く。
    pending: Vec<(Vec<(String, String)>, String, Term)>,
    fresh: u32,
    line: usize,
    snapshot: (Ctx, Option<Formula>),
    /// sorry で飛ばした箇所：(行, 文脈, 残っている goal)
    /// （行・文脈・goal の表示（ふつう・LaTeX））
    pub sorries: Vec<(usize, Vec<String>, (String, String))>,
    pub steps: Vec<StepTrace>,
    trace: bool,
    depth: usize,
}

impl<'a> Checker<'a> {
    fn new(env: &'a Env, trace: bool) -> Self {
        Checker {
            env,
            metas: vec![],
            sort_metas: vec![],
            fn_metas: vec![],
            pending: vec![],
            fresh: 0,
            line: 0,
            snapshot: (Ctx::default(), None),
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
            fix: None,
            alts: vec![],
            seqs: self.seq_vars(&self.snapshot.0),
        })
    }

    fn record_step(&mut self, line: usize, depth: usize, src: &str, ctx: &Ctx, goal: &Option<Formula>) {
        self.steps.push(StepTrace {
            line,
            depth,
            src: src.to_string(),
            ctx: ctx.show(),
            ctx_latex: ctx.show_latex(),
            goal: goal.as_ref().map(|g| g.to_string()),
            goal_latex: goal.as_ref().map(|g| g.to_latex()),
            hints: goal.as_ref().map(|g| self.hints(ctx, g)).unwrap_or_default(),
            terms: self.context_terms(ctx, goal),
            seqs: self.seq_vars(ctx).into_iter().filter(|x| !x.contains('\u{1}')).collect(),
        });
    }

    fn set_snapshot(&mut self, ctx: Ctx, goal: Option<Formula>) {
        crate::syntax::set_sub_seqs(self.seq_vars(&ctx));
        self.snapshot = (ctx, goal);
    }

    fn seq_vars(&self, ctx: &Ctx) -> std::collections::BTreeSet<String> {
        ctx.entries
            .iter()
            .flat_map(|e| match e {
                Entry::Var(x, s, _) => {
                    let s = self.zonk_sort(s);
                    let mut v = vec![];
                    if s.starts_with("ℕ →") {
                        v.push(x.clone());
                    }
                    // 添字 2 つ（A_{i,j}・p_{i,j}）の印
                    if crate::syntax::is_idx2_type(&s) {
                        v.push(format!("{x}\u{1}2"));
                    }
                    v
                }
                _ => vec![],
            })
            .collect()
    }

    /// 文脈に現れる式（goal が先、仮定は新しい順。定義の述語は 3 段まで展開した形も見る）
    fn context_terms(&self, ctx: &Ctx, goal: &Option<Formula>) -> Vec<String> {
        let seqs = self.seq_vars(ctx);
        let mut out: Vec<String> = Vec::new();
        let mut fs: Vec<Formula> = Vec::new();
        if let Some(g) = goal {
            let g = self.zonk_f(g);
            fs.push(self.unfold_deep(&g, 3));
            fs.push(g);
        }
        for e in ctx.entries.iter().rev() {
            match e {
                Entry::Hyp(h, f) if !h.starts_with('#') && !h.ends_with(".def") => {
                    let f = self.zonk_f(f);
                    fs.push(f.clone());
                    fs.push(self.unfold_deep(&f, 3));
                }
                Entry::Def(_, _, t) => fs.push(Formula::Atom("=".into(), vec![t.clone(), t.clone()])),
                _ => {}
            }
        }
        for f in &fs {
            collect_terms_f(f, &mut |t| {
                if out.len() < 80 && !t.has_meta() && !hidden_name(t) {
                    let s = crate::syntax::show_term_sub(t, &seqs);
                    if !out.contains(&s) {
                        out.push(s);
                    }
                }
            });
        }
        out
    }

    /// 述語の定義を、式のどの位置でも depth 段まで展開する
    fn unfold_deep(&self, f: &Formula, depth: u32) -> Formula {
        if depth == 0 {
            return f.clone();
        }
        let go = |g: &Formula| self.unfold_deep(g, depth);
        match f {
            Formula::Atom(..) => match self.unfold_head(f) {
                Some(g) => self.unfold_deep(&g, depth - 1),
                None => f.clone(),
            },
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => Formula::Imp(Box::new(go(a)), Box::new(go(b))),
            Formula::And(a, b) => Formula::And(Box::new(go(a)), Box::new(go(b))),
            Formula::Or(a, b) => Formula::Or(Box::new(go(a)), Box::new(go(b))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), t.clone(), Box::new(go(b))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), t.clone(), Box::new(go(b))),
        }
    }

    /// goal と仮定の形から、次に書けるもの（docs/language/syntax.md の早見表と同じ考え方）
    fn hints(&self, ctx: &Ctx, goal: &Formula) -> Vec<(String, String)> {
        let mut out: Vec<(String, String)> = Vec::new();
        let g = self.whnf(goal);
        // 仮定がそのまま goal なら、その名前で閉じられる
        for e in ctx.entries.iter().rev() {
            if let Entry::Hyp(h, f) = e {
                if !h.starts_with('#') && (f == goal || self.whnf(f) == g) {
                    out.push((h.clone(), format!("仮定 {h} がそのまま goal")));
                    break;
                }
            }
        }
        let hname = |x: &str| format!("h{x}");
        match &g {
            Formula::Forall(x, _, b) => match &**b {
                Formula::Imp(c, _) => out.push((format!("Fix {x} | {} : {c}", hname(x)), "goal が ∀（条件つき）".into())),
                _ => out.push((format!("Fix {x}"), "goal が ∀".into())),
            },
            Formula::Imp(a, b) if **b == Formula::Bot => out.push((format!("assume h : {a}"), "goal が ¬（⇒ ⊥）".into())),
            Formula::Imp(a, _) => out.push((format!("assume h : {a}"), "goal が ⇒".into())),
            Formula::And(..) => out.push(("根拠1, 根拠2".into(), "goal が ∧：両側を並べる".into())),
            Formula::Or(..) => {
                out.push(("choose left".into(), "goal が ∨：左を示す".into()));
                out.push(("choose right".into(), "goal が ∨：右を示す".into()));
            }
            Formula::Exists(x, _, _) => out.push((format!("choose 項"), format!("goal が ∃：{x} として何をとるか"))),
            Formula::Atom(r, _) if r == "=" => {
                out.push(("ring".into(), "式の計算で等しい".into()));
                out.push(("左辺\n  = …   by 根拠".into(), "等式の連鎖".into()));
            }
            Formula::Atom(r, _) if ["<", "≤", ">", "≥", "≠"].contains(&r.as_str()) => {
                out.push(("linarith".into(), "仮定からの一次不等式".into()));
                out.push(("左辺\n  ≤ …   by 根拠".into(), "不等式の連鎖".into()));
            }
            _ => {}
        }
        // 仮定の形
        for e in ctx.entries.iter().rev() {
            if out.len() >= 5 {
                break;
            }
            if let Entry::Hyp(h, f) = e {
                if h == "this" || h.starts_with('#') {
                    continue;
                }
                match self.whnf(f) {
                    Formula::Exists(x, _, _) => out.push((format!("Obtain {x}, h{x} : {h}"), format!("仮定 {h} が ∃：取り出す"))),
                    Formula::Or(..) => out.push((format!("cases {h}"), format!("仮定 {h} が ∨：場合分け"))),
                    Formula::And(..) => out.push((format!("{h}.left / {h}.right"), format!("仮定 {h} が ∧：片側を使う"))),
                    _ => {}
                }
            }
        }
        if !matches!(g, Formula::Bot) && out.len() < 6 {
            out.push(("by_contra h".into(), "背理法（どんな goal でも）".into()));
        }
        out
    }

    fn push(&self, ctx: &mut Ctx, e: Entry) {
        if self.trace {
            let pad = "  ".repeat(self.depth);
            let s = match &e {
                Entry::Var(x, t, _) if t.starts_with('\'') => x.clone(),
                Entry::Var(x, t, _) => format!("{x} : {t}"),
                Entry::Hyp(h, f) => format!("{h} : {f}"),
                Entry::Def(x, _, t) => format!("{x} := {t}"),
            };
            if !matches!(&e, Entry::Hyp(h, _) if h.ends_with(".def")) {
                println!("       │ {pad}    + {s}");
            }
        }
        ctx.entries.push(e);
    }

    /// 文脈の変数とその型（型推論・kernel 用）
    fn var_sorts(&self, ctx: &Ctx) -> Vec<(String, String)> {
        ctx.entries
            .iter()
            .filter_map(|e| match e {
                Entry::Var(x, s, _) | Entry::Def(x, s, _) => Some((x.clone(), self.zonk_sort(s))),
                _ => None,
            })
            .collect()
    }

    /// 証明の中で書かれた論理式の型を推論し、束縛変数の型を埋める
    fn infer_written(&mut self, ctx: &Ctx, f: &Formula) -> CResult<Formula> {
        let vs = self.var_sorts(ctx);
        match crate::sorts::infer_formula(&self.env.kernel, &vs, f) {
            Ok(f) => Ok(f),
            Err(m) => self.err(format!("型：{m}")),
        }
    }

    fn term_sort(&self, ctx: &Ctx, t: &Term) -> Option<String> {
        let vs = self.var_sorts(ctx);
        crate::sorts::term_sort(&self.env.kernel, &vs, &self.zonk_t(t))
    }

    /// 証明の中で書かれた項の λ・集合の型を埋める（expected はその項の型）
    fn annotate_term(&mut self, ctx: &Ctx, t: &Term, expected: Option<&str>) -> CResult<Term> {
        fn has_binder(t: &Term) -> bool {
            match t {
                Term::Lam(..) | Term::Set(..) => true,
                Term::App(_, a) => a.iter().any(has_binder),
                _ => false,
            }
        }
        if !has_binder(t) {
            return Ok(t.clone());
        }
        let vs = self.var_sorts(ctx);
        let e = expected.map(|e| self.zonk_sort(e)).filter(|e| !e.contains("?σ"));
        match crate::sorts::infer_term(&self.env.kernel, &vs, t, e.as_deref()) {
            Ok(t) => Ok(t),
            Err(m) => self.err(format!("型：{m}")),
        }
    }
}

// ================================================================ 宣言

pub struct Report {
    pub name: String,
    pub line: usize,
    pub is_axiom: bool,
    pub err: Option<CheckError>,
    /// 利用者の公理（kernel が数えたもの）
    pub axioms: BTreeSet<String>,
    /// 使った算術の規則と、未完成なら "sorry"
    pub oracles: BTreeSet<String>,
    /// （行・文脈・goal の表示（ふつう・LaTeX））
    pub sorries: Vec<(usize, Vec<String>, (String, String))>,
    pub steps: Vec<StepTrace>,
    /// 証明木（JSON。src/derivation.rs）
    pub tree: Option<String>,
    /// 古い書き方の警告：(行, 文, 書き換え先)
    pub warnings: Vec<(usize, String, Option<String>)>,
}

fn collect_warnings(stmts: &[crate::parser::Stmt], out: &mut Vec<(usize, String, Option<String>)>) {
    use crate::parser::StmtKind::*;
    for s in stmts {
        if let Some(w) = &s.warn {
            out.push((s.line, w.msg.clone(), w.replace.clone()));
        }
        match &s.kind {
            Fix { body, .. } | Assume { body, .. } | ByContra { body, .. } | Show { body, .. } => collect_warnings(body, out),
            Cases { left, right, .. } => {
                collect_warnings(&left.1, out);
                collect_warnings(&right.1, out);
            }
            Induction { zero, succ, .. } => {
                collect_warnings(zero, out);
                collect_warnings(&succ.3, out);
            }
            _ => {}
        }
    }
}

fn simple_err(line: usize, msg: String) -> CheckError {
    CheckError { line, msg, goal: None, ctx: vec![], ctx_latex: vec![], fix: None, alts: vec![], seqs: BTreeSet::new() }
}

/// 定理・公理の文の型を推論して、kernel に渡せる形にする
fn statement_of(env: &Env, d: &Decl, core: bool) -> Result<Statement, String> {
    let declared: Vec<(String, String)> = d
        .ctx
        .iter()
        .filter_map(|c| match c {
            CtxItem::Var(x, t) => Some((x.clone(), t.clone())),
            _ => None,
        })
        .collect();
    let mut inf = Infer::new(&env.kernel, declared.clone(), true);
    for c in &d.ctx {
        if let CtxItem::Hyp(_, f) = c {
            inf.formula(f)?;
        }
    }
    inf.formula(&d.concl)?;
    let r = inf.finish()?;
    let mut k = 0;
    let mut hyps = Vec::new();
    for c in &d.ctx {
        if let CtxItem::Hyp(h, f) = c {
            hyps.push((h.clone(), r.annotate(f, &mut k)));
        }
    }
    let concl = r.annotate(&d.concl, &mut k);
    let mut vars = declared;
    vars.extend(r.free.iter().cloned());
    Ok(Statement { name: d.name.clone(), type_params: r.type_params.clone(), vars, hyps, concl, is_axiom: d.is_axiom, core })
}

fn check_decl(env: &mut Env, d: &Decl, trace: bool, core: bool) -> Report {
    let mut report = Report {
        name: d.name.clone(),
        line: d.line,
        is_axiom: d.is_axiom,
        err: None,
        axioms: BTreeSet::new(),
        oracles: BTreeSet::new(),
        sorries: vec![],
        steps: vec![],
        tree: None,
        warnings: vec![],
    };
    collect_warnings(&d.body, &mut report.warnings);
    if env.kernel.thms.contains_key(&d.name) || env.failed.contains(&d.name) {
        report.err = Some(simple_err(
            d.line,
            format!("名前 `{}` はすでに使われている（組み込みの定理か、前に書いた定理）", d.name),
        ));
        report.is_axiom = false;
        return report;
    }
    let st = match statement_of(env, d, core) {
        Ok(x) => x,
        Err(m) => {
            env.failed.insert(d.name.clone());
            report.err = Some(simple_err(d.line, format!("型：{m}")));
            report.is_axiom = false;
            return report;
        }
    };
    if d.typedef.is_some() && !st.vars.is_empty() {
        env.failed.insert(d.name.clone());
        let vs: Vec<&str> = st.vars.iter().map(|(x, _)| x.as_str()).collect();
        report.err = Some(simple_err(
            d.line,
            format!("typedef の集合に、束縛されていない変数 {} がある（{{x : σ | φ}} の φ は x だけを使う）", vs.join(", ")),
        ));
        return report;
    }
    if d.is_axiom {
        if let Err(e) = env.kernel.add_statement(&st, None) {
            env.failed.insert(d.name.clone());
            report.err = Some(simple_err(d.line, format!("kernel：{}", e.msg)));
        }
        return report;
    }
    if trace {
        println!("\n── thm {} ──", d.name);
    }
    let mut ch = Checker::new(env, trace);
    let result = ch.check_decl(d, &st);
    crate::syntax::set_sub_seqs(BTreeSet::new());
    report.sorries = std::mem::take(&mut ch.sorries);
    report.steps = std::mem::take(&mut ch.steps);
    let proof = match result {
        Ok(p) => p,
        Err(e) => {
            env.failed.insert(d.name.clone());
            report.err = Some(e);
            return report;
        }
    };
    let added = match &d.typedef {
        // typedef：空でないことの証明を渡して、型と定数を作る
        Some(td) => match &st.concl {
            Formula::Exists(x, carrier, phi) if st.vars.is_empty() => {
                env.kernel.add_typedef(&td.name, x, carrier, phi, &proof)
            }
            _ => Err(crate::kernel::env::KError {
                line: None,
                msg: "typedef の集合に、束縛されていない変数がある（{x : σ | φ} の φ は x だけを使う）".into(),
            }),
        },
        None => env.kernel.add_statement(&st, Some(&proof)),
    };
    match added {
        Ok(deps) => {
            if d.typedef.is_none() {
                report.tree = crate::derivation::derivation(&env.kernel, &st, &proof).map(|n| n.to_json());
            }
            report.axioms = deps.axioms;
            report.oracles = deps.arith;
            if deps.sorry {
                report.oracles.insert("sorry".into());
            }
        }
        Err(e) => {
            env.failed.insert(d.name.clone());
            report.err = Some(simple_err(
                e.line.unwrap_or(d.line),
                format!("kernel が証明を受け付けなかった：{}", e.msg),
            ));
        }
    }
    report
}

/// def の引数の型を推論して kernel に登録する
fn add_def(env: &mut Env, d: &Def) -> Result<(), String> {
    let typed: Vec<(String, String)> = d.params.iter().filter(|(_, s)| s != "?").cloned().collect();
    let mut inf = Infer::new(&env.kernel, typed, true);
    match &d.term {
        None => inf.formula(&d.body)?,
        Some((r, t)) => inf.term_expect(t, r)?,
    }
    let r = inf.finish()?;
    if !r.type_params.is_empty() {
        return Err("定義の引数の型が決まらない。`def P(x : ℕ, …)` のように型を書く".into());
    }
    let mut params = Vec::new();
    for (x, s) in &d.params {
        if s != "?" {
            params.push((x.clone(), s.clone()));
            continue;
        }
        match r.free.iter().find(|(y, _)| y == x) {
            Some((_, t)) => params.push((x.clone(), t.clone())),
            None => return Err(format!("引数 `{x}` が本体で使われていないので型が決まらない。型を書く")),
        }
    }
    if let Some((v, _)) = r.free.iter().find(|(y, _)| !d.params.iter().any(|(x, _)| x == y)) {
        return Err(format!("定義の本体の `{v}` が引数にない（未定義の記号か）"));
    }
    let body = match &d.term {
        None => DefBody::Pred(r.annotate(&d.body, &mut 0)),
        Some((ty, t)) => DefBody::Term(ty.clone(), r.annotate_t(t, &mut 0)),
    };
    env.kernel.add_def(&d.name, &params, &body).map_err(|e| e.msg)
}

/// ファイルの宣言を順に検査する。def の誤りはファイル全体の誤りとして返す。
/// 報告は thm・axiom ごと（書かれた順）。
pub fn check_module(env: &mut Env, m: &Module, trace: bool, core: bool) -> Result<Vec<Report>, ParseError> {
    let mut reports = Vec::new();
    for it in &m.items {
        match it {
            Item::Def(d) => {
                // 通らない定義は報告して先へ進む（それを使う定理は、未定義の記号として通らない）
                if let Err(msg) = add_def(env, d) {
                    reports.push(Report {
                        name: d.name.clone(),
                        line: d.line,
                        is_axiom: false,
                        err: Some(simple_err(d.line, format!("定義 `{}`：{msg}", d.name))),
                        axioms: BTreeSet::new(),
                        oracles: BTreeSet::new(),
                        sorries: vec![],
                        steps: vec![],
                        tree: None,
                        warnings: vec![],
                    });
                }
            }
            Item::Decl(d) => reports.push(check_decl(env, d, trace, core)),
            Item::Broken { name, line, msg, .. } => reports.push(Report {
                name: name.clone(),
                line: *line,
                is_axiom: false,
                err: Some(simple_err(*line, format!("構文エラー：{msg}"))),
                axioms: BTreeSet::new(),
                oracles: BTreeSet::new(),
                sorries: vec![],
                steps: vec![],
                tree: None,
                warnings: vec![],
            }),
            Item::Const { name, ty, line } => {
                if let Err(e) = env.kernel.add_const(name, ty) {
                    reports.push(Report {
                        name: name.clone(),
                        line: *line,
                        is_axiom: false,
                        err: Some(simple_err(*line, format!("定数 `{name}`：{}", e.msg))),
                        axioms: BTreeSet::new(),
                        oracles: BTreeSet::new(),
                        sorries: vec![],
                        steps: vec![],
                        tree: None,
                        warnings: vec![],
                    });
                }
            }
            Item::Notation { .. } | Item::Import { .. } => {}
        }
    }
    Ok(reports)
}

/// 式の中の、変数・数でない項（外側から順に）
fn collect_terms_f(f: &Formula, k: &mut dyn FnMut(&Term)) {
    match f {
        Formula::Atom(_, ts) => ts.iter().for_each(|t| collect_terms_t(t, k)),
        Formula::Bot => {}
        Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
            collect_terms_f(a, k);
            collect_terms_f(b, k);
        }
        Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => collect_terms_f(b, k),
    }
}

fn collect_terms_t(t: &Term, k: &mut dyn FnMut(&Term)) {
    match t {
        Term::Var(_) | Term::Num(_) | Term::Meta(_) => {}
        Term::App(_, args) => {
            k(t);
            args.iter().for_each(|a| collect_terms_t(a, k));
        }
        Term::Lam(_, b) => {
            k(t);
            collect_terms_t(b, k);
        }
        Term::Set(_, f) => collect_terms_f(f, k),
    }
}

/// 内部の名前（#…・%…・?…）を含む項は、ソースに書けないので候補にしない
fn hidden_name(t: &Term) -> bool {
    let mut vs = std::collections::BTreeSet::new();
    t.vars(&mut vs);
    let bad = |x: &str| x.starts_with('#') || x.starts_with('%') || x.starts_with('?');
    vs.iter().any(|x| bad(x)) || matches!(t, Term::App(f, _) if bad(f))
}
