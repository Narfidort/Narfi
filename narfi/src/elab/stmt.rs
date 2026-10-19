//! 文（Fix・Obtain・have・連鎖など）を読み、証明項を組み立てる（仕様 §10 の対応表）。
//!
//! ブロックは「先頭の文」と「残りの文」に分けて再帰的に読む。Obtain や have のように
//! 後ろに続く文は、残りの文が作る証明を内側に包む（`ExE(…, 残り)`・`Cut(…, 残り)`）。
//! Fix や結論の根拠のように goal を閉じる文のあとには、`∴` しか書けない。

use super::{CResult, Checker, Ctx, Entry, VarKind};
use crate::kernel::Statement;
use crate::kernel::proof::Proof;
use crate::parser::{ChainStep, Choice, Decl, Stmt, StmtKind};
use crate::syntax::{Formula, Term, not};
use std::collections::BTreeSet;

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

/// 数字だけの項の型：使われた演算が意味を持つ最小の数のソート（仕様 §3.2）
fn literal_sort(t: &Term) -> &'static str {
    fn rank(t: &Term) -> u8 {
        match t {
            Term::App(f, a) => {
                let own = match f.as_str() {
                    "/" => 2,
                    "-" | "neg" | "abs" => 1,
                    _ => 0,
                };
                a.iter().map(rank).max().unwrap_or(0).max(own)
            }
            _ => 0,
        }
    }
    ["ℕ", "ℤ", "ℚ"][rank(t) as usize]
}

impl<'a> Checker<'a> {
    fn fresh_name(&self, ctx: &Ctx, x: &str) -> CResult<()> {
        if ctx.has_name(x) {
            return self.err(format!("名前 `{x}` はすでに使われている"));
        }
        if self.env.kernel.is_global(x) {
            return self.err(format!("`{x}` は定義・定数の名前なので、変数・仮定の名前には使えない"));
        }
        Ok(())
    }

    /// 定理の証明を読み、kernel に渡す証明項を返す
    pub(super) fn check_decl(&mut self, d: &Decl, st: &Statement) -> CResult<Proof> {
        let mut ctx = Ctx::default();
        for (x, s) in &st.vars {
            ctx.entries.push(Entry::Var(x.clone(), s.clone(), VarKind::Const));
        }
        for (h, f) in &st.hyps {
            ctx.entries.push(Entry::Hyp(h.clone(), f.clone()));
        }
        self.line = d.line;
        self.record_step(d.line, 0, &format!("thm {}", d.name), &ctx, &Some(st.concl.clone()));
        if d.body.is_empty() {
            self.snapshot = (ctx, Some(st.concl.clone()));
            return self.err("証明が書かれていない");
        }
        let p = self.block(ctx, &d.body, st.concl.clone(), d.line)?;
        self.solve_pending();
        self.zonk_proof(&p)
    }

    /// 定理を使ったときの型の約束を、穴が埋まった引数の型から解く
    fn solve_pending(&mut self) {
        let pending = std::mem::take(&mut self.pending);
        loop {
            let mut changed = false;
            for (vs, s, a) in &pending {
                if !self.zonk_sort(s).contains("?σ") {
                    continue;
                }
                let t = self.zonk_t(a);
                if let Some(ts) = crate::sorts::term_sort(&self.env.kernel, vs, &t) {
                    changed |= self.unify_sort(s, &ts);
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn block(&mut self, ctx: Ctx, stmts: &[Stmt], goal: Formula, parent_line: usize) -> CResult<Proof> {
        self.depth += 1;
        let r = self.seq(ctx, stmts, goal, None, parent_line);
        self.depth -= 1;
        r
    }

    /// goal を閉じた文のあと：`∴` だけが書ける
    fn after_closed(&mut self, ctx: &Ctx, rest: &[Stmt], closed: &Formula) -> CResult<()> {
        for s in rest {
            self.line = s.line;
            self.snapshot = (ctx.clone(), None);
            self.record_step(s.line, self.depth, &s.src, ctx, &None);
            match &s.kind {
                StmtKind::Therefore(f) => self.therefore(ctx, f, &Some(closed.clone()))?,
                _ => return self.err("goal はもう示し終わっている。この行は不要"),
            }
        }
        Ok(())
    }

    fn therefore(&mut self, ctx: &Ctx, f: &Formula, last: &Option<Formula>) -> CResult<()> {
        let f = self.infer_written(ctx, f)?;
        match last {
            Some(l) if self.unify(ctx, &f, l) => Ok(()),
            Some(l) => {
                let l = self.zonk_f(l);
                self.err(format!("∴ の命題が、直前に示したもの「{l}」と一致しない"))
            }
            None => self.err("∴ の前に、示し終わったものがない"),
        }
    }

    /// 書かれた仮定の型を、goal から決まるものと照合する（assume・Fix | h・Case succ）
    /// 仮定 h の中身。書かれていなければエラーにする（読む人に仮定が見えるように。直し方は示す）
    fn assumed(&mut self, ctx: &Ctx, h: &str, written: Option<&Formula>, expected: &Formula) -> CResult<Formula> {
        match written {
            None => {
                self.snapshot.0 = ctx.clone();
                let e = self.zonk_f(expected);
                let mut err = self
                    .err::<Formula>(format!(
                        "仮定 {h} の中身が書かれていない\n  help: goal から決まるのは「{e}」。`{h} : {e}` と書く（エディタでは行末で Tab）"
                    ))
                    .unwrap_err();
                err.fix = Some(format!(" : {e}"));
                Err(err)
            }
            Some(f) => {
                let f = self.infer_written(ctx, f)?;
                if self.unify(ctx, &f, expected) {
                    Ok(f)
                } else {
                    let e = self.zonk_f(expected);
                    self.err(format!("仮定の型が違う：goal から決まるのは「{e}」だが、「{f}」と書かれている"))
                }
            }
        }
    }

    fn seq(&mut self, ctx: Ctx, stmts: &[Stmt], goal: Formula, last: Option<Formula>, end_line: usize) -> CResult<Proof> {
        let Some(s) = stmts.first() else {
            self.line = end_line;
            let g = self.zonk_f(&goal);
            self.snapshot = (ctx, Some(g.clone()));
            return self.err(format!("ブロックが終わったが、goal「{g}」がまだ示されていない"));
        };
        let rest = &stmts[1..];
        self.line = s.line;
        let g = self.zonk_f(&goal);
        self.snapshot = (ctx.clone(), Some(g.clone()));
        self.record_step(s.line, self.depth, &s.src, &ctx, &Some(g.clone()));
        if self.trace {
            let pad = "  ".repeat(self.depth - 1);
            println!("  {:>4} │ {pad}{}", s.line, s.src);
            println!("       │ {pad}    ⊢ {g}");
        }
        let line = s.line;
        let at = |p: Proof| Proof::Line(line, p.b());
        let mut ctx = ctx;
        match &s.kind {
            // ---------------------------------------- goal を閉じる文
            StmtKind::Fix { vars, hyp, body } => {
                let mut c2 = ctx.clone();
                let mut cur = g.clone();
                let mut binders = Vec::new();
                for (x, ty) in vars {
                    match self.whnf(&cur) {
                        Formula::Forall(y, t, b) => {
                            if let Some(ty) = ty {
                                if !self.unify_sort(ty, &t) {
                                    let t = self.zonk_sort(&t);
                                    return self.err(format!("型が違う：goal の変数は {t} だが、{ty} と書かれている"));
                                }
                            }
                            self.fresh_name(&c2, x)?;
                            let sort = self.zonk_sort(&t);
                            self.push(&mut c2, Entry::Var(x.clone(), sort.clone(), VarKind::Fixed));
                            cur = b.subst(&y, &Term::Var(x.clone()));
                            binders.push((x.clone(), sort));
                        }
                        other => return self.err(format!("Fix できない：goal「{other}」は ∀ の形ではない")),
                    }
                }
                let mut hyp_info = None;
                if let Some((h, f)) = hyp {
                    match self.whnf(&cur) {
                        Formula::Imp(a, b) => {
                            let a = self.assumed(&c2, h, f.as_ref(), &a)?;
                            self.fresh_name(&c2, h)?;
                            self.push(&mut c2, Entry::Hyp(h.clone(), a.clone()));
                            cur = *b;
                            hyp_info = Some((h.clone(), a));
                        }
                        other => {
                            return self.err(format!("`| {h}` は使えない：goal「{other}」は「… → …」の形ではない"));
                        }
                    }
                }
                let mut p = self.block(c2, body, cur, line)?;
                if let Some((h, a)) = hyp_info {
                    p = Proof::ImpI { h, phi: a, body: p.b() };
                }
                for (x, sort) in binders.into_iter().rev() {
                    p = Proof::AllI { x, sort, body: p.b() };
                }
                self.after_closed(&ctx, rest, &g)?;
                Ok(at(p))
            }
            StmtKind::Assume { name, ty, body } => match self.whnf(&g) {
                Formula::Imp(a, b) => {
                    let mut c2 = ctx.clone();
                    let a = self.assumed(&c2, name, ty.as_ref(), &a)?;
                    self.fresh_name(&c2, name)?;
                    self.push(&mut c2, Entry::Hyp(name.clone(), a.clone()));
                    let p = self.block(c2, body, *b, line)?;
                    self.after_closed(&ctx, rest, &g)?;
                    Ok(at(Proof::ImpI { h: name.clone(), phi: a, body: p.b() }))
                }
                other => self.err(format!("assume できない：goal「{other}」は「… → …」の形ではない")),
            },
            StmtKind::ByContra { name, body } => {
                if matches!(self.whnf(&g), Formula::Imp(_, b) if *b == Formula::Bot) {
                    return self.err("goal が否定（¬φ）なので、by_contra ではなく assume を使う");
                }
                let mut c2 = ctx.clone();
                self.fresh_name(&c2, name)?;
                self.push(&mut c2, Entry::Hyp(name.clone(), not(g.clone())));
                let p = self.block(c2, body, Formula::Bot, line)?;
                self.after_closed(&ctx, rest, &g)?;
                Ok(at(Proof::Raa { h: name.clone(), phi: g, body: p.b() }))
            }
            StmtKind::Contradiction(a, b) => {
                let (fa, pa) = self.resolve(&ctx, a)?;
                let (fb, pb) = self.resolve(&ctx, b)?;
                let bot = if self.unify(&ctx, &fb, &not(fa.clone())) {
                    Proof::ImpE(pb.b(), pa.b())
                } else if self.unify(&ctx, &fa, &not(fb.clone())) {
                    Proof::ImpE(pa.b(), pb.b())
                } else {
                    let (fa, fb) = (self.norm(&ctx, &fa), self.norm(&ctx, &fb));
                    return self.err(format!("`{a}` : {fa} と `{b}` : {fb} は互いの否定になっていない"));
                };
                self.after_closed(&ctx, rest, &g)?;
                Ok(at(Proof::BotE(g, bot.b())))
            }
            StmtKind::Cases { hyp, left, right } => {
                let (f, pf) = self.resolve(&ctx, hyp)?;
                match self.whnf(&self.norm(&ctx, &f)) {
                    Formula::Or(a, b) => {
                        let mut qs = Vec::new();
                        for ((h, body), side) in [(left, *a), (right, *b)] {
                            let mut c2 = ctx.clone();
                            self.fresh_name(&c2, h)?;
                            self.push(&mut c2, Entry::Hyp(h.clone(), side));
                            qs.push(self.block(c2, body, g.clone(), line)?);
                        }
                        self.after_closed(&ctx, rest, &g)?;
                        let q2 = qs.pop().unwrap();
                        let q1 = qs.pop().unwrap();
                        Ok(at(Proof::OrE { p: pf.b(), h1: left.0.clone(), q1: q1.b(), h2: right.0.clone(), q2: q2.b() }))
                    }
                    other => self.err(format!("cases できない：`{hyp}` は「{other}」で ∨ の形ではない")),
                }
            }
            StmtKind::Induction { var, zero, succ, succ_line } => {
                self.fresh += 1;
                let x = format!("#ind{}", self.fresh);
                let (pv, pred, on_var) = if ctx.is_term_var(var) {
                    let s = self.var_sorts(&ctx).into_iter().rev().find(|(y, _)| y == var).map(|(_, s)| s);
                    if s.as_deref() != Some("ℕ") {
                        return self.err(format!("induction は ℕ の変数にしか使えない（`{var}` の型は {}）", s.unwrap_or("?".into())));
                    }
                    (var.clone(), g.clone(), true)
                } else {
                    match self.whnf(&g) {
                        Formula::Forall(y, s, b) => {
                            if !self.unify_sort(&s, "ℕ") {
                                return self.err(format!("induction は ℕ についての ∀ にしか使えない（{s}）"));
                            }
                            (y, *b, false)
                        }
                        other => {
                            return self.err(format!(
                                "induction できない：`{var}` は文脈になく、goal「{other}」も ∀ ではない"
                            ));
                        }
                    }
                };
                let base = self.block(ctx.clone(), zero, pred.subst(&pv, &Term::Num(0)), line)?;
                let (k, ih, ih_ty, body) = succ;
                let mut c2 = ctx.clone();
                self.line = *succ_line;
                self.fresh_name(&c2, k)?;
                self.push(&mut c2, Entry::Var(k.clone(), "ℕ".into(), VarKind::Fixed));
                let ih_f = pred.subst(&pv, &Term::Var(k.clone()));
                let ih_f = self.assumed(&c2, ih, ih_ty.as_ref(), &ih_f)?;
                self.fresh_name(&c2, ih)?;
                self.push(&mut c2, Entry::Hyp(ih.clone(), ih_f));
                let sg = pred.subst(&pv, &Term::App("S".into(), vec![Term::Var(k.clone())]));
                self.record_step(*succ_line, self.depth + 1, &format!("Case succ {k}, {ih}"), &c2, &Some(sg.clone()));
                let step = self.block(c2, body, sg, *succ_line)?;
                let ind = Proof::Ind {
                    x: x.clone(),
                    phi: pred.subst(&pv, &Term::Var(x)),
                    base: base.b(),
                    k: k.clone(),
                    ih: ih.clone(),
                    step: step.b(),
                };
                self.after_closed(&ctx, rest, &g)?;
                Ok(at(if on_var { Proof::AllE(ind.b(), Term::Var(var.clone())) } else { ind }))
            }
            StmtKind::Close(j) => {
                let p = self.check_just(&ctx, j, &g)?;
                self.after_closed(&ctx, rest, &g)?;
                Ok(at(p))
            }
            StmtKind::Chain { start, steps } if rest.is_empty() => {
                let (result, cp) = self.chain(&ctx, start, steps)?;
                self.line = line;
                if self.unify(&ctx, &result, &g) {
                    return Ok(at(cp));
                }
                match self.linarith(&ctx, vec![(result.clone(), cp)], &g) {
                    Ok(p) => Ok(at(p)),
                    Err(_) => self.err(format!("連鎖の結論「{result}」が goal「{g}」と一致しない")),
                }
            }
            // ---------------------------------------- 後ろに続く文
            StmtKind::Chain { start, steps } => {
                let (result, cp) = self.chain(&ctx, start, steps)?;
                self.push(&mut ctx, Entry::Hyp("this".into(), result.clone()));
                let r = self.seq(ctx, rest, goal, Some(result.clone()), line)?;
                Ok(at(Proof::Cut { h: "this".into(), phi: result, p: cp.b(), body: r.b() }))
            }
            StmtKind::Therefore(f) => {
                self.therefore(&ctx, f, &last)?;
                self.seq(ctx, rest, goal, last, line)
            }
            StmtKind::Obtain { var, deps, hyps, just } => {
                if just.len() != 1 {
                    return self.err("Obtain の根拠は1つ");
                }
                let (f, pf) = self.infer(&ctx, &just[0])?;
                let f = self.norm(&ctx, &f);
                if f.has_meta() {
                    return self.err(format!("根拠の引数が足りず、命題が決まらない：{f}"));
                }
                let Formula::Exists(y, ty, body) = self.whnf(&f) else {
                    return self.err(format!("Obtain できない：根拠が示すのは ∃ ではなく「{f}」"));
                };
                self.fresh_name(&ctx, var)?;
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
                let sort = self.zonk_sort(&ty);
                self.push(&mut ctx, Entry::Var(var.clone(), sort, VarKind::Obtained));
                let body = body.subst(&y, &Term::Var(var.clone()));
                let Some(parts) = self.split_and_w(&body, hyps.len()) else {
                    return self.err(format!("「{body}」を {} 個の ∧ に分けられない", hyps.len()));
                };
                for (h, p) in hyps.iter().zip(&parts) {
                    self.fresh_name(&ctx, h)?;
                    self.push(&mut ctx, Entry::Hyp(h.clone(), p.clone()));
                }
                let r = self.seq(ctx, rest, goal, Some(body), line)?;
                if hyps.len() == 1 {
                    return Ok(at(Proof::ExE { p: pf.b(), x: var.clone(), h: hyps[0].clone(), body: r.b() }));
                }
                // ∃ の中身を1つの仮定で受け、∧ を分けて h₁, h₂, … に名前をつける
                let inner = format!("#{var}");
                let mut body_p = r;
                for (i, (h, phi)) in hyps.iter().zip(&parts).enumerate().rev() {
                    let mut proj = Proof::Hyp(inner.clone());
                    for _ in 0..i {
                        proj = Proof::AndE { right: true, p: proj.b() };
                    }
                    if i + 1 < hyps.len() {
                        proj = Proof::AndE { right: false, p: proj.b() };
                    }
                    body_p = Proof::Cut { h: h.clone(), phi: phi.clone(), p: proj.b(), body: body_p.b() };
                }
                Ok(at(Proof::ExE { p: pf.b(), x: var.clone(), h: inner, body: body_p.b() }))
            }
            StmtKind::Have { name, ty, just } => {
                let ty = self.infer_written(&ctx, ty)?;
                let p = self.check_just(&ctx, just, &ty)?;
                self.fresh_name(&ctx, name)?;
                self.push(&mut ctx, Entry::Hyp(name.clone(), ty.clone()));
                let r = self.seq(ctx, rest, goal, Some(ty.clone()), line)?;
                Ok(at(Proof::Cut { h: name.clone(), phi: ty, p: p.b(), body: r.b() }))
            }
            StmtKind::Suffices { ty, just } => {
                let ty = self.infer_written(&ctx, ty)?;
                let need = Formula::Imp(Box::new(ty.clone()), Box::new(g.clone()));
                let p = self.check_just(&ctx, just, &need)?;
                let r = self.seq(ctx, rest, ty, last, line)?;
                Ok(at(Proof::ImpE(p.b(), r.b())))
            }
            StmtKind::Choose { choice, just } => {
                let mut witness: Option<Term> = None;
                let (next, other) = match (choice, self.whnf(&g)) {
                    (Choice::Term(t), Formula::Exists(y, s, b)) => {
                        self.check_term_scope(&ctx, t)?;
                        let t = &self.annotate_term(&ctx, t, Some(&s))?;
                        witness = Some(t.clone());
                        if let Some(ts) = self.term_sort(&ctx, t) {
                            if !self.unify_sort(&s, &ts) {
                                return self.err(format!("型が違う：`{t}` は {ts} だが、{s} の項を選ぶ必要がある"));
                            }
                        }
                        (b.subst(&y, t), None)
                    }
                    (Choice::Left, Formula::Or(a, b)) => (*a, Some(*b)),
                    (Choice::Right, Formula::Or(a, b)) => (*b, Some(*a)),
                    (Choice::Term(_), other) => {
                        return self.err(format!("choose できない：goal「{other}」は ∃ の形ではない"));
                    }
                    (_, other) => {
                        return self.err(format!("choose left/right できない：goal「{other}」は ∨ の形ではない"));
                    }
                };
                let (goal2, pj) = match just {
                    None => (next, None),
                    // choose t, j：範囲付き ∃ の条件 t > 0 などを j で示す
                    Some(j) => match self.whnf(&next) {
                        Formula::And(a, b) => {
                            let pj = self.check_just(&ctx, j, &a)?;
                            (*b, Some(pj))
                        }
                        other => {
                            return self.err(format!("`choose t, 根拠` は条件付きの ∃ にだけ使える（「{other}」）"));
                        }
                    },
                };
                let r = self.seq(ctx, rest, goal2, last, line)?;
                let inner = match pj {
                    Some(pj) => Proof::AndI(pj.b(), r.b()),
                    None => r,
                };
                Ok(at(match (choice, other) {
                    (Choice::Term(_), _) => Proof::ExI { target: g, witness: witness.unwrap(), p: inner.b() },
                    (Choice::Left, Some(o)) => Proof::OrI { right: false, other: o, p: inner.b() },
                    (_, Some(o)) => Proof::OrI { right: true, other: o, p: inner.b() },
                    _ => unreachable!(),
                }))
            }
            StmtKind::Let { name, term } => {
                self.check_term_scope(&ctx, term)?;
                let term = &self.annotate_term(&ctx, term, None)?;
                self.fresh_name(&ctx, name)?;
                let sort = self.term_sort(&ctx, term).unwrap_or_else(|| literal_sort(term).to_string());
                self.push(&mut ctx, Entry::Def(name.clone(), sort.clone(), term.clone()));
                let def = Formula::Atom("=".into(), vec![Term::Var(name.clone()), term.clone()]);
                ctx.entries.push(Entry::Hyp(format!("{name}.def"), def.clone()));
                let r = self.seq(ctx, rest, goal, last, line)?;
                let body = Proof::Cut { h: format!("{name}.def"), phi: def, p: Proof::Refl(term.clone()).b(), body: r.b() };
                Ok(at(Proof::Let { x: name.clone(), sort, t: term.clone(), body: body.b() }))
            }
            StmtKind::Unfold { names, at: hs } => {
                for n in names {
                    if !self.env.kernel.defs.contains_key(n) {
                        return self.err(format!("`{n}` は def で定義された名前ではない"));
                    }
                }
                // 定義の展開は kernel の δ で同一視されるので、証明項は変わらない
                if hs.is_empty() {
                    let g2 = self.unfold_named(&g, names);
                    if g2 == g {
                        return self.err(format!("goal「{g}」に {} は現れない", names.join(", ")));
                    }
                    return self.seq(ctx, rest, g2, last, line);
                }
                for h in hs {
                    let Some(k) = ctx.entries.iter().rposition(|e| matches!(e, Entry::Hyp(x, _) if x == h)) else {
                        return self.err(format!("仮定 `{h}` が文脈にない"));
                    };
                    let Entry::Hyp(_, f) = &ctx.entries[k] else { unreachable!() };
                    let f2 = self.unfold_named(f, names);
                    if f2 == *f {
                        return self.err(format!("`{h}` : {f} に {} は現れない", names.join(", ")));
                    }
                    ctx.entries[k] = Entry::Hyp(h.clone(), f2);
                }
                self.seq(ctx, rest, goal, last, line)
            }
        }
    }

    // ------------------------------------------------ 連鎖

    fn chain(&mut self, ctx: &Ctx, start: &Term, steps: &[ChainStep]) -> CResult<(Formula, Proof)> {
        self.check_term_scope(ctx, start)?;
        let mut cur = start.clone();
        let mut acc: Option<String> = None;
        let mut proof: Option<Proof> = None;
        for st in steps {
            self.line = st.line;
            let f = Formula::Atom(st.rel.clone(), vec![cur.clone(), st.term.clone()]);
            self.record_step(st.line, self.depth + 1, &format!("{} {} by ...", st.rel, st.term), ctx, &Some(f.clone()));
            self.check_term_scope(ctx, &st.term)?;
            let p = Proof::Line(st.line, self.chain_step(ctx, &st.just, &f)?.b());
            acc = Some(match compose(acc.as_deref(), &st.rel) {
                Some(r) => r,
                None => return self.err("連鎖の中で不等号の向きが混ざっている"),
            });
            proof = Some(match proof {
                None => p,
                Some(q) => Proof::Trans(q.b(), p.b()),
            });
            cur = st.term.clone();
        }
        let proof = proof.unwrap_or_else(|| Proof::Refl(start.clone()));
        Ok((Formula::Atom(acc.unwrap_or_else(|| "=".into()), vec![start.clone(), cur]), proof))
    }

    /// 連鎖の1段。根拠がそのまま当てはまらなければ、根拠の命題を事実として linarith で補う。
    fn chain_step(&mut self, ctx: &Ctx, j: &[Term], f: &Formula) -> CResult<Proof> {
        match self.check_just(ctx, j, f) {
            Ok(p) => Ok(p),
            Err(e) => {
                let mut facts = Vec::new();
                for p in j {
                    match self.infer(ctx, p) {
                        Ok(x) => facts.push(x),
                        Err(_) => return Err(e),
                    }
                }
                self.linarith(ctx, facts, f).map_err(|_| e)
            }
        }
    }
}
