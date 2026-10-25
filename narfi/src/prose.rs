//! Narfi の AST から「自然な日本語の証明（レポート・板書用）」「LaTeX ソース」「日本語シュガー Narfi」を生成する。

use crate::elab::StepTrace;
use crate::parser::{Choice, CtxItem, Decl, Item, Just, Stmt, StmtKind};
use crate::syntax::{Formula, Term, ident_to_latex, rel_to_latex};

#[derive(Debug, Clone)]
pub struct ProseBlock {
    pub depth: usize,
    /// Markdown + KaTeX ($...$ / $$...$$) 形式の日本語文
    pub text: String,
}

fn just_to_latex(j: &Just) -> String {
    let lc = crate::locale::current();
    let word = |k: &str| format!("\\text{{{}}}", lc.t(k, &[]));
    // 訳名のある定理は訳名で書く（和の線形性(a, b)）
    let named = |f: &str, args: &[Term]| -> Option<String> {
        let n = crate::syntax::display_name(f, lc.name)?;
        let a: Vec<String> = args.iter().map(|x| x.to_latex()).collect();
        Some(if a.is_empty() { format!("\\text{{{n}}}") } else { format!("\\text{{{n}}}({})", a.join(", ")) })
    };
    j.iter()
        .map(|t| match t {
            Term::Var(s) if s == "ring" => word("just_ring"),
            Term::Var(s) if s == "linarith" => word("just_linarith"),
            Term::Var(s) if s == "refl" => word("just_refl"),
            Term::Var(s) if s == "decide" => word("just_decide"),
            Term::Var(s) if s == "sorry" => word("just_sorry"),
            Term::Var(f) => named(f, &[]).unwrap_or_else(|| t.to_latex()),
            Term::App(f, args) => named(f, args).unwrap_or_else(|| t.to_latex()),
            _ => t.to_latex(),
        })
        .collect::<Vec<_>>()
        .join(",\\ ")
}

fn find_hyp_formula_latex(
    steps: &[StepTrace],
    after_line: usize,
    hyp_name: &str,
) -> Option<String> {
    let prefix = format!("{hyp_name} : ");
    let prefix_l = format!("{} : ", ident_to_latex(hyp_name));
    for st in steps {
        if st.line >= after_line {
            for (raw, lat) in st.ctx.iter().zip(st.ctx_latex.iter()) {
                if raw.starts_with(&prefix) {
                    if let Some(rest) = lat.strip_prefix(&prefix_l) {
                        return Some(rest.to_string());
                    }
                }
            }
        }
    }
    None
}

/// `x ∈ ℝ` / `a : ℕ → ℝ` の右側（関数型は ∈ ではなく : で書く）
fn sort_decl_latex(t: &str) -> String {
    if t.contains('→') {
        let parts: Vec<String> = t
            .split(' ')
            .map(|w| match w {
                "→" => "\\to".to_string(),
                "×" => "\\times".to_string(),
                _ => ident_to_latex(w),
            })
            .collect();
        format!(": {}", parts.join(" "))
    } else {
        format!("\\in {}", ident_to_latex(t))
    }
}

/// 長い数式を、括弧の外の ` + `・` - `・` = `・関係の記号の手前で折る（印刷・Prose で右にはみ出さないように）。
/// 1 行がおよそ width 文字（LaTeX のソースの文字数）を超えたら、次の候補で折る
pub fn break_math(s: &str, width: usize) -> Vec<String> {
    const OPS: [&str; 14] = [" + ", " - ", " = ", " \\leq ", " \\geq ", " \\neq ", " < ", " > ", " \\cup ", " \\cap ", " \\setminus ", " \\wedge ", " \\vee ", " \\Rightarrow "];
    let b = s.as_bytes();
    let mut depth = 0i32;
    let mut pieces: Vec<String> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < b.len() {
        if s[i..].starts_with("\\left") || s[i..].starts_with("\\begin") {
            depth += 1;
            i += 5;
            continue;
        }
        if s[i..].starts_with("\\right") || s[i..].starts_with("\\end") {
            depth -= 1;
            i += 4;
            continue;
        }
        match b[i] {
            b'{' => depth += 1,
            b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && s[start..i].chars().count() >= width {
            if let Some(op) = OPS.iter().find(|op| s[i..].starts_with(**op)) {
                pieces.push(s[start..i].trim().to_string());
                start = i + 1; // 先頭の空白は落とし、記号から次の行を始める
                i += op.len();
                continue;
            }
        }
        i += s[i..].chars().next().map_or(1, |c| c.len_utf8());
    }
    pieces.push(s[start..].trim().to_string());
    pieces
}

/// 文中の長い数式 $…$ は、\left( \right) をふつうの括弧にする（\left…\right の中では LaTeX が行を折れず、右にはみ出す）
pub fn relax_long_inline(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find('$') {
        out.push_str(&rest[..i]);
        let after = &rest[i..];
        if after.starts_with("$$") {
            // 別行の数式はそのまま
            match after[2..].find("$$") {
                Some(j) => {
                    out.push_str(&after[..j + 4]);
                    rest = &after[j + 4..];
                }
                None => {
                    out.push_str(after);
                    rest = "";
                }
            }
            continue;
        }
        match after[1..].find('$') {
            Some(j) => {
                let inner = &after[1..j + 1];
                if inner.chars().count() > 120 {
                    out.push('$');
                    out.push_str(&inner.replace("\\left(", "(").replace("\\right)", ")"));
                    out.push('$');
                } else {
                    out.push_str(&after[..j + 2]);
                }
                rest = &after[j + 2..];
            }
            None => {
                out.push_str(after);
                rest = "";
            }
        }
    }
    out.push_str(rest);
    out
}

/// aligned の行にする：最初の行はそのまま、続きの行は字下げして書く
fn aligned_rows(first_prefix: &str, expr: &str, cont_prefix: &str, width: usize) -> Vec<String> {
    let ps = break_math(expr, width);
    ps.iter()
        .enumerate()
        .map(|(k, p)| if k == 0 { format!("{first_prefix}{p}") } else { format!("{cont_prefix}{p}") })
        .collect()
}

pub fn decl_header_latex(d: &Decl) -> String {
    crate::syntax::with_sub_seqs(&crate::api::decl_seqs(d), || decl_header_latex_in(d))
}

fn decl_header_latex_in(d: &Decl) -> String {
    let mut parts = Vec::new();
    for c in &d.ctx {
        match c {
            CtxItem::Var(x, t) => {
                parts.push(format!("{} {}", ident_to_latex(x), sort_decl_latex(t)))
            }
            CtxItem::Hyp(h, f) => parts.push(format!("{} : {}", ident_to_latex(h), f.to_latex())),
        }
    }
    if parts.is_empty() {
        format!("\\vdash {}", d.concl.to_latex())
    } else if parts.len() == 1 {
        format!("{} \\;\\vdash\\; {}", parts[0], d.concl.to_latex())
    } else {
        let mut lines = Vec::new();
        for (i, p) in parts.iter().enumerate() {
            let tail = if i + 1 == parts.len() { "" } else { "," };
            let mut rows = aligned_rows("&", p, "&\\qquad ", 90);
            if let Some(last) = rows.last_mut() {
                last.push_str(tail);
            }
            lines.extend(rows);
        }
        lines.extend(aligned_rows("&\\quad\\vdash ", &d.concl.to_latex(), "&\\qquad\\quad ", 90));
        format!("\\begin{{aligned}}\n{}\n\\end{{aligned}}", lines.join(" \\\\\n"))
    }
}

/// 宣言の証明を、いまのロケール（既定は日本語。locale::set_current）の文章にする
pub fn decl_to_japanese_prose(d: &Decl, steps: &[StepTrace]) -> Vec<ProseBlock> {
    decl_to_prose(d, steps, crate::locale::current())
}

/// 宣言の証明を、ロケール（ja・en）の文章にする。文の型紙は src/locale/*.txt の [prose]
pub fn decl_to_prose(d: &Decl, steps: &[StepTrace], lc: &crate::locale::Locale) -> Vec<ProseBlock> {
    crate::syntax::with_sub_seqs(&crate::api::decl_seqs(d), || decl_to_prose_in(d, steps, lc))
}

fn decl_to_prose_in(d: &Decl, steps: &[StepTrace], lc: &crate::locale::Locale) -> Vec<ProseBlock> {
    let mut out = Vec::new();
    let il = |x: &str| ident_to_latex(x);
    if d.generated {
        out.push(ProseBlock { depth: 0, text: lc.t("decl_generated", &[("name", &d.name), ("f", &d.concl.to_latex())]) });
        return out;
    }
    if d.is_axiom {
        out.push(ProseBlock { depth: 0, text: lc.t("decl_axiom", &[("name", &d.name), ("f", &decl_header_latex(d))]) });
        return out;
    }
    let mut hyp_items = Vec::new();
    for c in &d.ctx {
        match c {
            CtxItem::Var(x, t) if t.contains('→') => {
                hyp_items.push(lc.t("ctx_fun", &[("x", &format!("{} {}", il(x), sort_decl_latex(t)))]))
            }
            CtxItem::Var(x, t) => hyp_items.push(lc.t("ctx_var", &[("x", &format!("{} {}", il(x), sort_decl_latex(t)))])),
            CtxItem::Hyp(h, f) => hyp_items.push(lc.t("ctx_hyp", &[("h", &il(h)), ("f", &f.to_latex())])),
        }
    }
    if !hyp_items.is_empty() {
        out.push(ProseBlock { depth: 0, text: lc.t("premises", &[]) });
        for item in hyp_items {
            out.push(ProseBlock { depth: 1, text: item });
        }
    }
    out.push(ProseBlock { depth: 0, text: lc.t("goal", &[("f", &d.concl.to_latex())]) });
    stmts_to_prose(&d.body, steps, 0, &mut out, lc);
    out
}

fn stmts_to_prose(stmts: &[Stmt], steps: &[StepTrace], depth: usize, out: &mut Vec<ProseBlock>, lc: &crate::locale::Locale) {
    let il = |x: &str| ident_to_latex(x);
    for s in stmts {
        match &s.kind {
            StmtKind::Fix { vars, hyp, body } => {
                let vs: Vec<String> = vars
                    .iter()
                    .map(|(x, ty)| match ty {
                        Some(t) if t != "?" => format!("{} \\in {}", il(x), il(t)),
                        _ => il(x),
                    })
                    .collect();
                let vs_str = vs.join(",\\ ");
                let text = match hyp {
                    Some((h, f)) => {
                        let fl = f.as_ref().map(|f| f.to_latex()).or_else(|| find_hyp_formula_latex(steps, s.line, h));
                        match fl {
                            Some(fl) => lc.t("fix_hyp", &[("f", &fl), ("x", &vs_str), ("h", &il(h))]),
                            None => lc.t("fix_hyp_unknown", &[("x", &vs_str), ("h", &il(h))]),
                        }
                    }
                    None => lc.t("fix", &[("x", &vs_str)]),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out, lc);
            }
            StmtKind::Assume { name, ty, body } => {
                let fl = ty.as_ref().map(|f| f.to_latex()).or_else(|| find_hyp_formula_latex(steps, s.line, name));
                let text = match fl {
                    Some(f) => lc.t("assume", &[("f", &f), ("h", &il(name))]),
                    None => lc.t("assume_unknown", &[("h", &il(name))]),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out, lc);
            }
            StmtKind::ByContra { name, body } => {
                let text = match find_hyp_formula_latex(steps, s.line, name) {
                    Some(f) => lc.t("by_contra", &[("f", &f), ("h", &il(name))]),
                    None => lc.t("by_contra_unknown", &[("h", &il(name))]),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out, lc);
            }
            StmtKind::Obtain { var, deps, hyps, just, .. } => {
                let dep_note = match deps {
                    Some(ds) if !ds.is_empty() => {
                        let dl: Vec<String> = ds.iter().map(|d| il(d)).collect();
                        lc.t("obtain_dep", &[("d", &dl.join(", "))])
                    }
                    _ => String::new(),
                };
                let h_descs: Vec<String> = hyps
                    .iter()
                    .map(|h| match find_hyp_formula_latex(steps, s.line + 1, h) {
                        Some(fl) => lc.t("obtain_hyp", &[("f", &fl), ("h", &il(h))]),
                        None => lc.t("obtain_hyp_unknown", &[("h", &il(h))]),
                    })
                    .collect();
                let text = lc.t(
                    "obtain",
                    &[("j", &just_to_latex(just)), ("hs", &h_descs.join(&lc.t("and", &[]))), ("dep", &dep_note), ("x", &il(var))],
                );
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Let { name, term } => {
                out.push(ProseBlock { depth, text: lc.t("let", &[("x", &il(name)), ("t", &term.to_latex())]) });
            }
            StmtKind::Choose { choice, just } => {
                let text = match (choice, just) {
                    (Choice::Term(t), Some(j)) => lc.t("choose_cond", &[("t", &t.to_latex()), ("j", &just_to_latex(j))]),
                    (Choice::Term(t), None) => lc.t("choose", &[("t", &t.to_latex())]),
                    (Choice::Left, _) => lc.t("choose_left", &[]),
                    (Choice::Right, _) => lc.t("choose_right", &[]),
                };
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Cases { hyp, left, right } => {
                out.push(ProseBlock { depth, text: lc.t("cases", &[("h", &il(hyp))]) });
                for (n, (h, body)) in [("1", left), ("2", right)] {
                    let text = match find_hyp_formula_latex(steps, s.line, h) {
                        Some(f) => lc.t("case", &[("n", n), ("f", &f), ("h", &il(h))]),
                        None => lc.t("case_unknown", &[("n", n), ("h", &il(h))]),
                    };
                    out.push(ProseBlock { depth: depth + 1, text });
                    stmts_to_prose(body, steps, depth + 2, out, lc);
                }
            }
            StmtKind::Induction { var, zero, succ, .. } => {
                let vl = il(var);
                out.push(ProseBlock { depth, text: lc.t("induction", &[("n", &vl)]) });
                out.push(ProseBlock { depth: depth + 1, text: lc.t("induction_zero", &[("n", &vl)]) });
                stmts_to_prose(zero, steps, depth + 2, out, lc);
                let (k, ih, ih_ty, body) = succ;
                let (kl, ihl) = (il(k), il(ih));
                let ihf = ih_ty.as_ref().map(|f| f.to_latex()).or_else(|| find_hyp_formula_latex(steps, s.line, ih));
                let ih_str = match ihf {
                    Some(f) => lc.t("induction_ih", &[("h", &ihl), ("f", &f)]),
                    None => lc.t("induction_ih_unknown", &[("h", &ihl)]),
                };
                out.push(ProseBlock { depth: depth + 1, text: lc.t("induction_succ", &[("n", &vl), ("k", &kl), ("ih", &ih_str)]) });
                stmts_to_prose(body, steps, depth + 2, out, lc);
            }
            StmtKind::Therefore(f) => {
                out.push(ProseBlock { depth, text: lc.t("therefore", &[("f", &f.to_latex())]) });
            }
            StmtKind::Show { name, ty, just, body } => {
                let label = name.as_ref().map(|h| lc.t("label", &[("h", &il(h))])).unwrap_or_default();
                if !body.is_empty() {
                    out.push(ProseBlock { depth, text: lc.t("show_block", &[("f", &ty.to_latex()), ("label", &label)]) });
                    stmts_to_prose(body, steps, depth + 1, out, lc);
                } else {
                    let text = match just {
                        Some(j) => lc.t("show", &[("j", &just_to_latex(j)), ("f", &ty.to_latex()), ("label", &label)]),
                        None => lc.t("show_unjustified", &[("f", &ty.to_latex()), ("label", &label)]),
                    };
                    out.push(ProseBlock { depth, text });
                }
            }
            StmtKind::Close(j) => {
                let text = match j.as_slice() {
                    [Term::Var(s)] if s == "sorry" => lc.t("sorry", &[]),
                    [Term::Var(s)] if s == "refl" => lc.t("close_refl", &[]),
                    [Term::Var(s)] if s == "ring" => lc.t("close_ring", &[]),
                    [Term::Var(s)] if s == "linarith" => lc.t("close_linarith", &[]),
                    [Term::Var(s)] if s == "decide" => lc.t("close_decide", &[]),
                    _ => lc.t("close", &[("j", &just_to_latex(j))]),
                };
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Chain { start, steps: csteps } => {
                let mut lines = Vec::new();
                for (idx, st) in csteps.iter().enumerate() {
                    let lhs = if idx == 0 { start.to_latex() } else { String::new() };
                    let rel = rel_to_latex(&st.rel);
                    let rhs = st.term.to_latex();
                    let j = just_to_latex(&st.just);
                    // 長い式は折る。根拠の注は最後の行の右に付ける
                    let lhs_rows = if lhs.is_empty() { vec![String::new()] } else { break_math(&lhs, 70) };
                    let (head, last_l) = lhs_rows.split_at(lhs_rows.len() - 1);
                    for h in head {
                        lines.push(format!("{h} &"));
                    }
                    let mut rows = aligned_rows(&format!("{} &{rel} ", last_l[0]), &rhs, "&\\quad ", 70);
                    let last_len = rows.last().map_or(0, |r| r.chars().count());
                    if last_len + j.chars().count() <= 90 {
                        // 短ければ、根拠の注は最後の行の右に付ける
                        if let Some(last) = rows.last_mut() {
                            last.push_str(&format!(" && \\left(\\because {j}\\right)"));
                        }
                        lines.extend(rows);
                    } else {
                        // 長ければ、次の行に字下げして書く（長い根拠はそこでも折る）
                        lines.extend(rows);
                        lines.extend(aligned_rows("&\\qquad \\left(\\because ", &format!("{j}\\right)"), "&\\qquad\\quad ", 80));
                    }
                }
                let math = format!("$$\\begin{{aligned}}\n{}\n\\end{{aligned}}$$", lines.join(" \\\\\n"));
                out.push(ProseBlock { depth, text: math });
            }
        }
    }
}

/// LaTeX の文書全体（LuaLaTeX + ltjsarticle）。title が空なら表題をつけない。
pub fn latex_document(title: &str, items: &[(&Decl, &[StepTrace])]) -> String {
    crate::locale::reset_variation();
    let mut out = String::new();
    out.push_str("\\documentclass[a4paper,11pt]{ltjsarticle}\n");
    out.push_str("\\usepackage{amsmath,amssymb,amsthm}\n");
    out.push_str("\\usepackage[margin=15mm]{geometry}\n");
    out.push_str("\\newtheorem{theorem}{定理}\n");
    out.push_str("\\newtheorem{axiom}{公理}\n");
    out.push_str("\\allowdisplaybreaks\n");
    out.push_str("\\begin{document}\n\n");
    if !title.is_empty() {
        let t = title.replace('_', "\\_").replace('&', "\\&").replace('%', "\\%").replace('#', "\\#");
        out.push_str(&format!("\\begin{{center}}{{\\Large {t}}}\\end{{center}}\n\n"));
    }
    for (d, steps) in items {
        out.push_str(&decl_to_latex_env(d, steps));
        out.push('\n');
    }
    out.push_str("\\end{document}\n");
    out
}

/// 1つの宣言を提出レポート用の LaTeX ソース（theorem + proof 環境）に変換する
pub fn decl_to_latex_env(d: &Decl, steps: &[StepTrace]) -> String {
    crate::syntax::with_sub_seqs(&crate::api::decl_seqs(d), || decl_to_latex_env_in(d, steps))
}

fn decl_to_latex_env_in(d: &Decl, steps: &[StepTrace]) -> String {
    // 文は見出しの下に、別行の数式として置く（見出しの横に置くと上下中央にそろって間が空く）
    let statement = format!("\\leavevmode\n\\[\n{}\n\\]", decl_header_latex(d));
    let title = crate::syntax::display_name(&d.name, crate::locale::current().name).unwrap_or_else(|| d.name.replace('_', "\\_"));
    if d.is_axiom {
        return format!("\\begin{{axiom}}[{title}]{statement}\n\\end{{axiom}}\n");
    }
    let prose = decl_to_japanese_prose(d, steps);
    let mut body = String::new();
    for b in prose {
        let indent = "  ".repeat(b.depth);
        // 証明の終わりの印は proof 環境の □ に任せる
        let line = relax_long_inline(&b.text.replace("**", "").replace("$\\blacksquare$", ""));
        body.push_str(&format!("{indent}{line}\n\n"));
    }
    format!(
        "\\begin{{theorem}}[{title}]{statement}\n\\end{{theorem}}\n\\begin{{proof}}\n{}\\end{{proof}}\n",
        body
    )
}

/// def・notation・import はそのまま書き戻す。thm・axiom なら返す。
fn emit_non_decl<'m>(it: &'m Item, out: &mut String) -> Option<&'m Decl> {
    match it {
        // rec から自動で作った定理は書き戻さない（rec の行から作り直される）
        Item::Decl(d) if d.generated => return None,
        Item::Decl(d) => return Some(d),
        Item::Def(d) => {
            out.push_str(&crate::syntax::display_name_lines(&d.name));
            out.push_str(&d.src)
        }
        Item::Notation { src, .. } => {
            // def の下の記法（`:=` を持たない）は、def の下に字下げして書く
            if !src.contains(":=") {
                out.push_str("  ");
            }
            out.push_str(src.trim_start())
        },
        Item::Import { path, .. } => out.push_str(&format!("import {path}")),
        Item::Const { name, ty, .. } => out.push_str(&format!("const {name} : {ty}")),
        // 読めなかった宣言は、そのまま書き戻す
        Item::Broken { src, .. } => out.push_str(src),
    }
    out.push_str("\n\n");
    None
}

/// 標準 Narfi のソースコードを「日本語シュガー Narfi」に変換する（カーネルでそのまま実行可能）
pub fn convert_source_to_japanese_sugar(src: &str) -> String {
    convert_source_to_locale(src, "ja")
}

/// 標準の書き方を、ロケール（ja・en）での読みに変換する。対応は src/locale/ の表だけで決まる
pub fn convert_source_to_locale(src: &str, locale: &str) -> String {
    let Some(loc) = crate::locale::locale(locale) else {
        return src.to_string();
    };
    let Ok(m) = crate::module::parse_source(src, None) else {
        return src.to_string();
    };
    let body = |stmts: &[Stmt], base: usize, out: &mut String| {
        let mut tmp = String::new();
        for st in stmts {
            stmt_to_standard(st, base, &mut tmp);
        }
        for line in tmp.lines() {
            let t = line.trim_start();
            let pad = &line[..line.len() - t.len()];
            out.push_str(pad);
            out.push_str(&crate::locale::stmt_from_standard(loc, t));
            out.push('\n');
        }
    };
    let mut out = String::new();
    if let Some(e) = &m.edition {
        out.push_str(&format!("edition {e}\n\n"));
    }
    for it in &m.items {
        let Some(d) = emit_non_decl(it, &mut out) else {
            continue;
        };
        if let (Some(td), Formula::Exists(x, ty, phi)) = (&d.typedef, &d.concl) {
            let set = Term::Set(vec![(x.clone(), ty.clone())], phi.clone());
            out.push_str(&format!("typedef {} := {set}\n", td.name));
            body(&d.body, 1, &mut out);
            out.push('\n');
            continue;
        }
        let kw = if d.is_axiom { "axiom" } else { "thm" };
        out.push_str(&crate::syntax::display_name_lines(&d.name));
        out.push_str(&crate::locale::decl_from_standard(loc, &format!("{kw} {} :", d.name)));
        out.push_str(if d.is_axiom { " " } else { "\n  " });
        let mut ctx_parts = Vec::new();
        for c in &d.ctx {
            match c {
                CtxItem::Var(x, t) => ctx_parts.push(format!("{x} : {t}")),
                CtxItem::Hyp(h, f) => ctx_parts.push(format!("{h} : {f}")),
            }
        }
        if !ctx_parts.is_empty() {
            out.push_str(&ctx_parts.join(", "));
            out.push_str(if d.is_axiom { " ⊢ " } else { "\n  ⊢ " });
        } else if !d.is_axiom {
            out.push_str("⊢ ");
        }
        out.push_str(&format!("{}\n\n", d.concl));
        if !d.is_axiom {
            body(&d.body, 0, &mut out);
            out.push('\n');
        }
    }
    out.trim_end().to_string() + "\n"
}

fn just_str(j: &Just) -> String {
    j.iter()
        .map(|t| t.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn convert_source_to_standard_narfi(src: &str) -> String {
    let Ok(m) = crate::module::parse_source(src, None) else {
        return src.to_string();
    };
    let mut out = String::new();
    if let Some(e) = &m.edition {
        out.push_str(&format!("edition {e}\n\n"));
    }
    for it in &m.items {
        let Some(d) = emit_non_decl(it, &mut out) else {
            continue;
        };
        // typedef T := {x : σ | φ}（文は ∃x:σ. φ として持っている）
        if let (Some(td), Formula::Exists(x, ty, phi)) = (&d.typedef, &d.concl) {
            let set = Term::Set(vec![(x.clone(), ty.clone())], phi.clone());
            out.push_str(&format!("typedef {} := {set}\n", td.name));
            for st in &d.body {
                stmt_to_standard(st, 1, &mut out);
            }
            out.push('\n');
            continue;
        }
        out.push_str(&crate::syntax::display_name_lines(&d.name));
        if d.is_axiom {
            out.push_str(&format!("axiom {} : ", d.name));
        } else {
            out.push_str(&format!("thm {} :\n  ", d.name));
        }
        let mut ctx_parts = Vec::new();
        for c in &d.ctx {
            match c {
                CtxItem::Var(x, t) => ctx_parts.push(format!("{x} : {t}")),
                CtxItem::Hyp(h, f) => ctx_parts.push(format!("{h} : {f}")),
            }
        }
        if !ctx_parts.is_empty() {
            out.push_str(&ctx_parts.join(", "));
            if d.is_axiom {
                out.push_str(" ⊢ ");
            } else {
                out.push_str("\n  ⊢ ");
            }
        } else if !d.is_axiom {
            out.push_str("⊢ ");
        }
        out.push_str(&format!("{}\n\n", d.concl));
        if !d.is_axiom {
            for s in &d.body {
                stmt_to_standard(s, 0, &mut out);
            }
            out.push('\n');
        }
    }
    to_ascii_code(&(out.trim_end().to_string())) + "\n"
}

fn stmt_to_standard(s: &Stmt, indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    match &s.kind {
        StmtKind::Fix { vars, hyp, body } => {
            let vs = vars
                .iter()
                .map(|(x, t)| match t {
                    Some(ty) => format!("{x} : {ty}"),
                    None => x.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ");
            match hyp {
                Some((h, Some(f))) => out.push_str(&format!("{pad}Fix {vs} | {h} : {f}\n")),
                Some((h, None)) => out.push_str(&format!("{pad}Fix {vs} | {h}\n")),
                None => out.push_str(&format!("{pad}Fix {vs}\n")),
            }
            for c in body {
                stmt_to_standard(c, indent + 1, out);
            }
        }
        StmtKind::Assume { name, ty, body } => {
            match ty {
                Some(f) => out.push_str(&format!("{pad}assume {name} : {f}\n")),
                None => out.push_str(&format!("{pad}assume {name}\n")),
            }
            for c in body {
                stmt_to_standard(c, indent + 1, out);
            }
        }
        StmtKind::ByContra { name, body } => {
            out.push_str(&format!("{pad}by_contra {name}\n"));
            for c in body {
                stmt_to_standard(c, indent + 1, out);
            }
        }
        StmtKind::Obtain {
            var,
            deps,
            hyps,
            stated,
            just,
        } => {
            let v_str = match deps {
                Some(ds) => format!("{var}({})", ds.join(", ")),
                None => var.clone(),
            };
            // 仮定の名前を省いた（x.prop）なら書かない
            let named: Vec<&String> = hyps.iter().filter(|h| !h.ends_with(".prop")).collect();
            let h_str = if named.is_empty() {
                String::new()
            } else {
                let hs: Vec<&str> = named.iter().map(|h| h.as_str()).collect();
                match stated {
                    Some(f) => format!(" | {} : {f}", hs.join(", ")),
                    None => format!(" | {}", hs.join(", ")),
                }
            };
            out.push_str(&format!("{pad}Obtain {v_str}{h_str} by {}\n", just_str(just)));
        }
        StmtKind::Choose { choice, just } => {
            let c_str = match choice {
                Choice::Term(t) => match just {
                    Some(j) => format!("choose {t}, {}", just_str(j)),
                    None => format!("choose {t}"),
                },
                Choice::Left => "left".to_string(),
                Choice::Right => "right".to_string(),
            };
            out.push_str(&format!("{pad}{c_str}\n"));
        }
        StmtKind::Cases { hyp, left, right } => {
            out.push_str(&format!("{pad}cases {hyp}\n"));
            out.push_str(&format!("{pad}  Case left {}\n", left.0));
            for c in &left.1 {
                stmt_to_standard(c, indent + 2, out);
            }
            out.push_str(&format!("{pad}  Case right {}\n", right.0));
            for c in &right.1 {
                stmt_to_standard(c, indent + 2, out);
            }
        }
        StmtKind::Induction {
            var, zero, succ, ..
        } => {
            out.push_str(&format!("{pad}induction {var}\n"));
            out.push_str(&format!("{pad}  Case zero\n"));
            for c in zero {
                stmt_to_standard(c, indent + 2, out);
            }
            let (k, ih, ih_ty, body) = succ;
            match ih_ty {
                Some(f) => out.push_str(&format!("{pad}  Case succ {k}, {ih} : {f}\n")),
                None => out.push_str(&format!("{pad}  Case succ {k}, {ih}\n")),
            }
            for c in body {
                stmt_to_standard(c, indent + 2, out);
            }
        }
        StmtKind::Let { name, term } => {
            out.push_str(&format!("{pad}let {name} := {term}\n"));
        }
        StmtKind::Therefore(f) => {
            out.push_str(&format!("{pad}∴ {f}\n"));
        }
        StmtKind::Close(j) => {
            out.push_str(&format!("{pad}{}\n", just_str(j)));
        }
        StmtKind::Show { name, ty, just, body } => {
            let label = name.as_ref().map(|h| format!("{h} : ")).unwrap_or_default();
            match just {
                Some(j) if body.is_empty() => out.push_str(&format!("{pad}{label}{ty} by {}\n", just_str(j))),
                _ => out.push_str(&format!("{pad}{label}{ty}\n")),
            }
            for c in body {
                stmt_to_standard(c, indent + 1, out);
            }
        }
        StmtKind::Chain { start, steps } => {
            out.push_str(&format!("{pad}{start}\n"));
            for st in steps {
                out.push_str(&format!(
                    "{pad}  {} {}   by {}\n",
                    st.rel,
                    st.term,
                    just_str(&st.just)
                ));
            }
        }
    }
}


fn greek_to_ascii_name(c: char) -> Option<&'static str> {
    Some(match c {
        'α' => "alpha",
        'β' => "beta",
        'γ' => "gamma",
        'δ' => "delta",
        'ε' => "eps",
        'ζ' => "zeta",
        'η' => "eta",
        'θ' => "theta",
        'ι' => "iota",
        'κ' => "kappa",
        'λ' => "lambda",
        'μ' => "mu",
        'ν' => "nu",
        'ξ' => "xi",
        'π' => "pi",
        'ρ' => "rho",
        'σ' => "sigma",
        'τ' => "tau",
        'υ' => "upsilon",
        'φ' => "phi",
        'χ' => "chi",
        'ψ' => "psi",
        'ω' => "omega",
        'Γ' => "Gamma",
        'Δ' => "Delta",
        'Θ' => "Theta",
        'Λ' => "Lambda",
        'Ξ' => "Xi",
        'Π' => "Pi",
        'Σ' => "Sigma",
        'Υ' => "Upsilon",
        'Φ' => "Phi",
        'Ψ' => "Psi",
        'Ω' => "Omega",
        '∞' => "infty",
        '∅' => "emptyset",
        '∂' => "partial",
        '∇' => "nabla",
        _ => return None,
    })
}

/// Unicode を含む Narfi コードをキーボード入力可能な純粋 ASCII 正規形に変換する
pub fn to_ascii_code(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    let mut out = String::new();
    for (idx, &c) in cs.iter().enumerate() {
        if let Some(gname) = greek_to_ascii_name(c) {
            if idx > 0 && cs[idx - 1].is_ascii_alphanumeric() {
                out.push_str(&format!("_{{{gname}}}"));
            } else {
                out.push_str(gname);
            }
            continue;
        }
        match c {
            '∀' => out.push_str("forall "),
            '∃' => out.push_str("exists "),
            '⟶' => {
                out.push_str("\\longrightarrow");
                if cs.get(idx + 1).is_some_and(|c| !c.is_whitespace()) {
                    out.push(' ');
                }
            }
            '→' => out.push_str("->"),
            '↔' => out.push_str("<->"),
            '∧' => out.push_str("and"),
            '∨' => out.push_str("or"),
            '¬' => out.push_str("not "),
            '⊥' => out.push_str("bot"),
            '⊢' => out.push_str("|-"),
            '∴' => out.push_str("therefore"),
            '≤' => out.push_str("<="),
            '≥' => out.push_str(">="),
            '≠' => out.push_str("!="),
            '∈' => out.push_str("in"),
            '∉' => out.push_str("notin"),
            '⊂' => out.push_str("subset"),
            '⊆' => out.push_str("subseteq"),
            '⊃' => out.push_str("supset"),
            '⊇' => out.push_str("supseteq"),
            '≡' => out.push_str("equiv"),
            '≈' => out.push_str("approx"),
            '∼' => out.push_str("sim"),
            '≅' => out.push_str("cong"),
            '∣' => out.push_str("divides"),
            // 集合の演算は lib/set の記法。ASCII では TeX のコマンドで書く（後ろに空白を置く）
            '∪' => out.push_str("\\cup "),
            '∩' => out.push_str("\\cap "),
            '∖' => out.push_str("\\setminus "),
            '∁' => out.push_str("\\complement "),
            '⊊' => out.push_str("subsetneq"),
            '⇒' => out.push_str("=>"),
            '⇔' => out.push_str("<=>"),
            '·' => out.push('*'),
            '²' => out.push_str("^2"),
            '³' => out.push_str("^3"),
            'ℕ' => out.push_str("Nat"),
            'ℤ' => out.push_str("Int"),
            'ℚ' => out.push_str("Rat"),
            'ℝ' => out.push_str("Real"),
            'ℂ' => out.push_str("Complex"),
            '𝔽' => out.push_str("Field"),
            'ℙ' => out.push_str("Primes"),
            c if ('₀'..='₉').contains(&c) => {
                let d = (c as u32 - '₀' as u32) as u8 + b'0';
                out.push('_');
                out.push(d as char);
            }
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod break_tests {
    use super::break_math;

    #[test]
    fn breaks_long_math_outside_brackets_only() {
        let long = "a + b + \\left(c + d + e\\right) + ffffffffffffffffffffffffffffff + gggggggggggggggggggggggggggggggggggggg + h";
        let ps = break_math(long, 40);
        assert!(ps.len() >= 2, "{ps:?}");
        // 括弧の中は折らない
        assert!(ps.iter().any(|p| p.contains("\\left(c + d + e\\right)")), "{ps:?}");
        // 折っても中身は変わらない（記号から次の行が始まる）
        assert_eq!(ps.join(" "), long);
        // 短い式は折らない
        assert_eq!(break_math("a + b", 40), vec!["a + b".to_string()]);
    }
}
