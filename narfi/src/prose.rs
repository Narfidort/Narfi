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
    j.iter()
        .map(|t| match t {
            Term::Var(s) if s == "ring" => "\\text{式変形(ring)}".to_string(),
            Term::Var(s) if s == "linarith" => "\\text{不等式評価(linarith)}".to_string(),
            Term::Var(s) if s == "refl" => "\\text{反射律}".to_string(),
            Term::Var(s) if s == "decide" => "\\text{計算}".to_string(),
            Term::Var(s) if s == "sorry" => "\\text{未完(sorry)}".to_string(),
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

pub fn decl_header_latex(d: &Decl) -> String {
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
            if i + 1 == parts.len() {
                lines.push(format!("&{}", p));
            } else {
                lines.push(format!("&{},", p));
            }
        }
        lines.push(format!("&\\quad\\vdash {}", d.concl.to_latex()));
        format!("\\begin{{aligned}}\n{}\n\\end{{aligned}}", lines.join(" \\\\\n"))
    }
}

pub fn decl_to_japanese_prose(d: &Decl, steps: &[StepTrace]) -> Vec<ProseBlock> {
    let mut out = Vec::new();
    if d.generated {
        out.push(ProseBlock {
            depth: 0,
            text: format!("**定義の等式 `{}`**: ${}$（再帰による定義から、再帰定理で示される）", d.name, d.concl.to_latex()),
        });
        return out;
    }
    if d.is_axiom {
        out.push(ProseBlock {
            depth: 0,
            text: format!("**公理 `{}`**: ${}$", d.name, decl_header_latex(d)),
        });
        return out;
    }

    // 前提条件の説明
    let mut hyp_items = Vec::new();
    for c in &d.ctx {
        match c {
            CtxItem::Var(x, t) if t.contains('→') => {
                hyp_items.push(format!("関数 ${} {}$", ident_to_latex(x), sort_decl_latex(t)));
            }
            CtxItem::Var(x, t) => {
                hyp_items.push(format!("変数 ${} {}$", ident_to_latex(x), sort_decl_latex(t)));
            }
            CtxItem::Hyp(h, f) => {
                hyp_items.push(format!(
                    "仮定 ${}$：${}$",
                    ident_to_latex(h),
                    f.to_latex()
                ));
            }
        }
    }

    if !hyp_items.is_empty() {
        out.push(ProseBlock {
            depth: 0,
            text: "**【前提】**".to_string(),
        });
        for item in hyp_items {
            out.push(ProseBlock {
                depth: 1,
                text: item,
            });
        }
    }
    out.push(ProseBlock {
        depth: 0,
        text: format!("**【目標】** ${}$ を示す。", d.concl.to_latex()),
    });

    stmts_to_prose(&d.body, steps, 0, &mut out);
    out
}

fn stmts_to_prose(stmts: &[Stmt], steps: &[StepTrace], depth: usize, out: &mut Vec<ProseBlock>) {
    for s in stmts {
        match &s.kind {
            StmtKind::Fix { vars, hyp, body } => {
                let vs: Vec<String> = vars
                    .iter()
                    .map(|(x, ty)| match ty {
                        Some(t) if t != "?" => {
                            format!("{} \\in {}", ident_to_latex(x), ident_to_latex(t))
                        }
                        _ => ident_to_latex(x),
                    })
                    .collect();
                let vs_str = vs.join(",\\ ");
                let text = match hyp {
                    Some((h, Some(f))) => {
                        format!(
                            "${}$ を満たす ${}$ を任意にとって固定する（仮定 ${}$）。",
                            f.to_latex(),
                            vs_str,
                            ident_to_latex(h)
                        )
                    }
                    Some((h, None)) => {
                        if let Some(fl) = find_hyp_formula_latex(steps, s.line, h) {
                            format!(
                                "${}$ を満たす ${}$ を任意にとって固定する（仮定 ${}$）。",
                                fl,
                                vs_str,
                                ident_to_latex(h)
                            )
                        } else {
                            format!(
                                "条件（仮定 ${}$）を満たす ${}$ を任意にとって固定する。",
                                ident_to_latex(h),
                                vs_str
                            )
                        }
                    }
                    None => format!("任意の ${}$ をとって固定する。", vs_str),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out);
            }
            StmtKind::Assume { name, ty, body } => {
                let fl = match ty {
                    Some(f) => Some(f.to_latex()),
                    None => find_hyp_formula_latex(steps, s.line, name),
                };
                let text = match fl {
                    Some(f) => format!("${}$ と仮定する（仮定 ${}$）。", f, ident_to_latex(name)),
                    None => format!("仮定 ${}$ をおく。", ident_to_latex(name)),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out);
            }
            StmtKind::ByContra { name, body } => {
                let fl = find_hyp_formula_latex(steps, s.line, name);
                let text = match fl {
                    Some(f) => format!(
                        "背理法による。結論の否定 ${}$ と仮定する（仮定 ${}$）。",
                        f,
                        ident_to_latex(name)
                    ),
                    None => format!(
                        "背理法により、結論の否定（仮定 ${}$）を仮定する。",
                        ident_to_latex(name)
                    ),
                };
                out.push(ProseBlock { depth, text });
                stmts_to_prose(body, steps, depth + 1, out);
            }
            StmtKind::Obtain {
                var,
                deps,
                hyps,
                just,
            } => {
                let dep_note = match deps {
                    Some(ds) if !ds.is_empty() => {
                        let dl: Vec<String> = ds.iter().map(|d| ident_to_latex(d)).collect();
                        format!("（${}$ に依存する）", dl.join(", "))
                    }
                    _ => String::new(),
                };
                let mut h_descs = Vec::new();
                for h in hyps {
                    if let Some(fl) = find_hyp_formula_latex(steps, s.line + 1, h) {
                        h_descs.push(format!("${}$（仮定 ${}$）", fl, ident_to_latex(h)));
                    } else {
                        h_descs.push(format!("仮定 ${}$", ident_to_latex(h)));
                    }
                }
                let text = format!(
                    "${}$ より、{} を満たす{} ${}$ をとる。",
                    just_to_latex(just),
                    h_descs.join(" かつ "),
                    dep_note,
                    ident_to_latex(var)
                );
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Let { name, term } => {
                out.push(ProseBlock {
                    depth,
                    text: format!(
                        "ここで、${} := {}$ とおく。",
                        ident_to_latex(name),
                        term.to_latex()
                    ),
                });
            }
            StmtKind::Have { name, ty, just } => {
                out.push(ProseBlock {
                    depth,
                    text: format!(
                        "${}$ より、${}$ が成り立つ（${}$）。",
                        just_to_latex(just),
                        ty.to_latex(),
                        ident_to_latex(name)
                    ),
                });
            }
            StmtKind::Suffices { ty, just } => {
                out.push(ProseBlock {
                    depth,
                    text: format!(
                        "${}$ より、${}$ を示せば十分である。",
                        just_to_latex(just),
                        ty.to_latex()
                    ),
                });
            }
            StmtKind::Choose { choice, just } => {
                let text = match (choice, just) {
                    (Choice::Term(t), Some(j)) => {
                        format!(
                            "${}$ をとればよい（条件は ${}$ より従う）。",
                            t.to_latex(),
                            just_to_latex(j)
                        )
                    }
                    (Choice::Term(t), None) => {
                        format!("${}$ をとればよい。", t.to_latex())
                    }
                    (Choice::Left, _) => "選言の左側を示す。".to_string(),
                    (Choice::Right, _) => "選言の右側を示す。".to_string(),
                };
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Contradiction(a, b) => {
                out.push(ProseBlock {
                    depth,
                    text: format!(
                        "これは ${}$ と ${}$ に矛盾する。$\\blacksquare$",
                        ident_to_latex(a),
                        ident_to_latex(b)
                    ),
                });
            }
            StmtKind::Cases { hyp, left, right } => {
                out.push(ProseBlock {
                    depth,
                    text: format!("${}$ について場合分けを行う。", ident_to_latex(hyp)),
                });
                let l_fl = find_hyp_formula_latex(steps, s.line, &left.0);
                out.push(ProseBlock {
                    depth: depth + 1,
                    text: match l_fl {
                        Some(f) => format!(
                            "**(場合 1)** ${}$ （仮定 ${}$）のとき：",
                            f,
                            ident_to_latex(&left.0)
                        ),
                        None => format!("**(場合 1)** 仮定 ${}$ のとき：", ident_to_latex(&left.0)),
                    },
                });
                stmts_to_prose(&left.1, steps, depth + 2, out);

                let r_fl = find_hyp_formula_latex(steps, s.line, &right.0);
                out.push(ProseBlock {
                    depth: depth + 1,
                    text: match r_fl {
                        Some(f) => format!(
                            "**(場合 2)** ${}$ （仮定 ${}$）のとき：",
                            f,
                            ident_to_latex(&right.0)
                        ),
                        None => {
                            format!("**(場合 2)** 仮定 ${}$ のとき：", ident_to_latex(&right.0))
                        }
                    },
                });
                stmts_to_prose(&right.1, steps, depth + 2, out);
            }
            StmtKind::Induction {
                var, zero, succ, ..
            } => {
                let vl = ident_to_latex(var);
                out.push(ProseBlock {
                    depth,
                    text: format!("${vl}$ に関する数学的帰納法で示す。"),
                });
                out.push(ProseBlock {
                    depth: depth + 1,
                    text: format!("**(基底段階)** ${vl} = 0$ のとき："),
                });
                stmts_to_prose(zero, steps, depth + 2, out);

                let (k, ih, ih_ty, body) = succ;
                let kl = ident_to_latex(k);
                let ihl = ident_to_latex(ih);
                let ih_str = match ih_ty {
                    Some(f) => format!("（帰納法の仮定 ${ihl} : {}$）", f.to_latex()),
                    None => match find_hyp_formula_latex(steps, s.line, ih) {
                        Some(f) => format!("（帰納法の仮定 ${ihl} : {f}$）"),
                        None => format!("（帰納法の仮定 ${ihl}$）"),
                    },
                };
                out.push(ProseBlock {
                    depth: depth + 1,
                    text: format!("**(帰納段階)** ${vl} = {kl}$ で成り立つと仮定し{ih_str}、$S({kl})$ のときを示す："),
                });
                stmts_to_prose(body, steps, depth + 2, out);
            }
            StmtKind::Unfold { names, at } => {
                let ns: Vec<String> = names.iter().map(|n| format!("${}$", ident_to_latex(n))).collect();
                let text = if at.is_empty() {
                    format!("{} の定義を展開する。", ns.join("、"))
                } else {
                    let hs: Vec<String> = at.iter().map(|h| format!("${}$", ident_to_latex(h))).collect();
                    format!("{} において {} の定義を展開する。", hs.join("、"), ns.join("、"))
                };
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Therefore(f) => {
                out.push(ProseBlock {
                    depth,
                    text: format!("したがって、${}$ が成り立つ。$\\blacksquare$", f.to_latex()),
                });
            }
            StmtKind::Show { ty, just } => {
                out.push(ProseBlock {
                    depth,
                    text: format!("${}$ より ${}$ が成り立つ。", just_to_latex(just), ty.to_latex()),
                });
            }
            StmtKind::Close(j) => {
                let text = match j.as_slice() {
                    [Term::Var(s)] if s == "sorry" => "（※ ここは未完成 `sorry`）".to_string(),
                    [Term::Var(s)] if s == "refl" => {
                        "反射律より直ちに成り立つ。$\\blacksquare$".to_string()
                    }
                    [Term::Var(s)] if s == "ring" => {
                        "式変形（環の計算）より成り立つ。$\\blacksquare$".to_string()
                    }
                    [Term::Var(s)] if s == "linarith" => {
                        "不等式の評価より成り立つ。$\\blacksquare$".to_string()
                    }
                    [Term::Var(s)] if s == "decide" => {
                        "直接計算により成り立つ。$\\blacksquare$".to_string()
                    }
                    _ => format!("${}$ より成り立つ。$\\blacksquare$", just_to_latex(j)),
                };
                out.push(ProseBlock { depth, text });
            }
            StmtKind::Chain {
                start,
                steps: csteps,
            } => {
                let mut lines = Vec::new();
                for (idx, st) in csteps.iter().enumerate() {
                    let lhs = if idx == 0 {
                        start.to_latex()
                    } else {
                        String::new()
                    };
                    let rel = rel_to_latex(&st.rel);
                    let rhs = st.term.to_latex();
                    let j = just_to_latex(&st.just);
                    lines.push(format!(
                        "{lhs} &{rel} {rhs} && \\left(\\because {j}\\right)"
                    ));
                }
                let math = format!(
                    "$$\\begin{{aligned}}\n{}\n\\end{{aligned}}$$",
                    lines.join(" \\\\\n")
                );
                out.push(ProseBlock { depth, text: math });
            }
        }
    }
}

/// LaTeX の文書全体（LuaLaTeX + ltjsarticle）。title が空なら表題をつけない。
pub fn latex_document(title: &str, items: &[(&Decl, &[StepTrace])]) -> String {
    let mut out = String::new();
    out.push_str("\\documentclass[a4paper,11pt]{ltjsarticle}\n");
    out.push_str("\\usepackage{amsmath,amssymb,amsthm}\n");
    out.push_str("\\usepackage[margin=22mm]{geometry}\n");
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
    // 文は見出しの下に、別行の数式として置く（見出しの横に置くと上下中央にそろって間が空く）
    let statement = format!("\\leavevmode\n\\[\n{}\n\\]", decl_header_latex(d));
    if d.is_axiom {
        return format!("\\begin{{axiom}}[{}]{statement}\n\\end{{axiom}}\n", d.name.replace('_', "\\_"));
    }
    let prose = decl_to_japanese_prose(d, steps);
    let mut body = String::new();
    for b in prose {
        let indent = "  ".repeat(b.depth);
        // 証明の終わりの印は proof 環境の □ に任せる
        let line = b.text.replace("**", "").replace("$\\blacksquare$", "");
        body.push_str(&format!("{indent}{line}\n\n"));
    }
    format!(
        "\\begin{{theorem}}[{}]{statement}\n\\end{{theorem}}\n\\begin{{proof}}\n{}\\end{{proof}}\n",
        d.name.replace('_', "\\_"),
        body
    )
}

/// def・notation・import はそのまま書き戻す。thm・axiom なら返す。
fn emit_non_decl<'m>(it: &'m Item, out: &mut String) -> Option<&'m Decl> {
    match it {
        // rec から自動で作った定理は書き戻さない（rec の行から作り直される）
        Item::Decl(d) if d.generated => return None,
        Item::Decl(d) => return Some(d),
        Item::Def(d) => out.push_str(&d.src),
        Item::Notation { src, .. } => out.push_str(src),
        Item::Import { path, .. } => out.push_str(&format!("import {path}")),
    }
    out.push_str("\n\n");
    None
}

/// 標準 Narfi のソースコードを「日本語シュガー Narfi」に変換する（カーネルでそのまま実行可能）
pub fn convert_source_to_japanese_sugar(src: &str) -> String {
    let Ok(m) = crate::module::parse_source(src, None) else {
        return src.to_string();
    };
    let mut out = String::new();
    for it in &m.items {
        let Some(d) = emit_non_decl(it, &mut out) else {
            continue;
        };
        // typedef T := {x : σ | φ}（文は ∃x:σ. φ として持っている）
        if let (Some(td), Formula::Exists(x, ty, phi)) = (&d.typedef, &d.concl) {
            let set = Term::Set(vec![(x.clone(), ty.clone())], phi.clone());
            out.push_str(&format!("typedef {} := {set}\n", td.name));
            for st in &d.body {
                stmt_to_japanese_sugar(st, 1, &mut out);
            }
            out.push('\n');
            continue;
        }
        if d.is_axiom {
            out.push_str(&format!("公理 {} : ", d.name));
        } else {
            out.push_str(&format!("定理 {} :\n  ", d.name));
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
                stmt_to_japanese_sugar(s, 0, &mut out);
            }
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

fn stmt_to_japanese_sugar(s: &Stmt, indent: usize, out: &mut String) {
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
                Some((h, Some(f))) => out.push_str(&format!(
                    "{pad}{h} : {f} を満たす {vs} を任意にとって固定する\n"
                )),
                Some((h, None)) => {
                    out.push_str(&format!("{pad}{h} を満たす {vs} を任意にとって固定する\n"))
                }
                None => out.push_str(&format!("{pad}{vs} を任意にとって固定する\n")),
            }
            for c in body {
                stmt_to_japanese_sugar(c, indent + 1, out);
            }
        }
        StmtKind::Assume { name, ty, body } => {
            match ty {
                Some(f) => out.push_str(&format!("{pad}{name} : {f} と仮定する\n")),
                None => out.push_str(&format!("{pad}{name} と仮定する\n")),
            }
            for c in body {
                stmt_to_japanese_sugar(c, indent + 1, out);
            }
        }
        StmtKind::ByContra { name, body } => {
            out.push_str(&format!("{pad}背理法により {name} と仮定する\n"));
            for c in body {
                stmt_to_japanese_sugar(c, indent + 1, out);
            }
        }
        StmtKind::Obtain {
            var,
            deps,
            hyps,
            just,
        } => {
            let v_str = match deps {
                Some(ds) => format!("{var}({})", ds.join(", ")),
                None => var.clone(),
            };
            let h_str = hyps.join(", ");
            out.push_str(&format!(
                "{pad}{} より {v_str}, {h_str} が存在する\n",
                just_str(just)
            ));
        }
        StmtKind::Have { name, ty, just } => {
            out.push_str(&format!(
                "{pad}{} より {name} : {ty} が成り立つ\n",
                just_str(just)
            ));
        }
        StmtKind::Suffices { ty, just } => {
            out.push_str(&format!(
                "{pad}{} より {ty} を示せば十分である\n",
                just_str(just)
            ));
        }
        StmtKind::Choose { choice, just } => {
            let c_str = match choice {
                Choice::Term(t) => match just {
                    Some(j) => format!("{t}, {} をとればよい", just_str(j)),
                    None => format!("{t} をとればよい"),
                },
                Choice::Left => "左を選ぶ".to_string(),
                Choice::Right => "右を選ぶ".to_string(),
            };
            out.push_str(&format!("{pad}{c_str}\n"));
        }
        StmtKind::Contradiction(a, b) => {
            out.push_str(&format!("{pad}{a} と {b} は矛盾\n"));
        }
        StmtKind::Cases { hyp, left, right } => {
            out.push_str(&format!("{pad}{hyp} で場合分けする\n"));
            out.push_str(&format!("{pad}  場合 左 {}\n", left.0));
            for c in &left.1 {
                stmt_to_japanese_sugar(c, indent + 2, out);
            }
            out.push_str(&format!("{pad}  場合 右 {}\n", right.0));
            for c in &right.1 {
                stmt_to_japanese_sugar(c, indent + 2, out);
            }
        }
        StmtKind::Induction {
            var, zero, succ, ..
        } => {
            out.push_str(&format!("{pad}{var} に関する帰納法\n"));
            out.push_str(&format!("{pad}  基底段階\n"));
            for c in zero {
                stmt_to_japanese_sugar(c, indent + 2, out);
            }
            let (k, ih, ih_ty, body) = succ;
            match ih_ty {
                Some(f) => out.push_str(&format!("{pad}  帰納段階 {k}, {ih} : {f}\n")),
                None => out.push_str(&format!("{pad}  帰納段階 {k}, {ih}\n")),
            }
            for c in body {
                stmt_to_japanese_sugar(c, indent + 2, out);
            }
        }
        StmtKind::Let { name, term } => {
            out.push_str(&format!("{pad}{name} := {term} とする\n"));
        }
        StmtKind::Unfold { names, at } => {
            if at.is_empty() {
                out.push_str(&format!("{pad}{} を展開する\n", names.join(", ")));
            } else {
                out.push_str(&format!("{pad}{} の {} を展開する\n", at.join(", "), names.join(", ")));
            }
        }
        StmtKind::Therefore(f) => {
            out.push_str(&format!("{pad}したがって {f}\n"));
        }
        StmtKind::Close(j) => {
            out.push_str(&format!("{pad}{}\n", just_str(j)));
        }
        StmtKind::Show { ty, just } => {
            out.push_str(&format!("{pad}{ty} by {}\n", just_str(just)));
        }
        StmtKind::Chain { start, steps } => {
            out.push_str(&format!("{pad}{start}\n"));
            for st in steps {
                out.push_str(&format!(
                    "{pad}  {} {}   (∵ {})\n",
                    st.rel,
                    st.term,
                    just_str(&st.just)
                ));
            }
        }
    }
}

/// 日本語シュガー等を含む Narfi ソースを標準の簡潔な Narfi 構文へ正規化する
pub fn convert_source_to_standard_narfi(src: &str) -> String {
    let Ok(m) = crate::module::parse_source(src, None) else {
        return src.to_string();
    };
    let mut out = String::new();
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
            just,
        } => {
            let v_str = match deps {
                Some(ds) => format!("{var}({})", ds.join(", ")),
                None => var.clone(),
            };
            let h_str = hyps.join(", ");
            out.push_str(&format!(
                "{pad}Obtain {v_str}, {h_str} : {}\n",
                just_str(just)
            ));
        }
        StmtKind::Have { name, ty, just } => {
            out.push_str(&format!("{pad}have {name} : {ty} := {}\n", just_str(just)));
        }
        StmtKind::Suffices { ty, just } => {
            out.push_str(&format!("{pad}suffices {ty} := {}\n", just_str(just)));
        }
        StmtKind::Choose { choice, just } => {
            let c_str = match choice {
                Choice::Term(t) => match just {
                    Some(j) => format!("choose {t}, {}", just_str(j)),
                    None => format!("choose {t}"),
                },
                Choice::Left => "choose left".to_string(),
                Choice::Right => "choose right".to_string(),
            };
            out.push_str(&format!("{pad}{c_str}\n"));
        }
        StmtKind::Contradiction(a, b) => {
            out.push_str(&format!("{pad}contradiction {a} {b}\n"));
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
        StmtKind::Unfold { names, at } => {
            if at.is_empty() {
                out.push_str(&format!("{pad}unfold {}\n", names.join(", ")));
            } else {
                out.push_str(&format!("{pad}unfold {} at {}\n", names.join(", "), at.join(", ")));
            }
        }
        StmtKind::Therefore(f) => {
            out.push_str(&format!("{pad}∴ {f}\n"));
        }
        StmtKind::Close(j) => {
            out.push_str(&format!("{pad}{}\n", just_str(j)));
        }
        StmtKind::Show { ty, just } => {
            out.push_str(&format!("{pad}{ty} by {}\n", just_str(just)));
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
            '⇐' => out.push_str("suffices"),
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
            '∪' => out.push_str("union"),
            '∩' => out.push_str("inter"),
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
