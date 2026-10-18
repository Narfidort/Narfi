//! 型（ソート）の推論（仕様 §3.3）。elab の一部で、kernel はこの結果を信じない（検算する）。
//!
//! 変数・数字・演算の結果ごとに「型の箱」を作り、同じ型であるべき箱を union-find でつなぐ。
//! 最後に、各グループの型を決める：
//!   - 書かれた型・文脈の型があればそれ
//!   - 数字だけのグループは、使われた演算が意味を持つ最小の数のソート（§3.2）
//!   - 数の演算に使われた変数なのに決まらなければエラー（`x : ℝ` と書いてもらう）
//!   - 何の制約もなければ、定理の文ではソート変数 `'a`、それ以外ではエラー

use crate::kernel::env::{FnSig, KEnv, LocalSig, NUM_SORTS, num_rank, op_min_rank};
use crate::syntax::{Formula, RELS, Term, is_fn_sort};
use std::collections::HashMap;

pub type SResult<T> = Result<T, String>;

#[derive(Clone, Debug)]
struct Node {
    parent: usize,
    sort: Option<String>,
    /// 数のソートでなければならない
    numeric: bool,
    /// 必要な最小の順位（`-` があれば ℤ 以上、`/` があれば ℚ 以上）
    rank: u8,
    /// 数字だけからなる
    lit: bool,
    /// エラーメッセージ用の名前
    name: Option<String>,
}

pub struct Infer<'a> {
    kenv: &'a KEnv,
    pub sig: LocalSig,
    /// 新しい局所記号を作ってよいか
    allow_new: bool,
    /// 文脈の変数（名前・型）
    ctx: Vec<(String, String)>,
    /// 文の自由変数を作ってよいか（定理の文のとき）
    statement: bool,
    nodes: Vec<Node>,
    scope: Vec<(String, usize)>,
    free: Vec<(String, usize)>,
    fn_vars: HashMap<String, (Vec<usize>, usize)>,
    pred_vars: HashMap<String, Vec<usize>>,
    binders: Vec<usize>,
}

pub struct Inferred {
    pub sig: LocalSig,
    pub free: Vec<(String, String)>,
    pub sort_params: Vec<String>,
    sorts: Vec<String>,
    binders: Vec<usize>,
    root: Vec<usize>,
}

const OP_NAME: [(&str, &str); 6] = [("-", "引き算"), ("neg", "符号の反転"), ("abs", "絶対値"), ("/", "割り算"), ("+", "足し算"), ("·", "掛け算")];

/// 箱の名前を、エラーメッセージ用の言葉にする
fn label(n: &str) -> String {
    if let Some(f) = n.strip_prefix("fn:") {
        format!("関数記号 `{f}` の")
    } else if let Some(p) = n.strip_prefix("pred:") {
        format!("述語 `{p}` の引数の")
    } else {
        format!("`{n}` の")
    }
}

fn op_label(f: &str) -> &str {
    OP_NAME.iter().find(|(k, _)| *k == f).map(|(_, v)| *v).unwrap_or(f)
}

impl<'a> Infer<'a> {
    pub fn new(kenv: &'a KEnv, sig: LocalSig, ctx: Vec<(String, String)>, statement: bool) -> Self {
        Infer {
            kenv,
            sig,
            allow_new: true,
            ctx,
            statement,
            nodes: vec![],
            scope: vec![],
            free: vec![],
            fn_vars: HashMap::new(),
            pred_vars: HashMap::new(),
            binders: vec![],
        }
    }

    fn node(&mut self, sort: Option<String>, lit: bool, name: Option<String>) -> usize {
        let i = self.nodes.len();
        self.nodes.push(Node { parent: i, sort, numeric: false, rank: 0, lit, name });
        i
    }

    fn fixed(&mut self, s: &str) -> usize {
        self.node(Some(s.to_string()), false, None)
    }

    fn find(&mut self, i: usize) -> usize {
        let p = self.nodes[i].parent;
        if p == i {
            return i;
        }
        let r = self.find(p);
        self.nodes[i].parent = r;
        r
    }

    fn check_node(&self, r: usize) -> SResult<()> {
        let n = &self.nodes[r];
        if let Some(s) = &n.sort {
            if n.numeric {
                match num_rank(s) {
                    Some(k) if k >= n.rank => {}
                    Some(_) => {
                        let need = NUM_SORTS[n.rank as usize];
                        return Err(format!("{s} では使えない演算がある（{need} 以上が必要）"));
                    }
                    None => return Err(format!("{s} に数の演算・大小関係を使っている")),
                }
            }
        }
        Ok(())
    }

    fn unify(&mut self, a: usize, b: usize) -> SResult<()> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return Ok(());
        }
        let (na, nb) = (self.nodes[ra].clone(), self.nodes[rb].clone());
        let sort = match (&na.sort, &nb.sort) {
            (Some(x), Some(y)) if x != y => {
                let who = na.name.or(nb.name).map(|n| label(&n)).unwrap_or_default();
                return Err(format!("{who}型が合わない：{x} と {y}"));
            }
            (Some(x), _) | (_, Some(x)) => Some(x.clone()),
            _ => None,
        };
        self.nodes[rb].parent = ra;
        let n = &mut self.nodes[ra];
        n.sort = sort;
        n.numeric = na.numeric || nb.numeric;
        n.rank = na.rank.max(nb.rank);
        n.lit = na.lit && nb.lit;
        n.name = na.name.or(nb.name);
        self.check_node(ra)
    }

    fn constrain_num(&mut self, i: usize, rank: u8, what: &str) -> SResult<()> {
        let r = self.find(i);
        self.nodes[r].numeric = true;
        self.nodes[r].rank = self.nodes[r].rank.max(rank);
        self.check_node(r).map_err(|e| format!("{what}：{e}"))
    }

    fn lookup_var(&mut self, x: &str) -> SResult<usize> {
        if let Some((_, i)) = self.scope.iter().rev().find(|(y, _)| y == x) {
            return Ok(*i);
        }
        if let Some((_, s)) = self.ctx.iter().rev().find(|(y, _)| y == x) {
            let s = s.clone();
            let i = self.fixed(&s);
            self.nodes[i].name = Some(x.to_string());
            return Ok(i);
        }
        if self.sig.fns.contains_key(x) || self.fn_vars.contains_key(x) {
            return Err(format!("関数記号 `{x}` を値として使うことはできない"));
        }
        if self.statement {
            if let Some((_, i)) = self.free.iter().find(|(y, _)| y == x) {
                return Ok(*i);
            }
            let i = self.node(None, false, Some(x.to_string()));
            self.free.push((x.to_string(), i));
            return Ok(i);
        }
        Err(format!("`{x}` は文脈にない"))
    }

    pub fn term(&mut self, t: &Term) -> SResult<usize> {
        match t {
            Term::Meta(_) => Ok(self.node(None, false, None)),
            Term::Num(_) => {
                let i = self.node(None, true, None);
                self.constrain_num(i, 0, "数")?;
                Ok(i)
            }
            Term::Var(x) => self.lookup_var(x),
            Term::App(f, args) => {
                if let Some(min) = op_min_rank(f, args.len()) {
                    let r = self.node(None, true, None);
                    for a in args {
                        let n = self.term(a)?;
                        self.unify(r, n).map_err(|e| format!("{}の両辺：{e}", op_label(f)))?;
                    }
                    self.constrain_num(r, min, op_label(f))?;
                    return Ok(r);
                }
                match (f.as_str(), args.as_slice()) {
                    ("S", [a]) => {
                        let n = self.term(a)?;
                        let k = self.fixed("ℕ");
                        self.unify(n, k).map_err(|e| format!("S の引数：{e}"))?;
                        Ok(self.fixed("ℕ"))
                    }
                    ("^", [a, e]) => {
                        let ne = self.term(e)?;
                        let k = self.fixed("ℕ");
                        self.unify(ne, k).map_err(|e| format!("指数：{e}"))?;
                        let n = self.term(a)?;
                        self.constrain_num(n, 0, "累乗")?;
                        Ok(n)
                    }
                    _ => {
                        let (arg_nodes, res) = self.fn_symbol(f, args.len())?;
                        for (a, n) in args.iter().zip(arg_nodes) {
                            let m = self.term(a)?;
                            self.unify(n, m).map_err(|e| format!("`{f}` の引数：{e}"))?;
                        }
                        Ok(res)
                    }
                }
            }
        }
    }

    /// 関数記号 f の引数・結果の型の箱
    fn fn_symbol(&mut self, f: &str, arity: usize) -> SResult<(Vec<usize>, usize)> {
        if let Some(sig) = self.sig.fns.get(f).cloned() {
            if sig.args.len() != arity {
                return Err(format!("`{f}` の引数は {} 個", sig.args.len()));
            }
            let args = sig.args.iter().map(|s| self.fixed(s)).collect();
            return Ok((args, self.fixed(&sig.res)));
        }
        if let Some((args, res)) = self.fn_vars.get(f).cloned() {
            if args.len() != arity {
                return Err(format!("`{f}` の引数の数が場所によって違う"));
            }
            return Ok((args, res));
        }
        if !self.allow_new {
            return Err(format!("関数記号 `{f}` が宣言されていない"));
        }
        let args: Vec<usize> = (0..arity).map(|_| self.node(None, false, Some(format!("fn:{f}")))).collect();
        let res = self.node(None, false, Some(format!("fn:{f}")));
        self.fn_vars.insert(f.to_string(), (args.clone(), res));
        Ok((args, res))
    }

    pub fn formula(&mut self, f: &Formula) -> SResult<()> {
        match f {
            Formula::Bot => Ok(()),
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                self.formula(a)?;
                self.formula(b)
            }
            Formula::Forall(x, s, b) | Formula::Exists(x, s, b) => {
                let n = if s == "?" {
                    self.node(None, false, Some(x.clone()))
                } else {
                    if num_rank(s).is_none() && !s.starts_with('\'') {
                        return Err(format!("`{x}` の型 `{s}` は使えない（ℕ・ℤ・ℚ・ℝ のどれか）"));
                    }
                    let i = self.fixed(s);
                    self.nodes[i].name = Some(x.clone());
                    i
                };
                self.binders.push(n);
                self.scope.push((x.clone(), n));
                let r = self.formula(b);
                self.scope.pop();
                r
            }
            Formula::Atom(r, ts) if r == "=" || ["<", "≤", ">", "≥"].contains(&r.as_str()) => {
                let [a, b] = ts.as_slice() else {
                    return Err(format!("`{r}` の引数は2つ"));
                };
                let (na, nb) = (self.term(a)?, self.term(b)?);
                self.unify(na, nb).map_err(|e| format!("`{a} {r} {b}`：{e}"))?;
                if r != "=" {
                    self.constrain_num(na, 0, &format!("`{r}`"))?;
                }
                Ok(())
            }
            Formula::Atom(r, _) if RELS.contains(&r.as_str()) => {
                Err(format!("関係 `{r}`（集合など）は v2.0 では使えない"))
            }
            Formula::Atom(p, ts) => {
                if let Some(d) = self.kenv.defs.get(p) {
                    let params = d.params.clone();
                    if params.len() != ts.len() {
                        return Err(format!("`{p}` の引数は {} 個", params.len()));
                    }
                    for ((_, s), t) in params.iter().zip(ts) {
                        self.def_arg(p, t, s)?;
                    }
                    return Ok(());
                }
                let nodes: Vec<usize> = if let Some(ss) = self.sig.preds.get(p).cloned() {
                    if ss.len() != ts.len() {
                        return Err(format!("`{p}` の引数は {} 個", ss.len()));
                    }
                    ss.iter().map(|s| self.fixed(s)).collect()
                } else if let Some(ns) = self.pred_vars.get(p).cloned() {
                    if ns.len() != ts.len() {
                        return Err(format!("`{p}` の引数の数が場所によって違う"));
                    }
                    ns
                } else if self.allow_new {
                    let ns: Vec<usize> = (0..ts.len()).map(|_| self.node(None, false, Some(format!("pred:{p}")))).collect();
                    self.pred_vars.insert(p.clone(), ns.clone());
                    ns
                } else {
                    return Err(format!("述語 `{p}` が宣言されていない"));
                };
                for (t, n) in ts.iter().zip(nodes) {
                    let m = self.term(t)?;
                    self.unify(n, m).map_err(|e| format!("`{p}` の引数：{e}"))?;
                }
                Ok(())
            }
        }
    }

    /// 定義の引数。関数型のパラメータには関数記号の名前を渡す。
    fn def_arg(&mut self, p: &str, t: &Term, s: &str) -> SResult<()> {
        if !is_fn_sort(s) {
            let n = self.term(t)?;
            let k = self.fixed(s);
            return self.unify(n, k).map_err(|e| format!("`{p}` の引数：{e}"));
        }
        let want = FnSig::parse(s).ok_or(format!("型 `{s}` が読めない"))?;
        let Term::Var(g) = t else {
            return Err(format!("`{p}` の {s} の引数には関数記号の名前だけを渡せる（`{t}` は v2.0 では渡せない）"));
        };
        let (args, res) = self.fn_symbol(g, want.args.len())?;
        for (n, w) in args.into_iter().zip(&want.args) {
            let k = self.fixed(w);
            self.unify(n, k).map_err(|e| format!("`{g}` の型：{e}"))?;
        }
        let k = self.fixed(&want.res);
        self.unify(res, k).map_err(|e| format!("`{g}` の型：{e}"))
    }

    /// 型を決める
    pub fn finish(mut self) -> SResult<Inferred> {
        let n = self.nodes.len();
        let root: Vec<usize> = (0..n).map(|i| self.find(i)).collect();
        let mut sorts = vec![String::new(); n];
        let mut params: Vec<String> = Vec::new();
        let mut param_of: HashMap<usize, String> = HashMap::new();
        for i in 0..n {
            if root[i] != i {
                continue;
            }
            let nd = &self.nodes[i];
            sorts[i] = match &nd.sort {
                Some(s) => s.clone(),
                None if nd.lit => NUM_SORTS[nd.rank as usize].to_string(),
                None if nd.numeric => {
                    let cand = NUM_SORTS[nd.rank as usize..].join("・");
                    return Err(match nd.name.as_deref() {
                        Some(n) if n.starts_with("fn:") => format!(
                            "関数記号 `{}` の型が決まらない（値は {cand} のどれか）。`{} : ℕ → ℝ` のように宣言する",
                            &n[3..],
                            &n[3..]
                        ),
                        Some(n) if n.starts_with("pred:") => format!(
                            "述語 `{}` の引数の型が決まらない（{cand} のどれか）。引数に使う変数の型を書く",
                            &n[5..]
                        ),
                        Some(n) => format!("`{n}` の型が決まらない（{cand} のどれか）。`{n} : ℝ` のように型を書く"),
                        None => format!("項の型が決まらない（{cand} のどれか）。変数の型を書く"),
                    });
                }
                None if self.statement => {
                    let p = format!("'{}", (b'a' + params.len() as u8) as char);
                    params.push(p.clone());
                    param_of.insert(i, p.clone());
                    p
                }
                None => {
                    let who = nd.name.clone().unwrap_or("項".into());
                    return Err(format!("`{who}` の型が決まらない。型を書く"));
                }
            };
        }
        let sort_of = |i: usize| sorts[root[i]].clone();
        let mut sig = self.sig.clone();
        for (f, (args, res)) in &self.fn_vars {
            sig.fns.insert(f.clone(), FnSig { args: args.iter().map(|&a| sort_of(a)).collect(), res: sort_of(*res) });
        }
        for (p, args) in &self.pred_vars {
            sig.preds.insert(p.clone(), args.iter().map(|&a| sort_of(a)).collect());
        }
        let free = self.free.iter().map(|(x, i)| (x.clone(), sort_of(*i))).collect();
        Ok(Inferred { sig, free, sort_params: params, sorts, binders: self.binders, root })
    }
}

impl Inferred {
    /// 推論した型を、論理式の束縛変数に書き込む（formula に渡したのと同じ順で呼ぶ）
    pub fn annotate(&self, f: &Formula, k: &mut usize) -> Formula {
        match f {
            Formula::Atom(..) | Formula::Bot => f.clone(),
            Formula::Imp(a, b) => {
                let a = self.annotate(a, k);
                Formula::Imp(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::And(a, b) => {
                let a = self.annotate(a, k);
                Formula::And(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::Or(a, b) => {
                let a = self.annotate(a, k);
                Formula::Or(Box::new(a), Box::new(self.annotate(b, k)))
            }
            Formula::Forall(x, _, b) | Formula::Exists(x, _, b) => {
                let s = self.sorts[self.root[self.binders[*k]]].clone();
                *k += 1;
                let b = Box::new(self.annotate(b, k));
                if matches!(f, Formula::Forall(..)) {
                    Formula::Forall(x.clone(), s, b)
                } else {
                    Formula::Exists(x.clone(), s, b)
                }
            }
        }
    }
}

/// 文脈の中の論理式 1 つの束縛変数の型を埋める（証明の中の have・assume など）。
/// 新しい局所記号が出てきたら sig に足す。
pub fn infer_formula(kenv: &KEnv, sig: &mut LocalSig, ctx: &[(String, String)], f: &Formula) -> SResult<Formula> {
    let mut inf = Infer::new(kenv, sig.clone(), ctx.to_vec(), false);
    inf.formula(f)?;
    let r = inf.finish()?;
    *sig = r.sig.clone();
    Ok(r.annotate(f, &mut 0))
}

/// 項の型（数字だけなら None）。elab がソートの具体化を決めるのに使う。
pub fn term_sort(kenv: &KEnv, sig: &LocalSig, ctx: &[(String, String)], t: &Term) -> Option<String> {
    let mut inf = Infer::new(kenv, sig.clone(), ctx.to_vec(), false);
    inf.allow_new = false;
    let n = inf.term(t).ok()?;
    let r = inf.find(n);
    let nd = &inf.nodes[r];
    if nd.lit { None } else { nd.sort.clone() }
}
