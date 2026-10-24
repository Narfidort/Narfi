//! 項・論理式の AST と、表示・代入・自由変数。

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::fmt;

/// 項。演算子も関数適用として表す（"+", "-", "·", "/", "^", "neg", "abs"）。
/// 関数適用の頭は名前（組み込みの演算・定義・関数型の変数）。λ を直接適用した形は持たない
/// （代入のときに β 簡約してしまう。`Term::subst` を参照）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Num(i64),
    App(String, Vec<Term>),
    /// 単一化用のメタ変数（ソースには現れない）
    Meta(u32),
    /// λ(x₁:σ₁, …). t（関数そのもの。型は正規形の文字列）
    Lam(Vec<(String, String)>, Box<Term>),
    /// {(x₁:σ₁, …) | φ}（述語・集合）
    Set(Vec<(String, String)>, Box<Formula>),
}

/// 論理式。¬φ は Imp(φ, Bot) で表す。範囲付き量化子は展開して持つ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    /// 関係（"=", "<", "≤", ">", "≥", "∈" 等）または述語の適用
    Atom(String, Vec<Term>),
    Imp(Box<Formula>, Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    /// 束縛変数名・型名（"?" は型が書かれていない）・本体
    Forall(String, String, Box<Formula>),
    Exists(String, String, Box<Formula>),
    Bot,
}

pub const RELS: [&str; 18] = [
    "=", "≠", "<", "≤", ">", "≥", "∈", "∉", "⊂", "⊆", "⊊", "⊃", "⊇", "≡", "≈", "∼", "≅", "∣",
];
pub const ORDER_RELS: [&str; 9] = ["<", "≤", ">", "≥", "∈", "⊂", "⊆", "⊃", "⊇"];

pub fn not(f: Formula) -> Formula {
    Formula::Imp(Box::new(f), Box::new(Formula::Bot))
}


// ---------------------------------------------------------------- 記法・定義の表
//
// notation は字句解析・構文解析・表示（Display / LaTeX）のすべてに効くので、
// スレッドごとの表に置く。読み込みの最初に reset_syntax() で空にする。

/// 略記（notation）：型紙 := 述語の適用。docs/language/syntax.md の「略記」。
///
/// `notation a → α (n → ∞) := is_lim((n : ℕ ↦ a), α)`
/// - 右辺の引数にある名前（a・α）が入る所、右辺の λ が束縛する名前（n）が束縛変数、それ以外は書いたとおりの記号。
/// - 式 `b_k → β (k → ∞)` は Atom("is_lim", [(k ↦ b_k), β]) になる（`(k ↦ b(k))` は b に縮める）。
#[derive(Clone, Debug)]
pub struct Notation {
    /// 右辺の述語・関数の名前
    pub pred: String,
    /// 命題になる略記（述語）か、値になる略記（関数）か
    pub kind: NKind,
    pub items: Vec<TItem>,
    /// 述語の引数ごとに、どの入る所から作るか
    pub args: Vec<NArg>,
    /// 束縛変数の、宣言に書いた名前（表示の既定）
    pub binders: Vec<String>,
    /// 入る所の名前（宣言に書いたもの）
    pub slots: Vec<String>,
    /// 宣言の型紙（エディタ・エラーの表示用）
    pub template: String,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum NKind {
    Pred,
    Func,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TItem {
    Lit(String),
    Slot(usize),
    Binder(usize),
}

#[derive(Clone, Debug, PartialEq)]
pub enum NArg {
    /// 入る所の式そのもの
    Slot(usize),
    /// (束縛変数 : 型 ↦ 入る所の式)
    Lam(usize, String, usize),
}

impl Notation {
    /// 型紙に当てはめた入る所・束縛変数から、述語の適用を作る
    pub fn build(&self, slots: &[Term], binders: &[String]) -> Formula {
        Formula::Atom(self.pred.clone(), self.build_args(slots, binders))
    }

    /// 値になる略記：関数の適用
    pub fn build_term(&self, slots: &[Term], binders: &[String]) -> Term {
        Term::App(self.pred.clone(), self.build_args(slots, binders))
    }

    fn build_args(&self, slots: &[Term], binders: &[String]) -> Vec<Term> {
        self.args
            .iter()
            .map(|a| match a {
                NArg::Slot(k) => slots[*k].clone(),
                NArg::Lam(b, sort, k) => lam_eta(&binders[*b], sort, &slots[*k]),
            })
            .collect()
    }

    /// 入る所 k が型紙の端（最初か最後）にあるか。値になる略記の端には 1 つのまとまりだけが入る
    pub fn slot_at_edge(&self, k: usize) -> bool {
        matches!(self.items.first(), Some(TItem::Slot(s)) if *s == k) || matches!(self.items.last(), Some(TItem::Slot(s)) if *s == k)
    }

    /// 表示：述語の引数 ts から、入る所の式と束縛変数の名前を取り出す
    pub fn split(&self, ts: &[Term]) -> Option<(Vec<Term>, Vec<String>)> {
        if ts.len() != self.args.len() {
            return None;
        }
        let mut slots: Vec<Option<Term>> = vec![None; self.slots.len()];
        let mut binders: Vec<Option<String>> = vec![None; self.binders.len()];
        // 束縛変数の名前：λ に書かれた名前を使う。なければ宣言の名前（ほかの引数に出てくるなら ' を付ける）
        let mut used = BTreeSet::new();
        for t in ts {
            t.vars(&mut used);
        }
        for (a, t) in self.args.iter().zip(ts) {
            if let (NArg::Lam(b, _, _), Term::Lam(ps, _)) = (a, t)
                && ps.len() == 1
                && binders[*b].is_none()
            {
                binders[*b] = Some(ps[0].0.clone());
            }
        }
        for (b, name) in binders.iter_mut().enumerate() {
            if name.is_none() {
                let mut x = self.binders[b].clone();
                while used.contains(&x) {
                    x.push('\'');
                }
                *name = Some(x);
            }
        }
        let binders: Vec<String> = binders.into_iter().map(|b| b.unwrap()).collect();
        for (a, t) in self.args.iter().zip(ts) {
            match a {
                NArg::Slot(k) => slots[*k] = Some(t.clone()),
                NArg::Lam(b, _, k) => {
                    let x = Term::Var(binders[*b].clone());
                    slots[*k] = Some(match t {
                        Term::Lam(ps, body) if ps.len() == 1 => body.subst(&ps[0].0, &x),
                        _ => apply_term(t, &[x]),
                    });
                }
            }
        }
        Some((slots.into_iter().map(|s| s.unwrap_or(Term::Var("?".into()))).collect(), binders))
    }

    /// 型紙の記号（名前の形でないもの。字句解析に登録する）
    pub fn symbols(&self) -> Vec<String> {
        self.items
            .iter()
            .filter_map(|i| match i {
                TItem::Lit(s) if !s.chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') => Some(s.clone()),
                _ => None,
            })
            .collect()
    }

    /// 型紙の記号の並び（あいまいさの検査に使う）
    pub fn lits(&self) -> Vec<String> {
        self.items
            .iter()
            .map(|i| match i {
                TItem::Lit(s) => s.clone(),
                TItem::Slot(_) => "\u{0}".into(),
                TItem::Binder(_) => "\u{1}".into(),
            })
            .collect()
    }

    /// 型紙で書いた文字列（表示）。show は入る所の式の書き方
    /// show は入る所の式の書き方（2 つ目の引数は、括弧が要るほど強く結びつく位置か）
    fn render(&self, ts: &[Term], show: &dyn Fn(&Term, u8) -> String, lit: &dyn Fn(&str) -> String, ident: &dyn Fn(&str) -> String) -> Option<String> {
        let (slots, binders) = self.split(ts)?;
        let mut out = String::new();
        // 下に添字の付く演算子（lim_( … )）は lim_{ … } と書く。closers は、その「(」に対応する括弧の深さ
        let mut depth = 0usize;
        let mut closers: Vec<usize> = vec![];
        let mut open_next = false;
        for it in &self.items {
            let piece = match it {
                TItem::Lit(s) if s.ends_with('_') && crate::parser::UNDER_OPS.contains(&&s[..s.len() - 1]) => {
                    open_next = true;
                    // 文字の表示でも \lim と書く（読み直したとき max_{i} が 1 つの名前 max_i にならないように）
                    let op = &s[..s.len() - 1];
                    let shown = lit(op);
                    if shown == op { format!("\\{op}_") } else { format!("{shown}_") }
                }
                TItem::Lit(s) if s == "(" && open_next => {
                    open_next = false;
                    depth += 1;
                    closers.push(depth);
                    "{".to_string()
                }
                TItem::Lit(s) if s == "(" => {
                    depth += 1;
                    lit(s)
                }
                TItem::Lit(s) if s == ")" => {
                    let close = closers.last() == Some(&depth);
                    depth = depth.saturating_sub(1);
                    if close {
                        closers.pop();
                        "}".to_string()
                    } else {
                        lit(s)
                    }
                }
                TItem::Lit(s) => lit(s),
                // 値になる略記の端の入る所は 1 つのまとまり（足し算・掛け算は括弧に入れる）
                TItem::Slot(k) => show(&slots[*k], if self.kind == NKind::Func && self.slot_at_edge(*k) { 5 } else { 0 }),
                TItem::Binder(b) => ident(&binders[*b]),
            };
            // 括弧・添字と、くっつけて書く記号（‖x‖・|x|・x²）の内側には空白を入れない
            let tight = |c: char| matches!(c, '‖' | '|' | '²' | '³' | '^');
            let glue = out.ends_with('(') || out.ends_with('[') || out.ends_with('_') || out.ends_with('{') || piece.starts_with(')') || piece.starts_with(']') || piece == "}" || piece == "_" || out.is_empty()
                || out.chars().last().is_some_and(tight) || piece.chars().next().is_some_and(tight)
                || piece.starts_with("\\Vert");
            if !glue {
                out.push(' ');
            }
            out.push_str(&piece);
        }
        Some(out)
    }
}

/// (x : σ ↦ t)。ただし t が「関数 f を x に適用しただけ」（f(x)・f_x）なら f に縮める（η。kernel は η を知らないため）
pub fn lam_eta(x: &str, sort: &str, t: &Term) -> Term {
    match t {
        Term::App(f, args) if args.len() == 1 && args[0] == Term::Var(x.to_string()) && f != x && f != "@" && !BUILTIN_FNS.contains(&f.as_str()) => Term::Var(f.clone()),
        Term::Var(v) if v.strip_suffix(x).and_then(|f| f.strip_suffix('_')).is_some_and(|f| !f.is_empty() && !f.contains('_')) => {
            Term::Var(v[..v.len() - x.len() - 1].to_string())
        }
        _ => Term::Lam(vec![(x.to_string(), sort.to_string())], Box::new(t.clone())),
    }
}

#[derive(Default)]
pub struct SyntaxTable {
    pub notations: Vec<Notation>,
    /// def で定義した述語の名前 → 引数の数
    pub defs: HashMap<String, usize>,
    /// そのうち値を返す関数（項の定義・rec）
    pub fns: BTreeSet<String>,
    /// ℕ を 1 つ受け取る const・def（添字で書ける列）
    pub seq_globals: BTreeSet<String>,
    /// 定義の本体に現れた述語（あとから同じ名前を def して循環させないため）
    pub def_preds: BTreeSet<String>,
    /// typedef で作った型・定数
    pub types: BTreeSet<String>,
    pub consts: BTreeSet<String>,
    /// 定理・定義の訳名（`@name ja "和の線形性"`）：名前 → (ロケール, 訳名)
    pub display_names: HashMap<String, Vec<(String, String)>>,
}

/// 定理・定義の、ロケール loc での訳名
pub fn display_name(name: &str, loc: &str) -> Option<String> {
    with_syntax(|t| t.display_names.get(name).and_then(|v| v.iter().find(|(l, _)| l == loc).map(|(_, n)| n.clone())))
}

/// 宣言の前に書く訳名の注釈（ソースの変換で書き戻す）
pub fn display_name_lines(name: &str) -> String {
    with_syntax(|t| {
        t.display_names
            .get(name)
            .map(|v| v.iter().map(|(l, n)| format!("@name {l} {n:?}\n")).collect::<String>())
            .unwrap_or_default()
    })
}

thread_local! {
    static SYNTAX: RefCell<SyntaxTable> = RefCell::new(SyntaxTable::default());
}

pub fn reset_syntax() {
    SYNTAX.with(|t| *t.borrow_mut() = SyntaxTable::default());
}

pub fn with_syntax<R>(f: impl FnOnce(&mut SyntaxTable) -> R) -> R {
    SYNTAX.with(|t| f(&mut t.borrow_mut()))
}

/// 型紙の文字を表示に使う形（LaTeX）
pub fn lit_latex(s: &str) -> String {
    match s {
        "→" => "\\to".into(),
        "⟶" => "\\longrightarrow".into(),
        "∞" => "\\infty".into(),
        "~" => "\\sim".into(),
        "∪" => "\\cup".into(),
        "∩" => "\\cap".into(),
        "∖" => "\\setminus".into(),
        "∁" => "\\complement".into(),
        "‖" => "\\Vert ".into(),
        "²" => "^{2}".into(),
        "³" => "^{3}".into(),
        "⇝" => "\\rightsquigarrow".into(),
        "≺" => "\\prec".into(),
        "≻" => "\\succ".into(),
        "≼" => "\\preceq".into(),
        "≽" => "\\succeq".into(),
        "(" | ")" | "[" | "]" | "," | "|" => s.into(),
        _ if crate::parser::UNDER_OPS.contains(&s) => format!("\\{s}"),
        _ if s.chars().all(|c| c.is_alphabetic()) && s.chars().count() > 1 => format!("\\mathrm{{{s}}}"),
        _ => ident_to_latex(s),
    }
}

/// 表示に使う記法（同じ述語に複数あるときは最初に宣言したもの）
pub fn notation_for_pred(pred: &str) -> Option<Notation> {
    with_syntax(|t| t.notations.iter().find(|n| n.pred == pred && n.kind == NKind::Pred).cloned())
}

/// 値になる略記で、表示に使うもの（関数 f に複数あるときは最初に宣言したもの）
pub fn notation_for_fn(f: &str) -> Option<Notation> {
    with_syntax(|t| t.notations.iter().find(|n| n.pred == f && n.kind == NKind::Func).cloned())
}

// ---------------------------------------------------------------- 定義・図式の具体化

/// 定義・図式のパラメータ params に args を同時に代入する（関数型・述語型のパラメータに
/// λ や集合を入れたときは、その場で β 簡約する）。
pub fn instantiate(params: &[(String, String)], body: &Formula, args: &[Term]) -> Formula {
    let subs: Vec<(String, Term)> = params.iter().map(|(p, _)| p.clone()).zip(args.iter().cloned()).collect();
    body.subst_many(&subs)
}

/// 組み込みの関数記号（自由変数として数えない）
pub const BUILTIN_FNS: [&str; 11] = ["+", "-", "·", "/", "neg", "abs", "^", "S", "max", "min", "some"];

fn is_builtin_head(f: &str) -> bool {
    BUILTIN_FNS.contains(&f)
}

fn is_builtin_rel(p: &str) -> bool {
    RELS.contains(&p)
}

// 同時代入の仮の変数名（%1, %2, …）。呼び出しのたびに新しい名前を使う。
// 使い回すと、代入の途中で束縛変数の付け替えのために内側でもう一度同時代入をしたとき、
// 外側の仮の変数と内側の仮の変数が混ざってしまう（v2.1 で実際にあった健全性のバグ）。
thread_local! {
    static PLACEHOLDER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn placeholder() -> String {
    PLACEHOLDER.with(|c| {
        c.set(c.get() + 1);
        format!("%{}", c.get())
    })
}

// 添字で書く数列の名前（show_term_sub の間だけ。a(n) を a_n と書く）
thread_local! {
    static SUB_SEQS: RefCell<BTreeSet<String>> = const { RefCell::new(BTreeSet::new()) };
}

/// 1 文字の名前で、引数 1 つに適用されているもの（略記の表示で a(n) を a_n と書くため）
fn applied_names(ts: &[Term]) -> BTreeSet<String> {
    fn go(t: &Term, out: &mut BTreeSet<String>) {
        match t {
            Term::App(f, args) => {
                if args.len() == 1 && f.chars().count() == 1 {
                    out.insert(f.clone());
                }
                args.iter().for_each(|a| go(a, out));
            }
            Term::Lam(_, b) => go(b, out),
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    ts.iter().for_each(|t| go(t, &mut out));
    out
}

/// 以後の表示で、seqs の適用を添字（a_n）で書く（検査中の文脈の数列）
pub fn set_sub_seqs(seqs: BTreeSet<String>) {
    SUB_SEQS.with(|s| *s.borrow_mut() = seqs);
}

/// seqs の適用を添字で書いて f を実行する
pub fn with_sub_seqs<R>(seqs: &BTreeSet<String>, f: impl FnOnce() -> R) -> R {
    let before = SUB_SEQS.with(|s| std::mem::replace(&mut *s.borrow_mut(), seqs.clone()));
    let out = f();
    SUB_SEQS.with(|s| *s.borrow_mut() = before);
    out
}

/// 項を、数列 seqs の適用を添字（a_n・a_{n+1}）にして書く（エディタに入れる形）
pub fn show_term_sub(t: &Term, seqs: &BTreeSet<String>) -> String {
    show_term_sub_prec(t, seqs, 0)
}

fn show_term_sub_prec(t: &Term, seqs: &BTreeSet<String>, prec: u8) -> String {
    let before = SUB_SEQS.with(|s| std::mem::replace(&mut *s.borrow_mut(), seqs.clone()));
    let out = show_term(t, prec);
    SUB_SEQS.with(|s| *s.borrow_mut() = before);
    out
}

// β 簡約が止まらない（型の合わない項を代入した）ときに、無限ループではなく止めるための深さ
thread_local! {
    static BETA_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

fn with_beta<R>(f: impl FnOnce() -> R) -> R {
    BETA_DEPTH.with(|d| {
        d.set(d.get() + 1);
        assert!(d.get() < 4000, "β 簡約が止まらない（型の合わない項を代入している）");
    });
    let r = f();
    BETA_DEPTH.with(|d| d.set(d.get() - 1));
    r
}

/// t(args)：t が名前なら適用、λ なら β 簡約
pub fn apply_term(t: &Term, args: &[Term]) -> Term {
    match t {
        Term::Var(g) => Term::App(g.clone(), args.to_vec()),
        Term::Lam(ps, body) if ps.len() == args.len() => with_beta(|| {
            let subs: Vec<(String, Term)> = ps.iter().map(|(p, _)| p.clone()).zip(args.iter().cloned()).collect();
            body.subst_many(&subs)
        }),
        // 型の合わない適用（kernel の型検査で止まる）
        _ => {
            let mut v = vec![t.clone()];
            v.extend(args.iter().cloned());
            Term::App("@".into(), v)
        }
    }
}

/// P(args)：P が名前なら述語の適用、集合 {x | φ} なら φ[x := args]
pub fn holds(t: &Term, args: &[Term]) -> Formula {
    match t {
        Term::Var(q) => Formula::Atom(q.clone(), args.to_vec()),
        Term::Set(ps, phi) if ps.len() == args.len() => with_beta(|| {
            let subs: Vec<(String, Term)> = ps.iter().map(|(p, _)| p.clone()).zip(args.iter().cloned()).collect();
            phi.subst_many(&subs)
        }),
        _ => {
            let mut v = vec![t.clone()];
            v.extend(args.iter().cloned());
            Formula::Atom("@".into(), v)
        }
    }
}

/// 束縛変数 ps のもとで x := t を代入するとき、t の自由変数を捕まえないよう ps の名前を付け替える。
/// 付け替えた名前の組と、本体に施す付け替え（旧名 → 新名）を返す。
fn avoid_capture(ps: &[(String, String)], t: &Term, body_fv: &BTreeSet<String>) -> (Vec<(String, String)>, Vec<(String, Term)>) {
    let mut tv = BTreeSet::new();
    t.vars(&mut tv);
    let mut new_ps = Vec::new();
    let mut ren = Vec::new();
    for (p, ty) in ps {
        if tv.contains(p) {
            let mut fresh = format!("{p}'");
            while tv.contains(&fresh) || body_fv.contains(&fresh) || ps.iter().any(|(q, _)| *q == fresh) {
                fresh.push('\'');
            }
            ren.push((p.clone(), Term::Var(fresh.clone())));
            new_ps.push((fresh, ty.clone()));
        } else {
            new_ps.push((p.clone(), ty.clone()));
        }
    }
    (new_ps, ren)
}

// ---------------------------------------------------------------- 自由変数・代入

impl Term {
    /// 自由変数（関数型の変数として使われた適用の頭も含む。組み込みの演算は含まない）
    pub fn vars(&self, out: &mut BTreeSet<String>) {
        self.vars_in(out, &mut Vec::new());
    }

    fn vars_in(&self, out: &mut BTreeSet<String>, bound: &mut Vec<String>) {
        match self {
            Term::Var(x) => {
                if !bound.contains(x) {
                    out.insert(x.clone());
                }
            }
            Term::App(f, args) => {
                if !is_builtin_head(f) && !bound.contains(f) && f != "@" {
                    out.insert(f.clone());
                }
                args.iter().for_each(|a| a.vars_in(out, bound));
            }
            Term::Lam(ps, body) => {
                let n = bound.len();
                bound.extend(ps.iter().map(|(p, _)| p.clone()));
                body.vars_in(out, bound);
                bound.truncate(n);
            }
            Term::Set(ps, phi) => {
                let n = bound.len();
                bound.extend(ps.iter().map(|(p, _)| p.clone()));
                phi.fv_into(out, bound);
                bound.truncate(n);
            }
            Term::Num(_) | Term::Meta(_) => {}
        }
    }

    pub fn has_meta(&self) -> bool {
        match self {
            Term::Meta(_) => true,
            Term::App(_, args) => args.iter().any(|a| a.has_meta()),
            Term::Lam(_, b) => b.has_meta(),
            Term::Set(_, phi) => phi.has_meta(),
            _ => false,
        }
    }

    pub fn mentions(&self, x: &str) -> bool {
        let mut vs = BTreeSet::new();
        self.vars(&mut vs);
        vs.contains(x)
    }

    /// 捕獲を避ける代入 t[x := u]。x が関数として適用されていて u が λ なら β 簡約する（遺伝的代入）。
    pub fn subst(&self, x: &str, u: &Term) -> Term {
        match self {
            Term::Var(y) if y == x => u.clone(),
            Term::App(f, args) => {
                let args: Vec<Term> = args.iter().map(|a| a.subst(x, u)).collect();
                if f == x {
                    apply_term(u, &args)
                } else if f == "@" && !args.is_empty() {
                    // 一般の適用 @(t, s…)：t が名前・λ になったら普通の適用・β 簡約に戻す
                    apply_term(&args[0], &args[1..])
                } else {
                    Term::App(f.clone(), args)
                }
            }
            Term::Lam(ps, body) => {
                if ps.iter().any(|(p, _)| p == x) {
                    return self.clone();
                }
                let mut fv = BTreeSet::new();
                body.vars(&mut fv);
                let (ps2, ren) = avoid_capture(ps, u, &fv);
                let body = if ren.is_empty() { (**body).clone() } else { body.subst_many(&ren) };
                Term::Lam(ps2, Box::new(body.subst(x, u)))
            }
            Term::Set(ps, phi) => {
                if ps.iter().any(|(p, _)| p == x) {
                    return self.clone();
                }
                let fv = phi.free_vars();
                let (ps2, ren) = avoid_capture(ps, u, &fv);
                let phi = if ren.is_empty() { (**phi).clone() } else { phi.subst_many(&ren) };
                Term::Set(ps2, Box::new(phi.subst(x, u)))
            }
            _ => self.clone(),
        }
    }

    /// 同時代入
    pub fn subst_many(&self, subs: &[(String, Term)]) -> Term {
        let tmp: Vec<String> = subs.iter().map(|_| placeholder()).collect();
        let mut t = self.clone();
        for ((x, _), p) in subs.iter().zip(&tmp) {
            t = t.subst(x, &Term::Var(p.clone()));
        }
        for ((_, u), p) in subs.iter().zip(&tmp) {
            t = t.subst(p, u);
        }
        t
    }

    pub fn map_sorts(&self, g: &impl Fn(&str) -> String) -> Term {
        match self {
            Term::App(f, args) => Term::App(f.clone(), args.iter().map(|a| a.map_sorts(g)).collect()),
            Term::Lam(ps, b) => Term::Lam(ps.iter().map(|(p, t)| (p.clone(), g(t))).collect(), Box::new(b.map_sorts(g))),
            Term::Set(ps, phi) => Term::Set(ps.iter().map(|(p, t)| (p.clone(), g(t))).collect(), Box::new(phi.map_sorts(g))),
            _ => self.clone(),
        }
    }

    /// 束縛変数の名前を位置で決まる名前に付け替えたもの（α 同値なら同じになる）
    pub fn canonical(&self) -> Term {
        self.canon_in(&mut 0)
    }

    fn canon_in(&self, k: &mut usize) -> Term {
        match self {
            Term::App(f, args) => Term::App(f.clone(), args.iter().map(|a| a.canon_in(k)).collect()),
            Term::Lam(ps, b) => {
                let mut ren = Vec::new();
                let mut ps2 = Vec::new();
                for (p, t) in ps {
                    let v = format!("#c{k}");
                    *k += 1;
                    ren.push((p.clone(), Term::Var(v.clone())));
                    ps2.push((v, t.clone()));
                }
                Term::Lam(ps2, Box::new(b.subst_many(&ren).canon_in(k)))
            }
            Term::Set(ps, phi) => {
                let mut ren = Vec::new();
                let mut ps2 = Vec::new();
                for (p, t) in ps {
                    let v = format!("#c{k}");
                    *k += 1;
                    ren.push((p.clone(), Term::Var(v.clone())));
                    ps2.push((v, t.clone()));
                }
                Term::Set(ps2, Box::new(phi.subst_many(&ren).canon_in(k)))
            }
            _ => self.clone(),
        }
    }

    pub fn to_latex(&self) -> String {
        show_term_latex(self, 0)
    }
}

impl Formula {
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.fv_into(&mut out, &mut Vec::new());
        out
    }

    fn fv_into(&self, out: &mut BTreeSet<String>, bound: &mut Vec<String>) {
        match self {
            Formula::Atom(p, ts) => {
                if !is_builtin_rel(p) && !bound.contains(p) && p != "@" {
                    out.insert(p.clone());
                }
                ts.iter().for_each(|t| t.vars_in(out, bound));
            }
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                a.fv_into(out, bound);
                b.fv_into(out, bound);
            }
            Formula::Forall(x, _, b) | Formula::Exists(x, _, b) => {
                bound.push(x.clone());
                b.fv_into(out, bound);
                bound.pop();
            }
            Formula::Bot => {}
        }
    }

    pub fn has_meta(&self) -> bool {
        match self {
            Formula::Atom(_, ts) => ts.iter().any(|t| t.has_meta()),
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => a.has_meta() || b.has_meta(),
            Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => b.has_meta(),
            Formula::Bot => false,
        }
    }

    /// 捕獲を避ける代入 φ[x := t]。x が述語として使われていて t が集合なら β 簡約する。
    pub fn subst(&self, x: &str, t: &Term) -> Formula {
        match self {
            Formula::Atom(p, ts) => {
                let ts: Vec<Term> = ts.iter().map(|s| s.subst(x, t)).collect();
                if p == x {
                    holds(t, &ts)
                } else if p == "@" && !ts.is_empty() {
                    holds(&ts[0], &ts[1..])
                } else {
                    Formula::Atom(p.clone(), ts)
                }
            }
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::And(a, b) => Formula::And(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.subst(x, t)), Box::new(b.subst(x, t))),
            Formula::Forall(y, ty, b) | Formula::Exists(y, ty, b) => {
                let is_all = matches!(self, Formula::Forall(..));
                let mk = |v: String, body: Formula| {
                    if is_all {
                        Formula::Forall(v, ty.clone(), Box::new(body))
                    } else {
                        Formula::Exists(v, ty.clone(), Box::new(body))
                    }
                };
                if y == x {
                    return self.clone();
                }
                if t.mentions(y) {
                    let mut avoid = b.free_vars();
                    t.vars(&mut avoid);
                    let mut fresh = format!("{y}'");
                    while avoid.contains(&fresh) {
                        fresh.push('\'');
                    }
                    let body = b.subst(y, &Term::Var(fresh.clone()));
                    mk(fresh, body.subst(x, t))
                } else {
                    mk(y.clone(), b.subst(x, t))
                }
            }
            Formula::Bot => Formula::Bot,
        }
    }

    pub fn to_latex(&self) -> String {
        show_formula_latex(self, 0)
    }

    /// 束縛変数・λ・集合の型を書き換える（図式の型変数の具体化など）
    pub fn map_sorts(&self, g: &impl Fn(&str) -> String) -> Formula {
        match self {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| t.map_sorts(g)).collect()),
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::And(a, b) => Formula::And(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.map_sorts(g)), Box::new(b.map_sorts(g))),
            Formula::Forall(x, t, b) => Formula::Forall(x.clone(), g(t), Box::new(b.map_sorts(g))),
            Formula::Exists(x, t, b) => Formula::Exists(x.clone(), g(t), Box::new(b.map_sorts(g))),
        }
    }

    /// 同時代入 φ[x₁ := t₁, …]（tᵢ の中の変数が xⱼ と同じ名前でも混ざらない）
    pub fn subst_many(&self, subs: &[(String, Term)]) -> Formula {
        let tmp: Vec<String> = subs.iter().map(|_| placeholder()).collect();
        let mut f = self.clone();
        for ((x, _), p) in subs.iter().zip(&tmp) {
            f = f.subst(x, &Term::Var(p.clone()));
        }
        for ((_, t), p) in subs.iter().zip(&tmp) {
            f = f.subst(p, t);
        }
        f
    }

    fn canon_in(&self, k: &mut usize) -> Formula {
        match self {
            Formula::Atom(p, ts) => Formula::Atom(p.clone(), ts.iter().map(|t| t.canon_in(k)).collect()),
            Formula::Bot => Formula::Bot,
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.canon_in(k)), Box::new(b.canon_in(k))),
            Formula::And(a, b) => Formula::And(Box::new(a.canon_in(k)), Box::new(b.canon_in(k))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.canon_in(k)), Box::new(b.canon_in(k))),
            Formula::Forall(x, t, b) | Formula::Exists(x, t, b) => {
                let v = format!("#c{k}");
                *k += 1;
                let body = Box::new(b.subst(x, &Term::Var(v.clone())).canon_in(k));
                if matches!(self, Formula::Forall(..)) {
                    Formula::Forall(v, t.clone(), body)
                } else {
                    Formula::Exists(v, t.clone(), body)
                }
            }
        }
    }

    /// 現れる述語の名前
    pub fn preds(&self, out: &mut BTreeSet<String>) {
        match self {
            Formula::Atom(p, _) => {
                out.insert(p.clone());
            }
            Formula::Imp(a, b) | Formula::And(a, b) | Formula::Or(a, b) => {
                a.preds(out);
                b.preds(out);
            }
            Formula::Forall(_, _, b) | Formula::Exists(_, _, b) => b.preds(out),
            Formula::Bot => {}
        }
    }
}

// ---------------------------------------------------------------- 表示

fn binder_names(ps: &[(String, String)]) -> String {
    if ps.len() == 1 {
        ps[0].0.clone()
    } else {
        format!("({})", ps.iter().map(|(p, _)| p.as_str()).collect::<Vec<_>>().join(", "))
    }
}

/// `x : ℕ` / `(x, y) : ℕ × ℕ`（型が表示しないものなら名前だけ）
fn binder_typed(ps: &[(String, String)]) -> String {
    if ps.iter().any(|(_, t)| hidden_sort(t)) {
        return binder_names(ps);
    }
    let ts: Vec<&str> = ps.iter().map(|(_, t)| t.as_str()).collect();
    format!("{} : {}", binder_names(ps), ts.join(" × "))
}

pub fn show_term(t: &Term, prec: u8) -> String {
    match t {
        Term::Var(x) => x.clone(),
        Term::Num(n) => n.to_string(),
        Term::Meta(m) => format!("?{m}"),
        Term::Lam(ps, b) => format!("({} ↦ {})", binder_typed(ps), show_term(b, 0)),
        Term::App(f, args) if f == "@" && !args.is_empty() => {
            let a: Vec<String> = args[1..].iter().map(|a| show_term(a, 0)).collect();
            format!("{}({})", show_term(&args[0], 5), a.join(", "))
        }
        Term::Set(ps, phi) => format!("{{{} | {}}}", binder_typed(ps), show_formula(phi, 0)),
        Term::App(f, args) if notation_for_fn(f).and_then(|n| n.split(args)).is_some() => {
            let n = notation_for_fn(f).unwrap();
            let seqs = applied_names(&n.split(args).unwrap().0);
            let s = n.render(args, &|t, p| show_term_sub_prec(t, &seqs, p), &|l| l.to_string(), &|x| x.to_string()).unwrap();
            if prec > 4 { format!("({s})") } else { s }
        }
        Term::App(f, args) => {
            let (s, p) = match (f.as_str(), args.as_slice()) {
                ("+" | "-", [a, b]) => {
                    (format!("{} {} {}", show_term(a, 1), f, show_term(b, 2)), 1)
                }
                ("·", [a, b]) => (format!("{}·{}", show_term(a, 2), show_term(b, 3)), 2),
                ("/", [a, b]) => (format!("{}/{}", show_term(a, 2), show_term(b, 3)), 2),
                ("neg", [a]) => (format!("-{}", show_term(a, 3)), 3),
                ("^", [a, Term::Num(2)]) => (format!("{}²", show_term(a, 5)), 4),
                ("^", [a, b]) => (format!("{}^{}", show_term(a, 5), show_term(b, 5)), 4),
                // 行列 [[a, b], [c, d]]
                (m @ ("mat2" | "mat3"), xs) if xs.len() == if m == "mat2" { 4 } else { 9 } => {
                    let n = if m == "mat2" { 2 } else { 3 };
                    let rows: Vec<String> = xs
                        .chunks(n)
                        .map(|r| format!("[{}]", r.iter().map(|x| show_term(x, 0)).collect::<Vec<_>>().join(", ")))
                        .collect();
                    (format!("[{}]", rows.join(", ")), 9)
                }
                ("max" | "min", [a, b]) => (format!("{f}{{{}, {}}}", show_term(a, 0), show_term(b, 0)), 5),
                ("abs", [a]) => {
                    // `|-x|` は `|-`（⊢）と読まれるので、空白を入れて `| -x|` と書く
                    let inner = show_term(a, 0);
                    let sep = if inner.starts_with('-') { " " } else { "" };
                    (format!("|{sep}{inner}|"), 5)
                }
                (_, [a]) if SUB_SEQS.with(|s| s.borrow().contains(f)) || with_syntax(|t| t.seq_globals.contains(f)) => match a {
                    Term::Var(x) if x.chars().count() == 1 => (format!("{f}_{x}"), 5),
                    Term::Num(n) if *n < 10 => (format!("{f}_{n}"), 5),
                    _ => (format!("{f}_{{{}}}", show_term(a, 0)), 5),
                },
                _ => {
                    let a: Vec<String> = args.iter().map(|a| show_term(a, 0)).collect();
                    (format!("{}({})", f, a.join(", ")), 5)
                }
            };
            if p < prec { format!("({s})") } else { s }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_term(self, 0))
    }
}

/// 範囲付き量化子の形 ∀x>t. φ / ∃x>t. φ を取り出す
pub fn bounded(x: &str, guard: &Formula) -> Option<(String, Term)> {
    if let Formula::Atom(r, ts) = guard {
        if ORDER_RELS.contains(&r.as_str())
            && ts.len() == 2
            && ts[0] == Term::Var(x.to_string())
            && !ts[1].mentions(x)
        {
            return Some((r.clone(), ts[1].clone()));
        }
    }
    None
}

/// 表示しない型：書かれていない型（?）・ソート変数（'a）・推論途中の型（?σ1）
fn hidden_sort(ty: &str) -> bool {
    ty == "?" || ty.starts_with('\'') || ty.starts_with("?σ")
}

/// `x` か `x:ℝ`（書かれた型は表示に残す。ソースに書き戻しても同じ型になるように）
fn typed_name(x: &str, ty: &str) -> String {
    if hidden_sort(ty) { x.to_string() } else { format!("{x}:{ty}") }
}

fn binder(q: &str, x: &str, ty: &str) -> String {
    if hidden_sort(ty) {
        format!("{q}{x}")
    } else {
        format!("{q}{x}:{ty}")
    }
}

/// (a ⇒ b) ∧ (b ⇒ a) を a ⇔ b として表示するための (a, b)
fn iff_parts(f: &Formula) -> Option<(&Formula, &Formula)> {
    match f {
        Formula::And(x, y) => match (&**x, &**y) {
            (Formula::Imp(a, b), Formula::Imp(c, d)) if a == d && b == c && **b != Formula::Bot && **a != Formula::Bot => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

pub fn show_formula(f: &Formula, prec: u8) -> String {
    let (s, p) = match f {
        Formula::Bot => ("⊥".to_string(), 5),
        Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => (
            format!("{} {} {}", show_term(&ts[0], 0), r, show_term(&ts[1], 0)),
            5,
        ),
        Formula::Atom(p, ts) if ts.is_empty() => (p.clone(), 5),
        // 式で表した集合への所属は x ∈ S（定義の所属 S(x) と同じ。紙の書き方）
        Formula::Atom(p, ts) if p == "@" && ts.len() == 2 && !matches!(ts[0], Term::Var(_)) => {
            (format!("{} ∈ {}", show_term(&ts[1], 0), show_term(&ts[0], 0)), 5)
        }
        Formula::Atom(p, ts) if p == "@" => {
            let a: Vec<String> = ts[1..].iter().map(|t| show_term(t, 0)).collect();
            (format!("{}({})", show_term(&ts[0], 5), a.join(", ")), 5)
        }
        Formula::Atom(p, ts) if notation_for_pred(p).and_then(|n| n.split(ts)).is_some() => {
            let n = notation_for_pred(p).unwrap();
            let seqs = applied_names(&n.split(ts).unwrap().0);
            let shown = n.render(ts, &|t, p| show_term_sub_prec(t, &seqs, p), &|l| l.to_string(), &|x| x.to_string()).unwrap();
            (shown, 5)
        }
        Formula::Atom(p, ts) => {
            let a: Vec<String> = ts.iter().map(|t| show_term(t, 0)).collect();
            (format!("{}({})", p, a.join(", ")), 5)
        }
        Formula::Imp(a, b) if **b == Formula::Bot => match &**a {
            Formula::Atom(r, ts) if r == "=" && ts.len() == 2 => (
                format!("{} ≠ {}", show_term(&ts[0], 0), show_term(&ts[1], 0)),
                5,
            ),
            // 関係は括弧に入れる（¬k < n は (¬k) < n と読める）
            Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => (format!("¬({})", show_formula(a, 0)), 4),
            _ => (format!("¬{}", show_formula(a, 4)), 4),
        },
        Formula::Imp(a, b) => (
            format!("{} ⇒ {}", show_formula(a, 2), show_formula(b, 1)),
            1,
        ),
        Formula::Or(a, b) => (
            format!("{} ∨ {}", show_formula(a, 2), show_formula(b, 3)),
            2,
        ),
        Formula::And(..) if iff_parts(f).is_some() => {
            let (a, b) = iff_parts(f).unwrap();
            (format!("{} ⇔ {}", show_formula(a, 1), show_formula(b, 1)), 0)
        }
        Formula::And(a, b) => (
            format!("{} ∧ {}", show_formula(a, 3), show_formula(b, 4)),
            3,
        ),
        Formula::Forall(x, ty, b) => {
            if let Formula::Imp(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!("∀{}{}{}. {}", typed_name(x, ty), r, show_term(&t, 0), show_formula(body, 0));
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (format!("{}. {}", binder("∀", x, ty), show_formula(b, 0)), 0)
        }
        Formula::Exists(x, ty, b) => {
            if let Formula::And(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!("∃{}{}{}. {}", typed_name(x, ty), r, show_term(&t, 0), show_formula(body, 0));
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (format!("{}. {}", binder("∃", x, ty), show_formula(b, 0)), 0)
        }
    };
    if p < prec { format!("({s})") } else { s }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_formula(self, 0))
    }
}

// ---------------------------------------------------------------- LaTeX 表示

fn greek_char_to_latex(c: char) -> Option<&'static str> {
    Some(match c {
        'α' => "\\alpha",
        'β' => "\\beta",
        'γ' => "\\gamma",
        'δ' => "\\delta",
        'ε' => "\\varepsilon",
        'ζ' => "\\zeta",
        'η' => "\\eta",
        'θ' => "\\theta",
        'ι' => "\\iota",
        'κ' => "\\kappa",
        'λ' => "\\lambda",
        'μ' => "\\mu",
        'ν' => "\\nu",
        'ξ' => "\\xi",
        'π' => "\\pi",
        'ρ' => "\\rho",
        'σ' => "\\sigma",
        'τ' => "\\tau",
        'υ' => "\\upsilon",
        'φ' => "\\varphi",
        'χ' => "\\chi",
        'ψ' => "\\psi",
        'ω' => "\\omega",
        'Γ' => "\\Gamma",
        'Δ' => "\\Delta",
        'Θ' => "\\Theta",
        'Λ' => "\\Lambda",
        'Ξ' => "\\Xi",
        'Π' => "\\Pi",
        'Σ' => "\\Sigma",
        'Υ' => "\\Upsilon",
        'Φ' => "\\Phi",
        'Ψ' => "\\Psi",
        'Ω' => "\\Omega",
        '∞' => "\\infty",
        '∅' => "\\emptyset",
        '∂' => "\\partial",
        '∇' => "\\nabla",
        _ => return None,
    })
}

pub fn ident_to_latex(s: &str) -> String {
    match s {
        "ℕ" => "\\mathbb{N}".to_string(),
        "ℤ" => "\\mathbb{Z}".to_string(),
        "ℚ" => "\\mathbb{Q}".to_string(),
        "ℝ" => "\\mathbb{R}".to_string(),
        "ℂ" => "\\mathbb{C}".to_string(),
        "𝔽" => "\\mathbb{F}".to_string(),
        "ℙ" => "\\mathbb{P}".to_string(),
        "Prop" => "\\mathrm{Prop}".to_string(),
        "max" => "\\max".to_string(),
        "min" => "\\min".to_string(),
        "sup" => "\\sup".to_string(),
        "inf" => "\\inf".to_string(),
        "sin" => "\\sin".to_string(),
        "cos" => "\\cos".to_string(),
        "tan" => "\\tan".to_string(),
        "exp" => "\\exp".to_string(),
        "log" => "\\log".to_string(),
        "ln" => "\\ln".to_string(),
        "gcd" => "\\gcd".to_string(),
        "det" => "\\det".to_string(),
        "dim" => "\\dim".to_string(),
        "ker" => "\\ker".to_string(),
        _ => {
            let cs: Vec<char> = s.chars().collect();
            // ギリシャ文字1文字
            if cs.len() == 1 {
                if let Some(gl) = greek_char_to_latex(cs[0]) {
                    return gl.to_string();
                }
                return s.to_string();
            }
            // ギリシャ文字 + 数字添字 (例: δ₁ -> \delta_{1})
            if cs.len() >= 2 && greek_char_to_latex(cs[0]).is_some() && cs[1..].iter().all(|c| ('₀'..='₉').contains(c)) {
                let ds: String = cs[1..].iter().map(|c| ((*c as u32 - '₀' as u32) as u8 + b'0') as char).collect();
                return format!("{}_{{{ds}}}", greek_char_to_latex(cs[0]).unwrap());
            }
            // 1文字英字 + 数字添字 (例: N₁, a₂, x₀)
            if cs.len() == 2 && cs[0].is_ascii_alphabetic() && ('₀'..='₉').contains(&cs[1]) {
                let d = (cs[1] as u32 - '₀' as u32) as u8 + b'0';
                return format!("{}_{{{}}}", cs[0], d as char);
            }
            // h + ギリシャ文字 (例: hε)
            if cs.len() == 2 && cs[0] == 'h' {
                if let Some(gl) = greek_char_to_latex(cs[1]) {
                    return format!("h_{{{gl}}}");
                }
                if cs[1].is_ascii_alphabetic() {
                    return format!("h_{{{}}}", cs[1]);
                }
            }
            // 仮定の名前 h + 変数（hδ₁・hN₂・hx₀）-> h_{\delta_{1}}（添字を 2 重にしない）
            if cs.len() >= 3
                && cs[0] == 'h'
                && (cs[1].is_alphabetic() && !cs[1].is_ascii_lowercase() || cs[1].is_ascii_alphabetic())
                && cs[2..].iter().all(|c| ('₀'..='₉').contains(c))
            {
                return format!("h_{{{}}}", ident_to_latex(&cs[1..].iter().collect::<String>()));
            }
            // hN₁ -> h_{N_1}
            if cs.len() == 3 && s.starts_with("hN") && ('₀'..='₉').contains(&cs[2]) {
                let d = (cs[2] as u32 - '₀' as u32) as u8 + b'0';
                return format!("h_{{N_{}}}", d as char);
            }
            // h.left・h.right（∧ の取り出し）：h は変数として、.left は立体で
            if let Some((head, field)) = s.rsplit_once('.') {
                if (field == "left" || field == "right") && !head.contains('.') && !head.is_empty() {
                    return format!("{}.\\mathrm{{{field}}}", ident_to_latex(head));
                }
            }
            // ドットを含む識別子 (例: ge.max.left)
            if s.contains('.') {
                return format!("\\mathrm{{{}}}", s);
            }
            // アンダースコアを含む識別子 (例: conv_a -> \mathrm{conv}_{a}, pos_half -> \mathrm{pos\_half})
            if let Some((p, rest)) = s.split_once('_') {
                if p.len() > 1 && p.chars().all(|c| c.is_ascii_alphabetic()) {
                    if rest.len() == 1 {
                        return format!("\\mathrm{{{}}}_{{{}}}", p, rest);
                    } else {
                        return format!("\\mathrm{{{}}}", s.replace('_', "\\_"));
                    }
                }
                return format!("\\mathrm{{{}}}", s.replace('_', "\\_"));
            }
            // 2文字以上の英単語 (例: triangle, pos, etc.)
            if s.len() > 1 && s.chars().all(|c| c.is_ascii_alphabetic()) {
                return format!("\\mathrm{{{}}}", s);
            }

            let mut out = String::new();
            let mut in_sub = false;
            for (idx, &c) in cs.iter().enumerate() {
                if ('₀'..='₉').contains(&c) {
                    if !in_sub {
                        out.push_str("_{");
                        in_sub = true;
                    }
                    let d = (c as u32 - '₀' as u32) as u8 + b'0';
                    out.push(d as char);
                } else if let Some(gl) = greek_char_to_latex(c) {
                    if in_sub {
                        out.push('}');
                        in_sub = false;
                    }
                    if idx > 0 && cs[idx - 1].is_ascii_alphabetic() {
                        out.push_str(&format!("_{{{gl}}}"));
                    } else {
                        out.push_str(gl);
                        out.push(' ');
                    }
                } else {
                    if in_sub {
                        out.push('}');
                        in_sub = false;
                    }
                    match c {
                        '_' => out.push_str("\\_"),
                        _ => out.push(c),
                    }
                }
            }
            if in_sub {
                out.push('}');
            }
            out.trim_end().to_string()
        }
    }
}

pub fn rel_to_latex(r: &str) -> &str {
    match r {
        "=" => "=",
        "≠" => "\\ne",
        "<" => "<",
        "≤" => "\\le",
        ">" => ">",
        "≥" => "\\ge",
        "∈" => "\\in",
        "∉" => "\\notin",
        "⊂" => "\\subset",
        "⊆" => "\\subseteq",
        "⊃" => "\\supset",
        "⊇" => "\\supseteq",
        "≡" => "\\equiv",
        "≈" => "\\approx",
        "∼" => "\\sim",
        "≅" => "\\cong",
        "∣" => "\\mid",
        _ => r,
    }
}

fn binder_latex_list(ps: &[(String, String)], typed: bool) -> String {
    let names: Vec<String> = ps.iter().map(|(p, _)| ident_to_latex(p)).collect();
    let names = if names.len() == 1 { names[0].clone() } else { format!("({})", names.join(", ")) };
    if !typed || ps.iter().any(|(_, t)| hidden_sort(t)) {
        return names;
    }
    let ts: Vec<String> = ps.iter().map(|(_, t)| type_latex(t)).collect();
    format!("{names} \\in {}", ts.join(" \\times "))
}

/// 型の LaTeX（`ℕ → ℝ` は `\mathbb{N} \to \mathbb{R}`）
pub fn type_latex(t: &str) -> String {
    t.split(' ')
        .map(|w| match w {
            "→" => "\\to".to_string(),
            "×" => "\\times".to_string(),
            _ => {
                let (open, rest) = match w.strip_prefix('(') { Some(r) => ("(", r), None => ("", w) };
                let (core, close) = match rest.strip_suffix(')') { Some(r) => (r, ")"), None => (rest, "") };
                format!("{open}{}{close}", ident_to_latex(core))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn show_term_latex(t: &Term, prec: u8) -> String {
    match t {
        Term::Var(x) => ident_to_latex(x),
        Term::Num(n) => n.to_string(),
        Term::Meta(m) => format!("?{m}"),
        Term::Lam(ps, b) => format!("\\left({} \\mapsto {}\\right)", binder_latex_list(ps, false), show_term_latex(b, 0)),
        Term::App(f, args) if notation_for_fn(f).and_then(|n| n.split(args)).is_some() => {
            let n = notation_for_fn(f).unwrap();
            let seqs = applied_names(&n.split(args).unwrap().0);
            let before = SUB_SEQS.with(|s| std::mem::replace(&mut *s.borrow_mut(), seqs));
            let s = n.render(args, &|t, p| show_term_latex(t, p), &|l| if l == "(" { "\\;(".into() } else { lit_latex(l) }, &ident_to_latex).unwrap();
            SUB_SEQS.with(|s| *s.borrow_mut() = before);
            if prec > 4 { format!("\\left({s}\\right)") } else { s }
        }
        Term::App(f, args) if f == "@" && !args.is_empty() => {
            let a: Vec<String> = args[1..].iter().map(|a| show_term_latex(a, 0)).collect();
            // 行列の式の成分は (AB)_{ij} と書く
            let is_matrix = matches!(&args[0], Term::App(g, _) if ["mmul", "madd", "msmul", "mat2", "mat3"].contains(&g.as_str()));
            if is_matrix && a.len() == 2 {
                return format!("\\left({}\\right)_{{{} {}}}", show_term_latex(&args[0], 0), a[0], a[1]);
            }
            format!("{}({})", show_term_latex(&args[0], 5), a.join(", "))
        }
        Term::Set(ps, phi) => format!(
            "\\left\\{{ {} \\mid {} \\right\\}}",
            binder_latex_list(ps, true),
            show_formula_latex(phi, 0)
        ),
        Term::App(f, args) => {
            let (s, p) = match (f.as_str(), args.as_slice()) {
                // 略記の表示の中の数列：a(n) を a_{n} と書く
                (_, [a]) if SUB_SEQS.with(|s| s.borrow().contains(f)) || with_syntax(|t| t.seq_globals.contains(f)) => (format!("{}_{{{}}}", ident_to_latex(f), show_term_latex(a, 0)), 5),
                ("max" | "min", [a, b]) => (format!("\\{f}\\{{{}, {}\\}}", show_term_latex(a, 0), show_term_latex(b, 0)), 5),
                ("+" | "-", [a, b]) => (
                    format!("{} {} {}", show_term_latex(a, 1), f, show_term_latex(b, 2)),
                    1,
                ),
                // 積は記号なしで並べる（2x・ab・b_n β）。右が数で始まるとき（2·3・a·2）だけ · を書く
                ("·", [a, b]) => {
                    let (l, r) = (show_term_latex(a, 2), show_term_latex(b, 3));
                    let dot = r.starts_with(|c: char| c.is_ascii_digit() || c == '-' || c == '.');
                    (if dot { format!("{l} \\cdot {r}") } else { format!("{l} {r}") }, 2)
                }
                ("/", [a, b]) => (
                    format!(
                        "\\frac{{{}}}{{{}}}",
                        show_term_latex(a, 0),
                        show_term_latex(b, 0)
                    ),
                    4,
                ),
                ("neg", [a]) => (format!("-{}", show_term_latex(a, 3)), 3),
                ("^", [a, b]) => (
                    format!(
                        "{{{}}}^{{{}}}",
                        show_term_latex(a, 5),
                        show_term_latex(b, 0)
                    ),
                    4,
                ),
                ("abs", [a]) => (format!("\\left| {} \\right|", show_term_latex(a, 0)), 5),
                (m @ ("mat2" | "mat3"), xs) if xs.len() == if m == "mat2" { 4 } else { 9 } => {
                    let n = if m == "mat2" { 2 } else { 3 };
                    let rows: Vec<String> = xs
                        .chunks(n)
                        .map(|r| r.iter().map(|x| show_term_latex(x, 0)).collect::<Vec<_>>().join(" & "))
                        .collect();
                    (format!("\\begin{{pmatrix}} {} \\end{{pmatrix}}", rows.join(" \\\\ ")), 9)
                }
                // 行列の演算（lib/algebra/matrix）
                ("det2", [a]) => (format!("\\det {}", show_term_latex(a, 6)), 5),
                ("mtr", [a, _]) => (format!("\\operatorname{{tr}} {}", show_term_latex(a, 6)), 5),
                ("mmul", [a, b, _]) => (format!("{} {}", show_term_latex(a, 3), show_term_latex(b, 3)), 2),
                ("madd", [a, b]) => (format!("{} + {}", show_term_latex(a, 1), show_term_latex(b, 2)), 1),
                ("msmul", [c, a]) => (format!("{} {}", show_term_latex(c, 3), show_term_latex(a, 3)), 2),
                // 有限和 sum(a, n)（lib/algebra/sum）は Σ_{k<n} a_k と書く
                ("sum", [a, n]) => {
                    let (k, body) = match a {
                        Term::Lam(ps, b) if ps.len() == 1 => (ps[0].0.clone(), show_term_latex(b, 2)),
                        _ => ("k".to_string(), format!("{}_{{k}}", show_term_latex(a, 6))),
                    };
                    (format!("\\sum_{{{} < {}}} {}", ident_to_latex(&k), show_term_latex(n, 0), body), 2)
                }
                ("norm", [a]) => (format!("\\left\\| {} \\right\\|", show_term_latex(a, 0)), 5),
                ("floor", [a]) => (
                    format!("\\left\\lfloor {} \\right\\rfloor", show_term_latex(a, 0)),
                    5,
                ),
                ("ceil", [a]) => (
                    format!("\\left\\lceil {} \\right\\rceil", show_term_latex(a, 0)),
                    5,
                ),
                ("set", [a]) => (
                    format!("\\left\\{{ {} \\right\\}}", show_term_latex(a, 0)),
                    5,
                ),
                ("inner", [a]) => (
                    format!("\\left\\langle {} \\right\\rangle", show_term_latex(a, 0)),
                    5,
                ),
                ("sqrt", [a]) => (format!("\\sqrt{{{}}}", show_term_latex(a, 0)), 5),
                ("root", [n, a]) => (
                    format!(
                        "\\sqrt[{}]{{{}}}",
                        show_term_latex(n, 0),
                        show_term_latex(a, 0)
                    ),
                    5,
                ),
                ("binom", [n, k]) => (
                    format!(
                        "\\binom{{{}}}{{{}}}",
                        show_term_latex(n, 0),
                        show_term_latex(k, 0)
                    ),
                    5,
                ),
                ("vec", [a]) => (format!("\\vec{{{}}}", show_term_latex(a, 0)), 5),
                ("hat", [a]) => (format!("\\hat{{{}}}", show_term_latex(a, 0)), 5),
                ("bar", [a]) => (format!("\\overline{{{}}}", show_term_latex(a, 0)), 5),
                ("tilde", [a]) => (format!("\\tilde{{{}}}", show_term_latex(a, 0)), 5),
                ("sum", [sub, sup, body]) => (
                    format!(
                        "\\sum_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("prod", [sub, sup, body]) => (
                    format!(
                        "\\prod_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("int", [sub, sup, body]) => (
                    format!(
                        "\\int_{{{}}}^{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(sup, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                ("lim", [sub, body]) => (
                    format!(
                        "\\lim_{{{}}} {}",
                        show_term_latex(sub, 0),
                        show_term_latex(body, 3)
                    ),
                    3,
                ),
                _ => {
                    let a: Vec<String> = args.iter().map(|a| show_term_latex(a, 0)).collect();
                    (format!("{}({})", ident_to_latex(f), a.join(", ")), 5)
                }
            };
            if p < prec {
                format!("\\left({s}\\right)")
            } else {
                s
            }
        }
    }
}

fn binder_latex(q: &str, x: &str, ty: &str) -> String {
    let xl = ident_to_latex(x);
    if hidden_sort(ty) {
        format!("{q} {xl}")
    } else if ty.contains('→') || ty == "Prop" {
        format!("{q} {xl} : {}", type_latex(ty))
    } else {
        format!("{q} {xl} \\in {}", ident_to_latex(ty))
    }
}

pub fn show_formula_latex(f: &Formula, prec: u8) -> String {
    let (s, p) = match f {
        Formula::Bot => ("\\bot".to_string(), 5),
        Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => (
            format!(
                "{} {} {}",
                show_term_latex(&ts[0], 0),
                rel_to_latex(r),
                show_term_latex(&ts[1], 0)
            ),
            5,
        ),
        Formula::Atom(p, ts) if ts.is_empty() => (ident_to_latex(p), 5),
        Formula::Atom(p, ts) if p == "@" && ts.len() == 2 && !matches!(ts[0], Term::Var(_)) => {
            (format!("{} \\in {}", show_term_latex(&ts[1], 0), show_term_latex(&ts[0], 0)), 5)
        }
        Formula::Atom(p, ts) if p == "@" => {
            let a: Vec<String> = ts[1..].iter().map(|t| show_term_latex(t, 0)).collect();
            (format!("{}({})", show_term_latex(&ts[0], 5), a.join(", ")), 5)
        }
        Formula::Atom(p, ts) if notation_for_pred(p).and_then(|n| n.split(ts)).is_some() => {
            let n = notation_for_pred(p).unwrap();
            let seqs = applied_names(&n.split(ts).unwrap().0);
            SUB_SEQS.with(|s| *s.borrow_mut() = seqs);
            // 型紙の中の「(」の前は少し空ける（a_n → α (n → ∞)）
            let shown = n.render(ts, &|t, p| show_term_latex(t, p), &|l| if l == "(" { "\\;(".into() } else { lit_latex(l) }, &ident_to_latex).unwrap();
            SUB_SEQS.with(|s| s.borrow_mut().clear());
            (shown, 5)
        }
        Formula::Atom(p, ts) => {
            let a: Vec<String> = ts.iter().map(|t| show_term_latex(t, 0)).collect();
            (format!("{}({})", ident_to_latex(p), a.join(", ")), 5)
        }
        Formula::Imp(a, b) if **b == Formula::Bot => match &**a {
            Formula::Atom(r, ts) if r == "=" && ts.len() == 2 => (
                format!(
                    "{} \\ne {}",
                    show_term_latex(&ts[0], 0),
                    show_term_latex(&ts[1], 0)
                ),
                5,
            ),
            Formula::Atom(r, ts) if RELS.contains(&r.as_str()) && ts.len() == 2 => {
                (format!("\\lnot ({})", show_formula_latex(a, 0)), 4)
            }
            _ => (format!("\\lnot {}", show_formula_latex(a, 4)), 4),
        },
        Formula::Imp(a, b) => (
            format!(
                "{} \\Rightarrow {}",
                show_formula_latex(a, 2),
                show_formula_latex(b, 1)
            ),
            1,
        ),
        Formula::Or(a, b) => (
            format!(
                "{} \\lor {}",
                show_formula_latex(a, 2),
                show_formula_latex(b, 3)
            ),
            2,
        ),
        Formula::And(..) if iff_parts(f).is_some() => {
            let (a, b) = iff_parts(f).unwrap();
            (format!("{} \\Leftrightarrow {}", show_formula_latex(a, 1), show_formula_latex(b, 1)), 0)
        }
        Formula::And(a, b) => (
            format!(
                "{} \\land {}",
                show_formula_latex(a, 3),
                show_formula_latex(b, 4)
            ),
            3,
        ),
        Formula::Forall(x, ty, b) => {
            if let Formula::Imp(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!(
                        "\\forall {} {} {},\\ {}",
                        ident_to_latex(x),
                        rel_to_latex(&r),
                        show_term_latex(&t, 0),
                        show_formula_latex(body, 0)
                    );
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (
                format!(
                    "{},\\ {}",
                    binder_latex("\\forall", x, ty),
                    show_formula_latex(b, 0)
                ),
                0,
            )
        }
        Formula::Exists(x, ty, b) => {
            if let Formula::And(g, body) = &**b {
                if let Some((r, t)) = bounded(x, g) {
                    let s = format!(
                        "\\exists {} {} {},\\ {}",
                        ident_to_latex(x),
                        rel_to_latex(&r),
                        show_term_latex(&t, 0),
                        show_formula_latex(body, 0)
                    );
                    return if prec > 0 { format!("({s})") } else { s };
                }
            }
            (
                format!(
                    "{},\\ {}",
                    binder_latex("\\exists", x, ty),
                    show_formula_latex(b, 0)
                ),
                0,
            )
        }
    };
    if p < prec { format!("({s})") } else { s }
}
