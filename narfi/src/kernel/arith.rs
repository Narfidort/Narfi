//! kernel の算術：有理数・多項式の正規化・証明書の検算（仕様 §7）。
//!
//! ここにあるのは「計算で確かめる」部分だけで、探索はしない。
//! 証明書（linarith の係数）を見つけるのは elab の仕事（src/arith.rs）。

use crate::syntax::{Formula, Term};
use std::collections::{BTreeMap, HashMap};

// ================================================================ 有理数

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Q {
    pub n: i128,
    pub d: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

// 桁あふれは黙って折り返さず、検査を止める（release ビルドでも）。誤って通すよりは止まるほうがよい。
fn ck(x: Option<i128>) -> i128 {
    x.expect("kernel の算術で桁あふれ（数が大きすぎる）")
}

impl Q {
    pub fn new(n: i128, d: i128) -> Q {
        assert!(d != 0, "分母が 0");
        let g = gcd(n, d).max(1);
        let s: i128 = if d < 0 { -1 } else { 1 };
        Q { n: ck(s.checked_mul(n)) / g, d: ck(s.checked_mul(d)) / g }
    }
    pub fn int(n: i128) -> Q {
        Q { n, d: 1 }
    }
    pub fn zero() -> Q {
        Q::int(0)
    }
    pub fn is_zero(&self) -> bool {
        self.n == 0
    }
    pub fn add(self, o: Q) -> Q {
        let a = ck(self.n.checked_mul(o.d));
        let b = ck(o.n.checked_mul(self.d));
        Q::new(ck(a.checked_add(b)), ck(self.d.checked_mul(o.d)))
    }
    pub fn mul(self, o: Q) -> Q {
        Q::new(ck(self.n.checked_mul(o.n)), ck(self.d.checked_mul(o.d)))
    }
    pub fn neg(self) -> Q {
        Q { n: -self.n, d: self.d }
    }
    pub fn inv(self) -> Q {
        Q::new(self.d, self.n)
    }
    pub fn sign(&self) -> i32 {
        self.n.signum() as i32
    }
}

impl std::fmt::Display for Q {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.d == 1 { write!(f, "{}", self.n) } else { write!(f, "{}/{}", self.n, self.d) }
    }
}

// ================================================================ 多項式

/// 単項式：(原子の番号, 指数) の列（番号順）。空なら定数項。
pub type Mono = Vec<(usize, u32)>;

#[derive(Clone, Debug, PartialEq)]
pub struct Poly(pub BTreeMap<Mono, Q>);

impl Poly {
    pub fn constant(c: Q) -> Poly {
        let mut m = BTreeMap::new();
        if !c.is_zero() {
            m.insert(vec![], c);
        }
        Poly(m)
    }
    fn atom(i: usize) -> Poly {
        Poly(BTreeMap::from([(vec![(i, 1)], Q::int(1))]))
    }
    pub fn add(&self, o: &Poly) -> Poly {
        let mut m = self.0.clone();
        for (k, v) in &o.0 {
            let e = m.entry(k.clone()).or_insert(Q::zero());
            *e = e.add(*v);
            if e.is_zero() {
                m.remove(k);
            }
        }
        Poly(m)
    }
    pub fn scale(&self, c: Q) -> Poly {
        if c.is_zero() {
            return Poly(BTreeMap::new());
        }
        Poly(self.0.iter().map(|(k, v)| (k.clone(), v.mul(c))).collect())
    }
    pub fn sub(&self, o: &Poly) -> Poly {
        self.add(&o.scale(Q::int(-1)))
    }
    fn mul(&self, o: &Poly) -> Poly {
        let mut r = Poly(BTreeMap::new());
        for (a, x) in &self.0 {
            for (b, y) in &o.0 {
                let mut m: BTreeMap<usize, u32> = a.iter().cloned().collect();
                for (i, e) in b {
                    *m.entry(*i).or_insert(0) += e;
                }
                r = r.add(&Poly(BTreeMap::from([(m.into_iter().collect(), x.mul(*y))])));
            }
        }
        r
    }
    /// 定数なら その値
    pub fn as_const(&self) -> Option<Q> {
        match self.0.len() {
            0 => Some(Q::zero()),
            1 => self.0.get(&vec![]).copied(),
            _ => None,
        }
    }
}

/// 項を多項式に直す。多項式でない部分（abs(t)、f(t)、x/y など）は「原子」にする。
/// 原子は引数を正規化した文字列で同一視する（合同性：等しい引数には等しい値）。
#[derive(Default)]
pub struct Normalizer {
    atoms: Vec<String>,
    index: HashMap<String, usize>,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer::default()
    }
    fn atom(&mut self, key: String) -> Poly {
        let n = self.atoms.len();
        let i = *self.index.entry(key.clone()).or_insert(n);
        if i == n {
            self.atoms.push(key);
        }
        Poly::atom(i)
    }
    fn canon(&self, p: &Poly) -> String {
        let mut ms: Vec<String> = p
            .0
            .iter()
            .map(|(m, c)| {
                let mut fs: Vec<String> =
                    m.iter().map(|(i, e)| format!("{}^{}", self.atoms[*i], e)).collect();
                fs.sort();
                format!("{}/{}*{}", c.n, c.d, fs.join("*"))
            })
            .collect();
        ms.sort();
        ms.join("+")
    }
    /// メタ変数を含む項は正規化できない（None）
    pub fn poly(&mut self, t: &Term) -> Option<Poly> {
        Some(match t {
            Term::Meta(_) => return None,
            Term::Num(n) => Poly::constant(Q::int(*n as i128)),
            Term::Var(x) => self.atom(format!("v:{x}")),
            Term::App(f, a) => match (f.as_str(), a.as_slice()) {
                ("+", [x, y]) => self.poly(x)?.add(&self.poly(y)?),
                ("-", [x, y]) => self.poly(x)?.sub(&self.poly(y)?),
                ("neg", [x]) => self.poly(x)?.scale(Q::int(-1)),
                ("·", [x, y]) => self.poly(x)?.mul(&self.poly(y)?),
                ("S", [x]) => self.poly(x)?.add(&Poly::constant(Q::int(1))),
                ("/", [x, y]) => {
                    let num = self.poly(x)?;
                    let den = self.poly(y)?;
                    match den.as_const() {
                        Some(c) if !c.is_zero() => num.scale(c.inv()),
                        _ => {
                            let key = format!("/({},{})", self.canon(&num), self.canon(&den));
                            self.atom(key)
                        }
                    }
                }
                ("^", [x, Term::Num(k)]) if *k <= 16 => {
                    let b = self.poly(x)?;
                    let mut r = Poly::constant(Q::int(1));
                    for _ in 0..*k {
                        r = r.mul(&b);
                    }
                    r
                }
                _ => {
                    let mut parts = Vec::new();
                    for x in a {
                        let p = self.poly(x)?;
                        parts.push(self.canon(&p));
                    }
                    self.atom(format!("{}({})", f, parts.join(",")))
                }
            },
        })
    }
}

/// l = r が可換環の等式として成り立つか（仕様 §7.1）
pub fn ring_eq(l: &Term, r: &Term) -> bool {
    let mut a = Normalizer::new();
    match (a.poly(l), a.poly(r)) {
        (Some(x), Some(y)) => x.sub(&y).0.is_empty(),
        _ => false,
    }
}

// ================================================================ 線形算術の証明書

/// 関係の「… ⋈ 0」の形。strict は >、eq は =、どちらでもなければ ≥。
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
    Gt,
    Ge,
    Eq,
}

/// 事実 l R r を「e ⋈ 0」に直す：(e の左, e の右, ⋈) で e = 左 - 右
pub fn fact_form<'t>(rel: &str, l: &'t Term, r: &'t Term) -> Option<(&'t Term, &'t Term, Cmp)> {
    Some(match rel {
        "<" => (r, l, Cmp::Gt),
        "≤" => (r, l, Cmp::Ge),
        ">" => (l, r, Cmp::Gt),
        "≥" => (l, r, Cmp::Ge),
        "=" => (l, r, Cmp::Eq),
        _ => return None,
    })
}

/// 目標 l R r の否定を「e ⋈ 0」に直す
pub fn negated_goal_form<'t>(rel: &str, l: &'t Term, r: &'t Term) -> Option<(&'t Term, &'t Term, Cmp)> {
    Some(match rel {
        "<" => (l, r, Cmp::Ge),  // ¬(l < r) は l ≥ r
        "≤" => (l, r, Cmp::Gt),  // ¬(l ≤ r) は l > r
        ">" => (r, l, Cmp::Ge),  // ¬(l > r) は r ≥ l
        "≥" => (r, l, Cmp::Gt),  // ¬(l ≥ r) は r > l
        _ => return None,
    })
}

/// 証明書の検算（仕様 §7.2）。forms は事実と目標の否定（最後）の「e ⋈ 0」、coeffs はその係数。
pub fn farkas_check(forms: &[(&Term, &Term, Cmp)], coeffs: &[Q]) -> Result<(), String> {
    if forms.len() != coeffs.len() {
        return Err("証明書の係数の数が合わない".into());
    }
    let mut a = Normalizer::new();
    let mut sum = Poly::constant(Q::zero());
    let mut strict = false;
    for ((l, r, cmp), c) in forms.iter().zip(coeffs) {
        if *cmp != Cmp::Eq && c.sign() < 0 {
            return Err("不等式に負の係数が掛かっている".into());
        }
        if *cmp == Cmp::Gt && c.sign() > 0 {
            strict = true;
        }
        let e = match (a.poly(l), a.poly(r)) {
            (Some(x), Some(y)) => x.sub(&y),
            _ => return Err("正規化できない項がある".into()),
        };
        sum = sum.add(&e.scale(*c));
    }
    match sum.as_const() {
        Some(k) if k.sign() < 0 || (k.is_zero() && strict) => Ok(()),
        Some(k) => Err(format!("証明書の和が矛盾にならない（定数 {k}）")),
        None => Err("証明書の和が定数にならない".into()),
    }
}

// ================================================================ decide

fn eval(t: &Term) -> Option<Q> {
    match t {
        Term::Num(n) => Some(Q::int(*n as i128)),
        Term::App(f, a) => {
            let v: Option<Vec<Q>> = a.iter().map(eval).collect();
            let v = v?;
            let max = |x: &Q, y: &Q| if x.add(y.neg()).sign() >= 0 { *x } else { *y };
            let min = |x: &Q, y: &Q| if x.add(y.neg()).sign() <= 0 { *x } else { *y };
            match (f.as_str(), v.as_slice()) {
                ("+", [x, y]) => Some(x.add(*y)),
                ("-", [x, y]) => Some(x.add(y.neg())),
                ("neg", [x]) => Some(x.neg()),
                ("·", [x, y]) => Some(x.mul(*y)),
                ("/", [x, y]) if !y.is_zero() => Some(x.mul(y.inv())),
                ("S", [x]) => Some(x.add(Q::int(1))),
                ("abs", [x]) => Some(if x.sign() < 0 { x.neg() } else { *x }),
                ("max", [x, y]) => Some(max(x, y)),
                ("min", [x, y]) => Some(min(x, y)),
                ("^", [x, y]) if y.d == 1 && (0..=64).contains(&y.n) => {
                    let mut r = Q::int(1);
                    for _ in 0..y.n {
                        r = r.mul(*x);
                    }
                    Some(r)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// 変数を含まない命題を計算で判定する（仕様 §7.3）。計算できなければ None。
pub fn decide(f: &Formula) -> Option<bool> {
    Some(match f {
        Formula::Bot => false,
        Formula::And(a, b) => decide(a)? && decide(b)?,
        Formula::Or(a, b) => decide(a)? || decide(b)?,
        Formula::Imp(a, b) => !decide(a)? || decide(b)?,
        Formula::Atom(r, ts) => {
            let v: Option<Vec<Q>> = ts.iter().map(eval).collect();
            let v = v?;
            let cmp = |x: &Q, y: &Q| x.add(y.neg()).sign();
            match (r.as_str(), v.as_slice()) {
                ("=", [x, y]) => cmp(x, y) == 0,
                ("<", [x, y]) => cmp(x, y) < 0,
                ("≤", [x, y]) => cmp(x, y) <= 0,
                (">", [x, y]) => cmp(x, y) > 0,
                ("≥", [x, y]) => cmp(x, y) >= 0,
                _ => return None,
            }
        }
        Formula::Forall(..) | Formula::Exists(..) => return None,
    })
}
