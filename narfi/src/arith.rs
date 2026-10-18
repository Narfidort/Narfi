//! 自動証明（oracle）：ring・linarith・decide。
//!
//! これらは証明書を出さない「信じるコード」であり、検査器の信頼の土台（TCB）に入る。
//! そのため検査器は、どの定理がどの自動証明に依存したかを報告する。

use crate::syntax::{Formula, Term};
use std::collections::{BTreeMap, HashMap};

// ================================================================ 有理数

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Q {
    n: i128,
    d: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 {
        a.abs()
    } else {
        gcd(b, a % b)
    }
}

impl Q {
    pub fn new(n: i128, d: i128) -> Q {
        let g = gcd(n, d).max(1);
        let s = if d < 0 { -1 } else { 1 };
        Q { n: s * n / g, d: s * d / g }
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
        Q::new(self.n * o.d + o.n * self.d, self.d * o.d)
    }
    pub fn mul(self, o: Q) -> Q {
        Q::new(self.n * o.n, self.d * o.d)
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

// ================================================================ 多項式

/// 単項式：(原子の番号, 指数) の列（番号順）。空なら定数項。
type Mono = Vec<(usize, u32)>;

#[derive(Clone, Debug, PartialEq)]
pub struct Poly(BTreeMap<Mono, Q>);

impl Poly {
    fn constant(c: Q) -> Poly {
        let mut m = BTreeMap::new();
        if !c.is_zero() {
            m.insert(vec![], c);
        }
        Poly(m)
    }
    fn atom(i: usize) -> Poly {
        Poly(BTreeMap::from([(vec![(i, 1)], Q::int(1))]))
    }
    fn add(&self, o: &Poly) -> Poly {
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
    fn scale(&self, c: Q) -> Poly {
        if c.is_zero() {
            return Poly(BTreeMap::new());
        }
        Poly(self.0.iter().map(|(k, v)| (k.clone(), v.mul(c))).collect())
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
    fn as_const(&self) -> Option<Q> {
        match self.0.len() {
            0 => Some(Q::zero()),
            1 => self.0.get(&vec![]).copied(),
            _ => None,
        }
    }
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

/// 項を多項式に直す。多項式でない部分（|x|、f(x)、x/y など）は「原子」として扱う。
/// 原子は中身を正規化した文字列で同一視するので、|(a+b)-(c+d)| と |a-c+(b-d)| は同じ原子になる。
pub struct Arith {
    atoms: Vec<String>,
    index: HashMap<String, usize>,
}

impl Arith {
    pub fn new() -> Arith {
        Arith { atoms: vec![], index: HashMap::new() }
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
                let mut fs: Vec<String> = m.iter().map(|(i, e)| format!("{}^{}", self.atoms[*i], e)).collect();
                fs.sort();
                format!("{}/{}*{}", c.n, c.d, fs.join("*"))
            })
            .collect();
        ms.sort();
        ms.join("+")
    }
    pub fn poly(&mut self, t: &Term) -> Option<Poly> {
        Some(match t {
            Term::Meta(_) => return None,
            Term::Num(n) => Poly::constant(Q::int(*n as i128)),
            Term::Var(x) => self.atom(format!("v:{x}")),
            Term::App(f, a) => match (f.as_str(), a.as_slice()) {
                ("+", [x, y]) => self.poly(x)?.add(&self.poly(y)?),
                ("-", [x, y]) => self.poly(x)?.add(&self.poly(y)?.scale(Q::int(-1))),
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
                ("^", [x, Term::Num(k)]) if *k >= 0 && *k <= 16 => {
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

// ================================================================ ring

/// l = r が環の等式として成り立つか
pub fn ring(l: &Term, r: &Term) -> bool {
    let mut a = Arith::new();
    match (a.poly(l), a.poly(r)) {
        (Some(x), Some(y)) => x.add(&y.scale(Q::int(-1))).is_zero(),
        _ => false,
    }
}

// ================================================================ linarith

/// Σ coef·mono + c ⋈ 0（strict なら >、そうでなければ ≥）
#[derive(Clone, Debug)]
struct Lin {
    coef: BTreeMap<Mono, Q>,
    c: Q,
    strict: bool,
}

fn to_lin(p: &Poly, strict: bool) -> Lin {
    let mut coef = p.0.clone();
    let c = coef.remove(&vec![]).unwrap_or(Q::zero());
    Lin { coef, c, strict }
}

/// 関係 l rel r から「… ⋈ 0」の制約を作る
fn constraints(a: &mut Arith, rel: &str, l: &Term, r: &Term) -> Option<Vec<Lin>> {
    let (pl, pr) = (a.poly(l)?, a.poly(r)?);
    let lr = pl.add(&pr.scale(Q::int(-1))); // l - r
    let rl = lr.scale(Q::int(-1)); // r - l
    Some(match rel {
        "<" => vec![to_lin(&rl, true)],
        "≤" => vec![to_lin(&rl, false)],
        ">" => vec![to_lin(&lr, true)],
        "≥" => vec![to_lin(&lr, false)],
        "=" => vec![to_lin(&lr, false), to_lin(&rl, false)],
        _ => return None,
    })
}

fn contradictory(l: &Lin) -> bool {
    l.coef.is_empty() && (l.c.sign() < 0 || (l.strict && l.c.sign() <= 0))
}

/// Fourier–Motzkin の消去法で、制約の集合が矛盾するかを調べる
fn infeasible(mut cs: Vec<Lin>) -> bool {
    const LIMIT: usize = 20000;
    loop {
        if cs.iter().any(contradictory) {
            return true;
        }
        let var = match cs.iter().find_map(|l| l.coef.keys().next().cloned()) {
            Some(v) => v,
            None => return false,
        };
        let (mut pos, mut neg, mut rest) = (vec![], vec![], vec![]);
        for l in cs {
            match l.coef.get(&var).map(|q| q.sign()) {
                Some(1) => pos.push(l),
                Some(-1) => neg.push(l),
                _ => rest.push(l),
            }
        }
        for p in &pos {
            for n in &neg {
                let a = p.coef[&var];
                let b = n.coef[&var].neg();
                // b·p + a·n で var を消す（a, b > 0）
                let mut coef = BTreeMap::new();
                for (k, v) in p.coef.iter() {
                    coef.insert(k.clone(), v.mul(b));
                }
                for (k, v) in n.coef.iter() {
                    let e = coef.entry(k.clone()).or_insert(Q::zero());
                    *e = e.add(v.mul(a));
                }
                coef.retain(|_, v| !v.is_zero());
                rest.push(Lin { coef, c: p.c.mul(b).add(n.c.mul(a)), strict: p.strict || n.strict });
                if rest.len() > LIMIT {
                    return false;
                }
            }
        }
        cs = rest;
    }
}

/// facts から goal（l rel r）が線形算術で従うか。単項式は独立な変数とみなす。
pub fn linarith(facts: &[(String, Term, Term)], goal: (&str, &Term, &Term)) -> bool {
    let (rel, l, r) = goal;
    if rel == "=" {
        return linarith(facts, ("≤", l, r)) && linarith(facts, ("≥", l, r));
    }
    let mut a = Arith::new();
    let mut cs = Vec::new();
    for (fr, fl, frr) in facts {
        if let Some(c) = constraints(&mut a, fr, fl, frr) {
            cs.extend(c);
        }
    }
    // goal の否定を加えて矛盾を探す
    let negated = match rel {
        "<" => "≥",
        "≤" => ">",
        ">" => "≤",
        "≥" => "<",
        _ => return false,
    };
    match constraints(&mut a, negated, l, r) {
        Some(c) => cs.extend(c),
        None => return false,
    }
    infeasible(cs)
}

// ================================================================ decide

fn eval(t: &Term) -> Option<Q> {
    match t {
        Term::Num(n) => Some(Q::int(*n as i128)),
        Term::App(f, a) => {
            let v: Option<Vec<Q>> = a.iter().map(eval).collect();
            let v = v?;
            match (f.as_str(), v.as_slice()) {
                ("+", [x, y]) => Some(x.add(*y)),
                ("-", [x, y]) => Some(x.add(y.neg())),
                ("neg", [x]) => Some(x.neg()),
                ("·", [x, y]) => Some(x.mul(*y)),
                ("/", [x, y]) if !y.is_zero() => Some(x.mul(y.inv())),
                ("S", [x]) => Some(x.add(Q::int(1))),
                ("abs", [x]) => Some(if x.sign() < 0 { x.neg() } else { *x }),
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

fn as_nat(q: Q) -> Option<i128> {
    (q.d == 1 && q.n >= 0).then_some(q.n)
}

/// 変数を含まない命題を計算で判定する
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
                ("even", [x]) => as_nat(*x)? % 2 == 0,
                ("odd", [x]) => as_nat(*x)? % 2 == 1,
                ("prime", [x]) => {
                    let n = as_nat(*x)?;
                    n >= 2 && (2..).take_while(|d| d * d <= n).all(|d| n % d != 0)
                }
                ("divides", [x, y]) => {
                    let (a, b) = (as_nat(*x)?, as_nat(*y)?);
                    if a == 0 { b == 0 } else { b % a == 0 }
                }
                _ => return None,
            }
        }
        Formula::Forall(..) | Formula::Exists(..) => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{lex, P};

    fn t(s: &str) -> Term {
        P::new(lex(s, 0).unwrap(), 0, vec![]).term().unwrap()
    }

    #[test]
    fn ring_basic() {
        assert!(ring(&t("ε/2 + ε/2"), &t("ε")));
        assert!(ring(&t("(a + b)²"), &t("a² + 2·a·b + b²")));
        assert!(!ring(&t("(a + b)²"), &t("a² + b²")));
    }

    #[test]
    fn linarith_basic() {
        let f = vec![("<".into(), t("x"), t("3")), ("≤".into(), t("y"), t("x"))];
        assert!(linarith(&f, ("<", &t("y"), &t("3"))));
        assert!(!linarith(&f, ("<", &t("y"), &t("2"))));
        let g = vec![("<".into(), t("|a - c|"), t("e/2")), ("<".into(), t("|b - d|"), t("e/2"))];
        assert!(linarith(&g, ("<", &t("|a - c| + |b - d|"), &t("e"))));
    }
}
