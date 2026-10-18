//! 証明項（仕様 §5 の表と1対1に対応する）。
//!
//! 証明項は「どの推論規則を、どの前提に、どの順で使ったか」を木として書き下したもの。
//! elab が作り、kernel が根から順に検算する。

use crate::kernel::arith::Q;
use crate::syntax::{Formula, Term};

#[derive(Clone, Debug)]
pub enum Proof {
    /// 文脈の仮定 h
    Hyp(String),
    /// 定理・公理の図式を、ソート σs と項 ts で具体化したもの
    Thm { name: String, sorts: Vec<String>, args: Vec<Term> },
    /// →導入：h : φ を仮定して body を示す
    ImpI { h: String, phi: Formula, body: Box<Proof> },
    /// →除去：φ → ψ と φ から ψ
    ImpE(Box<Proof>, Box<Proof>),
    AndI(Box<Proof>, Box<Proof>),
    /// ∧除去。right なら右側
    AndE { right: bool, p: Box<Proof> },
    /// ∨導入。right なら「other ∨ p の結論」、そうでなければ「p の結論 ∨ other」
    OrI { right: bool, other: Formula, p: Box<Proof> },
    /// ∨除去（場合分け）
    OrE { p: Box<Proof>, h1: String, q1: Box<Proof>, h2: String, q2: Box<Proof> },
    /// ∀導入（x は固有変数）
    AllI { x: String, sort: String, body: Box<Proof> },
    /// ∀除去：項 t を代入する
    AllE(Box<Proof>, Term),
    /// ∃導入：target は ∃x:σ. φ、witness は x に入れる項
    ExI { target: Formula, witness: Term, p: Box<Proof> },
    /// ∃除去：p : ∃y. φ から x, h : φ[y := x] を取り出して body を示す
    ExE { p: Box<Proof>, x: String, h: String, body: Box<Proof> },
    /// ⊥除去
    BotE(Formula, Box<Proof>),
    /// 背理法（古典論理）：h : ¬φ から ⊥ を出して φ
    Raa { h: String, phi: Formula, body: Box<Proof> },
    /// have：p で φ を示し、h : φ として body で使う
    Cut { h: String, phi: Formula, p: Box<Proof>, body: Box<Proof> },
    /// let：x := t として body を示す
    Let { x: String, sort: String, t: Term, body: Box<Proof> },
    /// t = t
    Refl(Term),
    /// 等号による書き換え：eq : s = t、p : φ[z := s] から φ[z := t]
    Subst { eq: Box<Proof>, z: String, motive: Formula, p: Box<Proof> },
    /// 数学的帰納法：base : φ[x:=0]、k, ih : φ[x:=k] のもとで step : φ[x:=S(k)]
    Ind { x: String, phi: Formula, base: Box<Proof>, k: String, ih: String, step: Box<Proof> },
    /// 推移律：a R b と b R' c から a R'' c
    Trans(Box<Proof>, Box<Proof>),
    /// a ≤ b と b ≤ a から a = b
    Antisymm(Box<Proof>, Box<Proof>),
    /// t : ℕ なら t ≥ 0
    NatNonneg(Term),
    /// 環の等式 l = r（kernel が正規化して確かめる）
    Ring { lhs: Term, rhs: Term },
    /// 線形算術：facts の結論と goal の否定に coeffs を掛けて足すと矛盾（最後の係数が goal の否定）
    LinArith { goal: Formula, facts: Vec<Proof>, coeffs: Vec<Q> },
    /// 変数を含まない命題を計算で確かめる
    Decide(Formula),
    /// 未完成（sorry）
    Sorry(Formula),
    /// エラーの位置を示すための印（論理的な意味はない）
    Line(usize, Box<Proof>),
}

impl Proof {
    pub fn b(self) -> Box<Proof> {
        Box::new(self)
    }
}
