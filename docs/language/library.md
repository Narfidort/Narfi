# 標準ライブラリ（v2.6）

`narfi/lib/`。`import 名前`（`/` の代わりに `.`）で読む。どの定理がどの公理に頼るかは、`narfi check` やエディタの Goal タブの一覧に出る。

| ファイル | 中身 | 頼る公理（核の公理以外） |
|---|---|---|
| `analysis/real.narfi` | 三角不等式・`pos_half`・`max` の性質（公理として置く） | それ自体が公理 |
| `analysis/limits.narfi` | 数列の極限 `is_lim`（`a_n → α (n → ∞)`）と和の極限 | `analysis/real` の公理 |
| `reals/rat.narfi` | ℚ の絶対値・`max` の性質 | `abs.sub_comm`・`abs.triangle` など（公理） |
| `reals/cauchy.narfi` | コーシー列 `cauchy`、その型 `CauSeq`、同値関係 `~` | `reals/rat` の公理 |
| `reals/real.narfi` | ℝ = コーシー列/~（typedef による商）、`cls` の sound・exact・surjective | 同上 |
| `set/real.narfi` | 実数の集合の演算：`A ∪ B`・`A ∩ B`・`A ∖ B`・`A^∁`・逆像 `f^{-1}[B]`・像 `f[A]`・`disjoint`（型を問わない形は v3） | なし |
| `algebra/nat_order.narfi` | ℕ の順序の基本：`nat.lt_succ`（k < m + 1 ⇒ k < m ∨ k = m）・`nat.not_lt`（¬(a < b) ⇒ b ≤ a） | それ自体が公理（仮置き） |
| `algebra/sum.narfi` | 有限和 `sum(a, n)` = Σ_{k<n} a_k（rec）、線形性、`sum.zeros`・`sum.cong`（項ごとに等しい）・`sum.swap`（二重和の交換）・`sum.single`（1 項だけ残る）・`sum.cat`（分割）・`sum.one` | `nat_order` |
| `algebra/delta.narfi` | 排中律 `em`、`nat.cases`、クロネッカーのデルタ `delta(i, j)`、δ を掛けた和 `dsum.pick`・`dsum.out`・`dsum.shift`・`dsum.below` | `nat_order` |
| `algebra/matrix.narfi` | 行列の和・積・トレース・2×2 の行列式、`[[…]]` の行列、2×2 のケイリー・ハミルトン、分配法則 | なし |
| `linear/dependence.narfi` | `lin.dep`：未知数が方程式より多い同次連立 1 次方程式には自明でない解がある（掃き出しの帰納法） | `mul.cancel`（xy = 0, y ≠ 0 ⇒ x = 0。仮置き）・`nat_order` |
| `linear/dimension.narfi` | `dim.bound`：1 次独立な f_0, …, f_N が m 個の関数の 1 次結合なら N + 1 ≤ m | 同上 |
| `linear/span.narfi` | `cdim(f, N, m)`（m 個の関数の 1 次結合に入る）と `cdim.bound`・`cdim.add`・`cdim.cong`・`cdim.resize` | 同上 |
| `linear/tri.narfi` | `tr(d)` = 0 + 1 + … + (d − 1)、`tr.double`、和の平方 `sq.sum`、三角形の対の族 `cdim.tri` | 同上 |

核の公理（`narfi/src/prelude.narfi`）：等号（`EQ1`）、ペアノ（`PA1`・`PA2`、加法・乗法）、外延性（`funext`・`propext`・`setext`）、選択（`choice`）、再帰定理（`rec.exists`）。[logic.md](logic.md) の §8.1。
