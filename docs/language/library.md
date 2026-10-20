# 標準ライブラリ（v2.6）

`narfi/lib/`。`import 名前`（`/` の代わりに `.`）で読む。どの定理がどの公理に頼るかは、`narfi check` やエディタの Goal タブの一覧に出る。

| ファイル | 中身 | 頼る公理（核の公理以外） |
|---|---|---|
| `analysis/real.narfi` | 三角不等式・`pos_half`・`max` の性質（公理として置く） | それ自体が公理 |
| `analysis/limits.narfi` | 数列の極限 `is_lim`（`a ⟶ α`）と和の極限 | `analysis/real` の公理 |
| `reals/rat.narfi` | ℚ の絶対値・`max` の性質 | `abs.sub_comm`・`abs.triangle` など（公理） |
| `reals/cauchy.narfi` | コーシー列 `cauchy`、その型 `CauSeq`、同値関係 `~` | `reals/rat` の公理 |
| `reals/real.narfi` | ℝ = コーシー列/~（typedef による商）、`cls` の sound・exact・surjective | 同上 |
| `algebra/sum.narfi` | 有限和 `sum(a, n)` = Σ_{k<n} a_k（rec）、線形性 | なし |
| `algebra/matrix.narfi` | 排中律、クロネッカーのデルタ、行列の和・積・トレース・2×2 の行列式、`[[…]]` の行列、2×2 のケイリー・ハミルトン、分配法則 | なし |

核の公理（`narfi/src/prelude.narfi`）：等号（`EQ1`）、ペアノ（`PA1`・`PA2`、加法・乗法）、外延性（`funext`・`propext`・`setext`）、選択（`choice`）、再帰定理（`rec.exists`）。[logic.md](logic.md) の §8.1。
