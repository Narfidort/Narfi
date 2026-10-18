# Narfi for VS Code

- `.narfi` のシンタックスハイライト（未定の対象を導入する Fix / Obtain / Case は太字）
- 保存時に `narfi check --diag` を実行し、エラーに波線、`sorry` には残っている goal を表示（波線にカーソルを当てる）
- 記号の入力：`\all` のあとにスペースで `∀`。`\ex ∃  \to →  \and ∧  \or ∨  \not ¬  \bot ⊥  \le ≤  \ge ≥  \ne ≠  \N ℕ  \R ℝ  \e ε  \d δ  \1 ₁  \sq ²  \tf ∴`

インストール：`./build.sh` で VSIX を作って入れる。
