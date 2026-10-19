# Narfi

Narfi は、Narfidort が設計・実装した自然演繹ベースの証明言語と、その付属エディタです。

- **証明言語**：`Fix` / `assume` / `Obtain` / `choose` / 等式・不等式の連鎖などで、紙の証明に近い形で書き、検査器（`narfi check`）が各ステップを検証します。仕様は `仕様書v0_*.md`、入門は `ガイドブック.md` を参照してください。
- **付属エディタ**（`narfi web`）：Mathcha 風の構造化数式エディタです。分数・添字・絶対値などを入力欄つきの数式として直接編集でき、裏のコードは純粋な ASCII の `.narfi` として保存されます。日本語の証明文として読める表示（JP Sugar View）や、各行の文脈・Goal の表示を備えています。

**Web 版（インストール不要）**：<https://narfi.pages.dev> — ブラウザの中で検査器（WebAssembly）が動く。
ファイルはブラウザ内に保存され、GitHub でログインするとクラウドと同期する（ほかの PC でも開ける）。

**ローカル版**（パソコンのフォルダを直接編集・LaTeX で PDF）：

```bash
cd narfi
cargo install --path .
narfi web --dir ~/授業/解析
```

## v2（現在）

v2 では、小さな核（kernel）がすべての証明を推論規則どおりに検算する構成に作り直しました。
論理の土台は単純型理論（HOL）で、関数・集合を値として扱えます。仕様・設計・学習ノートは
[`narfi/docs/v2/`](narfi/docs/v2/README.md) にあります。

v1 から書き方が変わった点（v1 のファイルはそのままでは通らないことがあります）：

- 型が決まらない変数には型を書く：`x : ℝ, h : x > 0 ⊢ x/2 > 0`、`∀ε:ℝ>0. …`
- 数列などの関数は型を宣言する：`a : ℕ → ℝ`。数列の和は λ で `(n ↦ a(n) + b(n))`
- 集合は述語として書く：`A : ℕ → Prop`、`{n : ℕ | n > 1}`

v1 は `v1.0` タグにあります（`git checkout v1.0`）。`仕様書v0_*.md`・`ガイドブック.md` は v1 時点の文書です。

Narfi is a natural-deduction proof language and its accompanying structured math editor, designed and implemented by Narfidort.

## License

Copyright (c) 2026 Narfidort. All rights reserved. See [LICENSE](LICENSE).
