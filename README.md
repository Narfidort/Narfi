# Narfi

Narfi は、Narfidort が設計・実装した自然演繹ベースの証明言語と、その付属エディタです。

- **証明言語**：`Fix` / `assume` / `Obtain` / `choose` / 等式・不等式の連鎖などで、紙の証明に近い形で書き、検査器（`narfi check`）が各ステップを検証します。仕様は `仕様書v0_*.md`、入門は `ガイドブック.md` を参照してください。
- **付属エディタ**（`narfi web`）：Mathcha 風の構造化数式エディタです。分数・添字・絶対値などを入力欄つきの数式として直接編集でき、裏のコードは純粋な ASCII の `.narfi` として保存されます。日本語の証明文として読める表示（JP Sugar View）や、各行の文脈・Goal の表示を備えています。

```bash
cd narfi
cargo run -- check examples/analysis.narfi
cargo run -- web
```

Narfi is a natural-deduction proof language and its accompanying structured math editor, designed and implemented by Narfidort.

## License

Copyright (c) 2026 Narfidort. All rights reserved. See [LICENSE](LICENSE).
