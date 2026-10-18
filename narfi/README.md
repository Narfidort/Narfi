# narfi — Narfi の証明検査器（試作）

> **v2**：小さな核（kernel）が証明項を検算する構成に作り直した。
> 仕様と学習ノートは [docs/v2/](docs/v2/README.md)。以下の表の多くは v1 からの説明で、v2 では型の書き方などが違う
> （v1 は `v1.0` タグ）。

`仕様書v0_5.md` の核に、フィードバックで出た拡張の一部を加えたものを検査する。Rust 製で、外部クレートは使わない。

```
cargo run -- check examples/basics.narfi examples/analysis.narfi
cargo run -- check examples/limits.narfi            # def・notation・import（lib/analysis/limits.narfi）
cargo run -- check --trace examples/analysis.narfi   # 各行の文脈と goal を表示
cargo run -- check examples/errors.narfi             # わざと間違えた証明
cargo test                                           # 正しい証明は通り、間違った証明は1本も通らないことを確認
```

拡張子は `.narfi`。練習問題は `../練習.narfi`、エディタ拡張は `../editors/vscode/`。

- `sorry`：どんな goal も仮に閉じる。その位置で残っている goal を表示し、定理は「△ 未完成」になる（sorry に頼る定理を使った定理も未完成になる）。
- `--diag`：エディタ向けの出力（`ERROR` / `SORRY`・行・本文のタブ区切り）。

## v0.5 に加えたもの

| 構文 | 意味 |
|---|---|
| `∀ε>0. φ` / `∃N:ℕ. φ` / `∀n≥N. φ` | 範囲付き量化子。`∀x>a. φ` は `∀x. x>a → φ`、`∃x>a. φ` は `∃x. x>a ∧ φ` の略記 |
| `Obtain N(ε), hN : e` | 依存関係の注釈。N を取り出す位置で、スコープにある Fix 変数がちょうど (ε) であることを検査する |
| `∴ φ` | 直前に示したもの（スコープを出た結果・have など）が φ であることを検査する |
| `suffices ψ := j` | `⇐` の別表記（`⇐` も使える） |
| `Fix n, m` | 複数の Fix |
| `Case succ k, IH : φ` | 末尾の `:` は書いても書かなくてもよい。IH の型も省略できる |
| `choose t, j` | 範囲付き ∃ の条件（`t > 0` など）を j で示す |
| `axiom name : Γ ⊢ φ` | 補題を公理として置く（三角不等式など） |
| `sorry` | 証明を後回しにする（残っている goal を表示） |
| `def is_lim(a, α) := φ` | 述語の定義。証明の中では必要なところで自動的に展開される（`conv_a(ε/2, …)`・`Fix ε` など）。引数 `a` は関数の位置（`a(n)`）にも置け、`a + b` を渡すと `a(n) + b(n)` と各点ごとに読む |
| `notation a "⟶" α := is_lim(a, α)` | 中置の記法。`a ⟶ α` は `is_lim(a, α)` として読まれ、表示・Prose・LaTeX でも記法のまま出る。ASCII では `\longrightarrow`（`\lto`）。組み込みの記号（`->` `<` など）とは衝突させられない |
| `import analysis.limits` | `analysis/limits.narfi` を、同じディレクトリ → `NARFI_PATH` → `narfi/lib/` の順に探して読み込む。循環 import はエラー |
| `unfold is_lim` / `unfold is_lim at h` | 定義を明示的に展開する（goal / 仮定）。定義の同値 `is_lim.def : is_lim(a, α) ↔ φ` も使える |

## Web エディタの操作

`cargo run -- web` で開く構造化エディタ。

| 操作 | キー |
|---|---|
| 元に戻す／やり直す | `Cmd/Ctrl+Z` ／ `Cmd+Shift+Z`・`Ctrl+Y` |
| 範囲選択 | `Shift+矢印`、マウスドラッグ、`Shift+クリック`、全選択 `Cmd/Ctrl+A` |
| コピー・切り取り・貼り付け | `Cmd/Ctrl+C` / `X` / `V`（クリップボードには ASCII のコードが入る。複数行は字下げも保つ） |
| 削除 | `Backspace` / `Delete`（選択中は選択範囲を消す。選択中に文字を打つと置き換わる） |

名前の字体は、宣言した名前（`thm` / `axiom` / `def` の直後）と 4 文字以上の名前が立体、1〜3 文字の変数はイタリックで描かれる。字体はコードから決まり、コードには書かない。

## 信頼の土台（何を信じれば結果を信じてよいか）

- **核**：`check.rs` の推論規則（→・∀・∃・∧・∨・⊥・背理法・帰納法・EQ2）と単一化。
- **自動証明（oracle）**：`arith.rs` の `ring`（多項式の正規化）、`linarith`（Fourier–Motzkin の消去法）、`decide`（計算）。今は証明書を出さないので、このコードも信じる必要がある。そのため、使った定理には `〔自動証明: …〕` と表示する（依存は定理をまたいで伝わる）。
- **公理**：自分で置いた `axiom` も、使った定理に `〔公理: …〕` と表示する。
- **連鎖**：`a ≤ b < c` の推移律は組み込み。各段の根拠がそのまま当てはまらないときは、根拠の命題を事実として linarith で補う（このときも `自動証明: linarith` と表示される）。

## まだできないこと・既知の穴

- **項の型検査をしていない**：`∀x:ℕ` に `-1` や実数を代入しても止められない。型 `?`（書かれていない型）は何にでも合うものとして扱う。
- 自動証明は証明書を出さない（上記）。
- 二階のペアノ公理 PA3 は書けない（帰納法は `induction` として組み込み）。λ を使った `EQ2(h, λz. …, hφ)` も未対応。
- `S(k)` と `k + 1` は核の中では別の項（ring・linarith の中でだけ同じとみなす）。
- 束縛の `.` の直後には空白が必要（`∀x:ℝ. φ`）。`∀x.φ` は `x.φ` という名前として読まれる。
