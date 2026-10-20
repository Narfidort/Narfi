# Narfi の文書（v2.6）

Narfi（**N**atural **A**nnotated **R**easoning **F**orward **I**nteractive）は、手書きの証明と対応する、
読める形式証明の言語と、その検査器・エディタ。設計の考え方は [principles.md](principles.md)。

| 文書 | 中身 |
|---|---|
| [principles.md](principles.md) | 設計原則（迷ったらこれに照らして決める） |
| [language/syntax.md](language/syntax.md) | 言語仕様：書き方の完全な一覧（文・根拠・規則の名前・日本語シュガー） |
| [language/logic.md](language/logic.md) | 言語仕様：核の論理（型・推論規則・定義的等しさ・算術・定義・typedef） |
| [language/library.md](language/library.md) | 標準ライブラリ（何がどの公理に頼るか） |
| [system/architecture.md](system/architecture.md) | システム構成：parser → elab → kernel、ファイルの読み込み、WebAssembly |
| [system/editor.md](system/editor.md) | エディタ（構造化された入力・表示の層・直し方） |
| [system/web-and-cloud.md](system/web-and-cloud.md) | ローカルサーバー・Web 版・クラウド保存・CI/CD |
| [system/testing.md](system/testing.md) | テストの種類と回し方 |
| [notes/](notes/README.md) | 学習ノート（論理学・型理論の考え方を、このコードに沿って説明する） |
| [proposals/](proposals/README.md) | 検討中の設計案（行列・自然言語の分離と定理の訳名） |
| [archived/](archived/README.md) | v1 時代の仕様書・計画書・ガイドブック |

v1（タグ `v1.0`）は「黒板の答案をそのまま検査する」試作だった。v2 の目標は、
**何を信じれば検査結果を信じてよいかが、小さく・明確に言える**証明言語にすること。

## 構成：信じる部分と信じなくてよい部分を分ける

```
ソース ──(parser)──► 構文木 ──(sorts)──► 型のついた構文木
                                              │
                                  (elab：推敲器。信じなくてよい)
                                   単一化・定義の展開・自動証明の探索
                                              │  証明項（Proof）を作る
                                              ▼
                                  (kernel：核。これだけを信じる)
                                   推論規則どおりかを1つずつ検算する
```

- **kernel**（`narfi/src/kernel/`）だけが「正しい」と判断する。elab にバグがあっても、
  kernel が通さなければ誤った定理は通らない。
- 自動証明（`ring`・`linarith`・`decide`）は **証明書** を出し、kernel がそれを検算する。
- この分け方を **de Bruijn 基準** と呼ぶ（Lean・Coq・Isabelle・HOL Light も同じ）。

## 論理の土台

v2 の土台は **単純型理論（HOL）**。v2.0 でその一階の部分（多ソート一階述語論理 + 等号 + 数の算術）を、
v2.1 で関数型・Prop・λ・集合を実装した。

| 段階 | 内容 | 状態 |
|---|---|---|
| v2.0 | 仕様書・ソート検査・証明項と kernel・証明書つき ring / linarith / decide | 実装済み（v1 のサンプルはすべて kernel を通る） |
| v2.1 | 単純型理論：関数型・Prop・λ・集合・二階の具体化・外延性と選択・項の定義 | 実装済み |
| v2.1.1 | kernel の健全性のバグ（同時代入の仮の名前の衝突で ⊥ が証明できた）の修正 | 修正済み |
| v2.2 | typedef（新しい型の定義）・一般の適用・商。ℝ = コーシー列/~ を型として構成（sound・exact・surjective） | 実装済み |
| v2.3 | エディタ：作業フォルダ・Mac のダイアログ・自動保存・印刷・LaTeX の PDF・ライブラリの置き場所・KaTeX の同梱、ローカルサーバーを他サイトから使わせない | 実装済み |
| v2.4 | Web 版：検査器を WebAssembly にしてブラウザで動かし、Cloudflare Pages に自動デプロイ（GitHub Actions） | 実装済み |
| v2.5 | 仮定の中身を省略できなくする（`Fix ε \| hε : ε > 0`。省略すると help つきのエラー）・Web 版のクラウド保存（GitHub でログイン、D1 と同期） | 実装済み |
| v2.5.x | 書き方・エディタの改善、原始再帰（rec）・Σ・行列（2×2 ケイリー・ハミルトン）、自然演繹の証明木、コース「公理へ」第 0〜4 章 | 実装済み |
| v2.6 | 証明の書き方の整理：事実の行 `h : φ by j`（have を置き換え）、根拠のない行はエラー＋根拠の探索（直し方として示す。勝手に補わない）、古い書き方は警告と書き換え、∴ の表示 | 実装済み |
| v2.7 | ℝ の演算（加法・乗法の well-definedness）と順序 | 未着手 |
| v2.8 | ℤ・ℚ をペアノから商で構成 | 未着手 |
| v2.9 | 外部の検査器（Lean 4 など）への書き出しによる再検査 | 未着手 |

## v1 からの書き方の違い

- 型が決まらない変数には型を書く：`axiom pos_half : x : ℝ, h : x > 0 ⊢ x/2 > 0`、`∀ε:ℝ>0. …`
- 数列などの関数記号は宣言する：`a : ℕ → ℝ`
- 定義の引数にも型を書く：`def is_lim(a : ℕ → ℝ, α : ℝ) := …`
- 数列の和は λ で書く：`(n ↦ a(n) + b(n)) ⟶ α + β`（v1 の `(a + b) ⟶ …` は書けない）
- 集合は述語として書く：`A : ℕ → Prop`、`{n : ℕ | n > 1}`、`x ∈ A`、`A ⊆ B`
- 仮定の中身は省略しない（v2.5）：`Fix ε | hε : ε > 0`・`assume h : P`・`Case succ k, IH : φ`
- 途中で示したことは事実の行 `h : φ by j` で書く（v2.6。`have` は古い書き方）
- 報告の `〔自動証明: …〕` は `〔算術: …〕` になった（kernel が検算しているので）

## テスト

```sh
cargo test                       # すべて
cargo test --lib kernel::        # kernel 単体（手で組み立てた誤った証明項を拒否するか）
```
