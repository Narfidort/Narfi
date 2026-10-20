# システム構成（v2.6）

リポジトリ：`narfi/`（Rust の crate。検査器・CLI・ローカルサーバー・Web 版）、`editors/`（VS Code・Zed の拡張、tree-sitter の文法）、`docs/`（この文書群）。
外部の crate は使わない（`Cargo.toml` の依存は空）。

## 検査の流れ

```
ソース ─ parser ─► 構文木（Module）─ elab ─► 証明項（Proof）─ kernel ─► 受理 / 拒否
          │                            │                          │
   字句・構文・日本語シュガー     型の推論・単一化・定義の展開       推論規則・定義的等しさ・
   notation・rec の展開・添字     根拠の解釈・自動証明の探索        算術の証明書の検算
   import の解決（module）        根拠の候補の探索（v2.6）
```

信じる必要があるのは kernel（と `syntax.rs`・`types.rs` の代入・型の読み書き）だけ（[principles.md](../principles.md) の原則 1）。

## ソースの配置（`narfi/src/`）

| ファイル | 役割 |
|---|---|
| `kernel/`（`mod.rs`・`env.rs`・`check.rs`・`proof.rs`・`arith.rs`・`tests.rs`） | **核**。証明項 `Proof`、環境 `KEnv`（定理・定義・型・定数）、文脈 `KCtx`、推論規則の検算 `Checker::infer`、算術の証明書（環の正規化・Farkas）、手で組んだ誤った証明項を拒否するテスト |
| `syntax.rs` | 項 `Term`・論理式 `Formula`、代入（hereditary substitution）、表示（Unicode・LaTeX）、notation の表 |
| `types.rs` | 型 `Ty` の読み書き |
| `parser.rs` | 字句解析・構文解析、日本語シュガーの正規化、`rec` の展開、数列の添字、宣言ごとの回復（`Item::Broken`）、古い書き方の警告 |
| `module.rs` | prelude と import の読み込み（ディスク・メモリ）、循環 import の検出 |
| `sorts.rs` | 型（ソート）の推論 |
| `elab/`（`mod.rs`・`stmt.rs`・`just.rs`・`unify.rs`） | 推敲器。文ごとの検査と証明項の組み立て、根拠の解釈と探索、単一化（高階のパターン単一化を含む）、各行の文脈・goal・次の一手の記録（`StepTrace`） |
| `derivation.rs` | 証明木（表示用）：kernel に検算させながら部分証明の結論を記録して、Gentzen 式の木にする |
| `prose.rs` | 日本語の証明文・LaTeX・日本語シュガー／標準形への変換 |
| `api.rs` | 検査結果を JSON にする（ローカルサーバーと WebAssembly で共通） |
| `web.rs` | ローカルサーバー（`narfi web`）：作業フォルダ・ファイル操作・PDF・AI |
| `wasm.rs` | WebAssembly の入口（`narfi_call` に JSON を渡す） |
| `stdlib.rs`・`build.rs` | 標準ライブラリ（`narfi/lib/**/*.narfi`）を実行ファイルに埋め込む |
| `main.rs` | CLI：`check`・`web`・`prose`・`latex`・`convert` |
| `prelude.narfi` | 核の公理（等号・ペアノ・外延性・選択・再帰定理）と最初の定理 |
| `web_ui.html` | エディタ（[editor.md](editor.md)） |
| `web_static.js` | Web 版：`/api/…` をブラウザの中で処理する（WebAssembly と保存領域・クラウド同期） |
| `tutorial.js`・`course.js` | Learn タブのチュートリアルとコース |

## 標準ライブラリ（`narfi/lib/`）

[../language/library.md](../language/library.md)。`import a.b` は、同じフォルダ → `NARFI_PATH` → `~/.narfi/lib`（Web 版は保存領域の `lib/`）→ 標準ライブラリ の順に探す。
