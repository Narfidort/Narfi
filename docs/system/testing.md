# テスト（v2.6）

```sh
cd narfi
cargo test                     # すべて
cargo test --lib kernel::      # kernel 単体
node tests/wasm_smoke.mjs site/narfi.wasm target/debug/narfi   # Web 版の検査器（./scripts/build-site.sh のあと）
```

| テスト | 確かめること |
|---|---|
| `src/kernel/tests.rs` | 手で組み立てた誤った証明項（変数の捕獲・型の不一致・選択・typedef・数の型など）を kernel が拒否すること、正しいものを受け付けること |
| `tests/examples.rs` | 例・ライブラリ・回帰（v2.1.1 の健全性のバグ）・通ってはいけない証明（`tests/unsound*.narfi`）・rec・添字・積・規則の名前・事実の行と古い書き方・行列 |
| `tests/ui.rs` | エディタの往復（ファイル → 木 → ASCII）で検査結果が変わらない・冪等・コメントが残る、ソースの変換（日本語シュガー・標準形）で結果が変わらない、エディタの操作（`tests/ui_edit.js`）、チュートリアルとコースの答えが通ること |
| `tests/wasm_smoke.mjs` | WebAssembly 版とローカル版の結果が一致すること |

クラウド保存は、手元の Cloudflare 環境（`npx wrangler pages dev site`、D1 は `--local`）とヘッドレスの Chrome で確かめている（手順は narfi/README.md の「クラウド保存」）。自動の e2e テストはまだない。
