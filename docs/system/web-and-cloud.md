# ローカル版・Web 版・クラウド保存（v2.6）

## ローカル版（`narfi web`）
- `narfi/src/web.rs`。`127.0.0.1` で待ち受け、`Host`・`Origin` を確かめて他のサイトからの要求を拒む。
- 作業フォルダ（`~/.narfi/workspace` に記録）のファイルを直接読み書きする。削除はゴミ箱（`~/.Trash`）へ移す。
- macOS のダイアログ（osascript）、LuaLaTeX（latexmk）での PDF、AI 補助（CLI・API）。

## Web 版（https://narfi.pages.dev）
- `scripts/build-site.sh` が `site/` を作る：`index.html`（エディタ）・`narfi.wasm`（検査器）・`narfi-web.js`（`src/web_static.js`）・`tutorial.js`・`course.js`・KaTeX。
- `narfi-web.js` が `fetch('/api/…')` を横取りして、WebAssembly とブラウザの保存領域（localStorage）で処理する。

## クラウド保存
- Cloudflare Pages Functions（`narfi/functions/`、共通部分は `narfi/server/common.js`）と D1（SQLite。表は `narfi/migrations/`）。
- Web 版はログインして使う（最初の画面で GitHub のログインを求める）。ログインは GitHub OAuth（権限は求めない。GitHub のトークンは保存しない）。右上に GitHub のアイコンと同期の状態の点を出す。セッションは Cookie `__Host-narfi_session`（HttpOnly・Secure・SameSite=Lax、30 日。開くたびに延びる）、D1 には値の SHA-256 だけを置く。
- 状態を変える要求は `X-Narfi-Cloud: 1` と `Origin` を確かめる（CSRF 対策）。上限は 1 人 1000 ファイル・20 MB。
- 同期：手元の保存領域が本体。ファイルごとに version を持ち、変更は後から送る。両方で変わったら、手元の版を残し、もう一方を `名前.conflict-日時.narfi` として残す。削除・名前の変更も同期する（tombstone）。

## CI/CD（`.github/workflows/web.yml`）
1. `cargo test`、Web 版の組み立て、WebAssembly とローカル版の結果の一致（`tests/wasm_smoke.mjs`）、Functions の構文
2. push のとき：`scripts/cloud-setup.sh`（D1 の作成・表の更新・OAuth の秘密の登録）→ `wrangler pages deploy`
   - `main` → 本番、ほかのブランチ → `https://<ブランチ>.narfi.pages.dev`
- 秘密（GitHub Secrets）：`CLOUDFLARE_API_TOKEN`・`CLOUDFLARE_ACCOUNT_ID`・`NARFI_GITHUB_CLIENT_ID`・`NARFI_GITHUB_CLIENT_SECRET`。

## リリース
0.1 ごとにタグを付けて `v2` に push し、`main` にマージする（事前に全テスト）。
