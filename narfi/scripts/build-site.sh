#!/bin/sh
# Web 版（サーバーなし）のサイトを site/ に組み立てる。Cloudflare Pages などの静的な置き場所にそのまま置ける。
#   narfi.wasm     検査器（src/wasm.rs）
#   index.html     エディタ（src/web_ui.html。ローカル版と同じもの）
#   narfi-web.js   /api/… をブラウザの中で処理する（src/web_static.js）
#   assets/katex/  数式表示（同梱の KaTeX）
set -eu
cd "$(dirname "$0")/.."
cargo rustc --lib --profile web --target wasm32-unknown-unknown --crate-type cdylib
rm -rf site
mkdir -p site/assets
cp target/wasm32-unknown-unknown/web/narfi.wasm site/narfi.wasm
cp src/web_ui.html site/index.html
cp src/web_static.js site/narfi-web.js
cp src/tutorial.js site/tutorial.js
cp src/course.js site/course.js
cp -R assets/katex site/assets/katex
# 404 はトップに戻す・キャッシュの設定（Cloudflare Pages の書式）
cat > site/_headers <<'HDR'
/narfi.wasm
  Content-Type: application/wasm
  Cache-Control: public, max-age=0, must-revalidate
/*
  X-Content-Type-Options: nosniff
  Referrer-Policy: same-origin
HDR
echo "site/ を作った：$(du -sh site | cut -f1)"
