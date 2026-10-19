#!/bin/sh
# クラウド保存（ログインと同期）の準備。CI のデプロイの前に動かす。
#   1. D1（Cloudflare の SQLite）のデータベース narfi を用意し、wrangler.toml の database_id を置き換える
#   2. 表を作る・変える（migrations/ のうち、まだ当てていないもの）
#   3. GitHub OAuth App の ID と秘密を、Pages の secret に入れる（環境変数 NARFI_GITHUB_CLIENT_ID / _SECRET があれば）
# どれかができなければ（API トークンに D1 の権限がないなど）、D1 なしで置けるようにして終わる。
# そのときサイトはこれまでどおり動き、ログインのボタンが出ないだけ。
set -u
cd "$(dirname "$0")/.."
W="npx --yes wrangler"

d1_id() {
  $W d1 list --json 2>/dev/null | node -e '
    let s = "";
    process.stdin.on("data", (d) => (s += d)).on("end", () => {
      try { const d = JSON.parse(s).find((x) => x.name === "narfi"); if (d) console.log(d.uuid); } catch (_) {}
    });'
}

without_d1() {
  echo "::warning::クラウド保存なしで置く：$1"
  node -e '
    const fs = require("fs");
    const s = fs.readFileSync("wrangler.toml", "utf8");
    fs.writeFileSync("wrangler.toml", s.replace(/\n\[\[d1_databases\]\][\s\S]*$/, "\n"));'
  exit 0
}

id=$(d1_id)
if [ -z "$id" ]; then
  $W d1 create narfi || without_d1 "D1 のデータベースを作れなかった（API トークンに「D1: Edit」の権限があるか）"
  id=$(d1_id)
fi
[ -n "$id" ] || without_d1 "D1 のデータベースが見つからない"
sed -i.bak "s/00000000-0000-0000-0000-000000000000/$id/" wrangler.toml && rm -f wrangler.toml.bak
$W d1 migrations apply narfi --remote || without_d1 "表を作れなかった"

if [ -n "${NARFI_GITHUB_CLIENT_ID:-}" ] && [ -n "${NARFI_GITHUB_CLIENT_SECRET:-}" ]; then
  printf %s "$NARFI_GITHUB_CLIENT_ID" | $W pages secret put GITHUB_CLIENT_ID --project-name=narfi >/dev/null
  printf %s "$NARFI_GITHUB_CLIENT_SECRET" | $W pages secret put GITHUB_CLIENT_SECRET --project-name=narfi >/dev/null
  echo "GitHub OAuth の設定を入れた"
else
  echo "::warning::NARFI_GITHUB_CLIENT_ID / NARFI_GITHUB_CLIENT_SECRET がないので、ログインはまだ使えない"
fi
