// GET /auth/callback?code=…&state=… → GitHub の利用者を確かめ、セッションを作ってエディタに戻る
import {
  SESSION_COOKIE,
  SESSION_DAYS,
  STATE_COOKIE,
  configured,
  cookie,
  getCookie,
  now,
  randomToken,
  sha256
} from "../../server/common.js";

function fail(msg) {
  const html = `<!doctype html><meta charset="utf-8"><title>Narfi</title>
<body style="font-family:system-ui;background:#0a0a0c;color:#ddd;padding:40px">
<p>ログインできなかった：${msg.replace(/[<>&]/g, "")}</p><p><a style="color:#8ab4ff" href="/">エディタに戻る</a></p>`;
  return new Response(html, {
    status: 400,
    headers: { "Content-Type": "text/html; charset=utf-8", "Set-Cookie": cookie(STATE_COOKIE, "", 0), "Cache-Control": "no-store" }
  });
}

export async function onRequestGet({ request, env }) {
  if (!configured(env)) return fail("クラウド保存はまだ設定されていない");
  const url = new URL(request.url);
  const code = url.searchParams.get("code");
  const state = url.searchParams.get("state");
  const expected = getCookie(request, STATE_COOKIE);
  if (!code || !state || !expected || state !== expected) return fail("ログインの途中の情報が合わない。もう一度やり直す");

  // code をアクセストークンに換える（トークンは利用者の確認にだけ使い、保存しない）
  const tr = await fetch("https://github.com/login/oauth/access_token", {
    method: "POST",
    headers: { Accept: "application/json", "Content-Type": "application/json" },
    body: JSON.stringify({
      client_id: env.GITHUB_CLIENT_ID,
      client_secret: env.GITHUB_CLIENT_SECRET,
      code,
      redirect_uri: new URL("/auth/callback", request.url).toString()
    })
  });
  const tok = await tr.json().catch(() => ({}));
  if (!tok.access_token) return fail("GitHub がログインを受け付けなかった");
  const ur = await fetch("https://api.github.com/user", {
    headers: { Authorization: `Bearer ${tok.access_token}`, Accept: "application/vnd.github+json", "User-Agent": "narfi" }
  });
  const gh = await ur.json().catch(() => ({}));
  if (!ur.ok || typeof gh.id !== "number" || typeof gh.login !== "string") return fail("GitHub の利用者の情報が取れなかった");

  const t = now();
  const session = randomToken();
  await env.DB.batch([
    env.DB.prepare(
      "INSERT INTO users (id, login, created_at, last_login) VALUES (?1, ?2, ?3, ?3) ON CONFLICT(id) DO UPDATE SET login = ?2, last_login = ?3"
    ).bind(gh.id, gh.login, t),
    env.DB.prepare("INSERT INTO sessions (token_hash, user_id, expires_at) VALUES (?, ?, ?)").bind(
      await sha256(session),
      gh.id,
      t + SESSION_DAYS * 86400
    ),
    // 期限切れのセッションを片づける
    env.DB.prepare("DELETE FROM sessions WHERE expires_at <= ?").bind(t)
  ]);
  const headers = new Headers({ Location: "/", "Cache-Control": "no-store" });
  headers.append("Set-Cookie", cookie(SESSION_COOKIE, session, SESSION_DAYS * 86400));
  headers.append("Set-Cookie", cookie(STATE_COOKIE, "", 0));
  return new Response(null, { status: 302, headers });
}
