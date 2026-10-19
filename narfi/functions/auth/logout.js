// POST /auth/logout → このブラウザのセッションを消す
import { SESSION_COOKIE, cookie, getCookie, json, sameSite, sha256 } from "../../server/common.js";

export async function onRequestPost({ request, env }) {
  if (!sameSite(request)) return json({ ok: false, error: "このサイトの画面からの要求ではない" }, 403);
  const token = getCookie(request, SESSION_COOKIE);
  if (env.DB && token) await env.DB.prepare("DELETE FROM sessions WHERE token_hash = ?").bind(await sha256(token)).run();
  return json({ ok: true }, 200, { "Set-Cookie": cookie(SESSION_COOKIE, "", 0) });
}
