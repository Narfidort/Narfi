// GET /cloud/me → ログイン中の利用者と使っている量
// DELETE /cloud/me → アカウントとクラウドのファイルをすべて消す
import { MAX_FILES, MAX_TOTAL_BYTES, SESSION_COOKIE, configured, cookie, currentUser, json, sameSite } from "../../server/common.js";

export async function onRequestGet({ request, env }) {
  if (!configured(env)) return json({ ok: false, configured: false });
  const user = await currentUser(request, env);
  if (!user) return json({ ok: false, configured: true, signed_in: false });
  const usage = await env.DB.prepare("SELECT COUNT(*) AS n, COALESCE(SUM(size), 0) AS bytes FROM files WHERE user_id = ?")
    .bind(user.id)
    .first();
  return json({
    ok: true,
    configured: true,
    signed_in: true,
    login: user.login,
    id: user.id,
    files: usage.n,
    bytes: usage.bytes,
    max_files: MAX_FILES,
    max_bytes: MAX_TOTAL_BYTES
  });
}

export async function onRequestDelete({ request, env }) {
  if (!sameSite(request)) return json({ ok: false, error: "このサイトの画面からの要求ではない" }, 403);
  const user = await currentUser(request, env);
  if (!user) return json({ ok: false, error: "ログインしていない" }, 401);
  await env.DB.batch([
    env.DB.prepare("DELETE FROM files WHERE user_id = ?").bind(user.id),
    env.DB.prepare("DELETE FROM sessions WHERE user_id = ?").bind(user.id),
    env.DB.prepare("DELETE FROM users WHERE id = ?").bind(user.id)
  ]);
  return json({ ok: true }, 200, { "Set-Cookie": cookie(SESSION_COOKIE, "", 0) });
}
