// GET /cloud/files → 自分のファイルの一覧（パスと version。中身は含めない）
import { configured, currentUser, json } from "../../server/common.js";

export async function onRequestGet({ request, env }) {
  if (!configured(env)) return json({ ok: false, error: "クラウド保存はまだ設定されていない" }, 503);
  const user = await currentUser(request, env);
  if (!user) return json({ ok: false, error: "ログインしていない" }, 401);
  const { results } = await env.DB.prepare("SELECT path, version, updated_at FROM files WHERE user_id = ? ORDER BY path")
    .bind(user.id)
    .all();
  return json({ ok: true, files: results });
}
