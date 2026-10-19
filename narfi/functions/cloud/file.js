// GET    /cloud/file?path=…                       → 中身と version
// PUT    /cloud/file  {path, src, base}           → 保存。base は手元が最後に同期した version（新しいファイルなら 0）
//                                                   クラウドの version が base でなければ 409（ほかの端末で変わった）
// DELETE /cloud/file?path=…&base=…                → 削除（version が base のときだけ）
import {
  MAX_FILES,
  MAX_FILE_BYTES,
  MAX_TOTAL_BYTES,
  configured,
  currentUser,
  json,
  now,
  sameSite,
  validPath
} from "../../server/common.js";

async function auth(request, env, mutating) {
  if (!configured(env)) return [null, json({ ok: false, error: "クラウド保存はまだ設定されていない" }, 503)];
  if (mutating && !sameSite(request)) return [null, json({ ok: false, error: "このサイトの画面からの要求ではない" }, 403)];
  const user = await currentUser(request, env);
  if (!user) return [null, json({ ok: false, error: "ログインしていない" }, 401)];
  return [user, null];
}

async function current(env, user, path) {
  return env.DB.prepare("SELECT src, version, updated_at FROM files WHERE user_id = ? AND path = ?").bind(user.id, path).first();
}

export async function onRequestGet({ request, env }) {
  const [user, err] = await auth(request, env, false);
  if (err) return err;
  const path = new URL(request.url).searchParams.get("path");
  if (!validPath(path)) return json({ ok: false, error: "パスが正しくない" }, 400);
  const row = await current(env, user, path);
  if (!row) return json({ ok: false, error: `${path} がない` }, 404);
  return json({ ok: true, path, src: row.src, version: row.version, updated_at: row.updated_at });
}

export async function onRequestPut({ request, env }) {
  const [user, err] = await auth(request, env, true);
  if (err) return err;
  const body = await request.json().catch(() => null);
  if (!body || !validPath(body.path) || typeof body.src !== "string" || !Number.isInteger(body.base)) {
    return json({ ok: false, error: "要求の形が正しくない" }, 400);
  }
  const size = new TextEncoder().encode(body.src).length;
  if (size > MAX_FILE_BYTES) return json({ ok: false, error: `1 つのファイルは ${MAX_FILE_BYTES / 1024} KB まで` }, 413);
  const t = now();

  let res;
  if (body.base === 0) {
    // 新しいファイル：上限を確かめてから作る（すでにあれば 409）
    const usage = await env.DB.prepare("SELECT COUNT(*) AS n, COALESCE(SUM(size), 0) AS bytes FROM files WHERE user_id = ?")
      .bind(user.id)
      .first();
    if (usage.n >= MAX_FILES) return json({ ok: false, error: `ファイルは ${MAX_FILES} 個まで` }, 413);
    if (usage.bytes + size > MAX_TOTAL_BYTES) return json({ ok: false, error: "クラウドの容量（20 MB）を超える" }, 413);
    res = await env.DB.prepare(
      "INSERT INTO files (user_id, path, src, size, version, updated_at) VALUES (?, ?, ?, ?, 1, ?) ON CONFLICT DO NOTHING"
    )
      .bind(user.id, body.path, body.src, size, t)
      .run();
  } else {
    const usage = await env.DB.prepare(
      "SELECT COALESCE(SUM(size), 0) AS bytes FROM files WHERE user_id = ? AND path != ?"
    )
      .bind(user.id, body.path)
      .first();
    if (usage.bytes + size > MAX_TOTAL_BYTES) return json({ ok: false, error: "クラウドの容量（20 MB）を超える" }, 413);
    res = await env.DB.prepare(
      "UPDATE files SET src = ?, size = ?, version = version + 1, updated_at = ? WHERE user_id = ? AND path = ? AND version = ?"
    )
      .bind(body.src, size, t, user.id, body.path, body.base)
      .run();
  }
  if (res.meta.changes === 0) {
    const row = await current(env, user, body.path);
    return json({ ok: false, conflict: true, path: body.path, version: row ? row.version : 0, src: row ? row.src : null }, 409);
  }
  const row = await current(env, user, body.path);
  return json({ ok: true, path: body.path, version: row.version, updated_at: row.updated_at });
}

export async function onRequestDelete({ request, env }) {
  const [user, err] = await auth(request, env, true);
  if (err) return err;
  const q = new URL(request.url).searchParams;
  const path = q.get("path");
  const base = Number(q.get("base"));
  if (!validPath(path) || !Number.isInteger(base)) return json({ ok: false, error: "要求の形が正しくない" }, 400);
  const res = await env.DB.prepare("DELETE FROM files WHERE user_id = ? AND path = ? AND version = ?").bind(user.id, path, base).run();
  if (res.meta.changes === 0) return json({ ok: false, conflict: true }, 409);
  return json({ ok: true });
}
