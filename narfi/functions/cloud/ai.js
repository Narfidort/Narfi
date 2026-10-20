// POST /cloud/ai → AI の API（OpenAI と同じ形式の chat/completions）への中継
//
// ブラウザから直接呼べない（CORS を許していない）接続先のため。キーは利用者のブラウザにだけ保存され、
// 要求のたびに送られてくる。ここでは保存も記録もしない（console.log しない）。
// 開いた中継にならないよう、ログイン中の利用者だけ・決まった接続先だけに送る。
import { currentUser, json, sameSite } from "../../server/common.js";

const HOSTS = [
  "opencode.ai",
  "generativelanguage.googleapis.com",
  "api.openai.com",
  "openrouter.ai",
  "api.anthropic.com"
];
const MAX_BODY = 256 * 1024;

export async function onRequestPost({ request, env }) {
  if (!sameSite(request)) return json({ ok: false, error: "このサイトの画面からの要求ではない" }, 403);
  const user = await currentUser(request, env);
  if (!user) return json({ ok: false, error: "ログインしていない" }, 401);
  const text = await request.text();
  if (text.length > MAX_BODY) return json({ ok: false, error: "要求が大きすぎる" }, 413);
  let body;
  try { body = JSON.parse(text); } catch (_) { return json({ ok: false, error: "JSON でない" }, 400); }
  let base;
  try { base = new URL(String(body.base || "")); } catch (_) { return json({ ok: false, error: "接続先の URL が正しくない" }, 400); }
  if (base.protocol !== "https:" || !HOSTS.includes(base.hostname)) {
    return json({ ok: false, error: `Web 版で使える接続先は ${HOSTS.join("・")} だけです` }, 400);
  }
  const headers = {
    "Content-Type": "application/json",
    Authorization: `Bearer ${String(body.key || "")}`,
    "User-Agent": "narfi-web/2"
  };
  if (base.hostname === "opencode.ai") headers["x-opencode-session"] = String(body.session || "narfi");
  const url = base.href.replace(/\/+$/, "") + "/chat/completions";
  let r;
  try {
    r = await fetch(url, { method: "POST", headers, body: String(body.payload || "{}") });
  } catch (e) {
    return json({ ok: false, error: `接続できない: ${e}` }, 502);
  }
  // 応答はそのまま返す（中身は OpenAI と同じ形式。エラーも接続先のもの）
  return new Response(await r.text(), { status: r.status, headers: { "Content-Type": "application/json", "Cache-Control": "no-store" } });
}
