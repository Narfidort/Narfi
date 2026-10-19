// クラウド保存（Cloudflare Pages Functions）の共通部分。functions/ の各ファイルから使う。
//
// 置き場所：D1（SQLite）のデータベース。binding の名前は DB（wrangler.toml）
// ログイン：GitHub OAuth。秘密は Cloudflare Pages の secret（GITHUB_CLIENT_ID・GITHUB_CLIENT_SECRET）
// セッション：Cookie（__Host-narfi_session。HttpOnly・Secure・SameSite=Lax）。D1 には値の SHA-256 だけを置く

export const SESSION_COOKIE = "__Host-narfi_session";
export const STATE_COOKIE = "__Host-narfi_oauth";
export const SESSION_DAYS = 30;

// 1 人あたりの上限（増えたらまた考える）
export const MAX_FILE_BYTES = 512 * 1024;
export const MAX_FILES = 1000;
export const MAX_TOTAL_BYTES = 20 * 1024 * 1024;

export function json(obj, status = 200, headers = {}) {
  return new Response(JSON.stringify(obj), {
    status,
    headers: { "Content-Type": "application/json", "Cache-Control": "no-store", ...headers }
  });
}

export function configured(env) {
  return !!(env.DB && env.GITHUB_CLIENT_ID && env.GITHUB_CLIENT_SECRET);
}

export function randomToken() {
  const b = new Uint8Array(32);
  crypto.getRandomValues(b);
  return [...b].map((x) => x.toString(16).padStart(2, "0")).join("");
}

export async function sha256(s) {
  const d = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(s));
  return [...new Uint8Array(d)].map((x) => x.toString(16).padStart(2, "0")).join("");
}

export function getCookie(request, name) {
  const h = request.headers.get("Cookie") || "";
  for (const part of h.split(";")) {
    const i = part.indexOf("=");
    if (i < 0) continue;
    if (part.slice(0, i).trim() === name) return decodeURIComponent(part.slice(i + 1).trim());
  }
  return null;
}

export function cookie(name, value, maxAge) {
  return `${name}=${encodeURIComponent(value)}; Path=/; Max-Age=${maxAge}; HttpOnly; Secure; SameSite=Lax`;
}

export function now() {
  return Math.floor(Date.now() / 1000);
}

/** ログイン中の利用者（いなければ null） */
export async function currentUser(request, env) {
  if (!env.DB) return null;
  const token = getCookie(request, SESSION_COOKIE);
  if (!token || !/^[0-9a-f]{64}$/.test(token)) return null;
  const row = await env.DB.prepare(
    "SELECT u.id, u.login FROM sessions s JOIN users u ON u.id = s.user_id WHERE s.token_hash = ? AND s.expires_at > ?"
  )
    .bind(await sha256(token), now())
    .first();
  return row || null;
}

/**
 * 状態を変える要求は、このサイトの画面からのものだけを受け付ける（CSRF 対策）。
 * 独自のヘッダーは他のサイトからは付けられない（付けると CORS の事前確認になり、ここは許可しない）。
 */
export function sameSite(request) {
  if (request.headers.get("X-Narfi-Cloud") !== "1") return false;
  const origin = request.headers.get("Origin");
  return !origin || origin === new URL(request.url).origin;
}

/** ブラウザ内の保存領域と同じ形の相対パス（week1/a.narfi など）だけを受け付ける */
export function validPath(p) {
  if (typeof p !== "string" || p.length === 0 || p.length > 200) return false;
  if (!p.endsWith(".narfi") || p.startsWith("/") || p.startsWith("lib:")) return false;
  if (/[\u0000-\u001f\\]/.test(p)) return false;
  return p.split("/").every((s) => s !== "" && s !== "." && s !== "..");
}
