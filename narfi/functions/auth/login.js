// GET /auth/login → GitHub のログイン画面へ。戻り先の検査用の state を Cookie に置く
import { STATE_COOKIE, configured, cookie, json, randomToken } from "../../server/common.js";

export async function onRequestGet({ request, env }) {
  if (!configured(env)) return json({ ok: false, error: "クラウド保存はまだ設定されていない" }, 503);
  const state = randomToken();
  const u = new URL("https://github.com/login/oauth/authorize");
  u.searchParams.set("client_id", env.GITHUB_CLIENT_ID);
  u.searchParams.set("redirect_uri", new URL("/auth/callback", request.url).toString());
  u.searchParams.set("state", state);
  // 権限は求めない（公開されているプロフィールの ID とログイン名だけを使う）
  u.searchParams.set("scope", "");
  u.searchParams.set("allow_signup", "true");
  return new Response(null, {
    status: 302,
    headers: { Location: u.toString(), "Set-Cookie": cookie(STATE_COOKIE, state, 600), "Cache-Control": "no-store" }
  });
}
