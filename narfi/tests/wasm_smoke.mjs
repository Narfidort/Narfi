// ブラウザ版の検査器（narfi.wasm）が、ローカル版（narfi check）と同じ結果を返すことを確かめる。
// 使い方: node tests/wasm_smoke.mjs site/narfi.wasm target/debug/narfi
import fs from "node:fs";
import { execFileSync } from "node:child_process";

const [wasmPath, bin] = process.argv.slice(2);
const bytes = fs.readFileSync(wasmPath);
if (WebAssembly.Module.imports(new WebAssembly.Module(bytes)).length !== 0) throw new Error("WASM が外部の関数を要求している");
const { instance } = await WebAssembly.instantiate(bytes, {});
const ex = instance.exports;
const enc = new TextEncoder(), dec = new TextDecoder();
function call(req) {
  const b = enc.encode(JSON.stringify(req));
  const p = ex.narfi_alloc(b.length);
  new Uint8Array(ex.memory.buffer, p, b.length).set(b);
  const n = ex.narfi_call(p, b.length);
  ex.narfi_free(p, b.length);
  return JSON.parse(dec.decode(new Uint8Array(ex.memory.buffer, ex.narfi_out_ptr(), n)));
}

const files = [
  "examples/basics.narfi", "examples/analysis.narfi", "examples/errors.narfi", "examples/hol.narfi",
  "examples/limits.narfi", "tests/exercises_answers.narfi", "tests/unsound.narfi", "tests/unsound_defs.narfi",
  "tests/unsound_sorts.narfi", "tests/unsound_hol.narfi", "tests/unsound_typedef.narfi",
  "tests/regress/subst_placeholder.narfi", "lib/reals/real.narfi",
];
const sym = { ok: "✓", error: "✗", sorry: "△", axiom: "公理" };
let bad = 0;
for (const f of files) {
  const r = call({ op: "check", src: fs.readFileSync(f, "utf8"), path: f.split("/").pop(), cursor_line: 0 });
  const web = r.parse_error ? ["構文エラー"] : r.decls.map((d) => `${sym[d.status]} ${d.name}`);
  let out = "";
  try { out = execFileSync(bin, ["check", f], { encoding: "utf8" }); } catch (e) { out = e.stdout; }
  const local = out.split("\n").map((l) => l.trim()).filter((l) => /^(✓|✗|△|公理|構文エラー)/.test(l))
    .map((l) => l.startsWith("構文エラー") ? "構文エラー" : l.split(/\s+/).slice(0, 2).join(" "));
  const same = JSON.stringify(web) === JSON.stringify(local);
  if (!same) { bad++; console.log("不一致", f, "\n  web  :", web.join(", "), "\n  local:", local.join(", ")); }
  else console.log("一致  ", f, `(${web.length})`);
}
if (bad) { console.error(`${bad} 個のファイルで結果が違う`); process.exit(1); }
