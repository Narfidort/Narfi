// エディタの見た目の確認（Chrome を使う）：tests/render/*.narfi を描いて、
//  1. どの行も、中の要素（分数・積分・添字など）が行の枠からはみ出していないこと（上下の行に重ならない）
//  2. 画面の写真を target/render/ に残す（目で見る用）
// 使い方：node tests/render_check.js [site のディレクトリ]   （事前に scripts/build-site.sh）
// puppeteer-core と Chrome が無いときは、何もせずに終わる（CI では動かさない）。
//   puppeteer-core は NODE_PATH か、このディレクトリの node_modules に置く（リポジトリには入れない）

const fs = require("fs");
const path = require("path");
const http = require("http");

let puppeteer;
try { puppeteer = require("puppeteer-core"); } catch (_) {
  console.log("skip - puppeteer-core がありません（npm i puppeteer-core）");
  process.exit(0);
}
const CHROME = process.env.CHROME || [
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  "/usr/bin/google-chrome", "/usr/bin/chromium", "/usr/bin/chromium-browser",
].find((p) => fs.existsSync(p));
if (!CHROME) { console.log("skip - Chrome がありません（CHROME=… で指定）"); process.exit(0); }

const root = path.resolve(__dirname, "..");
const site = path.resolve(process.argv[2] || path.join(root, "site"));
const outDir = path.join(root, "target", "render");
fs.mkdirSync(outDir, { recursive: true });

const MIME = { ".html": "text/html", ".js": "text/javascript", ".wasm": "application/wasm", ".css": "text/css", ".woff2": "font/woff2", ".woff": "font/woff", ".ttf": "font/ttf" };
const server = http.createServer((req, res) => {
  let f = path.join(site, decodeURIComponent(req.url.split("?")[0]));
  if (f.endsWith("/")) f += "index.html";
  fs.readFile(f, (e, b) => {
    if (e) { res.writeHead(404); return res.end(); }
    res.writeHead(200, { "Content-Type": MIME[path.extname(f)] || "application/octet-stream" });
    res.end(b);
  });
});

(async () => {
  await new Promise((r) => server.listen(0, r));
  const port = server.address().port;
  const browser = await puppeteer.launch({ executablePath: CHROME, headless: "new" });
  let bad = 0, total = 0;
  const dir = path.join(__dirname, "render");
  // 従来の描画（kx=0）と、KaTeX で描く構造ノード（kx=1）の両方を測る
  for (const kx of [0, 1]) for (const f of fs.readdirSync(dir).filter((n) => n.endsWith(".narfi")).sort()) {
    const page = await browser.newPage();
    await page.setViewport({ width: 1500, height: 1400, deviceScaleFactor: 2 });
    page.on("pageerror", (e) => { console.log("pageerror", e.message); bad++; });
    await page.goto(`http://localhost:${port}/?kx=${kx}`, { waitUntil: "networkidle0" });
    const src = fs.readFileSync(path.join(dir, f), "utf8");
    await page.evaluate((s) => { loadSourceIntoDoc(s); refreshAfterEdit(); }, src);
    await new Promise((r) => setTimeout(r, 1200));
    // 行ごとに、中の要素の上下が行の枠の内側にあるかを測る
    const found = await page.evaluate(() => {
      const out = [];
      document.querySelectorAll(".mc-line").forEach((line, k) => {
        const lr = line.getBoundingClientRect();
        let top = Infinity, bottom = -Infinity, who = "";
        line.querySelectorAll(".mc-content *").forEach((e) => {
          if (e.closest(".katex")) return;   // KaTeX の内部は、外側の枠（.mc-kx）が高さを確保している
          const r = e.getBoundingClientRect();
          if (r.width === 0 || r.height === 0) return;
          if (r.top < top) { top = r.top; who = e.className; }
          if (r.bottom > bottom) bottom = r.bottom;
        });
        if (top === Infinity) return;
        const over = Math.max(lr.top - top, bottom - lr.bottom);
        if (over > 1.5) out.push({ line: k + 1, over: Math.round(over * 10) / 10, who: String(who).slice(0, 40) });
        // 文字の絵そのものが、その要素の枠より高くないか（大きな ∫ ∑ など。枠だけ測ると見逃す）
        const cv = document.createElement("canvas").getContext("2d");
        line.querySelectorAll(".mc-content *").forEach((e) => {
          if (e.closest(".katex")) return;
          const t = [...e.childNodes].filter((n) => n.nodeType === 3).map((n) => n.textContent).join("").trim();
          if (!t) return;
          const cs = getComputedStyle(e), r = e.getBoundingClientRect();
          if (r.height === 0) return;
          cv.font = `${cs.fontStyle} ${cs.fontWeight} ${cs.fontSize} ${cs.fontFamily}`;
          const m = cv.measureText(t);
          const ink = m.actualBoundingBoxAscent + m.actualBoundingBoxDescent;
          if (ink - r.height > 1.5) out.push({ line: k + 1, over: Math.round((ink - r.height) * 10) / 10, who: `文字「${t.slice(0, 6)}」の絵が枠より高い ${e.className}` });
        });
      });
      return out;
    });
    total++;
    for (const o of found) { bad++; console.log(`NG ${f} (kx=${kx}) 行 ${o.line}: 枠から ${o.over}px はみ出す（${o.who}）`); }
    const el = await page.$("#editorRoot, .mc-doc, #editor");
    await page.screenshot({ path: path.join(outDir, f.replace(/\.narfi$/, `.kx${kx}.png`)) });
    await page.close();
  }
  await browser.close();
  server.close();
  console.log(bad ? `${bad} 件の問題` : `ok - ${total} ファイルで、はみ出しなし（写真：target/render/）`);
  process.exit(bad ? 1 : 0);
})();
