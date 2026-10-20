// web_ui.html の script を、偽の DOM の上で読み込む（tests/ui.rs から使うテスト用）。
// 登録されたイベントハンドラ（keydown・copy・paste など）はそのまま呼べる。
const fs = require("fs");

const stub = new Proxy(function () {}, {
  get: (t, k) => (k === Symbol.toPrimitive ? () => "" : stub),
  apply: () => stub,
  construct: () => stub,
  set: () => true,
});

function fakeElement(id) {
  const base = {
    id,
    handlers: {},
    innerHTML: "", value: "", textContent: "", style: {},
    addEventListener(type, fn) { (this.handlers[type] ||= []).push(fn); },
    focus() {}, contains() { return true; }, querySelector() { return null; },
    classList: { add() {}, remove() {}, toggle() {}, contains() { return false; } },
  };
  return new Proxy(base, {
    get: (t, k) => (k in t ? t[k] : k === Symbol.toPrimitive ? () => "" : stub),
    set: (t, k, v) => { t[k] = v; return true; },
  });
}

module.exports = function load(htmlPath) {
  const html = fs.readFileSync(htmlPath, "utf8");
  const code = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(m => m[1]).join("\n");
  const els = {};
  const doc = {
    handlers: {},
    activeElement: null,
    getElementById(id) { return (els[id] ||= fakeElement(id)); },
    addEventListener(type, fn) { (this.handlers[type] ||= []).push(fn); },
    querySelector() { return null; }, querySelectorAll() { return []; },
    createElement() { return stub; }, elementFromPoint() { return null; },
    documentElement: stub, body: stub,
  };
  global.document = doc;
  global.NARFI_LOCAL = true;
  global.window = new Proxy({ addEventListener() {} }, { get: (t, k) => (k in t ? t[k] : stub), set: () => true });
  global.localStorage = { getItem: () => null, setItem() {} };
  global.navigator = stub;
  global.requestAnimationFrame = () => 0;
  global.fetch = async () => ({ json: async () => ({}) });
  global.setTimeout = () => 0;
  global.setInterval = () => 0;
  global.addEventListener = () => {};
  try {
    (0, eval)(code + `
;globalThis.__api = {
  loadSourceIntoDoc, serializeDocToAscii, setCursor, undoDoc, selectionText, normalizeSel,
  get cursor() { return cursor; }, get docLines() { return docLines; },
  get selAnchor() { return selAnchor; }, get history() { return history; },
  hitTestPos,
  setCheckData(d) { lastCheckData = d; }, get acMatches() { return acMatches; },
};`);
  } catch (e) {
    console.error("init:", e.message);
  }
  const api = global.__api;
  doc.activeElement = doc.getElementById("editorSurface");
  const fire = (target, type, ev = {}) => {
    const e = { preventDefault() { this.defaultPrevented = true; }, defaultPrevented: false, ...ev };
    for (const h of target.handlers[type] || []) h(e);
    return e;
  };
  return {
    api,
    key(key, mods = {}) { return fire(doc.getElementById("editorSurface"), "keydown", { key, ...mods }); },
    type(text) { for (const ch of text) this.key(ch); },
    copy() { const data = {}; const e = fire(doc, "copy", { clipboardData: { setData: (t, v) => (data[t] = v) } }); return e.defaultPrevented ? data["text/plain"] : null; },
    cut() { const data = {}; const e = fire(doc, "cut", { clipboardData: { setData: (t, v) => (data[t] = v) } }); return e.defaultPrevented ? data["text/plain"] : null; },
    paste(text) { fire(doc, "paste", { clipboardData: { getData: () => text } }); },
    text() { return api.serializeDocToAscii(); },
    html() { return doc.getElementById("editorSurface").innerHTML; },
    // 行 line の文字を、描画されたクラスごとに並べる（例: { "mc-ident-fn": "triangle", "mc-var": "x" }）
    classesOfLine(line) {
      const div = this.html().split('<div class="mc-line').find(d => d.includes(`data-line-idx="${line}"`)) || "";
      const out = {};
      for (const m of div.matchAll(/<span class="([^"]*)" data-seq="\d+" data-idx="\d+">([^<]|&[a-z]+;)<\/span>/g)) {
        out[m[1]] = (out[m[1]] || "") + (m[2] === "&nbsp;" ? " " : m[2]);
      }
      return out;
    },
  };
};
