// エディタの編集操作（Undo/Redo・範囲選択・コピー/切り取り/貼り付け）を、実際のキーイベントで動かして確かめる。
// 使い方: node tests/ui_edit.js src/web_ui.html
const assert = require("assert");
const load = require("./ui_harness.js");

const SRC = [
  "axiom triangle : forall x:Real. forall y:Real. abs(x + y) <= abs(x) + abs(y)",
  "thm t :",
  "  h : x > 0",
  "  |- x/2 > 0",
  "",
  "linarith",
].join("\n");

function fresh(src = SRC) {
  const ui = load(process.argv[2]);
  ui.api.loadSourceIntoDoc(src);
  return ui;
}
const goto = (ui, line, off) => ui.api.setCursor(ui.api.docLines[line].rootSeq.id, off, line);
const mod = { metaKey: true };
let n = 0;
function test(name, fn) { fn(); n++; console.log("ok -", name); }

test("文字入力 → Undo → Redo", () => {
  const ui = fresh("");
  ui.type("abc");
  assert.strictEqual(ui.text(), "abc");
  ui.key("z", mod);
  assert.strictEqual(ui.text(), "");
  ui.key("z", { ...mod, shiftKey: true });
  assert.strictEqual(ui.text(), "abc");
  ui.key("z", mod);
  ui.key("y", { ctrlKey: true });
  assert.strictEqual(ui.text(), "abc");
});

test("Undo は空のスロットも元どおりに戻す（ASCII 経由だと 1 になる）", () => {
  const ui = fresh("");
  ui.type("a/");            // 分数ができ、分母にカーソル
  ui.api.history.length;    // 履歴は構造のまま持つ
  const before = ui.api.docLines[0].rootSeq.items.map(i => i.kind).join();
  ui.key("z", mod);
  ui.key("z", { ...mod, shiftKey: true });
  assert.strictEqual(ui.api.docLines[0].rootSeq.items.map(i => i.kind).join(), before);
  assert.ok(ui.api.docLines[0].rootSeq.items.some(i => i.kind === "frac"));
  // 戻したあともカーソルは分母の中で、そのまま打てる
  ui.type("2");
  assert.strictEqual(ui.text(), "a/2");
});

test("新しい編集のあとの Redo は効かない", () => {
  const ui = fresh("");
  ui.type("abc");
  ui.key("z", mod);
  ui.type("x");
  ui.key("y", mod);
  assert.strictEqual(ui.text(), "x");
});

test("Shift+矢印で範囲選択 → 削除", () => {
  const ui = fresh("hello world");
  goto(ui, 0, 5);
  for (let i = 0; i < 3; i++) ui.key("ArrowRight", { shiftKey: true });
  assert.strictEqual(ui.api.selectionText(), " wo");
  ui.key("Backspace");
  assert.strictEqual(ui.text(), "hellorld");
  assert.strictEqual(ui.api.selAnchor, null);
  ui.key("z", mod);
  assert.strictEqual(ui.text(), "hello world");
});

test("選択して文字を打つと置き換わる", () => {
  const ui = fresh("a + b");
  goto(ui, 0, 0);
  ui.key("ArrowRight", { shiftKey: true });
  ui.key("x");
  assert.strictEqual(ui.text(), "x + b");
});

test("選択中に矢印だけ押すと選択が畳まれる", () => {
  const ui = fresh("abcdef");
  goto(ui, 0, 1);
  ui.key("ArrowRight", { shiftKey: true });
  ui.key("ArrowRight", { shiftKey: true });
  ui.key("ArrowLeft");
  assert.strictEqual(ui.api.cursor.offset, 1);
  assert.strictEqual(ui.api.selAnchor, null);
});

test("コピー / 切り取り / 貼り付け（1行）", () => {
  const ui = fresh("forall x:Real. abs(x) >= 0");
  goto(ui, 0, 0);
  for (let i = 0; i < 4; i++) ui.key("ArrowRight", { shiftKey: true });
  const t = ui.copy();
  assert.ok(t && t.length > 0, "コピーできる");
  goto(ui, 0, ui.api.docLines[0].rootSeq.items.length);
  ui.paste(t);
  assert.ok(ui.text().endsWith(t), ui.text());
  assert.strictEqual(ui.copy(), null, "選択がなければコピーしない");

  goto(ui, 0, 0);
  for (let i = 0; i < 2; i++) ui.key("ArrowRight", { shiftKey: true });
  const cut = ui.cut();
  assert.ok(cut);
  assert.ok(!ui.text().startsWith(cut));
  ui.key("z", mod);
  assert.ok(ui.text().startsWith(cut));
});

test("分数ノードを含む範囲のコピーと貼り付け", () => {
  const ui = fresh("x + (a+b)/2 = y");
  goto(ui, 0, 0);
  ui.key("a", { metaKey: true });
  const t = ui.copy();
  assert.strictEqual(t, ui.text());
  ui.paste("");              // 空の貼り付けは何もしない
  assert.strictEqual(ui.text(), "x + (a+b)/2 = y");
  goto(ui, 0, ui.api.docLines[0].rootSeq.items.length);
  ui.paste(t);
  assert.strictEqual(ui.text(), t + t);
  assert.ok(ui.api.docLines[0].rootSeq.items.filter(i => i.kind === "frac").length === 2);
});

test("複数行の選択：コピー・削除・貼り付け（字下げを保つ）", () => {
  const ui = fresh(SRC);
  goto(ui, 1, 0);                 // thm t :
  for (let i = 0; i < 3; i++) ui.key("ArrowDown", { shiftKey: true });
  const t = ui.copy();
  assert.ok(t.startsWith("thm t :\n  h : x > 0\n  |- x/2 > 0"), JSON.stringify(t));
  ui.key("Backspace");
  assert.ok(!ui.text().includes("h : x > 0"), ui.text());
  ui.key("z", mod);
  assert.strictEqual(ui.text(), SRC);
  // 末尾に貼り付けると、字下げがそのまま再現される
  goto(ui, 5, ui.api.docLines[5].rootSeq.items.length);
  ui.key("Enter");
  ui.paste(t.split("\n").slice(0, 3).join("\n"));
  const lines = ui.text().split("\n");
  assert.deepStrictEqual(lines.slice(-3), ["thm t :", "  h : x > 0", "  |- x/2 > 0"].map(l => l));
});

test("行の途中への複数行貼り付けは、後ろの文字を最後の行につなぐ", () => {
  const ui = fresh("AAABBB");
  goto(ui, 0, 3);
  ui.paste("x\ny\nz");
  assert.strictEqual(ui.text(), "AAAx\ny\nzBBB");
  assert.strictEqual(ui.api.cursor.lineIdx, 2);
  ui.key("z", mod);
  assert.strictEqual(ui.text(), "AAABBB");
});

test("Cmd+A で全選択 → 削除", () => {
  const ui = fresh(SRC);
  ui.key("a", mod);
  ui.key("Backspace");
  assert.strictEqual(ui.text(), "");
  assert.strictEqual(ui.api.docLines.length, 1);
  ui.key("z", mod);
  assert.strictEqual(ui.text(), SRC);
});

test("分数の中から外へ選択を伸ばすと、分数ごと選ばれる", () => {
  const ui = fresh("a/b + c");
  const root = ui.api.docLines[0].rootSeq;
  const frac = root.items.find(i => i.kind === "frac");
  ui.api.setCursor(frac.num.id, 0);
  ui.key("ArrowLeft", { shiftKey: true });    // 分子の先頭から外へ
  const s = ui.api.normalizeSel();
  assert.ok(s && s.mode === "seq" && s.seq === root && s.to - s.from === 1 && root.items[s.from] === frac);
  assert.ok(ui.html().includes("mc-sel"), "選択が描画される");
  ui.key("Delete");
  assert.ok(!root.items.some(i => i.kind === "frac"));
  assert.ok(ui.text().includes("+ c"), ui.text());
});

test("Delete キーで次の1要素を消す", () => {
  const ui = fresh("abc");
  goto(ui, 0, 1);
  ui.key("Delete");
  assert.strictEqual(ui.text(), "ac");
});

test("宣言名・4文字以上の名前は立体、変数はイタリック", () => {
  const ui = fresh("axiom triangle : x = x\nthm ab : y = y\nabc + abcd + x");
  goto(ui, 2, 0);   // 描画させる
  const l0 = ui.classesOfLine(0), l1 = ui.classesOfLine(1), l2 = ui.classesOfLine(2);
  assert.ok((l0["mc-ident-fn"] || "").includes("triangle"), JSON.stringify(l0));
  assert.ok((l1["mc-ident-fn"] || "").includes("ab"), JSON.stringify(l1));   // 短くても宣言名なら立体
  assert.ok((l2["mc-ident-fn"] || "").includes("abcd"), JSON.stringify(l2));
  assert.ok((l2["mc-var"] || "").includes("abc"), JSON.stringify(l2));      // 未宣言の3文字はそのまま
  assert.ok((l2["mc-var"] || "").includes("x"), JSON.stringify(l2));
});

console.log(`${n} 件通過`);
