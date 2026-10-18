// ファイル → 構造化 AST → ASCII の往復を出力する（tests/ui.rs から使う）
// 使い方: node tests/ui_roundtrip.js src/web_ui.html <file.narfi>
const load = require("./ui_harness.js");
const ui = load(process.argv[2]);
ui.api.loadSourceIntoDoc(require("fs").readFileSync(process.argv[3], "utf8"));
process.stdout.write(ui.text());
