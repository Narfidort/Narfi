// Narfi の VS Code 拡張：保存時の検査と、\all → ∀ のような記号の入力補助。
const vscode = require('vscode');
const cp = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');

// \ に続けて書き、スペース・改行・記号で確定する（Lean と同じ流儀）
const ABBREV = {
  all: '∀', forall: '∀', ex: '∃', exists: '∃',
  to: '→', imp: '→', and: '∧', or: '∨', not: '¬', bot: '⊥',
  vdash: '⊢', tf: '∴', therefore: '∴', impby: '⇐',
  le: '≤', ge: '≥', ne: '≠', in: '∈', cdot: '·', sq: '²',
  N: 'ℕ', Z: 'ℤ', Q: 'ℚ', R: 'ℝ', C: 'ℂ',
  a: 'α', b: 'β', g: 'γ', d: 'δ', e: 'ε', eps: 'ε', alpha: 'α', beta: 'β', gamma: 'γ',
  delta: 'δ', epsilon: 'ε', lambda: 'λ', mu: 'μ', phi: 'φ', psi: 'ψ', tau: 'τ',
  '0': '₀', '1': '₁', '2': '₂', '3': '₃', '_0': '₀', '_1': '₁', '_2': '₂', '_3': '₃',
};

function narfiPath() {
  const conf = vscode.workspace.getConfiguration('narfi').get('path');
  if (conf) return conf;
  const cargo = path.join(os.homedir(), '.cargo', 'bin', 'narfi');
  return fs.existsSync(cargo) ? cargo : 'narfi';
}

function check(doc, diags, output) {
  if (doc.languageId !== 'narfi' || doc.uri.scheme !== 'file') return;
  cp.execFile(narfiPath(), ['check', '--diag', doc.fileName], { timeout: 20000 }, (err, stdout, stderr) => {
    if (err && !stdout) {
      output.appendLine(`narfi を実行できない: ${err.message}\n${stderr}`);
      output.show(true);
      return;
    }
    const list = [];
    for (const raw of stdout.split('\n')) {
      const m = raw.match(/^(ERROR|SORRY)\t(\d+)\t(.*)$/);
      if (!m) continue;
      const line = Math.max(0, Math.min(doc.lineCount - 1, Number(m[2]) - 1));
      const text = m[3].replace(/\\n/g, '\n').replace(/\\\\/g, '\\');
      const l = doc.lineAt(line);
      const range = new vscode.Range(line, l.firstNonWhitespaceCharacterIndex, line, l.text.length);
      const sev = m[1] === 'ERROR' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning;
      const d = new vscode.Diagnostic(range, text, sev);
      d.source = 'narfi';
      list.push(d);
    }
    diags.set(doc.uri, list);
  });
}

function activate(context) {
  const diags = vscode.languages.createDiagnosticCollection('narfi');
  const output = vscode.window.createOutputChannel('Narfi');
  context.subscriptions.push(diags, output);

  const onSave = (doc) => {
    if (vscode.workspace.getConfiguration('narfi').get('checkOnSave')) check(doc, diags, output);
  };
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(onSave),
    vscode.workspace.onDidOpenTextDocument(onSave),
    vscode.workspace.onDidCloseTextDocument((doc) => diags.delete(doc.uri)),
    vscode.commands.registerCommand('narfi.check', () => {
      const ed = vscode.window.activeTextEditor;
      if (ed) check(ed.document, diags, output);
    }),
  );
  vscode.workspace.textDocuments.forEach(onSave);

  // 記号の入力補助
  context.subscriptions.push(vscode.workspace.onDidChangeTextDocument((e) => {
    if (e.document.languageId !== 'narfi') return;
    const ed = vscode.window.activeTextEditor;
    if (!ed || ed.document !== e.document) return;
    for (const ch of e.contentChanges) {
      if (!/^[\s().,:|]/.test(ch.text)) continue;
      const pos = ch.range.start;
      const before = e.document.lineAt(pos.line).text.slice(0, pos.character);
      const m = before.match(/\\([A-Za-z0-9_]+)$/);
      if (!m || !(m[1] in ABBREV)) continue;
      const range = new vscode.Range(pos.line, pos.character - m[0].length, pos.line, pos.character);
      ed.edit((b) => b.replace(range, ABBREV[m[1]]), { undoStopBefore: false, undoStopAfter: false });
      break;
    }
  }));
}

function deactivate() {}

module.exports = { activate, deactivate };
