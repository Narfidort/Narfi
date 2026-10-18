# Narfi for Zed

Zed で `zed: install dev extension` を実行し、このディレクトリ（editors/zed）を選ぶ。

- 文法は `../tree-sitter-narfi`（extension.toml の rev のコミットを Zed が読み込んでビルドする）。
  文法を直したら、そちらでコミットし、extension.toml の rev を書き換えて、Zed の拡張ページで Rebuild する。
- 検査は Narfi/.zed/tasks.json のタスク（`task: spawn` → narfi check）で実行する。
- 記号の入力：`snippets.json` を `~/.config/zed/snippets/narfi.json` に置いてある。`\all` と打つと補完候補に `∀` が出るので、Tab/Enter で確定する。
