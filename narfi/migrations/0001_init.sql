-- クラウド保存（Cloudflare D1 = SQLite）
-- users：GitHub のアカウント（id は GitHub の数のID。ログイン名は変わりうるので表示用）
CREATE TABLE users (
  id INTEGER PRIMARY KEY,
  login TEXT NOT NULL,
  created_at INTEGER NOT NULL,
  last_login INTEGER NOT NULL
);

-- sessions：ログイン中のブラウザ。Cookie の値そのものではなく、その SHA-256 を持つ
CREATE TABLE sessions (
  token_hash TEXT PRIMARY KEY,
  user_id INTEGER NOT NULL,
  expires_at INTEGER NOT NULL
);
CREATE INDEX sessions_user ON sessions(user_id);

-- files：利用者ごとのファイル。version は保存のたびに 1 増える（同時に編集したときの衝突の検出用）
CREATE TABLE files (
  user_id INTEGER NOT NULL,
  path TEXT NOT NULL,
  src TEXT NOT NULL,
  size INTEGER NOT NULL,
  version INTEGER NOT NULL,
  updated_at INTEGER NOT NULL,
  PRIMARY KEY (user_id, path)
);
