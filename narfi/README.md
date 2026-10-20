# narfi — Narfi の証明検査器（試作）

> **v2**：小さな核（kernel）が証明項を検算する構成に作り直した。
> 仕様と学習ノートは [docs/](../docs/README.md)。以下の表の多くは v1 からの説明で、v2 では型の書き方などが違う
> （v1 は `v1.0` タグ）。

v1 の仕様（[docs/archived/](../docs/archived/README.md)）の核に、フィードバックで出た拡張の一部を加えたものを検査する。Rust 製で、外部クレートは使わない。

```
cargo run -- check examples/basics.narfi examples/analysis.narfi
cargo run -- check examples/limits.narfi            # def・notation・import（lib/analysis/limits.narfi）
cargo run -- check --trace examples/analysis.narfi   # 各行の文脈と goal を表示
cargo run -- check examples/errors.narfi             # わざと間違えた証明
cargo test                                           # 正しい証明は通り、間違った証明は1本も通らないことを確認
```

拡張子は `.narfi`。練習問題は `../練習.narfi`、エディタ拡張は `../editors/vscode/`。

- `sorry`：どんな goal も仮に閉じる。その位置で残っている goal を表示し、定理は「△ 未完成」になる（sorry に頼る定理を使った定理も未完成になる）。
- 数のあとの積（v2.5.6）：`2x`・`2(a + b)`・`3a_n` は `2 * x` などと同じ。`ab` は 1 つの名前（積にはしない）。Prose・LaTeX では積を記号なしで並べて表示する（`2x`、`ab`）。
- 数列の添字（v2.5.4）：`a : ℕ → ℝ` と宣言した a について、`a_n`・`a_{n+1}`・`a_1` は `a(n)`・`a(n+1)`・`a(1)` と読む（`N_1` のように宣言した名前はそのまま名前）。
- 仮定の中身は省略できない（v2.5 から）：`Fix ε | hε : ε > 0`・`assume h : P`・`Case succ k, IH : φ`。書かないとエラーになり、goal から決まる中身を `help:` に示す（エディタでは行末で Tab を押すと入る）。変数の型（`Fix ε` の `: ℝ`）は goal から決まるので省略してよい。
- `--diag`：エディタ向けの出力（`ERROR` / `SORRY`・行・本文のタブ区切り）。

## v0.5 に加えたもの

| 構文 | 意味 |
|---|---|
| `∀ε>0. φ` / `∃N:ℕ. φ` / `∀n≥N. φ` | 範囲付き量化子。`∀x>a. φ` は `∀x. x>a → φ`、`∃x>a. φ` は `∃x. x>a ∧ φ` の略記 |
| `Obtain N(ε), hN : e` | 依存関係の注釈。N を取り出す位置で、スコープにある Fix 変数がちょうど (ε) であることを検査する |
| `∴ φ` | 直前に示したもの（スコープを出た結果・事実の行など）が φ であることを検査する |
| `Fix n, m` | 複数の Fix |
| `Case succ k, IH : φ` | 末尾の `:` は書いても書かなくてもよい。IH の中身 `: φ` は v2.5 から必ず書く |
| `choose t, j` | 範囲付き ∃ の条件（`t > 0` など）を j で示す |
| `axiom name : Γ ⊢ φ` | 補題を公理として置く（三角不等式など） |
| `sorry` | 証明を後回しにする（残っている goal を表示） |
| `def is_lim(a, α) := φ` | 述語の定義。証明の中では必要なところで自動的に展開される（`conv_a(ε/2, …)`・`Fix ε` など）。引数 `a` は関数の位置（`a(n)`）にも置け、`a + b` を渡すと `a(n) + b(n)` と各点ごとに読む |
| `notation a "⟶" α := is_lim(a, α)` | 中置の記法。`a ⟶ α` は `is_lim(a, α)` として読まれ、表示・Prose・LaTeX でも記法のまま出る。ASCII では `\longrightarrow`（`\lto`）。組み込みの記号（`->` `<` など）とは衝突させられない |
| `import analysis.limits` | `analysis/limits.narfi` を、同じディレクトリ → `NARFI_PATH` → `narfi/lib/` の順に探して読み込む。循環 import はエラー |
| `h : φ by j` | 事実の行（v2.6 から。`have` は古い書き方）。`φ` だけ書くと、根拠の候補がエラーの直し方として出る |

## Web 版（インストール不要）

ブラウザで開くだけで使える版。検査器を WebAssembly にしてブラウザの中で動かすので、
証明の内容がサーバーに送られることはない。`main` に push すると GitHub Actions がテストを回し、
Cloudflare Pages に自動で置く（`.github/workflows/web.yml`）。

| | ローカル版（`narfi web`） | Web 版 |
|---|---|---|
| ファイル | パソコンのフォルダ | ブラウザ内の保存領域。`File` → `Upload File…`・`Upload Folder…` で読み込み、`Download All (.zip)` で書き出す。GitHub でログインするとクラウドと同期（削除・名前の変更も） |
| 自分用ライブラリ | `~/.narfi/lib` | 保存領域の `lib/`（`lib/mydefs.narfi` は `import mydefs`） |
| PDF | LaTeX で組版 | `Print` から「PDF として保存」 |
| AI 補助（自分の API キー。Preferences で登録） | 使える | 使える（ブラウザから直接呼べない接続先は Narfi のサーバーが中継する。キーは保存しない） |

ブラウザの保存領域は、ブラウザのデータを消すと消える。大事なファイルは `Export` で書き出しておくか、クラウド保存を使う。

### クラウド保存（GitHub でログイン）

右上の `Sign in with GitHub` でログインすると、ファイルがクラウドにも保存され、ほかの PC・ブラウザでも同じファイルが開ける。
誰でも GitHub のアカウントで使える（1 人あたり 1000 ファイル・20 MB まで）。

- 編集はこれまでどおりブラウザ内の保存領域に保存し、少し後でクラウドに送る（右上に `同期済み`・`未送信あり`・`オフライン`）。
  ネットにつながっていない間も使え、つながったら送る。ほかの端末の変更は、タブに戻ったときと 30 秒ごとに取ってくる。
- 2 つの端末で同じファイルを同時に変えたときは、どちらも消さない：そのブラウザの変更をそのまま残し、
  もう一方を `名前.conflict-日時.narfi` として残す。
- 保存先は Cloudflare D1（SQLite）。表は `users`（GitHub の ID とログイン名）・`sessions`・`files`（`migrations/`）。
  GitHub には権限を求めない（公開プロフィールの ID とログイン名だけを使う。GitHub のトークンは保存しない）。
- メニューの `Log out` でこのブラウザからファイルを消してログアウト、`アカウントを削除…` でクラウドのファイルと記録をすべて消す。

仕組み：`functions/`（Cloudflare Pages Functions。`/auth/login`・`/auth/callback`・`/auth/logout`・`/cloud/me`・`/cloud/files`・`/cloud/file`）、
`server/common.js`（セッション・CSRF 対策・上限）、`src/web_static.js`（同期）。
D1 の用意と秘密の登録は CI（`scripts/cloud-setup.sh`）が行う。最初に一度だけ必要な設定：

1. GitHub の Settings → Developer settings → OAuth Apps → New OAuth App
   - Homepage URL：`https://narfi.pages.dev`
   - Authorization callback URL：`https://narfi.pages.dev/auth/callback`
2. できた App の Client ID と、Generate a new client secret で作った秘密を、リポジトリの
   Settings → Secrets and variables → Actions に `NARFI_GITHUB_CLIENT_ID`・`NARFI_GITHUB_CLIENT_SECRET` として登録する
3. Cloudflare の API トークン（`CLOUDFLARE_API_TOKEN`）に、Account の「D1: Edit」の権限を足す

手元でログインと同期を確かめる（GitHub には行かず、セッションを手で作る）：

```
./scripts/build-site.sh
npx wrangler d1 migrations apply narfi --local
printf 'GITHUB_CLIENT_ID=dummy\nGITHUB_CLIENT_SECRET=dummy\n' > .dev.vars
npx wrangler pages dev site --port 8799
```

手元で組み立てて確かめる：

```
rustup target add wasm32-unknown-unknown
./scripts/build-site.sh                                # site/ にできる
node tests/wasm_smoke.mjs site/narfi.wasm target/debug/narfi   # ローカル版と結果が同じか
python3 -m http.server -d site 8000                    # http://127.0.0.1:8000 で開く
```

## Web エディタの操作

```
cargo install --path .        # narfi コマンドを入れる（~/.cargo/bin）
narfi web                     # 前回のフォルダで起動（初回はカレントディレクトリ）
narfi web --dir ~/授業/解析    # 作業フォルダを指定して起動（次回からはこのフォルダ）
```

ブラウザで `http://127.0.0.1:3000` が開く。サーバーは自分の Mac の中だけで動き、ほかの Web サイトからは使えない
（`Host`・`Origin` を確認して拒否する）。数式の表示（KaTeX）も同梱しているので、ネットにつながっていなくても使える。

| 操作 | やり方 |
|---|---|
| 画面 | 上：`File` メニュー・開いたファイルのタブ・検査の結果。下：左がファイル一覧の表示切り替え（アイコン）と開いているファイルのパス、右が言語のボタン（読みの表示のオン・オフ。言語は Preferences（Web 版は右上のアイコンのメニュー、ローカル版は右下の歯車。⌘,））・GitHub・ライト／ダーク・右側（Goal など）の表示切り替え |
| タブ | 開いたファイルが上にタブとして並ぶ。切り替えても保存していない変更は残り（● が付く）、再読み込みしても前回のタブが戻る。`×` か中クリックで閉じる |
| チュートリアル | 右の `Learn` タブ（はじめて開いたときに出る）。8 つのレッスンと練習・答え。`練習を開く` で新しいタブに練習が開く |
| コース「公理へ」 | `Learn` タブの後半。和の極限から始めて、章ごとに定理が頼る公理（Goal タブの一覧に出る）を短く・弱くしていく。`コースのファイルを開く` で `course/` にファイルができる |
| 証明木 | 証明の行で右クリック →「証明木を見る」。kernel が検算した証明を自然演繹の木（Gentzen 式・Fitch 式）で見る |
| 記法の補完 | 文脈（goal と仮定）にある式を候補に出す。`\|` で絶対値（`\|a_n − α\|`）、`(n \|->` で数列（`(n : ℕ ↦ a_n + b_n)`）、`\sum` で和（Σ_{k<n} a_k）、`Ctrl+Space` で全部。Tab・Enter で入る |
| 記号の入力 | `\|-`・`\vdash`（⊢）、`|->`・`\mapsto`（↦）、`<=`（≤）、`->`（→）、`_`（添字）、`/`・`\fr`（分数）。`|-x|` は絶対値のまま（⊢ にならない） |
| ファイル一覧 | フォルダは開閉できる。上のアイコンか右クリックで新しいファイル・フォルダ、右クリックで名前の変更・削除、ドラッグでフォルダに移す。ローカル版で削除したものはゴミ箱に入る |
| フォルダを開く | `File` → `Open Folder…`、または `⇧⌘O`（Mac のダイアログ）。前回のフォルダを覚えている |
| ファイルを開く | 一覧をクリック、`File` → `Open…`、または `⌘O` |
| 新しいファイル／保存／名前を付けて保存 | `File` → `New`／`Save`（`⌘S`）／`Save As…`（`⇧⌘S`） |
| 自動保存 | `File` → `Auto Save`（✓ が付いているとき）：編集が止まって約1秒後と、タブを切り替えたときに保存する。名前のない文書はブラウザ内に下書きとして残る |
| 印刷 | `File` → `Print`（`⌘P`）：証明文（Prose）を印刷用に整えて開く。「PDF として保存」もできる |
| PDF | `File` → `PDF (LaTeX)`（`⇧⌘P`）：LaTeX（LuaLaTeX）で組版した PDF を作る。TeX が入っていない場合は `Print` を使う |
| ライブラリ | 自分用は `~/.narfi/lib`（ここに置いた `.narfi` は `import` できる）、標準は同梱の `lib/`。一覧から読み取り専用で開ける |
| 元に戻す／やり直す | `⌘Z` ／ `⇧⌘Z`・`Ctrl+Y` |
| 範囲選択 | `Shift+矢印`、マウスドラッグ、`Shift+クリック`、全選択 `⌘A` |
| コピー・切り取り・貼り付け | `⌘C` / `⌘X` / `⌘V`（クリップボードには ASCII のコードが入る） |

名前の字体は、宣言した名前（`thm` / `axiom` / `def` の直後）と 4 文字以上の名前が立体、1〜3 文字の変数はイタリックで描かれる。

## 信頼の土台（何を信じれば結果を信じてよいか）

- **核**：`check.rs` の推論規則（→・∀・∃・∧・∨・⊥・背理法・帰納法・EQ2）と単一化。
- **自動証明（oracle）**：`arith.rs` の `ring`（多項式の正規化）、`linarith`（Fourier–Motzkin の消去法）、`decide`（計算）。今は証明書を出さないので、このコードも信じる必要がある。そのため、使った定理には `〔自動証明: …〕` と表示する（依存は定理をまたいで伝わる）。
- **公理**：自分で置いた `axiom` も、使った定理に `〔公理: …〕` と表示する。
- **連鎖**：`a ≤ b < c` の推移律は組み込み。各段の根拠がそのまま当てはまらないときは、根拠の命題を事実として linarith で補う（このときも `自動証明: linarith` と表示される）。

## まだできないこと・既知の穴

- **項の型検査をしていない**：`∀x:ℕ` に `-1` や実数を代入しても止められない。型 `?`（書かれていない型）は何にでも合うものとして扱う。
- 自動証明は証明書を出さない（上記）。
- 二階のペアノ公理 PA3 は書けない（帰納法は `induction` として組み込み）。λ を使った `EQ2(h, λz. …, hφ)` も未対応。
- `S(k)` と `k + 1` は核の中では別の項（ring・linarith の中でだけ同じとみなす）。
- 束縛の `.` の直後には空白が必要（`∀x:ℝ. φ`）。`∀x.φ` は `x.φ` という名前として読まれる。
