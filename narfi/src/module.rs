//! ファイルの読み込み：prelude・import の解決・循環 import の検出。
//!
//! `import analysis.limits` は `analysis/limits.narfi` を次の順に探す。
//!   1. import を書いたファイルと同じディレクトリ
//!   2. ライブラリ（ディスクなら NARFI_PATH・~/.narfi/lib・同梱の lib/、ブラウザなら保存領域の lib/ と同梱の lib/）
//! 読み込んだファイルはその場で検査され、定理・定義・notation が環境に入る。
//!
//! ファイルの置き場所は `FileSource` で差し替えられる（ディスク：`DiskSource`、ブラウザ：`MemSource`）。
//! どちらでも、ファイルは「鍵」（パスの文字列）で区別する。

use crate::elab::{Env, Report, check_module};
use crate::parser::{Module, ParseError, parse_module, parse_standalone};
use crate::syntax::{SyntaxTable, reset_syntax, syntax_restore, syntax_snapshot};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

const PRELUDE: &str = include_str!("prelude.narfi");

/// ファイルの置き場所
pub trait FileSource {
    /// `import name` を、dir（import を書いたファイルのディレクトリの鍵）から探す。見つかれば (鍵, 中身)。
    fn find(&self, name: &str, dir: Option<&str>) -> Option<(String, String)>;
    /// 鍵のディレクトリ（その中の import の起点）
    fn dir_of(&self, key: &str) -> Option<String>;
    /// エラーメッセージ用の短い名前
    fn short(&self, key: &str) -> String {
        key.rsplit('/').next().unwrap_or(key).to_string()
    }
    /// 探した場所の説明（見つからなかったとき）
    fn searched(&self) -> String;
}

fn rel_path(name: &str) -> String {
    format!("{}.narfi", name.replace('.', "/"))
}

// ---------------------------------------------------------------- ディスク

pub struct DiskSource {
    search: Vec<PathBuf>,
}

impl DiskSource {
    /// NARFI_PATH・~/.narfi/lib・同梱の lib/ を探す
    pub fn new() -> DiskSource {
        let mut search: Vec<PathBuf> = std::env::var("NARFI_PATH")
            .map(|v| v.split(':').filter(|s| !s.is_empty()).map(PathBuf::from).collect())
            .unwrap_or_default();
        if let Some(h) = std::env::var_os("HOME") {
            search.push(PathBuf::from(h).join(".narfi").join("lib"));
        }
        search.push(Path::new(env!("CARGO_MANIFEST_DIR")).join("lib"));
        DiskSource { search }
    }
}

impl FileSource for DiskSource {
    fn find(&self, name: &str, dir: Option<&str>) -> Option<(String, String)> {
        let rel = rel_path(name);
        let path = dir
            .map(PathBuf::from)
            .into_iter()
            .chain(self.search.iter().cloned())
            .map(|d| d.join(&rel))
            .find(|p| p.is_file())?;
        let path = path.canonicalize().unwrap_or(path);
        let src = std::fs::read_to_string(&path).ok()?;
        Some((path.to_string_lossy().into_owned(), src))
    }
    fn dir_of(&self, key: &str) -> Option<String> {
        Path::new(key).parent().map(|p| p.to_string_lossy().into_owned())
    }
    fn searched(&self) -> String {
        "同じディレクトリ・NARFI_PATH・~/.narfi/lib・narfi/lib/".into()
    }
}

// ---------------------------------------------------------------- メモリ（ブラウザ）

/// ブラウザの保存領域のファイル（鍵は `week1/a.narfi` のような相対パス）と、同梱の標準ライブラリ（`lib:std/…`）
pub struct MemSource {
    pub files: HashMap<String, String>,
}

impl FileSource for MemSource {
    fn find(&self, name: &str, dir: Option<&str>) -> Option<(String, String)> {
        let rel = rel_path(name);
        let mut cands = Vec::new();
        if let Some(d) = dir.filter(|d| !d.is_empty() && !d.starts_with("lib:")) {
            cands.push(format!("{d}/{rel}"));
        }
        cands.push(rel.clone());
        cands.push(format!("lib/{rel}"));
        for c in cands {
            if let Some(s) = self.files.get(&c) {
                return Some((c, s.clone()));
            }
        }
        crate::stdlib::get(&rel).map(|s| (format!("lib:std/{rel}"), s.to_string()))
    }
    fn dir_of(&self, key: &str) -> Option<String> {
        Some(key.rsplit_once('/').map(|(d, _)| d.to_string()).unwrap_or_default())
    }
    fn searched(&self) -> String {
        "同じフォルダ・保存領域の直下と lib/・標準ライブラリ".into()
    }
}

// ---------------------------------------------------------------- 読み込み

pub struct Loader {
    source: Box<dyn FileSource>,
    loaded: HashSet<String>,
    /// 読み込み中のファイル（循環の検出用）
    stack: Vec<String>,
    /// 読み込んだファイル：(import の名前, 探した起点, 見つかった鍵, 中身の要約)。使い回しの確かめに使う
    trace: Vec<(String, Option<String>, String, u64)>,
}

// ---------------------------------------------------------------- 使い回し（編集のたびの検査を速くする）
//
// 編集のたびに prelude と import したライブラリを読み直して検査すると重い（ライブラリが大きいと検査の大半）。
// そこで、prelude を読んだ状態と、ファイル冒頭の import をすべて読み終えた状態（環境と記法の表）を覚えておき、
// 次のときに使い回す。検査は決定的なので、次の条件がすべて同じなら、読み直しても同じ状態になる：
//   ・冒頭の import の並び・起点のディレクトリ・言語
//   ・前回読み込んだすべてのファイルが、同じ名前で探して同じ鍵で見つかり、中身が同じ
// 1 つでも違えば使い回さずに読み直す。使い回した結果と読み直した結果が同じことは tests/examples.rs で確かめる。

struct PrefixCache {
    key: String,
    trace: Vec<(String, Option<String>, String, u64)>,
    env: Env,
    syntax: SyntaxTable,
    loaded: HashSet<String>,
}

thread_local! {
    static PRELUDE_STATE: RefCell<Option<(Env, SyntaxTable)>> = const { RefCell::new(None) };
    static PREFIXES: RefCell<Vec<PrefixCache>> = const { RefCell::new(Vec::new()) };
    static CACHE_ON: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// 使い回しを止める・戻す（テストで、使い回した結果と読み直した結果を比べるため）
pub fn set_cache_enabled(on: bool) {
    CACHE_ON.with(|c| c.set(on));
    if !on {
        PREFIXES.with(|p| p.borrow_mut().clear());
    }
}

fn hash_str(s: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

/// ファイル冒頭の import の行（空行・コメントは飛ばし、それ以外の行が来たら終わり）
fn header_imports(src: &str) -> String {
    let mut out = Vec::new();
    for l in src.lines() {
        let t = l.trim();
        // 空行・コメント・見出し（# …）・版（edition）は飛ばす
        if t.is_empty() || t.starts_with("--") || t.starts_with("//") || t.starts_with('#') || t.starts_with("edition ") {
            continue;
        }
        if t.starts_with("import ") {
            out.push(t.to_string());
        } else {
            break;
        }
    }
    out.join("\n")
}

/// 記法の表を空にし、prelude を読み込んだ環境を作る（prelude は変わらないので、一度読んだものを写して使う）
fn fresh_env() -> Env {
    if CACHE_ON.with(|c| c.get()) {
        if let Some((env, syn)) = PRELUDE_STATE.with(|p| p.borrow().clone()) {
            syntax_restore(syn);
            return env;
        }
    }
    let env = fresh_env_uncached();
    PRELUDE_STATE.with(|p| *p.borrow_mut() = Some((env.clone(), syntax_snapshot())));
    env
}

fn fresh_env_uncached() -> Env {
    reset_syntax();
    let mut env = Env::default();
    let prelude = parse_standalone(PRELUDE).expect("prelude のパースに失敗");
    let reports =
        check_module(&mut env, &prelude, false, true).unwrap_or_else(|e| panic!("prelude:{}: {}", e.line, e.msg));
    for r in reports {
        if let Some(e) = &r.err {
            panic!("prelude の定理 {} が通らない: {}", r.name, e.msg);
        }
    }
    env
}

thread_local! {
    /// ブラウザ版：ディスクの代わりに読むファイルの表（wasm.rs が設定する）
    static MEMORY_FILES: std::cell::RefCell<Option<HashMap<String, String>>> = const { std::cell::RefCell::new(None) };
}

/// これ以降のローダーが、ディスクではなく files（とメモリの標準ライブラリ）から読むようにする
pub fn use_memory_files(files: HashMap<String, String>) {
    MEMORY_FILES.with(|m| *m.borrow_mut() = Some(files));
}

impl Loader {
    /// ローダー（ふつうはディスクから。ブラウザ版では use_memory_files で設定した表から）
    pub fn new() -> (Loader, Env) {
        match MEMORY_FILES.with(|m| m.borrow().clone()) {
            Some(files) => Self::with_source(Box::new(MemSource { files })),
            None => Self::with_source(Box::new(DiskSource::new())),
        }
    }

    pub fn with_source(source: Box<dyn FileSource>) -> (Loader, Env) {
        (Loader { source, loaded: HashSet::new(), stack: Vec::new(), trace: Vec::new() }, fresh_env())
    }

    /// ファイル冒頭の import を先に読む。前回と同じ（上の条件）なら、覚えておいた状態を使い回す。
    /// このあと本体を読むと、冒頭の import は読み込み済みとして飛ばされる。
    /// key は本体のファイルの鍵（自分自身を import する循環の検出のため）
    fn prepare_imports(&mut self, env: &mut Env, src: &str, key: Option<&str>, dir: Option<&str>) {
        if !CACHE_ON.with(|c| c.get()) {
            return;
        }
        let header = header_imports(src);
        if header.is_empty() {
            return;
        }
        let ck = format!("{}\u{1}{}\u{1}{}\u{1}{}", key.unwrap_or(""), dir.unwrap_or(""), crate::locale::current().name, header);
        let hit = PREFIXES.with(|p| {
            let p = p.borrow();
            let e = p.iter().find(|e| e.key == ck)?;
            // 読み込んだファイルが、同じ鍵で見つかり、中身も同じか
            let same = e.trace.iter().all(|(name, d, k, h)| match self.source.find(name, d.as_deref()) {
                Some((k2, s2)) => &k2 == k && hash_str(&s2) == *h,
                None => false,
            });
            same.then(|| (e.env.clone(), e.syntax.clone(), e.loaded.clone()))
        });
        if let Some((e, syn, loaded)) = hit {
            *env = e;
            syntax_restore(syn);
            self.loaded = loaded;
            return;
        }
        // 読み直して覚える。エラーなら覚えない（本体を読むときに、正しい行番号で報告される）
        let (saved_env, saved_syn) = (env.clone(), syntax_snapshot());
        self.trace.clear();
        if let Some(k) = key {
            self.stack.push(k.to_string());
        }
        let r = self.parse(env, &header, dir);
        if key.is_some() {
            self.stack.pop();
        }
        match r {
            Ok(_) => {
                let entry = PrefixCache { key: ck, trace: self.trace.clone(), env: env.clone(), syntax: syntax_snapshot(), loaded: self.loaded.clone() };
                PREFIXES.with(|p| {
                    let mut p = p.borrow_mut();
                    p.retain(|e| e.key != entry.key);
                    p.insert(0, entry);
                    p.truncate(4);
                });
            }
            Err(_) => {
                *env = saved_env;
                syntax_restore(saved_syn);
                self.loaded.clear();
            }
        }
    }

    /// ソースを読む（import 先は検査して env に入れる）。このソース自身の検査はしない。
    /// dir は相対 import の起点（ディレクトリの鍵）。
    pub fn parse(&mut self, env: &mut Env, src: &str, dir: Option<&str>) -> Result<Module, ParseError> {
        let dir = dir.map(str::to_string);
        parse_module(src, &mut |name, line| self.import(env, name, line, dir.as_deref()))
    }

    /// 鍵 key のファイルとして読む。自分自身を import する循環も検出できるよう、読み込み中として扱う。
    pub fn parse_key(&mut self, env: &mut Env, src: &str, key: &str) -> Result<Module, ParseError> {
        self.stack.push(key.to_string());
        let dir = self.source.dir_of(key);
        let m = self.parse(env, src, dir.as_deref());
        self.stack.pop();
        self.loaded.insert(key.to_string());
        m
    }

    /// ディスクのファイルとして読む
    pub fn parse_file(&mut self, env: &mut Env, src: &str, file: &Path) -> Result<Module, ParseError> {
        let path = file.canonicalize().unwrap_or_else(|_| file.to_path_buf());
        self.parse_key(env, src, &path.to_string_lossy())
    }

    fn import(&mut self, env: &mut Env, name: &str, line: usize, dir: Option<&str>) -> Result<(), ParseError> {
        let err = |msg: String| Err(ParseError { line, msg });
        let Some((key, src)) = self.source.find(name, dir) else {
            return err(format!("import {name}: {} が見つからない（{} を探した）", rel_path(name), self.source.searched()));
        };
        self.trace.push((name.to_string(), dir.map(str::to_string), key.clone(), hash_str(&src)));
        if let Some(k) = self.stack.iter().position(|p| *p == key) {
            let cycle: Vec<String> =
                self.stack[k..].iter().chain(std::iter::once(&key)).map(|p| self.source.short(p)).collect();
            return err(format!("循環 import: {}", cycle.join(" → ")));
        }
        if self.loaded.contains(&key) {
            return Ok(());
        }
        let shown = key.clone();
        self.stack.push(key.clone());
        let dir = self.source.dir_of(&key);
        let m = self.parse(env, &src, dir.as_deref());
        self.stack.pop();
        let m = match m {
            Ok(m) => m,
            // 循環 import の報告は内側のものをそのまま伝える
            Err(e) if e.msg.starts_with("循環 import") => return err(e.msg),
            Err(e) => return err(format!("import {name}: {shown}:{}: {}", e.line, e.msg)),
        };
        let reports: Vec<Report> = match check_module(env, &m, false, false) {
            Ok(r) => r,
            Err(e) => return err(format!("import {name}: {shown}:{}: {}", e.line, e.msg)),
        };
        if let Some(r) = reports.iter().find(|r| r.err.is_some()) {
            let e = r.err.as_ref().unwrap();
            return err(format!(
                "import {name}: {shown}:{} の定理 {} が通らない: {}",
                e.line,
                r.name,
                e.msg.lines().next().unwrap_or("")
            ));
        }
        self.loaded.insert(key);
        Ok(())
    }
}

pub type Loaded = (Env, Module, Vec<Report>);

/// 1つのソースを新しい環境で読み込み、検査する（ディスク版。Web・prose 用）
/// file は相対 import の起点（まだ保存されていないソースなら None）。
pub fn load_and_check(src: &str, file: Option<&Path>) -> Result<Loaded, ParseError> {
    let (mut ld, mut env) = Loader::new();
    let key = file.map(|f| f.canonicalize().unwrap_or_else(|_| f.to_path_buf()).to_string_lossy().into_owned());
    let dir = key.as_deref().and_then(|k| ld.source.dir_of(k));
    ld.prepare_imports(&mut env, src, key.as_deref(), dir.as_deref());
    let m = match file {
        Some(f) => ld.parse_file(&mut env, src, f)?,
        None => ld.parse(&mut env, src, None)?,
    };
    let reports = check_module(&mut env, &m, false, false)?;
    Ok((env, m, reports))
}

/// ファイルの置き場所を指定して読み込み、検査する（ブラウザ版）
pub fn load_and_check_with(source: Box<dyn FileSource>, src: &str, key: &str) -> Result<Loaded, ParseError> {
    let (mut ld, mut env) = Loader::with_source(source);
    let dir = ld.source.dir_of(key);
    ld.prepare_imports(&mut env, src, Some(key), dir.as_deref());
    let m = ld.parse_key(&mut env, src, key)?;
    let reports = check_module(&mut env, &m, false, false)?;
    Ok((env, m, reports))
}

/// 読み込むだけで検査はしない（ソース変換用）。import 先は検査される。
pub fn parse_source(src: &str, dir: Option<&Path>) -> Result<Module, ParseError> {
    let (mut ld, mut env) = Loader::new();
    let dir = dir.map(|d| d.to_string_lossy().into_owned());
    ld.parse(&mut env, src, dir.as_deref())
}
