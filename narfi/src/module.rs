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
use crate::syntax::reset_syntax;
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
}

/// 記法の表を空にし、prelude を読み込んだ環境を作る
fn fresh_env() -> Env {
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
        (Loader { source, loaded: HashSet::new(), stack: Vec::new() }, fresh_env())
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
