//! ファイルの読み込み：prelude・import の解決・循環 import の検出。
//!
//! `import analysis.limits` は `analysis/limits.narfi` を次の順に探す。
//!   1. import を書いたファイルと同じディレクトリ
//!   2. 環境変数 NARFI_PATH（`:` 区切り）
//!   3. 標準ライブラリ `narfi/lib/`
//! 読み込んだファイルはその場で検査され、定理・定義・notation が環境に入る。

use crate::check::{Env, Report, check_module};
use crate::parser::{Module, ParseError, parse_module, parse_standalone};
use crate::syntax::reset_syntax;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

const PRELUDE: &str = include_str!("prelude.narfi");

pub struct Loader {
    search: Vec<PathBuf>,
    loaded: HashSet<PathBuf>,
    /// 読み込み中のファイル（循環の検出用）
    stack: Vec<PathBuf>,
}

impl Loader {
    /// 記法の表を空にし、prelude を読み込んだ環境とローダーを作る
    pub fn new() -> (Loader, Env) {
        reset_syntax();
        let mut env = Env::default();
        let prelude = parse_standalone(PRELUDE).expect("prelude のパースに失敗");
        for r in check_module(&mut env, &prelude, false, true) {
            assert!(r.err.is_none(), "prelude の定理 {} が通らない", r.name);
        }
        let mut search: Vec<PathBuf> = std::env::var("NARFI_PATH")
            .map(|v| v.split(':').filter(|s| !s.is_empty()).map(PathBuf::from).collect())
            .unwrap_or_default();
        search.push(Path::new(env!("CARGO_MANIFEST_DIR")).join("lib"));
        let ld = Loader {
            search,
            loaded: HashSet::new(),
            stack: Vec::new(),
        };
        (ld, env)
    }

    /// ソースを読む（import 先は検査して env に入れる）。このソース自身の検査はしない。
    /// dir は相対 import の起点。
    pub fn parse(&mut self, env: &mut Env, src: &str, dir: Option<&Path>) -> Result<Module, ParseError> {
        let dir = dir.map(Path::to_path_buf);
        parse_module(src, &mut |name, line| self.import(env, name, line, dir.as_deref()))
    }

    /// ファイルを読む。自分自身を import する循環も検出できるよう、読み込み中として扱う。
    pub fn parse_file(&mut self, env: &mut Env, src: &str, file: &Path) -> Result<Module, ParseError> {
        let path = file.canonicalize().unwrap_or_else(|_| file.to_path_buf());
        self.stack.push(path.clone());
        let m = self.parse(env, src, file.parent());
        self.stack.pop();
        self.loaded.insert(path);
        m
    }

    fn resolve(&self, name: &str, dir: Option<&Path>) -> Option<PathBuf> {
        let rel: PathBuf = name.split('.').collect::<PathBuf>().with_extension("narfi");
        dir.into_iter()
            .chain(self.search.iter().map(PathBuf::as_path))
            .map(|d| d.join(&rel))
            .find(|p| p.is_file())
            .map(|p| p.canonicalize().unwrap_or(p))
    }

    fn import(&mut self, env: &mut Env, name: &str, line: usize, dir: Option<&Path>) -> Result<(), ParseError> {
        let err = |msg: String| Err(ParseError { line, msg });
        let Some(path) = self.resolve(name, dir) else {
            return err(format!(
                "import {name}: {} が見つからない（同じディレクトリ・NARFI_PATH・narfi/lib/ を探した）",
                name.replace('.', "/") + ".narfi"
            ));
        };
        if let Some(k) = self.stack.iter().position(|p| *p == path) {
            let cycle: Vec<String> = self.stack[k..]
                .iter()
                .chain(std::iter::once(&path))
                .map(|p| p.file_name().unwrap_or_default().to_string_lossy().into_owned())
                .collect();
            return err(format!("循環 import: {}", cycle.join(" → ")));
        }
        if self.loaded.contains(&path) {
            return Ok(());
        }
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => return err(format!("import {name}: {} が読めない: {e}", path.display())),
        };
        let shown = path.display().to_string();
        self.stack.push(path.clone());
        let m = self.parse(env, &src, path.parent());
        self.stack.pop();
        let m = match m {
            Ok(m) => m,
            // 循環 import の報告は内側のものをそのまま伝える
            Err(e) if e.msg.starts_with("循環 import") => return err(e.msg),
            Err(e) => return err(format!("import {name}: {shown}:{}: {}", e.line, e.msg)),
        };
        let reports: Vec<Report> = check_module(env, &m, false, false);
        if let Some(r) = reports.iter().find(|r| r.err.is_some()) {
            let e = r.err.as_ref().unwrap();
            return err(format!(
                "import {name}: {shown}:{} の定理 {} が通らない: {}",
                e.line,
                r.name,
                e.msg.lines().next().unwrap_or("")
            ));
        }
        self.loaded.insert(path);
        Ok(())
    }
}

/// 1つのソースを新しい環境で読み込み、検査する（Web・prose 用）
/// file は相対 import の起点（まだ保存されていないソースなら None）。
pub fn load_and_check(src: &str, file: Option<&Path>) -> Result<(Env, Module, Vec<Report>), ParseError> {
    let (mut ld, mut env) = Loader::new();
    let m = match file {
        Some(f) => ld.parse_file(&mut env, src, f)?,
        None => ld.parse(&mut env, src, None)?,
    };
    let reports = check_module(&mut env, &m, false, false);
    Ok((env, m, reports))
}

/// 読み込むだけで検査はしない（ソース変換用）。import 先は検査される。
pub fn parse_source(src: &str, dir: Option<&Path>) -> Result<Module, ParseError> {
    let (mut ld, mut env) = Loader::new();
    ld.parse(&mut env, src, dir)
}
