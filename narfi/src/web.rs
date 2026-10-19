//! 軽量ローカル Web サーバー (`narfi web`)。
//! 外部クレートを使わず `std::net::TcpListener` のみで動作し、
//! リアルタイム検証・日本語証明生成・LaTeX出力・ファイル保存・AIアシストを提供する。

use crate::api::{check_json, json_get_str, json_get_usize, json_str, json_str_array};
use crate::module::load_and_check;
use crate::parser::Decl;
use crate::prose;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU16, AtomicU64, Ordering};

const WEB_UI_HTML: &str = include_str!("web_ui.html");

/// 待ち受けているポート（Host・Origin の確認に使う）
static PORT: AtomicU16 = AtomicU16::new(0);

pub fn serve(port: u16, open_browser: bool, dir: Option<PathBuf>) -> std::io::Result<()> {
    init_workspace(dir);
    PORT.store(port, Ordering::SeqCst);
    let addr = format!("127.0.0.1:{port}");
    let listener = TcpListener::bind(&addr)?;
    let url = format!("http://{addr}");
    println!("============================================================");
    println!("  Narfi Live Editor & Execution Environment");
    println!("  URL: {url}");
    println!("  作業フォルダ: {}", workspace_root().display());
    println!("  終了するには Ctrl+C を押してください");
    println!("============================================================");

    if open_browser {
        let _ = Command::new("open").arg(&url).spawn();
    }

    for stream in listener.incoming() {
        if let Ok(stream) = stream {
            std::thread::spawn(move || {
                let _ = handle_client(stream);
            });
        }
    }
    Ok(())
}

fn handle_client(mut stream: TcpStream) -> std::io::Result<()> {
    let mut buf = [0u8; 65536];
    let mut data = Vec::new();
    let mut header_end = None;
    let mut content_length = 0usize;

    loop {
        let n = stream.read(&mut buf)?;
        if n == 0 {
            break;
        }
        data.extend_from_slice(&buf[..n]);
        if header_end.is_none() {
            if let Some(pos) = find_subsequence(&data, b"\r\n\r\n") {
                header_end = Some(pos + 4);
                let headers = String::from_utf8_lossy(&data[..pos]);
                for line in headers.lines() {
                    if let Some((k, v)) = line.split_once(':') {
                        if k.trim().eq_ignore_ascii_case("content-length") {
                            content_length = v.trim().parse().unwrap_or(0);
                        }
                    }
                }
            }
        }
        if let Some(hend) = header_end {
            if data.len() >= hend + content_length {
                break;
            }
        }
    }

    let Some(hend) = header_end else {
        return Ok(());
    };
    let req_header = String::from_utf8_lossy(&data[..hend]);
    let first_line = req_header.lines().next().unwrap_or("");
    let mut parts = first_line.split_whitespace();
    let method = parts.next().unwrap_or("GET");
    let full_path = parts.next().unwrap_or("/");
    let (path, query) = full_path.split_once('?').unwrap_or((full_path, ""));
    let body =
        String::from_utf8_lossy(&data[hend..(hend + content_length).min(data.len())]).to_string();

    // ほかの Web サイトからこのサーバーを使わせない（ファイルの読み書きができるため）。
    // Host が自分自身であること（DNS リバインディング対策）、Origin があれば自分自身であること。
    if !request_is_local(&req_header) {
        return send_response(&mut stream, 403, "text/plain; charset=utf-8", "forbidden".as_bytes());
    }

    match (method, path) {
        ("GET", "/") | ("GET", "/index.html") => {
            // ローカル版の印。Web 版のスクリプト（narfi-web.js）はこれを見て何もしない
            let html = WEB_UI_HTML.replacen("<!--NARFI_LOCAL-->", "<script>window.NARFI_LOCAL = true;</script>", 1);
            send_response(&mut stream, 200, "text/html; charset=utf-8", html.as_bytes())
        }
        ("GET", "/narfi-web.js") => send_response(
            &mut stream,
            200,
            "application/javascript; charset=utf-8",
            include_str!("web_static.js").as_bytes(),
        ),
        ("GET", p) if p.starts_with("/assets/katex/") => {
            let name = &p["/assets/katex/".len()..];
            match crate::assets::KATEX_FILES.iter().find(|(n, _)| *n == name) {
                Some((n, bytes)) => send_response(&mut stream, 200, crate::assets::content_type(n), bytes),
                None => send_response(&mut stream, 404, "text/plain", b"not found"),
            }
        }
        ("POST", "/api/check") => {
            let src = json_get_str(&body, "src").unwrap_or_default();
            let cursor_line = json_get_usize(&body, "cursor_line");
            let path = json_get_str(&body, "path").filter(|p| !p.is_empty());
            let res = api_check(&src, cursor_line, path.as_deref());
            send_response(
                &mut stream,
                200,
                "application/json; charset=utf-8",
                res.as_bytes(),
            )
        }
        ("POST", "/api/convert") => {
            let src = json_get_str(&body, "src").unwrap_or_default();
            let mode = json_get_str(&body, "mode").unwrap_or_default();
            let converted = match mode.as_str() {
                "to_jp_sugar" => prose::convert_source_to_japanese_sugar(&src),
                "to_standard" => prose::convert_source_to_standard_narfi(&src),
                _ => src,
            };
            let res = format!("{{\"src\":{}}}", json_str(&converted));
            send_response(
                &mut stream,
                200,
                "application/json; charset=utf-8",
                res.as_bytes(),
            )
        }
        ("GET", "/api/files") => {
            let res = api_list_files();
            send_response(
                &mut stream,
                200,
                "application/json; charset=utf-8",
                res.as_bytes(),
            )
        }
        ("GET", "/api/file") => {
            let rel = query_param(query, "path").unwrap_or_default();
            match resolve_readable(&rel) {
                Some(p) => match std::fs::read_to_string(&p) {
                    Ok(content) => {
                        let res = format!(
                            "{{\"ok\":true,\"path\":{},\"src\":{}}}",
                            json_str(&rel),
                            json_str(&content)
                        );
                        send_response(
                            &mut stream,
                            200,
                            "application/json; charset=utf-8",
                            res.as_bytes(),
                        )
                    }
                    Err(e) => {
                        let res =
                            format!("{{\"ok\":false,\"error\":{}}}", json_str(&e.to_string()));
                        send_response(
                            &mut stream,
                            400,
                            "application/json; charset=utf-8",
                            res.as_bytes(),
                        )
                    }
                },
                None => send_response(
                    &mut stream,
                    400,
                    "application/json; charset=utf-8",
                    b"{\"ok\":false,\"error\":\"invalid path\"}",
                ),
            }
        }
        ("POST", "/api/save") => {
            let rel = json_get_str(&body, "path").unwrap_or_default();
            let src = json_get_str(&body, "src").unwrap_or_default();
            match safe_resolve_path(&rel) {
                Some(p) => match p.parent().map(std::fs::create_dir_all).unwrap_or(Ok(())).and_then(|_| std::fs::write(&p, &src)) {
                    Ok(()) => {
                        let res = format!("{{\"ok\":true,\"path\":{}}}", json_str(&rel));
                        send_response(
                            &mut stream,
                            200,
                            "application/json; charset=utf-8",
                            res.as_bytes(),
                        )
                    }
                    Err(e) => {
                        let res =
                            format!("{{\"ok\":false,\"error\":{}}}", json_str(&e.to_string()));
                        send_response(
                            &mut stream,
                            400,
                            "application/json; charset=utf-8",
                            res.as_bytes(),
                        )
                    }
                },
                None => send_response(
                    &mut stream,
                    400,
                    "application/json; charset=utf-8",
                    b"{\"ok\":false,\"error\":\"invalid path\"}",
                ),
            }
        }
        ("GET", "/api/workspace") => {
            let res = api_workspace();
            send_response(&mut stream, 200, "application/json; charset=utf-8", res.as_bytes())
        }
        ("POST", "/api/open-folder") => {
            let path = json_get_str(&body, "path").unwrap_or_default();
            let dir = if path.is_empty() { mac_choose_folder() } else { Some(PathBuf::from(path)) };
            let res = match dir {
                Some(d) if d.is_dir() => {
                    set_workspace(d);
                    api_workspace()
                }
                Some(d) => json_err(&format!("フォルダがない：{}", d.display())),
                None => json_cancel(),
            };
            send_response(&mut stream, 200, "application/json; charset=utf-8", res.as_bytes())
        }
        ("POST", "/api/open-file") => {
            let res = match mac_choose_file() {
                Some(p) => api_open_abs(&p),
                None => json_cancel(),
            };
            send_response(&mut stream, 200, "application/json; charset=utf-8", res.as_bytes())
        }
        ("POST", "/api/save-as") => {
            let src = json_get_str(&body, "src").unwrap_or_default();
            let name = json_get_str(&body, "name").unwrap_or_else(|| "note.narfi".into());
            let res = match mac_choose_save(&name) {
                Some(mut p) => {
                    if p.extension().is_none() {
                        p.set_extension("narfi");
                    }
                    match std::fs::write(&p, &src) {
                        Ok(()) => api_open_abs(&p),
                        Err(e) => json_err(&e.to_string()),
                    }
                }
                None => json_cancel(),
            };
            send_response(&mut stream, 200, "application/json; charset=utf-8", res.as_bytes())
        }
        ("POST", "/api/reveal") => {
            let target = json_get_str(&body, "target").unwrap_or_default();
            let dir = if target == "lib" { user_lib_dir() } else { Some(workspace_root()) };
            if let Some(d) = dir {
                let _ = std::fs::create_dir_all(&d);
                let _ = Command::new("open").arg(&d).spawn();
            }
            send_response(&mut stream, 200, "application/json; charset=utf-8", b"{\"ok\":true}")
        }
        ("POST", "/api/pdf") => {
            let src = json_get_str(&body, "src").unwrap_or_default();
            let path = json_get_str(&body, "path").unwrap_or_default();
            match api_pdf(&src, &path) {
                Ok(pdf) => send_response(&mut stream, 200, "application/pdf", &pdf),
                Err(e) => send_response(&mut stream, 400, "application/json; charset=utf-8", json_err(&e).as_bytes()),
            }
        }
        ("GET", "/api/ai/providers") => {
            let res = api_detect_ai_providers();
            send_response(
                &mut stream,
                200,
                "application/json; charset=utf-8",
                res.as_bytes(),
            )
        }
        ("POST", "/api/ai") => {
            let res = api_run_ai(&body);
            send_response(
                &mut stream,
                200,
                "application/json; charset=utf-8",
                res.as_bytes(),
            )
        }
        _ => send_response(&mut stream, 404, "text/plain; charset=utf-8", b"Not Found"),
    }
}

fn find_subsequence(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn send_response(
    stream: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let status_text = match status {
        200 => "OK",
        400 => "Bad Request",
        403 => "Forbidden",
        404 => "Not Found",
        _ => "Error",
    };
    let header = format!(
        "HTTP/1.1 {status} {status_text}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

/// /api/check（ディスク版）：相対 import の起点は開いているファイル（未保存なら作業フォルダの直下）
pub fn api_check(src: &str, cursor_line: Option<usize>, path: Option<&str>) -> String {
    let file = path.and_then(safe_resolve_path).unwrap_or_else(|| workspace_root().join("untitled.narfi"));
    check_json(src, cursor_line, &|s| load_and_check(s, Some(&file)))
}

// ================================================================ ファイル管理

// ================================================================ 作業フォルダ・ライブラリ

static WORKSPACE: Mutex<Option<PathBuf>> = Mutex::new(None);

fn narfi_home() -> Option<PathBuf> {
    std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".narfi"))
}

/// 自分用のライブラリ（~/.narfi/lib）。import の探索先にもなる（module.rs）
pub fn user_lib_dir() -> Option<PathBuf> {
    narfi_home().map(|h| h.join("lib"))
}

fn std_lib_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("lib")
}

/// 起動時：--dir、前回のフォルダ（~/.narfi/workspace）、カレントディレクトリの順
fn init_workspace(dir: Option<PathBuf>) {
    if let Some(lib) = user_lib_dir() {
        let _ = std::fs::create_dir_all(lib);
    }
    let saved = narfi_home()
        .and_then(|h| std::fs::read_to_string(h.join("workspace")).ok())
        .map(|s| PathBuf::from(s.trim()))
        .filter(|p| p.is_dir());
    match dir.or(saved) {
        Some(d) => set_workspace(d),
        None => {}
    }
}

fn set_workspace(d: PathBuf) {
    let d = d.canonicalize().unwrap_or(d);
    if let Some(h) = narfi_home() {
        let _ = std::fs::create_dir_all(&h);
        let _ = std::fs::write(h.join("workspace"), d.to_string_lossy().as_bytes());
    }
    *WORKSPACE.lock().unwrap() = Some(d);
}

fn workspace_root() -> PathBuf {
    if let Some(d) = WORKSPACE.lock().unwrap().clone() {
        return d;
    }
    default_workspace()
}

fn default_workspace() -> PathBuf {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if cwd.ends_with("narfi") {
        if let Some(parent) = cwd.parent() {
            if parent.join("練習.narfi").exists() || parent.join("narfi").exists() {
                return parent.to_path_buf();
            }
        }
    }
    cwd
}

fn safe_resolve_path(rel: &str) -> Option<PathBuf> {
    if rel.is_empty() || rel.contains("..") || Path::new(rel).is_absolute() {
        return None;
    }
    let root = workspace_root();
    Some(root.join(rel))
}

/// 読めるファイル：作業フォルダの相対パス、または `lib:user/…`・`lib:std/…`（ライブラリ、読み取り専用）
fn resolve_readable(rel: &str) -> Option<PathBuf> {
    if let Some(rest) = rel.strip_prefix("lib:") {
        let (label, sub) = rest.split_once('/')?;
        if sub.contains("..") || Path::new(sub).is_absolute() {
            return None;
        }
        let base = match label {
            "user" => user_lib_dir()?,
            "std" => std_lib_dir(),
            _ => return None,
        };
        return Some(base.join(sub));
    }
    safe_resolve_path(rel)
}

fn json_err(msg: &str) -> String {
    format!("{{\"ok\":false,\"error\":{}}}", json_str(msg))
}

fn json_cancel() -> String {
    "{\"ok\":false,\"cancelled\":true}".to_string()
}

fn list_narfi(dir: &Path) -> Vec<String> {
    let mut files = Vec::new();
    collect_narfi_files(dir, dir, &mut files);
    files.sort();
    files
}

fn api_workspace() -> String {
    let root = workspace_root();
    let name = root.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
    let mut libs = Vec::new();
    if let Some(u) = user_lib_dir() {
        libs.push(format!(
            "{{\"label\":\"user\",\"dir\":{},\"files\":{}}}",
            json_str(&u.to_string_lossy()),
            json_str_array(&list_narfi(&u))
        ));
    }
    let s = std_lib_dir();
    libs.push(format!(
        "{{\"label\":\"std\",\"dir\":{},\"files\":{}}}",
        json_str(&s.to_string_lossy()),
        json_str_array(&list_narfi(&s))
    ));
    format!(
        "{{\"ok\":true,\"root\":{},\"name\":{},\"files\":{},\"libs\":[{}],\"dialogs\":{}}}",
        json_str(&root.to_string_lossy()),
        json_str(&name),
        json_str_array(&list_narfi(&root)),
        libs.join(","),
        cfg!(target_os = "macos")
    )
}

/// 絶対パスのファイルを開く。作業フォルダの外なら、そのファイルのフォルダを作業フォルダにする。
fn api_open_abs(p: &Path) -> String {
    let p = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let root = workspace_root();
    let rel = match p.strip_prefix(&root) {
        Ok(r) => r.to_path_buf(),
        Err(_) => {
            if let Some(parent) = p.parent() {
                set_workspace(parent.to_path_buf());
            }
            PathBuf::from(p.file_name().unwrap_or_default())
        }
    };
    match std::fs::read_to_string(&p) {
        Ok(src) => format!(
            "{{\"ok\":true,\"path\":{},\"src\":{},\"root\":{}}}",
            json_str(&rel.to_string_lossy()),
            json_str(&src),
            json_str(&workspace_root().to_string_lossy())
        ),
        Err(e) => json_err(&e.to_string()),
    }
}

// ---------------------------------------------------------------- macOS の標準ダイアログ（osascript）

fn osascript(lines: &[String]) -> Option<String> {
    if !cfg!(target_os = "macos") {
        return None;
    }
    let mut cmd = Command::new("osascript");
    for l in lines {
        cmd.arg("-e").arg(l);
    }
    let out = cmd.output().ok()?;
    if !out.status.success() {
        return None; // キャンセル
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!s.is_empty()).then_some(s)
}

fn applescript_str(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// ダイアログを前面に出すため、System Events の中で開く
fn front_dialog(expr: &str) -> Vec<String> {
    vec![
        "tell application \"System Events\"".into(),
        "activate".into(),
        format!("set p to POSIX path of ({expr})"),
        "end tell".into(),
        "return p".into(),
    ]
}

fn mac_choose_folder() -> Option<PathBuf> {
    let root = workspace_root();
    let expr = format!(
        "choose folder with prompt \"Narfi：作業フォルダを選ぶ\" default location (POSIX file {})",
        applescript_str(&root.to_string_lossy())
    );
    osascript(&front_dialog(&expr)).map(PathBuf::from)
}

fn mac_choose_file() -> Option<PathBuf> {
    let root = workspace_root();
    let expr = format!(
        "choose file with prompt \"Narfi：開くファイル\" default location (POSIX file {})",
        applescript_str(&root.to_string_lossy())
    );
    osascript(&front_dialog(&expr)).map(PathBuf::from)
}

fn mac_choose_save(name: &str) -> Option<PathBuf> {
    let root = workspace_root();
    let expr = format!(
        "choose file name with prompt \"Narfi：保存先\" default name {} default location (POSIX file {})",
        applescript_str(name),
        applescript_str(&root.to_string_lossy())
    );
    osascript(&front_dialog(&expr)).map(PathBuf::from)
}

// ---------------------------------------------------------------- PDF（LuaLaTeX）

static PDF_SEQ: AtomicU64 = AtomicU64::new(0);

fn api_pdf(src: &str, path: &str) -> Result<Vec<u8>, String> {
    let file = safe_resolve_path(path).unwrap_or_else(|| workspace_root().join("untitled.narfi"));
    let (_, m, reports) = load_and_check(src, Some(&file)).map_err(|e| format!("{}行目：{}", e.line, e.msg))?;
    let decls: Vec<&Decl> = m.decls().collect();
    let items: Vec<(&Decl, &[crate::elab::StepTrace])> =
        decls.iter().zip(reports.iter()).map(|(d, r)| (*d, r.steps.as_slice())).collect();
    let title = file.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let tex = prose::latex_document(&title, &items);
    let dir = std::env::temp_dir().join(format!("narfi-pdf-{}-{}", std::process::id(), PDF_SEQ.fetch_add(1, Ordering::SeqCst)));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    std::fs::write(dir.join("doc.tex"), tex).map_err(|e| e.to_string())?;
    let out = Command::new("latexmk")
        .args(["-lualatex", "-interaction=nonstopmode", "-halt-on-error", "doc.tex"])
        .current_dir(&dir)
        .output()
        .map_err(|_| "LaTeX（latexmk・lualatex）が見つからない。TeX をインストールするか「印刷」を使う".to_string())?;
    let pdf = std::fs::read(dir.join("doc.pdf"));
    let log = std::fs::read_to_string(dir.join("doc.log")).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    match pdf {
        Ok(p) if out.status.success() => Ok(p),
        _ => {
            let err: Vec<&str> = log.lines().filter(|l| l.starts_with('!')).take(3).collect();
            Err(format!("LaTeX のコンパイルに失敗した：{}", err.join(" / ")))
        }
    }
}

fn api_list_files() -> String {
    let root = workspace_root();
    let mut files = Vec::new();
    collect_narfi_files(&root, &root, &mut files);
    files.sort();
    format!("{{\"files\":{}}}", json_str_array(&files))
}

fn collect_narfi_files(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        let name = e.file_name().to_string_lossy().to_string();
        if name.starts_with('.') || name == "target" || name == "node_modules" {
            continue;
        }
        if p.is_dir() {
            collect_narfi_files(root, &p, out);
        } else if name.ends_with(".narfi") && name != "prelude.narfi" {
            if let Ok(rel) = p.strip_prefix(root) {
                out.push(rel.to_string_lossy().to_string());
            }
        }
    }
}

// ================================================================ AI アシスト連携

fn cmd_exists(bin: &str) -> bool {
    Command::new("which")
        .arg(bin)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn api_detect_ai_providers() -> String {
    let has_claude = cmd_exists("claude");
    let has_gemini = cmd_exists("gemini");
    let has_opencode = cmd_exists("opencode");
    let has_gh = cmd_exists("gh");
    format!(
        "{{\"claude_cli\":{has_claude},\"gemini_cli\":{has_gemini},\"opencode_cli\":{has_opencode},\"gh_cli\":{has_gh}}}"
    )
}

const NARFI_AI_SYSTEM_PROMPT: &str = r#"あなたは自然演繹ベースの証明記述言語「Narfi (v0.5)」の専門アシスタントです。
ユーザーの証明作成・次の一手の提案・日本語/LaTeXメモからのNarfiコード生成・エラー解決を的確に支援してください。

【Narfi 構文の核心ルール】
1. 定理宣言:
   thm 定理名 :
     仮定1 : φ1, 仮定2 : φ2
     ⊢ 結論
2. 証明ステップ（字下げ 2スペースでブロックを作る）:
   - ∀導入: `Fix x` または条件付き `Fix ε | hε` （または日本語シュガー: `hε を満たす ε を任意にとって固定する`）
   - →導入: `assume h : P` （型 `: P` は省略可 `assume h`）
   - 背理法: `by_contra hn` （Goal が `⊥` になる。Goal自体が `¬P` のときは `assume` を使う）
   - ∃除去: `Obtain x, hx : 根拠` または依存関係注釈付き `Obtain N(ε), hN : conv_a(ε/2, pos_half(hε))`
   - ∃導入: `choose 項` または範囲付き `choose 項, 条件の根拠` （例: `choose 1/2, decide`）
   - ∨導入: `choose left` / `choose right`
   - ∨除去: `cases h` の下に字下げして `Case left h1` と `Case right h2`
   - 帰納法: `induction n` の下に字下げして `Case zero` と `Case succ k, IH`
   - 中間主張: `have h : φ := 根拠`
   - 十分条件: `suffices ψ := 根拠`
   - 局所定義: `let N := max(N₁, N₂)`
   - 等式・不等式の連鎖:
     左辺
       ≤ 中間項   by 根拠1
       < 右辺     by 根拠2
   - 結論の確認: `∴ φ`
   - 組み込み根拠・決定手続き: `refl`, `ring`, `linarith`, `decide`, `sorry`, `eq.symm(h)`, `eq.trans(h1, h2)`, `congr.S(h)`, `add.zero(n)`, `add.succ(n, m)`
   - ∧の取り出し: `h.left`, `h.right` / ∧導入: `根拠1, 根拠2`

回答は簡潔にし、Narfiコードを提案する場合は ```narfi ... ``` ブロックで囲んでください。"#;

fn api_run_ai(body: &str) -> String {
    let provider = json_get_str(body, "provider").unwrap_or_else(|| "auto".into());
    let prompt = json_get_str(body, "prompt").unwrap_or_default();
    let src = json_get_str(body, "src").unwrap_or_default();
    let goal_info = json_get_str(body, "goal_info").unwrap_or_default();
    let api_key = json_get_str(body, "api_key").unwrap_or_default();
    let api_base = json_get_str(body, "api_base").unwrap_or_default();
    let model = json_get_str(body, "model").unwrap_or_default();

    let full_prompt = format!(
        "{NARFI_AI_SYSTEM_PROMPT}\n\n【現在のファイルのコード】\n```narfi\n{src}\n```\n\n【カーソル位置の文脈・Goal状態】\n{goal_info}\n\n【ユーザーの依頼】\n{prompt}"
    );

    let chosen = if provider == "auto" {
        if !api_key.is_empty() {
            "openai_compat"
        } else if cmd_exists("claude") {
            "claude_cli"
        } else if cmd_exists("gemini") {
            "gemini_cli"
        } else {
            "none"
        }
    } else {
        provider.as_str()
    };

    let result = match chosen {
        "claude_cli" => run_cli_ai("claude", &["-p", &full_prompt]),
        "gemini_cli" => run_cli_ai("gemini", &["-p", &full_prompt]),
        "openai_compat" | "opencode_go" => {
            let base = if api_base.is_empty() {
                "https://api.openai.com/v1/chat/completions"
            } else {
                api_base.as_str()
            };
            let m = if model.is_empty() { "gpt-4o-mini" } else { model.as_str() };
            run_openai_compat_curl(base, &api_key, m, &full_prompt)
        }
        "anthropic_api" => {
            let m = if model.is_empty() { "claude-sonnet-4-20250514" } else { model.as_str() };
            run_anthropic_curl(&api_key, m, &full_prompt)
        }
        "gemini_api" => {
            let m = if model.is_empty() { "gemini-2.5-flash" } else { model.as_str() };
            run_gemini_curl(&api_key, m, &full_prompt)
        }
        _ => Err("利用可能なAIプロバイダが見つかりません。設定から Claude CLI / Gemini CLI または API Key を指定してください。".into()),
    };

    match result {
        Ok(ans) => format!(
            "{{\"ok\":true,\"provider\":{},\"reply\":{}}}",
            json_str(chosen),
            json_str(&ans)
        ),
        Err(e) => format!(
            "{{\"ok\":false,\"provider\":{},\"error\":{}}}",
            json_str(chosen),
            json_str(&e)
        ),
    }
}

fn run_cli_ai(bin: &str, args: &[&str]) -> Result<String, String> {
    let out = Command::new(bin)
        .args(args)
        .output()
        .map_err(|e| format!("{bin} の起動に失敗しました: {e}"))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
    } else {
        let err = String::from_utf8_lossy(&out.stderr).trim().to_string();
        let out_s = String::from_utf8_lossy(&out.stdout).trim().to_string();
        Err(format!("{bin} エラー: {err} {out_s}"))
    }
}

fn run_openai_compat_curl(
    url: &str,
    key: &str,
    model: &str,
    prompt: &str,
) -> Result<String, String> {
    if key.is_empty() {
        return Err("API Key が入力されていません。右上の「AI設定」から設定してください。".into());
    }
    let payload = format!(
        "{{\"model\":{},\"messages\":[{{\"role\":\"user\",\"content\":{}}}]}}",
        json_str(model),
        json_str(prompt)
    );
    let out = Command::new("curl")
        .args([
            "-sS",
            "-X",
            "POST",
            url,
            "-H",
            "Content-Type: application/json",
            "-H",
            &format!("Authorization: Bearer {key}"),
            "-d",
            &payload,
        ])
        .output()
        .map_err(|e| format!("curl 実行エラー: {e}"))?;
    let resp = String::from_utf8_lossy(&out.stdout).to_string();
    if let Some(content) = json_get_str(&resp, "content") {
        Ok(content)
    } else {
        Err(format!("API応答の解析に失敗しました: {resp}"))
    }
}

fn run_anthropic_curl(key: &str, model: &str, prompt: &str) -> Result<String, String> {
    if key.is_empty() {
        return Err("Anthropic API Key が入力されていません。".into());
    }
    let payload = format!(
        "{{\"model\":{},\"max_tokens\":2048,\"messages\":[{{\"role\":\"user\",\"content\":{}}}]}}",
        json_str(model),
        json_str(prompt)
    );
    let out = Command::new("curl")
        .args([
            "-sS",
            "-X",
            "POST",
            "https://api.anthropic.com/v1/messages",
            "-H",
            "Content-Type: application/json",
            "-H",
            &format!("x-api-key: {key}"),
            "-H",
            "anthropic-version: 2023-06-01",
            "-d",
            &payload,
        ])
        .output()
        .map_err(|e| format!("curl 実行エラー: {e}"))?;
    let resp = String::from_utf8_lossy(&out.stdout).to_string();
    if let Some(text) = json_get_str(&resp, "text") {
        Ok(text)
    } else {
        Err(format!("API応答の解析に失敗しました: {resp}"))
    }
}

fn run_gemini_curl(key: &str, model: &str, prompt: &str) -> Result<String, String> {
    if key.is_empty() {
        return Err("Gemini API Key が入力されていません。".into());
    }
    let url = format!(
        "https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={key}"
    );
    let payload = format!(
        "{{\"contents\":[{{\"parts\":[{{\"text\":{}}}]}}]}}",
        json_str(prompt)
    );
    let out = Command::new("curl")
        .args([
            "-sS",
            "-X",
            "POST",
            &url,
            "-H",
            "Content-Type: application/json",
            "-d",
            &payload,
        ])
        .output()
        .map_err(|e| format!("curl 実行エラー: {e}"))?;
    let resp = String::from_utf8_lossy(&out.stdout).to_string();
    if let Some(text) = json_get_str(&resp, "text") {
        Ok(text)
    } else {
        Err(format!("API応答の解析に失敗しました: {resp}"))
    }
}

fn query_param(query: &str, key: &str) -> Option<String> {
    for pair in query.split('&') {
        if let Some((k, v)) = pair.split_once('=') {
            if k == key {
                return Some(url_decode(v));
            }
        }
    }
    None
}

fn url_decode(s: &str) -> String {
    let mut bytes = Vec::new();
    let bs = s.as_bytes();
    let mut i = 0;
    while i < bs.len() {
        if bs[i] == b'+' {
            bytes.push(b' ');
            i += 1;
        } else if bs[i] == b'%' && i + 2 < bs.len() {
            if let Ok(hex) = std::str::from_utf8(&bs[i + 1..i + 3]) {
                if let Ok(b) = u8::from_str_radix(hex, 16) {
                    bytes.push(b);
                    i += 3;
                    continue;
                }
            }
            bytes.push(bs[i]);
            i += 1;
        } else {
            bytes.push(bs[i]);
            i += 1;
        }
    }
    String::from_utf8_lossy(&bytes).to_string()
}

/// Host が自分自身で、Origin（あれば）も自分自身のリクエストか
fn request_is_local(header: &str) -> bool {
    let port = PORT.load(Ordering::SeqCst);
    let ok_hosts = [format!("127.0.0.1:{port}"), format!("localhost:{port}")];
    let mut host_ok = false;
    for line in header.lines() {
        let Some((k, v)) = line.split_once(':') else { continue };
        let (k, v) = (k.trim().to_ascii_lowercase(), v.trim());
        if k == "host" {
            host_ok = ok_hosts.iter().any(|h| h == v);
        }
        if k == "origin" && !ok_hosts.iter().any(|h| v == format!("http://{h}")) {
            return false;
        }
    }
    host_ok
}
