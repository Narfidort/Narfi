//! 軽量ローカル Web サーバー (`narfi web`)。
//! 外部クレートを使わず `std::net::TcpListener` のみで動作し、
//! リアルタイム検証・日本語証明生成・LaTeX出力・ファイル保存・AIアシストを提供する。

use crate::check::Report;
use crate::module::load_and_check;
use crate::parser::Decl;
use crate::syntax::with_syntax;
use crate::prose;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::Command;

const WEB_UI_HTML: &str = include_str!("web_ui.html");

pub fn serve(port: u16, open_browser: bool) -> std::io::Result<()> {
    let addr = format!("127.0.0.1:{port}");
    let listener = TcpListener::bind(&addr)?;
    let url = format!("http://{addr}");
    println!("============================================================");
    println!("  Narfi Live Editor & Execution Environment");
    println!("  URL: {url}");
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

    match (method, path) {
        ("GET", "/") | ("GET", "/index.html") => send_response(
            &mut stream,
            200,
            "text/html; charset=utf-8",
            WEB_UI_HTML.as_bytes(),
        ),
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
            match safe_resolve_path(&rel) {
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
                Some(p) => match std::fs::write(&p, &src) {
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
        404 => "Not Found",
        _ => "Error",
    };
    let header = format!(
        "HTTP/1.1 {status} {status_text}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nAccess-Control-Allow-Origin: *\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

// ================================================================ 検証・ノート解析 API

struct NoteBlock {
    line: usize,
    kind: &'static str, // "heading" | "markdown" | "comment"
    text: String,
}

fn extract_notes(src: &str) -> Vec<NoteBlock> {
    let mut notes = Vec::new();
    let mut in_fence = false;
    let mut fence_start = 1;
    let mut fence_buf = String::new();

    for (i, raw) in src.lines().enumerate() {
        let lno = i + 1;
        let trimmed = raw.trim();
        if trimmed.starts_with("```") {
            if in_fence {
                notes.push(NoteBlock {
                    line: fence_start,
                    kind: "markdown",
                    text: fence_buf.trim_end().to_string(),
                });
                fence_buf.clear();
                in_fence = false;
            } else {
                in_fence = true;
                fence_start = lno;
            }
            continue;
        }
        if in_fence {
            fence_buf.push_str(raw);
            fence_buf.push('\n');
            continue;
        }
        if trimmed.starts_with('#') {
            notes.push(NoteBlock {
                line: lno,
                kind: "heading",
                text: trimmed.to_string(),
            });
            continue;
        }
        // 行全体がコメント（`//` または `--`）の場合
        if let Some(c) = trimmed
            .strip_prefix("//")
            .or_else(|| trimmed.strip_prefix("--"))
        {
            let c = c.trim();
            if !c.is_empty() && !c.starts_with("====") {
                notes.push(NoteBlock {
                    line: lno,
                    kind: "comment",
                    text: c.to_string(),
                });
            }
        }
    }
    notes
}

pub fn api_check(src: &str, cursor_line: Option<usize>, path: Option<&str>) -> String {
    let notes = extract_notes(src);
    // 相対 import の起点：開いているファイル（未保存ならワークスペース直下）
    let file = path
        .and_then(safe_resolve_path)
        .unwrap_or_else(|| workspace_root().join("untitled.narfi"));

    // まずそのままパースを試みる。もし編集中（空行や入力途中）でパースエラーになった場合、
    // カーソル行を sorry に置き換えたフォールバックも試して Goal 表示を維持する。
    // 試すたびに環境と記法の表を作り直す（load_and_check）。
    let (decls, reports, parse_err) = match load_and_check(src, Some(&file)) {
        Ok((_, m, r)) => (m.decls().cloned().collect::<Vec<Decl>>(), r, None),
        Err(e) => {
            let mut lines = vec![];
            lines.extend(cursor_line);
            lines.push(e.line);
            let recovered = lines
                .into_iter()
                .filter_map(|l| load_and_check(&patch_line_with_sorry(src, l), Some(&file)).ok())
                .find(|(_, m, _)| m.decls().next().is_some());
            match recovered {
                Some((_, m, r)) => (m.decls().cloned().collect(), r, Some(e)),
                None => (vec![], vec![], Some(e)),
            }
        }
    };

    let mut decls_json = Vec::new();
    for (d, r) in decls.iter().zip(reports.iter()) {
        decls_json.push(format_decl_report_json(d, r));
    }

    let notes_json: Vec<String> = notes
        .iter()
        .map(|n| {
            format!(
                "{{\"line\":{},\"kind\":{},\"text\":{}}}",
                n.line,
                json_str(n.kind),
                json_str(&n.text)
            )
        })
        .collect();

    let perr_json = match parse_err {
        Some(e) => format!("{{\"line\":{},\"msg\":{}}}", e.line, json_str(&e.msg)),
        None => "null".to_string(),
    };

    // エディタの補完候補に出す notation（import 先のものも含む）
    let notations_json: Vec<String> = with_syntax(|t| {
        t.notations
            .iter()
            .map(|n| {
                format!(
                    "{{\"sym\":{},\"pred\":{},\"latex\":{}}}",
                    json_str(&n.sym),
                    json_str(&n.pred),
                    json_str(&n.latex)
                )
            })
            .collect()
    });

    format!(
        "{{\"ok\":{},\"parse_error\":{},\"decls\":[{}],\"notes\":[{}],\"notations\":[{}]}}",
        perr_json == "null" && reports.iter().all(|r| r.err.is_none()),
        perr_json,
        decls_json.join(","),
        notes_json.join(","),
        notations_json.join(",")
    )
}

fn patch_line_with_sorry(src: &str, target_line: usize) -> String {
    src.lines()
        .enumerate()
        .map(|(i, l)| {
            if i + 1 == target_line {
                let indent: String = l.chars().take_while(|c| *c == ' ' || *c == '\t').collect();
                format!("{indent}sorry")
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_decl_report_json(d: &Decl, r: &Report) -> String {
    let status = if r.is_axiom {
        "axiom"
    } else if r.err.is_some() {
        "error"
    } else if r.oracles.contains("sorry") {
        "sorry"
    } else {
        "ok"
    };

    let header_latex = prose::decl_header_latex(d);
    let concl_latex = d.concl.to_latex();
    let prose_blocks = prose::decl_to_japanese_prose(d, &r.steps);
    let latex_env = prose::decl_to_latex_env(d, &r.steps);

    let err_json = match &r.err {
        Some(e) => {
            let g_str = e
                .goal
                .as_ref()
                .map(|g| json_str(&g.to_string()))
                .unwrap_or_else(|| "null".into());
            let gl_str = e
                .goal
                .as_ref()
                .map(|g| json_str(&g.to_latex()))
                .unwrap_or_else(|| "null".into());
            format!(
                "{{\"line\":{},\"msg\":{},\"goal\":{},\"goal_latex\":{},\"ctx\":{},\"ctx_latex\":{}}}",
                e.line,
                json_str(&e.msg),
                g_str,
                gl_str,
                json_str_array(&e.ctx),
                json_str_array(&e.ctx_latex)
            )
        }
        None => "null".to_string(),
    };

    let sorries_json: Vec<String> = r
        .sorries
        .iter()
        .map(|(line, ctx, g)| {
            format!(
                "{{\"line\":{},\"ctx\":{},\"goal\":{},\"goal_latex\":{}}}",
                line,
                json_str_array(ctx),
                json_str(&g.to_string()),
                json_str(&g.to_latex())
            )
        })
        .collect();

    let steps_json: Vec<String> = r
        .steps
        .iter()
        .map(|st| {
            let g = st.goal.as_ref().map(|x| json_str(x)).unwrap_or_else(|| "null".into());
            let gl = st.goal_latex.as_ref().map(|x| json_str(x)).unwrap_or_else(|| "null".into());
            format!(
                "{{\"line\":{},\"depth\":{},\"src\":{},\"ctx\":{},\"ctx_latex\":{},\"goal\":{},\"goal_latex\":{}}}",
                st.line,
                st.depth,
                json_str(&st.src),
                json_str_array(&st.ctx),
                json_str_array(&st.ctx_latex),
                g,
                gl
            )
        })
        .collect();

    let prose_json: Vec<String> = prose_blocks
        .iter()
        .map(|b| format!("{{\"depth\":{},\"text\":{}}}", b.depth, json_str(&b.text)))
        .collect();

    let axioms_vec: Vec<String> = r.axioms.iter().cloned().collect();
    let oracles_vec: Vec<String> = r
        .oracles
        .iter()
        .filter(|o| *o != "sorry")
        .cloned()
        .collect();

    format!(
        "{{\"name\":{},\"line\":{},\"is_axiom\":{},\"status\":{},\"header_latex\":{},\"concl_latex\":{},\"axioms\":{},\"oracles\":{},\"error\":{},\"sorries\":[{}],\"steps\":[{}],\"prose\":[{}],\"latex_env\":{}}}",
        json_str(&r.name),
        r.line,
        r.is_axiom,
        json_str(status),
        json_str(&header_latex),
        json_str(&concl_latex),
        json_str_array(&axioms_vec),
        json_str_array(&oracles_vec),
        err_json,
        sorries_json.join(","),
        steps_json.join(","),
        prose_json.join(","),
        json_str(&latex_env)
    )
}

// ================================================================ ファイル管理

fn workspace_root() -> PathBuf {
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

// ================================================================ 軽量 JSON ヘルパ

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_str_array(items: &[String]) -> String {
    let v: Vec<String> = items.iter().map(|s| json_str(s)).collect();
    format!("[{}]", v.join(","))
}

fn json_get_str(json: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\"");
    let mut search_from = 0;
    while let Some(rel_idx) = json[search_from..].find(&pat) {
        let idx = search_from + rel_idx + pat.len();
        let rest = json[idx..].trim_start();
        if let Some(after_colon) = rest.strip_prefix(':') {
            let after_colon = after_colon.trim_start();
            if let Some(after_quote) = after_colon.strip_prefix('"') {
                return Some(parse_json_string_body(after_quote));
            }
        }
        search_from = idx;
    }
    None
}

fn json_get_usize(json: &str, key: &str) -> Option<usize> {
    let pat = format!("\"{key}\"");
    let idx = json.find(&pat)? + pat.len();
    let rest = json[idx..].trim_start().strip_prefix(':')?.trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn parse_json_string_body(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '"' {
            break;
        }
        if c == '\\' {
            if let Some(esc) = chars.next() {
                match esc {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    '/' => out.push('/'),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    'u' => {
                        let hex: String = chars.by_ref().take(4).collect();
                        if let Ok(code) = u32::from_str_radix(&hex, 16) {
                            if let Some(ch) = char::from_u32(code) {
                                out.push(ch);
                            }
                        }
                    }
                    other => out.push(other),
                }
            }
        } else {
            out.push(c);
        }
    }
    out
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
