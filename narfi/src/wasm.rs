//! ブラウザ版の入口（WebAssembly）。外部クレートを使わない素の書き出し。
//!
//! JavaScript 側（site/narfi-web.js）は、要求の JSON を `narfi_alloc` で確保した領域に書いて
//! `narfi_call` を呼び、応答の JSON を `narfi_out_ptr` から長さぶん読む。
//!
//! 要求（`op` で分ける）：
//! - `put_file` {path, src}・`remove_file` {path}・`clear_files` {}：ブラウザの保存領域のファイルを知らせる
//! - `check` {src, path, cursor_line}：/api/check と同じ応答
//! - `convert` {src, mode}：/api/convert と同じ応答
//! - `stdlib_list` {}・`stdlib_get` {path}：同梱の標準ライブラリ

use crate::api::{check_json_in, json_get_str, json_get_usize, json_str};
use crate::module::{load_and_check, use_memory_files};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;

thread_local! {
    static FILES: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
    static OUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

/// JavaScript が要求を書き込む領域を確保する
#[unsafe(no_mangle)]
pub extern "C" fn narfi_alloc(len: usize) -> *mut u8 {
    let mut v = Vec::<u8>::with_capacity(len.max(1));
    let p = v.as_mut_ptr();
    std::mem::forget(v);
    p
}

/// # Safety
/// `p` は `narfi_alloc(len)` が返したもので、まだ解放していないこと
#[unsafe(no_mangle)]
pub unsafe extern "C" fn narfi_free(p: *mut u8, len: usize) {
    unsafe { drop(Vec::from_raw_parts(p, 0, len.max(1))) }
}

/// 直前の応答の先頭
#[unsafe(no_mangle)]
pub extern "C" fn narfi_out_ptr() -> *const u8 {
    OUT.with(|o| o.borrow().as_ptr())
}

/// 要求を処理し、応答の長さを返す（応答は narfi_out_ptr から読む）
///
/// # Safety
/// `p` から `len` バイトが UTF-8 の要求であること
#[unsafe(no_mangle)]
pub unsafe extern "C" fn narfi_call(p: *const u8, len: usize) -> usize {
    let req = unsafe { std::str::from_utf8(std::slice::from_raw_parts(p, len)) }.unwrap_or("");
    let res = handle(req);
    OUT.with(|o| {
        let mut o = o.borrow_mut();
        *o = res.into_bytes();
        o.len()
    })
}

fn handle(req: &str) -> String {
    let get = |k: &str| json_get_str(req, k).unwrap_or_default();
    match get("op").as_str() {
        "put_file" => {
            FILES.with(|f| f.borrow_mut().insert(get("path"), get("src")));
            "{\"ok\":true}".into()
        }
        "remove_file" => {
            FILES.with(|f| f.borrow_mut().remove(&get("path")));
            "{\"ok\":true}".into()
        }
        "clear_files" => {
            FILES.with(|f| f.borrow_mut().clear());
            "{\"ok\":true}".into()
        }
        "check" => {
            use_memory_files(FILES.with(|f| f.borrow().clone()));
            let src = get("src");
            let path = get("path");
            let key = if path.is_empty() { "untitled.narfi".to_string() } else { path };
            check_json_in(&src, json_get_usize(req, "cursor_line"), &json_get_str(req, "locale").unwrap_or_default(), &|s| load_and_check(s, Some(Path::new(&key))))
        }
        "convert" => {
            use_memory_files(FILES.with(|f| f.borrow().clone()));
            let src = get("src");
            let out = match get("mode").as_str() {
                "to_jp_sugar" | "to_ja" => crate::prose::convert_source_to_locale(&src, "ja"),
                "to_en" => crate::prose::convert_source_to_locale(&src, "en"),
                "to_standard" => crate::prose::convert_source_to_standard_narfi(&src),
                _ => src,
            };
            format!("{{\"src\":{}}}", json_str(&out))
        }
        // 同梱の標準ライブラリの一覧・中身
        "stdlib_list" => {
            let files: Vec<String> = crate::stdlib::STDLIB.iter().map(|(p, _)| p.to_string()).collect();
            format!("{{\"files\":{}}}", crate::api::json_str_array(&files))
        }
        "stdlib_get" => match crate::stdlib::get(&get("path")) {
            Some(s) => format!("{{\"ok\":true,\"src\":{}}}", json_str(s)),
            None => "{\"ok\":false,\"error\":\"not found\"}".into(),
        },
        "version" => format!("{{\"version\":{}}}", json_str(env!("CARGO_PKG_VERSION"))),
        other => format!("{{\"ok\":false,\"error\":{}}}", json_str(&format!("unknown op: {other}"))),
    }
}
