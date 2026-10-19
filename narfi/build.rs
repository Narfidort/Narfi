//! 同梱の標準ライブラリ（lib/ の .narfi）を実行ファイルに埋め込む一覧を作る。
//! ブラウザ版（WASM）はディスクを読めないので、これを使う（src/stdlib.rs）。

use std::path::Path;

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = rd.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(root, &p, out);
        } else if p.extension().is_some_and(|e| e == "narfi") {
            out.push(p.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/"));
        }
    }
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("lib");
    println!("cargo:rerun-if-changed=lib");
    let mut files = Vec::new();
    walk(&root, &root, &mut files);
    let mut code = String::from("pub const STDLIB: &[(&str, &str)] = &[\n");
    for f in &files {
        let abs = root.join(f);
        code.push_str(&format!("    ({:?}, include_str!({:?})),\n", f, abs.to_string_lossy()));
    }
    code.push_str("];\n");
    let out = Path::new(&std::env::var("OUT_DIR").unwrap()).join("stdlib_table.rs");
    std::fs::write(out, code).unwrap();
}
