//! 同梱の標準ライブラリ（lib/ の .narfi を build.rs が埋め込む）

include!(concat!(env!("OUT_DIR"), "/stdlib_table.rs"));

/// `analysis/limits.narfi` のような相対パスで引く
pub fn get(rel: &str) -> Option<&'static str> {
    STDLIB.iter().find(|(p, _)| *p == rel).map(|(_, s)| *s)
}
