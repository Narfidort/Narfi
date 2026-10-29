//! Narfi の検査器（ライブラリ）。
//!
//! コマンド `narfi`（src/main.rs）とブラウザ版（src/wasm.rs、wasm32 向けにビルドしたときだけ）から使う。
//! 信じる必要があるのは `kernel`（と `syntax`・`types` の一部）だけ。仕様は docs/language/（リポジトリ直下）。

// エラーには、その行の goal・文脈・直し方の候補を持たせる（利用者に見せるため）ので、エラー型が大きいのは意図どおり
#![allow(clippy::result_large_err)]

pub mod api;
pub mod arith;
pub mod assets;
pub mod derivation;
pub mod elab;
pub mod format;
pub mod kernel;
pub mod locale;
pub mod migrate;
pub mod module;
pub mod parser;
pub mod prose;
pub mod sorts;
pub mod stdlib;
pub mod syntax;
pub mod types;

#[cfg(not(target_arch = "wasm32"))]
pub mod web;

#[cfg(target_arch = "wasm32")]
pub mod wasm;
