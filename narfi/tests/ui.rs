//! Web エディタの往復（ファイル → 構造化 AST → ASCII）で証明の意味が変わらないことを確かめる。
//! web_ui.html の読み込み・直列化を node で動かす（tests/ui_roundtrip.js）。node がなければ飛ばす。

use std::path::Path;
use std::process::Command;

const FILES: [&str; 11] = [
    "examples/hol.narfi",
    "tests/unsound_hol.narfi",
    "examples/basics.narfi",
    "examples/analysis.narfi",
    "examples/errors.narfi",
    "examples/limits.narfi",
    "tests/exercises_answers.narfi",
    "tests/unsound.narfi",
    "tests/unsound_defs.narfi",
    "lib/analysis/limits.narfi",
    "lib/analysis/real.narfi",
];

/// 定理ごとの結果（✓ / ✗ / △ / 公理 と名前、または構文エラー）
fn statuses(file: &Path) -> Vec<String> {
    let out = Command::new(env!("CARGO_BIN_EXE_narfi")).arg("check").arg(file).output().unwrap();
    String::from_utf8(out.stdout)
        .unwrap()
        .lines()
        .map(str::trim)
        .filter_map(|l| {
            if l.starts_with("構文エラー") {
                return Some("構文エラー".to_string());
            }
            let mut w = l.split_whitespace();
            match (w.next(), w.next()) {
                (Some(k @ ("✓" | "✗" | "△" | "公理")), Some(name)) => Some(format!("{k} {name}")),
                _ => None,
            }
        })
        .collect()
}

fn roundtrip(file: &Path) -> String {
    let out = Command::new("node")
        .args(["tests/ui_roundtrip.js", "src/web_ui.html"])
        .arg(file)
        .output()
        .unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn editor_roundtrip_preserves_proofs() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node がないので飛ばす");
        return;
    }
    for f in FILES {
        let f = Path::new(f);
        // 相対 import が解決できるよう、同じディレクトリに書き出す
        let tmp = f.with_file_name(format!(".roundtrip-{}.narfi", std::process::id()));
        let once = roundtrip(f);
        std::fs::write(&tmp, &once).unwrap();
        let twice = roundtrip(&tmp);
        let got = statuses(&tmp);
        std::fs::remove_file(&tmp).unwrap();
        assert_eq!(statuses(f), got, "{}: エディタを通すと検査結果が変わる\n{once}", f.display());
        assert_eq!(once, twice, "{}: 往復が冪等でない", f.display());
    }
}

/// 元に戻す・範囲選択・コピー／切り取り／貼り付け・描画クラスを、実際のキーイベントで動かして確かめる
#[test]
fn editor_operations() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node がないので飛ばす");
        return;
    }
    let out = Command::new("node").args(["tests/ui_edit.js", "src/web_ui.html"]).output().unwrap();
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
