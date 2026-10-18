//! examples/ の正しい証明は全部通り、errors.narfi と tests/unsound*.narfi の証明は1本も通らないことを確かめる。

use std::process::Command;

fn run(files: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_narfi")).arg("check").args(files).output().unwrap();
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn correct_proofs_pass() {
    let out = run(&["examples/basics.narfi", "examples/analysis.narfi"])
        + &run(&["tests/exercises_answers.narfi"])
        + &run(&["examples/limits.narfi"]);
    assert!(!out.contains('✗'), "{out}");
    assert!(out.contains("すべて検証しました"), "{out}");
}

#[test]
fn wrong_proofs_fail() {
    for f in [
        "examples/errors.narfi",
        "tests/unsound.narfi",
        "tests/unsound_defs.narfi",
        "tests/unsound_sorts.narfi",
    ] {
        let out = run(&[f]);
        let passed: Vec<&str> = out.lines().filter(|l| l.trim_start().starts_with('✓')).collect();
        assert!(passed.is_empty(), "{f} で通ってしまった証明: {passed:?}\n{out}");
        assert!(out.contains('✗'), "{out}");
    }
}

#[test]
fn circular_import_is_rejected() {
    let out = run(&["tests/cyclic/a.narfi"]);
    assert!(out.contains("循環 import: a.narfi → b.narfi → a.narfi"), "{out}");
}

/// 組み込みの記号と衝突する notation・再帰的な def・引数の数の間違いは構文エラーになる
#[test]
fn bad_definitions_are_rejected() {
    let dir = std::env::temp_dir().join(format!("narfi-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("notation a \"->\" b := P(a, b)", "衝突する"),
        ("def r(a) := r(a)", "自身を使っている"),
        ("def p(x) := q(x)\ndef q(x) := p(x)", "あとから定義できない"),
        ("def bad(a) := a(n) > 0", "引数にない"),
        ("def pos(x) := x > 0\nthm t : ⊢ pos(1, 2)\nsorry", "引数 1 個の定義"),
    ];
    for (i, (src, msg)) in cases.iter().enumerate() {
        let f = dir.join(format!("case{i}.narfi"));
        std::fs::write(&f, src).unwrap();
        let out = run(&[f.to_str().unwrap()]);
        assert!(out.contains("構文エラー") && out.contains(msg), "{src}\n{out}");
    }
}
