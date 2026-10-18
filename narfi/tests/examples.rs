//! examples/ の正しい証明は全部通り、errors.narfi と tests/unsound.narfi の証明は1本も通らないことを確かめる。

use std::process::Command;

fn run(files: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_narfi")).arg("check").args(files).output().unwrap();
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn correct_proofs_pass() {
    let out = run(&["examples/basics.narfi", "examples/analysis.narfi"])
        + &run(&["tests/exercises_answers.narfi"]);
    assert!(!out.contains('✗'), "{out}");
    assert!(out.contains("すべて検証しました"), "{out}");
}

#[test]
fn wrong_proofs_fail() {
    for f in ["examples/errors.narfi", "tests/unsound.narfi"] {
        let out = run(&[f]);
        let passed: Vec<&str> = out.lines().filter(|l| l.trim_start().starts_with('✓')).collect();
        assert!(passed.is_empty(), "{f} で通ってしまった証明: {passed:?}\n{out}");
        assert!(out.contains('✗'), "{out}");
    }
}
