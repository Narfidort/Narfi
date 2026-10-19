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
        + &run(&["examples/limits.narfi"])
        + &run(&["examples/hol.narfi"])
        + &run(&["lib/reals/rat.narfi", "lib/reals/cauchy.narfi", "lib/reals/real.narfi"]);
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
        "tests/unsound_hol.narfi",
        "tests/unsound_typedef.narfi",
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
        ("def p(x) := q(x)\ndef q(x) := p(x)", "定義済みの記号でもない"),
        ("def bad(a) := a(n) > 0", "定義済みの記号でもない"),
        ("def pos(x) := x > 0\nthm t : ⊢ pos(1, 2)\nsorry", "引数 1 個の定義"),
    ];
    for (i, (src, msg)) in cases.iter().enumerate() {
        let f = dir.join(format!("case{i}.narfi"));
        std::fs::write(&f, src).unwrap();
        let out = run(&[f.to_str().unwrap()]);
        assert!(out.contains("構文エラー") && out.contains(msg), "{src}\n{out}");
    }
}

/// v2.1 の健全性のバグの回帰テスト：⊥ の証明が通ってはいけない
#[test]
fn regression_subst_placeholder() {
    let out = run(&["tests/regress/subst_placeholder.narfi"]);
    assert!(out.contains("✗ k.bug"), "{out}");
    assert!(out.contains("✗ boom"), "{out}");
    assert!(!out.lines().any(|l| l.trim_start().starts_with("✓ boom")), "{out}");
}

/// 仮定の中身を省略するとエラーになり、goal から決まる中身を help に示す（v2.5）
#[test]
fn omitted_hypothesis_is_an_error() {
    let dir = std::env::temp_dir().join(format!("narfi-hyp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("thm t :\n  ⊢ ∀ε:ℝ>0. ε > 0\n\nFix ε | hε\n  hε\n", "`hε : ε > 0` と書く"),
        ("thm t :\n  P : Prop\n  ⊢ P → P\n\nassume h\n  h\n", "`h : P` と書く"),
    ];
    for (i, (src, msg)) in cases.iter().enumerate() {
        let f = dir.join(format!("case{i}.narfi"));
        std::fs::write(&f, src).unwrap();
        let out = run(&[f.to_str().unwrap()]);
        assert!(out.contains("✗ t") && out.contains("中身が書かれていない") && out.contains(msg), "{src}\n{out}");
        let fixed = src.replace("| hε\n", "| hε : ε > 0\n").replace("assume h\n", "assume h : P\n");
        std::fs::write(&f, &fixed).unwrap();
        let out = run(&[f.to_str().unwrap()]);
        assert!(out.contains("✓ t"), "{fixed}\n{out}");
    }
}

/// 数列の添字 a_n（v2.5.4）
#[test]
fn sequence_subscripts() {
    let out = run(&["tests/subscript.narfi"]);
    for n in ["sub.basic", "sub.chain", "sub.name", "show.and_swap", "show.then"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
}
