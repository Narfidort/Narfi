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
        // 書き方が古くなって構文エラーで落ちているなら、確かめたい誤りを確かめていない
        assert!(!out.contains("構文エラー"), "{f} が構文エラーで失敗している（確かめたい誤りではない）\n{out}");
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
        ("def P(a : ℕ, b : ℕ) :⇔ a = b\nnotation a => b := P(a, b)", "あいまい"),
        ("def P(a : ℕ, b : ℕ) :⇔ a = b\nnotation a ~> b := P(a, b)\nnotation x ~> y := P(y, x)", "あいまい"),
        ("def P(a : ℕ → ℝ, b : ℝ) :⇔ a(0) = b\nnotation a_n ~> b (n) := P((n : ℕ ↦ a), b)", "「a」と書く"),
        ("def P(a : ℕ, b : ℕ) :⇔ a = b\nnotation a ~> a := P(a, a)", "2 回"),
        ("def P(a : ℕ → ℝ, b : ℝ) :⇔ a(0) = b\nnotation a ~> b := P((n : ℕ ↦ a), b)", "束縛変数「n」を書く"),
        ("def P(a : ℕ, b : ℕ) :⇔ a = b\nnotation a b := P(a, b)", "少なくとも 1 つ"),
        ("def r(a) :⇔ r(a)", "自身を使っている"),
        ("def p(x) :⇔ q(x)\ndef q(x) :⇔ p(x)", "定義済みの記号でもない"),
        ("def bad(a) :⇔ a(n) > 0", "定義済みの記号でもない"),
        ("def pos(x) :⇔ x > 0\nthm t : ⊢ pos(1, 2)\nsorry", "引数 1 個の定義"),
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
        ("thm t :\n  P : Prop\n  ⊢ P ⇒ P\n\nassume h\n  h\n", "`h : P` と書く"),
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
    for n in ["sub.basic", "sub.chain", "sub.name", "show.and_swap", "show.then", "mul.implicit", "mul.by", "sub.two", "sub.fn", "sub.greek", "sup.norm"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
}

/// 規則の名前：and.intro・and.left・and.right・imp.elim・all.elim・bot.elim
#[test]
fn rule_names() {
    let out = run(&["tests/rules.narfi"]);
    for n in ["r1", "r2", "r3", "r4", "r5", "r6", "r7"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
}

/// 原始再帰の定義（rec）：等式の定理ができ、原始再帰でないものは拒否する
#[test]
fn primitive_recursion() {
    let out = run(&["tests/rec.narfi"]);
    for n in ["sum.zero", "sum.succ", "fact.zero", "fact.succ", "sum2", "fact1", "Dn.zero", "Dn.succ", "Dn.step", "Dn.base"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
    let dir = std::env::temp_dir().join(format!("narfi-rec-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("rec f(n : ℕ) : ℕ\n  f(0) = 0\n  f(n + 1) = f(n + 1)\n", "原始再帰"),
        ("rec f(n : ℕ) : ℕ\n  f(0) = f(0)\n  f(n + 1) = f(n)\n", "0 のときの右辺"),
        ("rec f(n : ℕ) : ℕ\n  f(0) = 0\n", "2 つの等式"),
    ];
    for (i, (src, msg)) in cases.iter().enumerate() {
        let f = dir.join(format!("rec{i}.narfi"));
        std::fs::write(&f, src).unwrap();
        let out = run(&[f.to_str().unwrap()]);
        assert!(out.contains("構文エラー") && out.contains(msg), "{src}\n{out}");
    }
}

/// const で宣言した述語記号（… → Prop）は、命題の中で述語として使える（`f ∈ Sm` の書き方も）
#[test]
fn const_predicates() {
    let out = run(&["tests/const_pred.narfi"]);
    for n in ["P.one", "Sm.DD"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
    assert!(!out.contains("✗"), "{out}");
}

/// funext（型は使う所から決まる）と η 変換（(x ↦ F(x)) は F と同じ）
#[test]
fn funext_and_eta() {
    let out = run(&["tests/funext.narfi"]);
    for n in ["fn.ext", "fn.ext.lam", "fn.ext.rec", "eta.int", "eta.int.rec"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
    assert!(!out.contains("✗"), "{out}");
}

/// 数の埋め込み（ℕ ⊂ ℝ）：自然数は実数の式に書け、逆は書けない
#[test]
fn numeric_embedding() {
    let out = run(&["tests/coerce.narfi"]);
    for n in ["co.arg", "co.lin", "co.seq", "co.int"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
    for n in ["co.bad.real_index", "co.bad.sub_index"] {
        assert!(out.contains(&format!("✗ {n}")), "{out}");
    }
}

/// 行列（関数を値にする定義・β・Σ）：2×2 のケイリー・ハミルトンなどがすべて通る
#[test]
fn matrices() {
    let out = run(&["lib/algebra/delta.narfi", "lib/algebra/matrix.narfi"]);
    assert!(!out.contains('✗') && !out.contains("構文エラー"), "{out}");
    for n in ["cayley_hamilton2", "mmul.add_left", "mat2.det", "delta.same"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
}

/// 一般の大きさの行列 [[…], …]（matent の和の λ）：2×3 の成分が求まり、表示は [[…]] に戻る
#[test]
fn general_matrices() {
    let out = run(&["tests/matrix_general.narfi"]);
    assert!(out.contains("✓ m23.entry"), "{out}");
    let conv = Command::new(env!("CARGO_BIN_EXE_narfi")).args(["convert", "--std", "tests/matrix_general.narfi"]).output().unwrap();
    let conv = String::from_utf8(conv.stdout).unwrap();
    assert!(conv.contains("[[1, 2, 3], [4, 5, 6]]"), "{conv}");
}

/// 事実の行（v2.6）：根拠がなければエラーにし、見つかった根拠を help に出す。消した書き方（have など）は、今の書き方を案内するエラー
#[test]
fn fact_lines_and_old_forms() {
    let out = run(&["tests/missing_just.narfi"]);
    for (n, j) in [("m1", "by linarith"), ("m2", "by h.right"), ("m3", "by f(a)")] {
        assert!(out.contains(&format!("✗ {n}")), "{out}");
        assert!(out.contains(j), "{n} の候補 {j} がない\n{out}");
    }
    let dir = std::env::temp_dir().join(format!("narfi-old-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("old.narfi");
    std::fs::write(&f, "thm t :\n  P : Prop, h : P\n  ⊢ P\n\nhave k : P := h\nk\n").unwrap();
    let out = run(&[f.to_str().unwrap()]);
    assert!(out.contains("✗ t") && out.contains("`have` は使わない") && out.contains("h : φ by 根拠"), "{out}");
}

/// 記号を "…" で囲む notation（v2.8 までの書き方）は構文エラー
#[test]
fn quoted_notation_is_an_error() {
    let dir = std::env::temp_dir().join(format!("narfi-notation-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("old.narfi");
    std::fs::write(&f, "def P(a : ℕ, b : ℕ) :⇔ a = b\nnotation a \"≺\" b := P(a, b)\n").unwrap();
    let out = run(&[f.to_str().unwrap()]);
    assert!(out.contains("構文エラー") && out.contains("引用符"), "{out}");
}


/// ベンチマーク（lib/bench、docs/bench.md）：構文エラーがないこと、通っている定理が通り続けること
#[test]
fn benchmarks() {
    let passing = [
        ("calculus", "cont.add"),
        ("calculus", "squeeze"),
        ("complex", "cabs.mul"),
        ("functional_analysis", "parallelogram"),
        ("linear_algebra", "ch2"),
        ("logic", "injective.comp"),
        ("logic", "surjective.comp"),
        ("number_theory", "dvd.trans"),
        ("number_theory", "even.add"),
        ("number_theory", "odd.sq"),
        ("numerical", "contraction"),
        ("probability", "ex.add"),
        ("sets", "preimage.cup"),
        ("sets", "de_morgan"),
        ("sets", "image.cap"),
        ("linear_algebra", "ker.add"),
        ("measure", "measure.mono"),
    ];
    for f in ["calculus", "complex", "functional_analysis", "graph", "linear_algebra", "logic", "measure", "number_theory", "numerical", "probability", "sets"] {
        let out = run(&[&format!("lib/bench/{f}.narfi")]);
        assert!(!out.contains("構文エラー"), "lib/bench/{f}.narfi に構文エラー\n{out}");
        for (g, name) in passing {
            if g == f {
                assert!(out.lines().any(|l| l.trim_start().starts_with(&format!("✓ {name}"))), "lib/bench/{f}.narfi の {name} が通らなくなった\n{out}");
            }
        }
    }
}

/// 線形代数：未知数が方程式より多ければ自明でない解（lin.dep）、次元の上界（dim.bound）
#[test]
fn linear_algebra_lib() {
    let out = run(&["lib/linear/dependence.narfi", "lib/linear/dimension.narfi", "lib/linear/span.narfi", "lib/linear/tri.narfi"]);
    assert!(!out.contains('✗') && !out.contains('△') && !out.contains("構文エラー"), "{out}");
    for n in ["lin.dep", "dim.bound", "cdim.add", "cdim.tri", "sq.sum"] {
        assert!(out.contains(&format!("✓ {n}")), "{out}");
    }
}

/// 古い書き方は narfi migrate で今の書き方に直り、検査が通る
#[test]
fn migrate_legacy() {
    let dir = std::env::temp_dir().join("narfi_migrate_test");
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("legacy.narfi");
    std::fs::copy("tests/regress/legacy.narfi", &f).unwrap();
    let before = run(&[f.to_str().unwrap()]);
    assert!(before.contains("構文エラー"), "{before}");
    let st = std::process::Command::new(env!("CARGO_BIN_EXE_narfi")).args(["migrate", "--write", f.to_str().unwrap()]).status().unwrap();
    assert!(st.success());
    let after = run(&[f.to_str().unwrap()]);
    assert!(!after.contains("構文エラー") && after.contains("3 個の定理をすべて検証しました"), "{after}");
}

/// 読み込みの使い回し（module.rs）：使い回した結果が、毎回読み直した結果と完全に同じ（JSON の全体を比べる）
#[test]
fn import_cache_gives_identical_results() {
    // 検査は深く再帰する。テストのスレッドの既定のスタック（2MB）では極端に遅くなるので、大きくして走らせる
    std::thread::Builder::new().stack_size(256 << 20).spawn(import_cache_body).unwrap().join().unwrap();
}

fn import_cache_body() {
    use std::path::Path;
    let mut files: Vec<String> = Vec::new();
    for dir in ["lib", "examples", "tests"] {
        let mut stack = vec![std::path::PathBuf::from(dir)];
        while let Some(d) = stack.pop() {
            for e in std::fs::read_dir(&d).unwrap().flatten() {
                let p = e.path();
                if p.is_dir() {
                    if !p.ends_with("cyclic") {
                        stack.push(p);
                    }
                } else if p.extension().is_some_and(|x| x == "narfi") {
                    files.push(p.to_string_lossy().into_owned());
                }
            }
        }
    }
    files.sort();
    let check = |src: &str, f: &str| narfi::api::check_json_in(src, Some(3), "ja", &|s| narfi::module::load_and_check(s, Some(Path::new(f))));
    for f in &files {
        let src = std::fs::read_to_string(f).unwrap();
        narfi::module::set_cache_enabled(false);
        let fresh = check(&src, f);
        narfi::module::set_cache_enabled(true);
        let first = check(&src, f);
        let second = check(&src, f);
        // 本体だけを書き換えた（冒頭の import は同じ）ときも同じ
        let edited = format!("{src}\n-- edit\n");
        narfi::module::set_cache_enabled(false);
        let fresh_e = check(&edited, f);
        narfi::module::set_cache_enabled(true);
        let cached_e = check(&edited, f);
        assert_eq!(fresh, first, "{f}: 使い回しの 1 回目が違う");
        assert_eq!(fresh, second, "{f}: 使い回しの 2 回目が違う");
        assert_eq!(fresh_e, cached_e, "{f}: 本体を変えたときに違う");
    }
}

/// 読み込みの使い回し：import したファイルを書き換えたら、使い回さずに読み直す
#[test]
fn import_cache_notices_changed_library() {
    std::thread::Builder::new().stack_size(256 << 20).spawn(|| {
        use std::path::Path;
        let dir = std::env::temp_dir().join(format!("narfi-cache-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let lib = dir.join("mylib.narfi");
        let main = dir.join("main.narfi");
        std::fs::write(&lib, "thm one_pos :\n  |- 1 > 0\n\ndecide\n").unwrap();
        let src = "import mylib\n\nthm use_it :\n  |- 1 > 0\n\none_pos\n";
        std::fs::write(&main, src).unwrap();
        let check = || narfi::api::check_json_in(src, Some(1), "ja", &|s| narfi::module::load_and_check(s, Some(Path::new(&main))));
        narfi::module::set_cache_enabled(true);
        let a = check();
        assert!(a.contains("\"status\":\"ok\""), "{a}");
        // ライブラリの定理の名前を変える：main の one_pos は見つからなくなるはず
        std::fs::write(&lib, "thm one_pos2 :\n  |- 1 > 0\n\ndecide\n").unwrap();
        let b = check();
        assert!(b.contains("\"status\":\"error\""), "ライブラリの変更が反映されない:\n{b}");
        // 元に戻せば、また通る
        std::fs::write(&lib, "thm one_pos :\n  |- 1 > 0\n\ndecide\n").unwrap();
        let c = check();
        assert_eq!(a, c);
    }).unwrap().join().unwrap();
}
