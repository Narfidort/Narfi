//! Web エディタの往復（ファイル → 構造化 AST → ASCII）で証明の意味が変わらないことを確かめる。
//! web_ui.html の読み込み・直列化を node で動かす（tests/ui_roundtrip.js）。node がなければ飛ばす。

use std::path::Path;
use std::process::Command;

const FILES: [&str; 18] = [
    "tests/rec.narfi",
    "lib/algebra/sum.narfi",
    "tests/rules.narfi",
    "tests/subscript.narfi",
    "lib/reals/rat.narfi",
    "lib/reals/cauchy.narfi",
    "lib/reals/real.narfi",
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

/// ソースの変換（日本語シュガー・標準 ASCII）で検査結果が変わらないこと。
/// 変換したものをさらにエディタの往復にかけても変わらないこと。
#[test]
fn source_conversion_preserves_proofs() {
    let node = Command::new("node").arg("--version").output().is_ok();
    let mut files: Vec<&str> = FILES.to_vec();
    files.extend(["tests/unsound_typedef.narfi", "tests/regress/subst_placeholder.narfi"]);
    for f in files {
        let f = Path::new(f);
        for mode in ["--jp", "--std"] {
            let out = Command::new(env!("CARGO_BIN_EXE_narfi")).args(["convert", mode]).arg(f).output().unwrap();
            let converted = String::from_utf8(out.stdout).unwrap();
            let tmp = f.with_file_name(format!(".convert-{}{}.narfi", std::process::id(), mode));
            std::fs::write(&tmp, &converted).unwrap();
            let got = statuses(&tmp);
            let via_ui = if node {
                let rt = roundtrip(&tmp);
                std::fs::write(&tmp, &rt).unwrap();
                Some(statuses(&tmp))
            } else {
                None
            };
            std::fs::remove_file(&tmp).unwrap();
            assert_eq!(statuses(f), got, "{} {mode}: 変換すると検査結果が変わる\n{converted}", f.display());
            if let Some(v) = via_ui {
                assert_eq!(statuses(f), v, "{} {mode}: 変換してエディタを通すと検査結果が変わる", f.display());
            }
        }
    }
}

/// エディタの往復でコメント・見出しの行が失われないこと（自動保存でファイルから消えないように）
#[test]
fn editor_roundtrip_keeps_comments() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node がないので飛ばす");
        return;
    }
    let comment_lines = |s: &str| -> Vec<String> {
        s.lines()
            .map(str::trim)
            .filter(|l| l.starts_with("--") || l.starts_with("//") || l.starts_with('#'))
            .map(String::from)
            .collect()
    };
    for f in FILES {
        let src = std::fs::read_to_string(f).unwrap();
        let once = roundtrip(Path::new(f));
        assert_eq!(comment_lines(&src), comment_lines(&once), "{f}: エディタを通すとコメントが変わる");
    }
}

/// チュートリアル（src/tutorial.js）の答えがすべて通り、練習は sorry だけが残る（構文エラーにならない）こと
#[test]
fn tutorial_answers_check() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node がないので飛ばす");
        return;
    }
    let script = r#"
        global.window = {};
        require(process.argv[1]);
        require(process.argv[1].replace("tutorial.js", "course.js"));
        process.stdout.write(JSON.stringify([...window.NARFI_TUTORIAL, ...window.NARFI_COURSE].filter(l => l.exercise)));
    "#;
    let out = Command::new("node").args(["-e", script, "./src/tutorial.js"]).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let json = String::from_utf8(out.stdout).unwrap();
    // 小さな JSON の取り出し（"exercise" と "answer" の文字列）
    let field = |obj: &str, key: &str| -> Vec<String> {
        let mut v = Vec::new();
        let pat = format!("\"{key}\":\"");
        let mut rest = obj;
        while let Some(k) = rest.find(&pat) {
            let s = &rest[k + pat.len()..];
            let mut out = String::new();
            let mut it = s.chars();
            while let Some(c) = it.next() {
                match c {
                    '\\' => match it.next() {
                        Some('n') => out.push('\n'),
                        Some('t') => out.push('\t'),
                        Some('u') => {
                            let h: String = it.by_ref().take(4).collect();
                            out.push(char::from_u32(u32::from_str_radix(&h, 16).unwrap()).unwrap());
                        }
                        Some(c) => out.push(c),
                        None => {}
                    },
                    '"' => break,
                    c => out.push(c),
                }
            }
            v.push(out);
            rest = &s[1..];
        }
        v
    };
    let exercises = field(&json, "exercise");
    let answers = field(&json, "answer");
    assert_eq!(exercises.len(), answers.len());
    assert!(answers.len() >= 12);
    let dir = std::env::temp_dir().join(format!("narfi-tut-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for (k, (ex, ans)) in exercises.iter().zip(&answers).enumerate() {
        let fa = dir.join(format!("ans{k}.narfi"));
        std::fs::write(&fa, ans).unwrap();
        let st = statuses(&fa);
        assert!(st.iter().any(|s| s.starts_with('✓')) && st.iter().all(|s| s.starts_with('✓') || s.starts_with("公理")), "答え {k} が通らない: {st:?}\n{ans}");
        let fe = dir.join(format!("ex{k}.narfi"));
        std::fs::write(&fe, ex).unwrap();
        let st = statuses(&fe);
        // 練習は sorry が残る（△）。コースでは、すでに証明してある補題は ✓ のままでよい
        assert!(
            st.iter().any(|s| s.starts_with('△')) && st.iter().all(|s| s.starts_with('△') || s.starts_with('✓') || s.starts_with("公理")),
            "練習 {k} が △ にならない: {st:?}\n{ex}"
        );
    }
}
