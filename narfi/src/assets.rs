//! 同梱した KaTeX（MIT ライセンス、assets/katex/LICENSE）。ネットにつながっていなくても数式を表示できるように。

pub const KATEX_FILES: &[(&str, &[u8])] = &[
    ("katex.min.js", include_bytes!("../assets/katex/katex.min.js")),
    ("katex.min.css", include_bytes!("../assets/katex/katex.min.css")),
    ("fonts/KaTeX_AMS-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_AMS-Regular.woff2")),
    ("fonts/KaTeX_Caligraphic-Bold.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Caligraphic-Bold.woff2")),
    ("fonts/KaTeX_Caligraphic-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Caligraphic-Regular.woff2")),
    ("fonts/KaTeX_Fraktur-Bold.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Fraktur-Bold.woff2")),
    ("fonts/KaTeX_Fraktur-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Fraktur-Regular.woff2")),
    ("fonts/KaTeX_Main-Bold.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Main-Bold.woff2")),
    ("fonts/KaTeX_Main-BoldItalic.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Main-BoldItalic.woff2")),
    ("fonts/KaTeX_Main-Italic.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Main-Italic.woff2")),
    ("fonts/KaTeX_Main-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Main-Regular.woff2")),
    ("fonts/KaTeX_Math-BoldItalic.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Math-BoldItalic.woff2")),
    ("fonts/KaTeX_Math-Italic.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Math-Italic.woff2")),
    ("fonts/KaTeX_SansSerif-Bold.woff2", include_bytes!("../assets/katex/fonts/KaTeX_SansSerif-Bold.woff2")),
    ("fonts/KaTeX_SansSerif-Italic.woff2", include_bytes!("../assets/katex/fonts/KaTeX_SansSerif-Italic.woff2")),
    ("fonts/KaTeX_SansSerif-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_SansSerif-Regular.woff2")),
    ("fonts/KaTeX_Script-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Script-Regular.woff2")),
    ("fonts/KaTeX_Size1-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Size1-Regular.woff2")),
    ("fonts/KaTeX_Size2-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Size2-Regular.woff2")),
    ("fonts/KaTeX_Size3-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Size3-Regular.woff2")),
    ("fonts/KaTeX_Size4-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Size4-Regular.woff2")),
    ("fonts/KaTeX_Typewriter-Regular.woff2", include_bytes!("../assets/katex/fonts/KaTeX_Typewriter-Regular.woff2")),
];

pub fn content_type(path: &str) -> &'static str {
    if path.ends_with(".js") {
        "application/javascript; charset=utf-8"
    } else if path.ends_with(".css") {
        "text/css; charset=utf-8"
    } else if path.ends_with(".woff2") {
        "font/woff2"
    } else {
        "application/octet-stream"
    }
}
