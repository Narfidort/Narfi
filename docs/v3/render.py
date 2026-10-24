"""docs/ の *.md を、数式（KaTeX）と表を描画した HTML にする（確認用）。使い方: python3 render.py 名前.md"""
import html, re, sys, pathlib

def inline(s):
    out, parts = "", re.split(r"(`[^`]+`|\$[^$]+\$)", s)
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) > 1:
            out += f"<code>{html.escape(p[1:-1])}</code>"
        elif p.startswith("$") and p.endswith("$") and len(p) > 1:
            out += f'<span class="m">{html.escape(p[1:-1])}</span>'
        else:
            t = html.escape(p)
            t = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", t)
            t = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r'<a href="\2">\1</a>', t)
            out += t
    return out

def convert(md):
    lines, out, i = md.split("\n"), [], 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("```"):
            j = i + 1
            while j < len(lines) and not lines[j].startswith("```"): j += 1
            out.append("<pre>" + html.escape("\n".join(lines[i + 1:j])) + "</pre>"); i = j + 1; continue
        if l.strip().startswith("$$"):
            j, buf = i, l.strip()
            while not (len(buf) > 2 and buf.endswith("$$")) and j + 1 < len(lines):
                j += 1; buf += " " + lines[j].strip()
            out.append(f'<div class="m d">{html.escape(buf[2:-2])}</div>'); i = j + 1; continue
        m = re.match(r"^(#{1,4})\s+(.*)", l)
        if m:
            n = len(m.group(1)); out.append(f"<h{n}>{inline(m.group(2))}</h{n}>"); i += 1; continue
        if l.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                if not re.match(r"^\|[\s\-|:]+\|$", lines[i]):
                    rows.append([c.strip().replace("\\|", "|") for c in re.split(r"(?<!\\)\|", lines[i].strip().strip("|"))])
                i += 1
            t = "<table><tr>" + "".join(f"<th>{inline(c)}</th>" for c in rows[0]) + "</tr>"
            for r in rows[1:]: t += "<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>"
            out.append(t + "</table>"); continue
        if re.match(r"^\s*(- |\d+\. )", l):
            items, ordered = [], bool(re.match(r"^\s*\d+\.", l))
            while i < len(lines) and re.match(r"^\s*(- |\d+\. )", lines[i]):
                depth = len(lines[i]) - len(lines[i].lstrip())
                items.append((depth, re.sub(r"^\s*(- |\d+\. )", "", lines[i]))); i += 1
            tag = "ol" if ordered else "ul"
            out.append(f"<{tag}>" + "".join(f'<li style="margin-left:{d*12}px">{inline(t)}</li>' for d, t in items) + f"</{tag}>"); continue
        if not l.strip(): i += 1; continue
        para = []
        while i < len(lines) and lines[i].strip() and not re.match(r"^(#|```|\||\s*- |\s*\d+\. )", lines[i]):
            para.append(lines[i]); i += 1
        out.append("<p>" + inline(" ".join(para)) + "</p>")
    return "\n".join(out)

src = pathlib.Path(sys.argv[1]); body = convert(src.read_text())
import os
root = pathlib.Path(__file__).resolve().parents[2]
katex = os.path.relpath(root / "narfi/site/assets/katex", src.resolve().parent)
page = f"""<!doctype html><html lang="ja"><head><meta charset="utf-8"><title>{src.stem}</title>
<link rel="stylesheet" href="{katex}/katex.min.css"><script src="{katex}/katex.min.js"></script>
<style>body{{font-family:-apple-system,"Hiragino Sans",sans-serif;background:#0d1117;color:#e6edf3;max-width:1050px;margin:28px auto;padding:0 24px;line-height:1.75;font-size:15px}}
h1{{font-size:22px}}h2{{font-size:18px;margin-top:34px;border-bottom:1px solid #30363d;padding-bottom:4px}}h3{{font-size:16px;margin-top:24px}}
code{{font-family:"JetBrains Mono",Menlo,monospace;font-size:13px;background:#161b22;padding:1px 5px;border-radius:4px;color:#a5d6ff}}
pre{{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:12px 16px;font-family:"JetBrains Mono",Menlo,monospace;font-size:13.5px;line-height:1.6;overflow-x:auto;color:#e6edf3}}
table{{border-collapse:collapse;width:100%;font-size:14px;margin:10px 0}}th,td{{border:1px solid #30363d;padding:6px 9px;vertical-align:top;text-align:left}}th{{background:#161b22;color:#8b949e;font-weight:500}}
a{{color:#58a6ff}}li{{margin:3px 0}}</style></head><body>{body}
<script>document.querySelectorAll('.m').forEach(e=>{{try{{katex.render(e.textContent,e,{{throwOnError:false,displayMode:e.classList.contains('d')}})}}catch(_){{}}}})</script></body></html>"""
dst = src.with_suffix(".html"); dst.write_text(page); print(dst)
