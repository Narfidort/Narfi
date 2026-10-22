import json, html
# (記法 LaTeX, 意味, Narfi のファイルでの形, 状態, 判断・メモ)
# 状態: ok=済, nodef=書けるが定義なし, no=未対応, dec=決めること
G = []
def g(title, rows): G.append((title, rows))

g("論理", [
 (r"\forall x.\ P,\ \exists x.\ P", "全称・存在", "forall x. P", "ok", ""),
 (r"\forall \varepsilon>0.\ P,\ \forall x \in A.\ P", "範囲付き量化子", "forall eps>0. P", "ok", ""),
 (r"\exists!\, x.\ P", "ただ 1 つ存在", "", "no", ""),
 (r"P \land Q,\ P \lor Q,\ \lnot P", "かつ・または・否定", "P and Q", "ok", ""),
 (r"P \Rightarrow Q \quad / \quad P \to Q", "ならば", "P -> Q（→ で表示）", "dec",
  r"教科書は $\Rightarrow$、Narfi は $\to$。$\to$ は関数の型 $\mathbb{N}\to\mathbb{R}$ と極限 $a_n\to\alpha$ にも使うので、<b>ならばは $\Rightarrow$ にそろえる</b>のを推奨"),
 (r"P \Leftrightarrow Q \quad / \quad P \leftrightarrow Q", "同値", "P <-> Q", "dec", r"上と同じく $\Leftrightarrow$ を推奨"),
 (r"x := t,\quad P :\Leftrightarrow Q", "定義", "def … := …", "ok", r"述語の定義を $:\Leftrightarrow$ で書くかは任意（今は := のみ）"),
])
g("集合", [
 (r"x \in A,\ x \notin A", "属する", "x in A", "ok", ""),
 (r"A \subseteq B", "部分集合", "A subseteq B", "ok", ""),
 (r"A \subset B", "部分集合（等しくてもよい？）", "A subset B（今は ⊆ と同じ）", "dec",
  r"日本の教科書は $\subset$ を $\subseteq$ の意味で使うことが多い。<b>$\subset$ = $\subseteq$、真部分集合は $\subsetneq$</b> を推奨"),
 (r"\{x \in A \mid P(x)\}", "条件で作る集合", "{x : ℕ | P}（型で書く）", "no", r"$\{x \in A \mid \dots\}$（集合で絞る形）は未対応"),
 (r"\{a, b, c\}", "要素を並べた集合", "", "no", ""),
 (r"\emptyset", "空集合", "", "no", ""),
 (r"A \cup B,\ A \cap B,\ A \setminus B", "和・共通部分・差", "A ∪ B", "ok", ""),
 (r"A^c \quad / \quad \overline{A} \quad / \quad A^\complement", "補集合", "", "dec",
  r"$A^c$ は冪 $A^c$ と、$\overline{A}$ は閉包・共役と衝突。<b>$A^\complement$（別の記号）</b>を推奨"),
 (r"A \times B", "直積", "", "no", ""),
 (r"\mathcal{P}(A) \quad / \quad 2^A", "冪集合", "", "dec", r"$2^A$ は冪と衝突。<b>$\mathcal{P}(A)$</b> を推奨"),
 (r"|A| \quad / \quad \#A", "要素の個数", "", "dec", r"$|A|$ は絶対値と衝突（型で読み分けない方針）。<b>$\#A$</b> を推奨"),
 (r"\mathbb{N}", "自然数", "ℕ（0 を含む）", "dec", r"日本の高校・一部の教科書は $\mathbb{N}=\{1,2,\dots\}$。<b>0 を含む</b>（今のまま、ペアノ）を推奨。正の整数は $\mathbb{Z}_{>0}$"),
 (r"\mathbb{Z},\ \mathbb{Q},\ \mathbb{R}", "整数・有理数・実数", "ℤ ℚ ℝ", "ok", ""),
 (r"\mathbb{C}", "複素数", "", "no", ""),
])
g("区間・組", [
 (r"(a, b)", "開区間？ 順序対？", "", "dec",
  r"開区間・順序対・最大公約数の 3 通り。<b>$(a,b)$ は順序対、開区間は $]a,b[$</b>、最大公約数は $\gcd(a,b)$ を推奨（別案：区間を $(a,b)$ にして、対を $\langle a,b\rangle$）"),
 (r"[a, b],\ [a, b[",  "閉区間・半開区間", "", "no", r"行列 $[[a,b],[c,d]]$ と書き分けられる"),
])
g("関数", [
 (r"f\colon A \to B", "関数の宣言", "f : A -> B", "ok", ""),
 (r"x \mapsto t", "関数そのもの", "(x : ℝ |-> t)", "ok", ""),
 (r"g \circ f", "合成", "", "no", ""),
 (r"f^{-1}", "逆関数", "", "dec", r"逆関数・逆像・逆数の 3 通り。<b>$f^{-1}$ は逆関数だけ</b>を推奨"),
 (r"f^{-1}(B) \quad / \quad f^{-1}[B]", "逆像", "", "dec", r"逆関数の値と衝突（型で読み分けない方針）。<b>$f^{-1}[B]$</b> を推奨"),
 (r"f(A) \quad / \quad f[A]", "像", "", "dec", r"関数の値 $f(x)$ と衝突。<b>$f[A]$</b> を推奨"),
 (r"f|_A", "制限", "", "no", ""),
 (r"f^n \quad / \quad f^{\circ n}", "n 回の合成", "", "dec", r"冪・n 階導関数と衝突。<b>$f^{\circ n}$</b> を推奨。$f^n$ は書けない（関数の冪はない）"),
 (r"\sin^2 x", "$(\sin x)^2$", "", "dec", r"$\sin^{-1}x$（逆関数）と一貫しない。<b>$(\sin x)^2$ と書く</b>を推奨"),
 (r"\mathrm{id}_A", "恒等写像", "", "no", ""),
])
g("数と演算", [
 (r"a + b,\ a - b,\ -a", "和・差・符号", "a + b", "ok", ""),
 (r"2x,\ 3a_n", "数のあとの積", "2x", "ok", ""),
 (r"ab \quad / \quad a \cdot b", "文字どうしの積", "a * b（ab は 1 つの名前）", "dec",
  r"教科書は $ab$。Narfi では $ab$ は名前。<b>ファイルは $a\cdot b$、表示で $ab$ に</b>するか、<b>1 文字の変数を並べたら積</b>にするか"),
 (r"\frac{a}{b},\ a^n,\ |x|", "商・冪・絶対値", "a / b", "ok", ""),
 (r"\sqrt{x},\ \sqrt[n]{x}", "平方根・n 乗根", "sqrt(x)", "nodef", r"書けるが、定義（性質）がまだない"),
 (r"n!", "階乗", "", "no", ""),
 (r"\binom{n}{k}", "二項係数", "binom(n, k)", "nodef", ""),
 (r"\lfloor x \rfloor,\ \lceil x \rceil", "床・天井", "floor(x)", "nodef", ""),
 (r"a \mid b", "割り切る", "", "no", r"記号はあるが使えない"),
 (r"a \equiv b \pmod{n}", "合同", "", "no", ""),
 (r"\gcd(a, b)", "最大公約数", "", "no", ""),
 (r"\max(a, b) \quad / \quad \max\{a, b\}", "大きいほう", "max(a, b)", "dec", r"教科書は $\max\{a,b\}$（集合の最大）が多い。集合の $\max$ を作るなら <b>$\max\{a,b\}$ に統一</b>"),
 (r"\log x \quad / \quad \ln x", "自然対数", "", "dec", r"<b>$\log$ を自然対数</b>（大学の慣習）を推奨"),
 (r"e,\ \pi", "定数", "", "no", ""),
 (r"a \le b \le c", "不等式の連なり", "", "no", r"今は $a\le b \land b\le c$ と書く"),
])
g("列・極限・和", [
 (r"a_n,\ a_{n+1}", "数列の項", "a_n", "ok", ""),
 (r"(a_n)_{n} \quad / \quad \{a_n\}", "数列そのもの", "a（名前）", "dec", r"$\{a_n\}$ は 1 点集合と衝突。<b>$(a_n)_n$</b> を推奨（または名前 $a$ だけ）"),
 (r"a_n \to \alpha\ (n \to \infty)", "収束する", "a_n -> alpha (n -> infty)", "ok", ""),
 (r"\lim_{n\to\infty} a_n", "極限の値", "", "no", r"極限が 1 つであることを証明してから、値を返す関数として"),
 (r"\sum_{k<n} a_k", "有限和", "Σ の入力欄", "ok", ""),
 (r"\sum_{k=1}^{n} a_k", "有限和（1 から）", "", "no", r"$\sum_{k=0}^{m}$ は書ける。1 から始まる形は未対応"),
 (r"\prod_{k=1}^{n} a_k", "有限積", "", "no", ""),
 (r"\sup A,\ \inf A,\ \max A,\ \min A", "上限・下限・最大・最小", "", "no", ""),
 (r"\sup_{x\in A} f(x)", "像の上限", "", "no", r"入力欄（v2.10）はある。定義がない"),
 (r"\limsup_{n\to\infty} a_n", "上極限", "", "no", ""),
])
g("微分積分（B の範囲）", [
 (r"f'(x) \quad / \quad \frac{df}{dx}", "導関数", "", "dec",
  r"$x'$（名前）と衝突。<b>$'$ を名前に使えなくして導関数にする</b>か、<b>名前のままにして $\frac{d}{dx}$ だけにする</b>か"),
 (r"f^{(n)}", "n 階導関数", "", "dec", r"上と一緒に決める"),
 (r"\frac{d}{dx}(x^2+1)", "式の微分", "", "no", ""),
 (r"\int_a^b f(x)\,dx", "定積分", "", "no", r"型紙と束縛変数で書ける見込み（$dx$ の $x$ が束縛）"),
 (r"\frac{\partial f}{\partial x}", "偏微分", "", "no", r"関数の引数に名前がないので、多変数のライブラリと一緒に（F1 寄り）"),
])
g("線形代数のうち広く使うもの", [
 (r"A^T \quad / \quad A^\top", "転置", "", "dec", r"$A^T$ は変数 $T$ の冪と衝突。<b>$A^\top$</b> を推奨"),
 (r"AB", "行列の積", "", "dec", r"上の「文字どうしの積」と一緒に決める"),
 (r"\det A", "行列式", "", "no", ""),
 (r"\langle x, y \rangle", "内積", "", "no", r"入力欄はある"),
 (r"\|x\|", "ノルム", "", "no", r"入力欄はある"),
])


# 決定（docs/language/notation.md）。impl=True は v2.11 で実装済み
DECIDED = {
 r"P \Rightarrow Q \quad / \quad P \to Q": ("$\\Rightarrow$（=>）。$\\to$ は関数の型と略記だけ", True),
 r"P \Leftrightarrow Q \quad / \quad P \leftrightarrow Q": ("$\\Leftrightarrow$（<=>）", True),
 r"x := t,\quad P :\Leftrightarrow Q": ("述語は $:\\Leftrightarrow$、値は $:=$", True),
 r"A \subset B": ("$\\subset$ = $\\subseteq$、真部分集合は $\\subsetneq$", True),
 r"A^c \quad / \quad \overline{A} \quad / \quad A^\complement": ("$A^\\complement$", False),
 r"\mathcal{P}(A) \quad / \quad 2^A": ("$\\mathcal{P}(A)$", False),
 r"|A| \quad / \quad \#A": ("$\\#A$", False),
 r"\mathbb{N}": ("0 を含む（$\\mathbb{Z}_{\\ge 0}$ も）", True),
 r"\sin^2 x": ("$(\\sin x)^2$ と書く", False),
 r"ab \quad / \quad a \cdot b": ("ファイルは a b（空白）、表示は ab", False),
 r"\max(a, b) \quad / \quad \max\{a, b\}": ("$\\max\\{a, b\\}$", True),
 r"\log x \quad / \quad \ln x": ("$\\log$ が自然対数", False),
 r"(a_n)_{n} \quad / \quad \{a_n\}": ("$(a_n)_n$", False),
 r"A^T \quad / \quad A^\top": ("$A^\\top$", False),
 r"AB": ("文字どうしの積と同じ", False),
 r"f'(x) \quad / \quad \frac{df}{dx}": ("$\\frac{d}{dx}$・$\\frac{\\partial}{\\partial x}$ だけ", False),
 r"f^{(n)}": ("$\\frac{d^n}{dx^n}$ だけ", False),
 r"(a, b)": ("型で 1 つに決まるときだけ読み分け（両方通ればエラー）", False),
 r"f(A) \quad / \quad f[A]": ("型で読み分け（A が集合なら像）", False),
 r"f^{-1}(B) \quad / \quad f^{-1}[B]": ("型で読み分け（B が集合なら逆像）", False),
 r"f^{-1}": ("$f^{\\circ -1}$ の方向で検討", False),
 r"f^n \quad / \quad f^{\circ n}": ("$f^{\\circ n}$ か宣言", False),
}
for _, rs in G:
    for k, r in enumerate(rs):
        if r[0] in DECIDED:
            text, impl = DECIDED[r[0]]
            FILE = {r"P \Rightarrow Q \quad / \quad P \to Q": "P => Q", r"P \Leftrightarrow Q \quad / \quad P \leftrightarrow Q": "P <=> Q",
                    r"x := t,\quad P :\Leftrightarrow Q": "def p(x) :<=> φ ／ def f(x) : ℝ := t", r"A \subset B": "A subset B ／ A subsetneq B",
                    r"\max(a, b) \quad / \quad \max\{a, b\}": "max{a, b}"}
            rs[k] = (r[0], r[1], FILE.get(r[0], r[2]), "done" if impl else "decided", "<b>決定：" + text + "</b>" + ("（v2.11 で実装）" if impl else "（ライブラリを作るときに実装）"))

OPTS = {
 r"P \Rightarrow Q \quad / \quad P \to Q": ["ならばは $\\Rightarrow$（推奨）", "ならばは $\\to$ のまま"],
 r"P \Leftrightarrow Q \quad / \quad P \leftrightarrow Q": ["$\\Leftrightarrow$（推奨）", "$\\leftrightarrow$ のまま"],
 r"A \subset B": ["$\\subset$ = $\\subseteq$、真部分集合は $\\subsetneq$（推奨）", "$\\subset$ は真部分集合", "$\\subset$ は使わない（$\\subseteq$・$\\subsetneq$ だけ）"],
 r"A^c \quad / \quad \overline{A} \quad / \quad A^\complement": ["$A^\\complement$（推奨）", "$A^c$（c は文字の c）", "$\\overline{A}$", "$X \\setminus A$ と書く"],
 r"\mathcal{P}(A) \quad / \quad 2^A": ["$\\mathcal{P}(A)$（推奨）", "$2^A$"],
 r"|A| \quad / \quad \#A": ["$\\#A$（推奨）", "$|A|$（絶対値と型で読み分ける）", "$\\mathrm{card}\\,A$"],
 r"\mathbb{N}": ["0 を含む（推奨）", "0 を含まない（$\\{1, 2, \\dots\\}$）"],
 r"(a, b)": ["$(a,b)$ は順序対、開区間は $]a,b[$（推奨）", "$(a,b)$ は開区間、順序対は $\\langle a,b\\rangle$", "どちらも $(a,b)$、文脈で（型で読み分け）"],
 r"f^{-1}": ["$f^{-1}$ は逆関数だけ（推奨）", "逆像にも使う"],
 r"f^{-1}(B) \quad / \quad f^{-1}[B]": ["$f^{-1}[B]$（推奨）", "$f^{-1}(B)$（型で読み分け）", "$\\mathrm{preimage}(f, B)$ など名前で"],
 r"f(A) \quad / \quad f[A]": ["$f[A]$（推奨）", "$f(A)$（型で読み分け）", "$\\mathrm{image}(f, A)$ など名前で"],
 r"f^n \quad / \quad f^{\circ n}": ["$f^{\\circ n}$（推奨）", "$f^n$ を合成に（関数の冪は書けない）"],
 r"\sin^2 x": ["$(\\sin x)^2$ と書く（推奨）", "$\\sin^2 x$ を 2 乗として特別に許す"],
 r"ab \quad / \quad a \cdot b": ["ファイルは $a \\cdot b$、表示で $ab$", "1 文字の変数を並べたら積", "今のまま（$a \\cdot b$ と書いて $a \\cdot b$ と表示）"],
 r"\max(a, b) \quad / \quad \max\{a, b\}": ["$\\max\\{a,b\\}$ に統一", "$\\max(a,b)$ のまま"],
 r"\log x \quad / \quad \ln x": ["$\\log$ を自然対数（推奨）", "$\\ln$ を自然対数、$\\log$ は使わない", "両方（同じ意味）"],
 r"(a_n)_{n} \quad / \quad \{a_n\}": ["$(a_n)_n$（推奨）", "名前 $a$ だけ", "$\\{a_n\\}$"],
 r"f'(x) \quad / \quad \frac{df}{dx}": ["$'$ は導関数、名前に $'$ は使えない", "$'$ は名前のまま、導関数は $\\frac{d}{dx}$ だけ", "微分のライブラリを作るときに決める"],
 r"f^{(n)}": ["$f^{(n)}$", "$\\frac{d^n f}{dx^n}$ だけ", "微分のライブラリを作るときに決める"],
 r"A^T \quad / \quad A^\top": ["$A^\\top$（推奨）", "$A^T$（T は文字の T）", "$\\mathrm{transpose}(A)$"],
 r"AB": ["「文字どうしの積」と同じに", "行列だけは並べたら積"],
}

lab = {"done": ("v2.11 で実装", "ok"), "decided": ("決定（未実装）", "nodef"), "ok": ("済", "ok"), "nodef": ("書けるが定義なし", "nodef"), "no": ("未対応", "no"), "dec": ("決めること", "dec")}
n_dec = sum(1 for _, rs in G for r in rs if r[3] == "dec")
n_done = sum(1 for _, rs in G for r in rs if r[3] in ("done", "decided"))
n_all = sum(len(rs) for _, rs in G)
data = [{"t": t, "rows": [{"id": t + "|" + r[0], "m": r[0], "mean": r[1], "file": r[2], "st": r[3], "note": r[4], "opts": OPTS.get(r[0], []) if r[3] == "dec" else []} for r in rs]} for t, rs in G]
missing=[r[0] for _,rs in G for r in rs if r[3]=="dec" and r[0] not in OPTS]

page = r"""<!doctype html><html lang="ja"><head><meta charset="utf-8"><title>Narfi 記法 B（大学以上で広く共通）の候補</title>
<link rel="stylesheet" href="../../narfi/site/assets/katex/katex.min.css">
<script src="../../narfi/site/assets/katex/katex.min.js"></script>
<style>
body{font-family:-apple-system,"Hiragino Sans",sans-serif;background:#0d1117;color:#e6edf3;max-width:1400px;margin:24px auto;padding:0 20px;line-height:1.6}
h1{font-size:22px}h2{font-size:17px;margin-top:30px;border-bottom:1px solid #30363d;padding-bottom:4px}
table{border-collapse:collapse;width:100%;font-size:14px}th,td{border-bottom:1px solid #21262d;padding:7px 8px;vertical-align:top;text-align:left}
th{color:#8b949e;font-weight:500;font-size:12px}td.m{font-size:16px;white-space:nowrap}code{font-size:12.5px;color:#a5d6ff}
.st{font-size:11.5px;padding:2px 7px;border-radius:10px;white-space:nowrap}.ok{background:#12361f;color:#7ee2a8}.nodef{background:#2d2a12;color:#e3c55a}.no{background:#262c36;color:#9aa4b2}.dec{background:#3d1d1d;color:#ff9b8f}.done{background:#12361f;color:#7ee2a8}.decided{background:#1d2b3d;color:#8cc4ff}
tr.decrow td{background:#1a1416}.note{color:#c9d1d9;font-size:13px}.legend span{margin-right:14px}
.filter{margin:10px 0}
.pick label{display:block;font-size:13px;margin:2px 0;cursor:pointer}.pick input{margin-right:6px}
textarea.cm{width:100%;min-height:28px;background:#0d1117;color:#e6edf3;border:1px solid #30363d;border-radius:5px;font:13px -apple-system,"Hiragino Sans",sans-serif;padding:4px 6px;margin-top:4px;resize:vertical}
textarea.cm:focus{outline:none;border-color:#58a6ff}
.bar{position:sticky;top:0;background:#0d1117;padding:8px 0;z-index:2;display:flex;gap:10px;align-items:center;border-bottom:1px solid #21262d}
.bar button{background:#21262d;color:#e6edf3;border:1px solid #30363d;border-radius:6px;padding:5px 12px;font-size:13px;cursor:pointer}.bar button:hover{border-color:#58a6ff}
.bar .msg{font-size:12px;color:#7ee2a8}.prog{font-size:12px;color:#8b949e}.filter label{margin-right:14px;font-size:13px;color:#8b949e}
</style></head><body>
<h1>記法 B（大学以上で広く共通）の候補</h1>
<p>__SUMMARY__</p>
<p class="note">方針：B の中でも 1 対 1 にする（同じ見た目に 2 つの意味を持たせない）。型で読み方を変えない（例外：数列の $a_n$）。<b>推奨</b>は案で、決めるのはあなたです。</p>
<div class="legend"><span class="st done">v2.11 で実装</span><span class="st decided">決定（未実装）</span><span class="st ok">済</span><span class="st nodef">書けるが定義なし</span><span class="st no">未対応</span><span class="st dec">決めること</span></div>
<div class="bar"><label class="prog"><input type="checkbox" id="onlydec"> 決めることだけ表示</label><span class="prog" id="prog"></span><span style="flex:1"></span><button id="copy">Markdown でコピー</button><button id="save">ファイルに書き出す</button><span class="msg" id="msg"></span></div>
<div id="out"></div>
<script>
const DATA = __DATA__;
const LAB = __LAB__;
const KEY = "narfi.notationB.notes";
let notes = {};
try { notes = JSON.parse(localStorage.getItem(KEY) || "{}"); } catch (e) {}
function persist(){ localStorage.setItem(KEY, JSON.stringify(notes)); progress(); }
function mathify(s){return s.replace(/\$([^$]+)\$/g,(_,m)=>{try{return katex.renderToString(m,{throwOnError:false})}catch(e){return m}})}
function esc(s){return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/"/g,'&quot;')}
function progress(){
 const dec=DATA.flatMap(g=>g.rows).filter(r=>r.st==='dec');
 const done=dec.filter(r=>notes[r.id]&&notes[r.id].pick!=null).length;
 const cm=Object.values(notes).filter(n=>n.comment&&n.comment.trim()).length;
 document.getElementById('prog').textContent=`決めること ${done}/${dec.length} 件を選択済み・コメント ${cm} 件`;
}
function render(){
 const only=document.getElementById('onlydec').checked;let h='';
 for(const g of DATA){const rows=g.rows.filter(r=>!only||r.st==='dec');if(!rows.length)continue;
  h+=`<h2>${g.t}</h2><table><tr><th style="width:20%">記法</th><th style="width:12%">意味</th><th style="width:14%">Narfi のファイル</th><th style="width:8%">状態</th><th style="width:22%">判断・メモ</th><th>あなたの選択・コメント</th></tr>`;
  for(const r of rows){
   const n=notes[r.id]||{};
   let pick='';
   if(r.opts.length){pick='<div class="pick">'+[...r.opts,'保留','その他（コメントに）'].map((o,k)=>`<label><input type="radio" name="${esc(r.id)}" data-id="${esc(r.id)}" value="${k}" ${n.pick===k?'checked':''}>${mathify(o)}</label>`).join('')+'</div>'}
   h+=`<tr class="${r.st==='dec'?'decrow':''}"><td class="m">${katex.renderToString(r.m,{throwOnError:false})}</td><td>${mathify(r.mean)}</td><td>${r.file?'<code>'+esc(r.file)+'</code>':''}</td><td><span class="st ${r.st}">${LAB[r.st][0]}</span></td><td class="note">${mathify(r.note)}</td><td>${pick}<textarea class="cm" data-id="${esc(r.id)}" placeholder="コメント">${esc(n.comment||'')}</textarea></td></tr>`}
  h+='</table>'}
 document.getElementById('out').innerHTML=h;
 document.querySelectorAll('p.note').forEach(p=>{if(!p.dataset.done){p.innerHTML=mathify(p.innerHTML);p.dataset.done=1}});
 progress();
}
document.addEventListener('change',e=>{
 const t=e.target;
 if(t.type==='radio'&&t.dataset.id){(notes[t.dataset.id]||(notes[t.dataset.id]={})).pick=+t.value;persist();}
});
document.addEventListener('input',e=>{
 const t=e.target;
 if(t.classList&&t.classList.contains('cm')){(notes[t.dataset.id]||(notes[t.dataset.id]={})).comment=t.value;persist();}
});
function exportMd(){
 let out='# 記法 B：選択とコメント\n\n';
 for(const g of DATA){
  const rows=g.rows.filter(r=>{const n=notes[r.id];return n&&(n.pick!=null||(n.comment&&n.comment.trim()))});
  if(!rows.length)continue;
  out+=`## ${g.t}\n\n`;
  for(const r of rows){const n=notes[r.id];const all=[...r.opts,'保留','その他（コメントに）'];
   out+=`- \`${r.m}\`（${r.mean.replace(/\$/g,'')}）\n`;
   if(n.pick!=null)out+=`  - 選択：${all[n.pick].replace(/\$/g,'')}${n.pick===0&&r.opts.length?'':''}\n`;
   if(n.comment&&n.comment.trim())out+=`  - コメント：${n.comment.trim().replace(/\n/g,'\n    ')}\n`;}
  out+='\n'}
 return out;
}
function flash(m){const el=document.getElementById('msg');el.textContent=m;setTimeout(()=>el.textContent='',2500)}
document.getElementById('copy').onclick=()=>{navigator.clipboard.writeText(exportMd()).then(()=>flash('コピーしました'),()=>flash('コピーできませんでした'))};
document.getElementById('save').onclick=()=>{
 const blob=new Blob([exportMd()],{type:'text/markdown'});
 const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download='notation-B-notes.md';a.click();
 flash('ダウンロードに notation-B-notes.md を書き出しました');
};
document.getElementById('onlydec').addEventListener('change',render);render();
</script></body></html>"""
page = page.replace("__DATA__", json.dumps(data, ensure_ascii=False)).replace("__LAB__", json.dumps(lab, ensure_ascii=False))
page = page.replace("__SUMMARY__", f"全 {n_all} 項目。決定 <b>{n_done}</b> 件、残りの決めること <b>{n_dec}</b> 件。決まりの本文は docs/language/notation.md。")
open("/Users/nabito/data/osk/Narfi/docs/proposals/notation-B.html","w").write(page)
print(n_all, n_dec)
