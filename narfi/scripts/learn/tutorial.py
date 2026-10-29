# Learn タブのチュートリアル（src/tutorial.js）を作る。使い方：python3 scripts/learn/tutorial.py
# レッスンを直すときはこのファイルを直して作り直す（src/tutorial.js は直接直さない）。例と答えが通ることは tests/ui.rs で確かめる。
import json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))

def thm_src(stmt, proof):
    return stmt.rstrip() + "\n\n" + proof.strip("\n") + "\n"

def exercise(num, title, pre, stmts):
    head = f"-- 練習 {num}：{title}\n-- sorry を消して証明を書く。Goal タブに、使える仮定と示すべきものが出る。\n\n"
    body = "\n\n".join(st.rstrip() + "\n\nsorry" for st in stmts)
    return head + (pre.strip() + "\n\n" if pre else "") + body + "\n"

def answer(pre, parts):
    body = "\n\n".join(thm_src(st, pf).rstrip() for st, pf in parts)
    return (pre.strip() + "\n\n" if pre else "") + body + "\n"

L = []
def lesson(num, title, slug, blocks, task=None, hints=None, pre="", stmt=None, proof=None, ex_title=None, parts=None, uses=None):
    d = {"title": f"{num}. {title}", "blocks": blocks}
    if parts is None and stmt:
        parts = [(stmt, proof)]
    if parts:
        d["file"] = f"learn/{num:02d}-{slug}.narfi"
        d["task"] = task
        d["hints"] = hints
        d["exercise"] = exercise(num, ex_title or title, pre, [st for st, _ in parts])
        d["answer"] = answer(pre, parts)
        d["uses"] = uses or []
    L.append(d)

# ---------------------------------------------------------------- 1
lesson(1, "はじめての証明", "はじめての証明", [
  {"p": "**ねらい**：定理を書いて、正しいかどうかを検査器に確かめてもらう。Narfi では、書いた証明の一歩一歩を検査器が確かめ、通れば右上が緑（verified）になる。"},
  {"paper": ["**定理**　実数 $x$ が $x > 1$ を満たすとき、$2x > 2$ である。", "**証明**　$x > 1$ の両辺を 2 倍すればよい。$\\blacksquare$"]},
  {"p": "Narfi では、同じことをこう書く。"},
  {"code": "thm double_gt :\n  x : Real, h : x > 1\n  |- 2x > 2\n\nlinarith"},
  {"steps": [
    ["thm double_gt :", "「定理を書く。名前は double_gt」。名前は自分で決める（英字・数字・`_`・`.`）"],
    ["x : Real, h : x > 1", "**仮定**。$x$ は実数（`Real`）。$x > 1$ が成り立ち、その事実に $h$ という名前を付ける。名前を付けるのは、あとで「$h$ より」と使うため"],
    ["|- 2x > 2", "`|-`（⊢）の右が**示したいこと**（結論）"],
    ["linarith", "**証明**。空行のあとに書く。`linarith` は「仮定の一次の不等式を足したり定数倍したりすれば分かる」という根拠。検査器がその計算を実際に確かめる"]]},
  {"p": "仮定と結論をまとめた形 `仮定 ⊢ 結論` は、「仮定がすべて成り立つとき、結論が成り立つ」と読む。"},
  {"type": [["Real", "ℝ（実数）。`Nat` は ℕ（0, 1, 2, …）"], ["\\|-", "⊢（仮定と結論の区切り）"], [">=  <=  !=", "≥　≤　≠（打つと自動で変わる）"], ["2x", "2·x（数と文字の積は、間に何も書かなくてよい）"]]},
  {"check": "「練習のファイルを開く」を押すと、自分のファイルに `learn/01-…` ができて開く。証明の所が `sorry`（まだ書いていない、の印）で、右上は **incomplete**（黄色）。`sorry` の行にカーソルを置くと、右の **Goal** タブに使える仮定と示すべきもの（⊢ の右）が出る。`sorry` を正しい証明に書き換えると緑になる。"},
  {"pitfalls": [["「linarith では … を示せない」", "一次の不等式の計算では出ない。仮定が足りないか、使い方を変える必要がある（このあとのレッスンで、根拠の書き方を増やしていく）"]]},
], task="実数 $a < b$ のとき、$a < \\dfrac{a+b}{2}$（$a$ と $b$ の真ん中は $a$ より大きい）を示す。",
 hints=["Goal タブで、仮定 $h : a < b$ と、示すべき $a < (a+b)/2$ を確かめる。", "両辺を 2 倍すると $2a < a + b$、つまり $a < b$。一次の不等式の計算なので `linarith` で通る。"],
 stmt="thm mid_left :\n  a : Real, b : Real, h : a < b\n  |- a < (a + b)/2", proof="linarith", uses=["linarith"], ex_title="真ん中は左端より大きい")

# ---------------------------------------------------------------- 2
lesson(2, "式変形をつなげる", "式変形", [
  {"p": "**ねらい**：紙と同じように、式を縦に並べて変形する（**連鎖**）。各行の右に、その変形の**根拠**を `by` の後ろに書く。"},
  {"paper": ["$a \\le b$ のとき　$a + 1 \\le b + 1 \\le b + 2$"]},
  {"code": "thm chain :\n  a : Real, b : Real, h : a <= b\n  |- a + 1 <= b + 2\n\na + 1\n  <= b + 1   by linarith\n  <= b + 2   by linarith"},
  {"steps": [["a + 1", "変形を始める式"], ["<= b + 1   by linarith", "1 段目。字下げして、関係（`=`・`<=`・`<` など）から書く"], ["<= b + 2   by linarith", "2 段目。最後まで来ると、全体として $a + 1 \\le b + 2$ が示されたことになる"]]},
  {"h": "根拠の種類"},
  {"p": "`by` の後ろに書けるもの：`ring`（多項式の計算で等しい）、`linarith`（一次の不等式の計算）、**仮定の名前**。"},
  {"p": "**等式の仮定を根拠に書くと、その等式で書き換える**。たとえば $h : a = b + 2$ のとき、`by h` は「$a$ を $b + 2$ に置き換えた」という意味になる。"},
  {"code": "thm sub_two :\n  a : Real, b : Real, h : a = b + 2\n  |- a - b = 2\n\na - b\n  = (b + 2) - b   by h\n  = 2             by ring"},
  {"steps": [["= (b + 2) - b   by h", "$h$ で $a$ を $b + 2$ に書き換えた"], ["= 2             by ring", "あとは文字式の計算（展開・整理）。`ring` が確かめる"]]},
  {"p": "**根拠がわからないとき**は、`by …` を書かずに `= 2` とだけ書いてみる。エラーになり、検査器が見つけた根拠の候補が行末に薄く出る。**Tab** で入る。"},
  {"type": [["<=", "≤"], ["x^2", "$x^2$（`^` で上付きの欄ができる）"], ["by", "根拠を書く前の区切り"]]},
  {"pitfalls": [["「ring では … を示せない」", "左右が文字式として等しくない。書き換えが足りない（先に `by h` の段を入れる）か、変形を写し間違えている"], ["`2ab` が通らない", "`ab` は「ab という 1 つの名前」と読まれる。文字どうしの積は `a*b`（表示は $a \\cdot b$）、`2*a*b` と書く"]]},
], task="$x = y + 1$ のとき、$x^2 = y^2 + 2y + 1$ を、連鎖で示す。",
 hints=["$x^2$ から始める。1 段目で $x$ を $y + 1$ に書き換える：`= (y + 1)^2   by h`。", "2 段目は展開：`= y^2 + 2y + 1   by ring`。"],
 stmt="thm square_shift :\n  x : Real, y : Real, h : x = y + 1\n  |- x^2 = y^2 + 2y + 1",
 proof="x^2\n  = (y + 1)^2       by h\n  = y^2 + 2y + 1    by ring", uses=["by h", "by ring"], ex_title="書き換えてから展開する")

# ---------------------------------------------------------------- 3
lesson(3, "途中の事実と、定理を使う", "定理を使う", [
  {"p": "**ねらい**：証明の途中で分かったことを書き留める（**事実の行**）。前に示した定理（や認めた事実）を名前で呼んで使う。"},
  {"p": "**事実の行** `名前 : 命題 by 根拠` は「根拠より、命題が成り立つ。これを 名前 と呼ぶ」。書き留めた事実は、それより下の行で使える。"},
  {"code": "axiom sq_nonneg : x : Real |- x^2 >= 0\n\nthm sq_plus_one :\n  t : Real\n  |- t^2 + 1 > 0\n\nh : t^2 >= 0 by sq_nonneg\nlinarith"},
  {"steps": [["axiom sq_nonneg : x : Real |- x^2 >= 0", "**公理**：証明しないで認める事実（「2 乗は 0 以上」）。`thm` と同じ形で書き、証明は付けない"], ["h : t^2 >= 0 by sq_nonneg", "sq_nonneg を使って「$t^2 \\ge 0$」を書き留める。$x$ に何を入れるか（ここでは $t$）は、書いた命題から検査器が読み取る"], ["linarith", "$h$ を使って $t^2 + 1 > 0$"]]},
  {"p": "自分で書いた `thm` も同じように名前で使える。`linarith` は $t^2$ のような式も 1 つのかたまりとして扱えるので、事実の行で書き留めておけば計算に使える。"},
  {"type": [["axiom 名前 : 仮定 |- 結論", "証明なしで認める事実（練習のため。ライブラリの数学では、なるべく定理として示す）"], ["h : φ by 根拠", "事実の行：φ を書き留めて h と呼ぶ"]]},
  {"pitfalls": [["「引数が多すぎる」", "`sq_nonneg(t)` のように変数を渡す必要はない（仮定の並びの変数は、命題から読み取られる）。`by sq_nonneg` と書く"]]},
], task="すべての実数 $a, b$ で $a^2 + b^2 \\ge 2ab$ を示す（相加・相乗平均の不等式のもと）。",
 hints=["$(a - b)^2 \\ge 0$ を使う。", "`h : (a - b)^2 >= 0 by sq_nonneg` と書き留める。", "$(a-b)^2 = a^2 - 2ab + b^2$ なので、あとは `linarith`（展開は linarith がする）。"],
 pre="axiom sq_nonneg : x : Real |- x^2 >= 0",
 stmt="thm am_gm2 :\n  a : Real, b : Real\n  |- a^2 + b^2 >= 2*a*b",
 proof="h : (a - b)^2 >= 0 by sq_nonneg\nlinarith", uses=["by sq_nonneg"], ex_title="a² + b² ≥ 2ab")

# ---------------------------------------------------------------- 4
lesson(4, "「ならば」を示す・使う", "ならば", [
  {"p": "**ねらい**：「$P$ ならば $Q$」（$P \\Rightarrow Q$）を**示す**には、$P$ を仮定して $Q$ を示す。仮定 $f : P \\Rightarrow Q$ を**使う**には、$P$ の根拠 $p$ を渡して `f(p)` と書く（すると $Q$）。"},
  {"paper": ["**定理**　$x > 2$ ならば $x > 1$。", "**証明**　$x > 2$ と仮定する。すると $x > 1$。$\\blacksquare$"]},
  {"code": "thm gt_two :\n  x : Real\n  |- x > 2 => x > 1\n\nassume h : x > 2\n  linarith"},
  {"steps": [["assume h : x > 2", "「$x > 2$ と仮定する」。仮定の名前を $h$ にする。中身 `: x > 2` は省略できない"], ["  linarith", "**字下げした所**では $h$ が使える。示すべきものは $x > 1$ に変わっている"]]},
  {"p": "**字下げ**が「仮定が使える範囲」。`assume` の下は 1 段（スペース 2 つ）下げる。"},
  {"code": "thm syllogism :\n  P : Prop, Q : Prop, f : P => Q, p : P\n  |- Q\n\nf(p)"},
  {"steps": [["f(p)", "$f$（$P$ ならば $Q$）に $P$ の根拠 $p$ を渡すと、$Q$ の根拠になる（三段論法）"]]},
  {"type": [["=>", "⇒（ならば）"], ["Prop", "命題（正しいか正しくないかが決まる文）"]]},
  {"pitfalls": [["「仮定 h の中身が書かれていない」", "`assume h` だけでなく `: x > 2` まで書く（行末で Tab を押すと入る）"]]},
], task="実数 $a, b$ について「$a > 0$ ならば $b > 0$」が成り立つとする。このとき「$a > 1$ ならば $a + b > 1$」を示す。",
 hints=["示すのは「ならば」なので、`assume h : a > 1` から始める。", "$f$ を使うには $a > 0$ の根拠が要る。`ha : a > 0 by linarith` と書き留める。", "`hb : b > 0 by f(ha)`。あとは `linarith`。"],
 stmt="thm imp_use :\n  a : Real, b : Real, f : a > 0 => b > 0\n  |- a > 1 => a + b > 1",
 proof="assume h : a > 1\n  ha : a > 0 by linarith\n  hb : b > 0 by f(ha)\n  linarith", uses=["assume", "f(ha)"], ex_title="ならばを使う")

# ---------------------------------------------------------------- 5
lesson(5, "「かつ」", "かつ", [
  {"p": "**ねらい**：「$P$ かつ $Q$」（$P \\land Q$）の仮定 $h$ からは、`h.left` で $P$、`h.right` で $Q$ が取り出せる。$P \\land Q$ を**示す**には、2 つの根拠を `,` で並べる（`p, q`）。"},
  {"paper": ["**定理**　$x > 0$ かつ $y > 0$ ならば $x + y > 0$。", "**証明**　$x > 0$ と $y > 0$ を足せばよい。$\\blacksquare$"]},
  {"code": "thm pos_add :\n  x : Real, y : Real\n  |- x > 0 and y > 0 => x + y > 0\n\nassume h : x > 0 and y > 0\n  hx : x > 0 by h.left\n  hy : y > 0 by h.right\n  linarith"},
  {"steps": [["hx : x > 0 by h.left", "$h$ の左側を取り出して $hx$ と呼ぶ"], ["hy : y > 0 by h.right", "右側も同じ"], ["linarith", "$hx$ と $hy$ を足して $x + y > 0$（`linarith` は「かつ」の仮定の中も見るので、取り出さなくても通る）"]]},
  {"p": "**示す**側の例：$a \\le b$ と $b \\le a$ をまとめた $a \\le b \\land b \\le a$ を示すなら、2 つの根拠を並べて `h1, h2`。それぞれの根拠が `linarith` なら `linarith, linarith` と書ける。"},
  {"type": [["and", "∧（かつ）"], ["h.left / h.right", "∧ の左側・右側を取り出す"], ["p, q", "$P$ の根拠 p と $Q$ の根拠 q で、$P \\land Q$ の根拠"]]},
], task="(1) 「$P$ かつ（$P$ ならば $Q$）」から $Q$ を示す（かつを**使う**）。(2) $a < b$ ならば「$a < \\dfrac{a+b}{2}$ かつ $\\dfrac{a+b}{2} < b$」を示す（かつを**作る**）。",
 hints=["(1) `h.left` が $P$、`h.right` が「$P$ ならば $Q$」。", "(1) 「ならば」に $P$ の根拠を渡すと $Q$：`h.right(h.left)`。", "(2) `assume h : a < b` のあと、左右それぞれ一次の不等式なので `linarith, linarith`。"],
 parts=[("thm and_use :\n  P : Prop, Q : Prop, h : P and (P => Q)\n  |- Q", "h.right(h.left)"),
        ("thm midpoint :\n  a : Real, b : Real\n  |- a < b => a < (a + b)/2 and (a + b)/2 < b", "assume h : a < b\n  linarith, linarith")],
 uses=["h.left", "h.right", "linarith, linarith"], ex_title="かつを使う・作る")

# ---------------------------------------------------------------- 6
lesson(6, "「または」", "または", [
  {"p": "**ねらい**：「$P$ または $Q$」（$P \\lor Q$）を**示す**には、どちらを示すかを選ぶ：`left`（左の $P$ を示す）か `right`（右の $Q$ を示す）。$P \\lor Q$ の仮定を**使う**には、場合分けする（`cases`）。"},
  {"paper": ["**定理**　$P$ または $Q$ ならば、$Q$ または $P$。", "**証明**　$P$ の場合は右側、$Q$ の場合は左側を示せばよい。$\\blacksquare$"]},
  {"code": "thm or_swap :\n  P : Prop, Q : Prop, h : P or Q\n  |- Q or P\n\ncases h\n  Case left hp\n    right\n    hp\n  Case right hq\n    left\n    hq"},
  {"steps": [["cases h", "$h$（$P$ または $Q$）で場合分けする"], ["Case left hp", "$P$ の場合。分かっていること（$P$）に $hp$ と名前を付ける。この下に、その場合の証明を字下げして書く"], ["right", "示したい $Q \\lor P$ のうち、右（$P$）を示すと決める。この行は `right` だけ"], ["hp", "$P$ は $hp$ そのもの"]]},
  {"p": "場合分けでは、**それぞれの場合で**結論を示す。`left`・`right` は字下げしない（次の行から、選んだ側を示す）。"},
  {"type": [["or", "∨（または）"], ["cases h", "場合分け。下に `Case left …` と `Case right …` を同じ字下げで"], ["left / right", "∨ の左（右）を示すと決める"]]},
], task="(1) $x > 2$ または $x < -2$ ならば、$x > 1$ または $x < -1$（場合分けで**使い**、`left`/`right` で**作る**）。(2) $x = 1$ または $x = 2$ のとき $x^2 - 3x + 2 = 0$。",
 hints=["(1) `cases h` で 2 つの場合に分ける。", "(1) $x > 2$ の場合は `left`（示すのは $x > 1$）のあと `linarith`。$x < -2$ の場合は `right`。", "(2) 場合ごとに連鎖：`= 1^2 - 3*1 + 2   by h1`、`= 0   by ring`。"],
 parts=[("thm widen :\n  x : Real, h : x > 2 or x < -2\n  |- x > 1 or x < -1", "cases h\n  Case left h1\n    left\n    linarith\n  Case right h2\n    right\n    linarith"),
        ("thm roots :\n  x : Real, h : x = 1 or x = 2\n  |- x^2 - 3x + 2 = 0", "cases h\n  Case left h1\n    x^2 - 3x + 2\n      = 1^2 - 3*1 + 2   by h1\n      = 0               by ring\n  Case right h2\n    x^2 - 3x + 2\n      = 2^2 - 3*2 + 2   by h2\n      = 0               by ring")],
 uses=["cases h", "Case left", "    left\n", "    right\n"], ex_title="または を使う・作る")

# ---------------------------------------------------------------- 7
lesson(7, "「すべての」", "すべての", [
  {"p": "**ねらい**：「すべての $x$ について …」（$\\forall x$）を**示す**には、$x$ を 1 つ任意にとって（`Fix x`）、その $x$ で示す。仮定の $\\forall$ を**使う**には、具体的な値を入れる（`h(2)` のように）。"},
  {"paper": ["**定理**　すべての実数 $x$ について $x + 1 > x$。", "**証明**　$x$ を任意にとる。$x + 1 > x$ である。$\\blacksquare$"]},
  {"code": "thm add_one :\n  |- forall x:Real. x + 1 > x\n\nFix x\n  linarith"},
  {"steps": [["Fix x", "「$x$ を任意にとって固定する」。字下げした所では、示すべきものが $x + 1 > x$ になる"], ["  linarith", "その $x$ について示す"]]},
  {"p": "**使う**例：仮定 $h : \\forall x.\\ f(x) \\ge 0$ があれば、`h(2)` が「$f(2) \\ge 0$」の根拠。「すべての $x, y$ について、$x \\le y$ ならば …」のような仮定には、値と根拠を順に渡す：`h(1, 2, k)`（$k$ は $1 \\le 2$ の根拠）。"},
  {"code": "thm f_two :\n  f : Real -> Real, h : forall x:Real. f(x) >= 0\n  |- f(2) + 1 > 0\n\nk : f(2) >= 0 by h(2)\nlinarith"},
  {"type": [["forall x:Real.", "∀x ∈ ℝ,（すべての実数 x について）"], ["Fix x, y", "2 つまとめて任意にとる"], ["f : Real -> Real", "関数 $f : \\mathbb{R} \\to \\mathbb{R}$。`->` は関数の型の矢印"]]},
], task="$f$ が単調増加（$x \\le y$ ならば $f(x) \\le f(y)$）のとき、$g(x) = f(x) + 1$ も単調増加であることを示す。",
 hints=["示すのは「すべての $x, y$ について、$x \\le y$ ならば …」。`Fix x, y` のあと `assume hxy : x <= y`。", "$h$ に $x, y, hxy$ を渡す：`k : f(x) <= f(y) by h(x, y, hxy)`。", "あとは `linarith`。"],
 stmt="thm mono_shift :\n  f : Real -> Real, h : forall x:Real. forall y:Real. x <= y => f(x) <= f(y)\n  |- forall x:Real. forall y:Real. x <= y => f(x) + 1 <= f(y) + 1",
 proof="Fix x, y\n  assume hxy : x <= y\n    k : f(x) <= f(y) by h(x, y, hxy)\n    linarith", uses=["Fix x, y", "h(x, y, hxy)"], ex_title="単調増加")

# ---------------------------------------------------------------- 8
lesson(8, "「ある」", "ある", [
  {"p": "**ねらい**：「… となる $x$ がある」（$\\exists x$）を**示す**には、例を 1 つ挙げる（`choose 2` のように）。仮定の「ある」を**使う**には、その $x$ を取り出して名前を付ける（`Obtain`）。"},
  {"paper": ["**定理**　$x + 3 = 5$ となる実数 $x$ がある。", "**証明**　$x = 2$ とすればよい。$\\blacksquare$"]},
  {"code": "thm solve :\n  |- exists x:Real. x + 3 = 5\n\nchoose 2\nring"},
  {"steps": [["choose 2", "例として $x = 2$ を挙げる。示すべきものは $2 + 3 = 5$ になる。字下げはしない"], ["ring", "計算で確かめる"]]},
  {"p": "**使う**例：仮定 $h$ が「$a > 5$ となる $a$ がある」なら、`Obtain a | ha by h` で、その $a$ と性質 $ha : a > 5$ が手に入る（「$h$ より、$ha$ を満たす $a$ をとる」と読む）。`|` の左が取り出すもの、右がその性質の名前、`by` の右が根拠。"},
  {"code": "thm exists_gt :\n  h : exists x:Real. x > 5\n  |- exists y:Real. y > 4\n\nObtain a | ha by h\nchoose a\nlinarith"},
  {"type": [["exists x:Real.", "∃x ∈ ℝ,（ある実数 x が存在して）"], ["choose t", "例として t を挙げる"], ["Obtain a | ha by h", "h から a と、a の性質 ha を取り出す"]]},
  {"pitfalls": [["`Obtain a, ha : h` と書いた", "古い書き方。`:` の右は命題、根拠は `by` の右に書く：`Obtain a | ha by h`（File → Update Old Syntax で直る）"]]},
], task="自然数 $n$ が偶数（$n = 2k$ となる $k$ がある）のとき、$n + 2$ も偶数であることを示す。",
 hints=["$h$ から $k$ を取り出す：`Obtain k | hk by h`（$hk : n = 2k$）。", "$n + 2 = 2(k + 1)$ なので、例として `choose k + 1`。", "残りは $n + 2 = 2(k+1)$。連鎖で `= 2k + 2   by hk`、`= 2(k + 1)   by ring`。"],
 stmt="thm even_add_two :\n  n : Nat, h : exists k:Nat. n = 2k\n  |- exists m:Nat. n + 2 = 2m",
 proof="Obtain k | hk by h\nchoose k + 1\nn + 2\n  = 2k + 2        by hk\n  = 2(k + 1)      by ring", uses=["Obtain k | hk by h", "choose"], ex_title="偶数に 2 を足しても偶数")

# ---------------------------------------------------------------- 9
lesson(9, "「でない」と背理法", "でない", [
  {"p": "**ねらい**：「$P$ でない」（$\\lnot P$）は Narfi の中では「$P$ ならば矛盾」（$P \\Rightarrow \\bot$）。だから**示す**には $P$ を仮定して矛盾を示し、**使う**には $P$ の根拠を渡す（`hn(p)` で矛盾）。"},
  {"paper": ["**定理**　$x > 1$ かつ $x < 0$、ということはない。", "**証明**　そう仮定すると $1 < x < 0$ で矛盾。$\\blacksquare$"]},
  {"code": "thm not_both :\n  x : Real\n  |- not (x > 1 and x < 0)\n\nassume h : x > 1 and x < 0\n  linarith"},
  {"steps": [["assume h : x > 1 and x < 0", "否定を示すので、中身を仮定する。示すべきものは矛盾（⊥）になる"], ["  linarith", "**矛盾も `linarith` で示せる**（仮定の不等式から $0 < 0$ が出ることを確かめる）"]]},
  {"p": "**背理法**：結論 $P$ そのものを示すのに「$P$ でない」と仮定して矛盾を導くこともできる。`by_contra hn` と書く。"},
  {"code": "thm dne :\n  P : Prop, h : not not P\n  |- P\n\nby_contra hn\n  h(hn)"},
  {"steps": [["by_contra hn", "「$P$ でない」と仮定し、$hn$ と呼ぶ。示すべきものは矛盾"], ["  h(hn)", "$h$ は「$\\lnot P$ ならば矛盾」。$hn$ を渡すと矛盾"]]},
  {"type": [["not", "¬（でない）"], ["false", "⊥（矛盾）"], ["by_contra hn", "背理法：結論の否定を hn として仮定する"]]},
], task="(1) 「$Q$ ならば $P$」と「$P$ でない」から「$Q$ でない」を示す（対偶。でないを**使い**、**作る**）。(2) 実数 $x$ が「すべての $\\varepsilon > 0$ について $x < \\varepsilon$」を満たすなら、$x > 0$ ではない。(3) 「$P$ でないなら $Q$」と「$Q$ でない」から $P$ を示す（背理法）。",
 hints=["(1) 示すのは「$Q$ でない」。`assume q : Q`（示すべきものは矛盾）。", "(1) $f(q)$ が $P$。$h$（$P$ でない）に渡すと矛盾：`h(f(q))`。", "(2) `assume hx : x > 0` のあと、$h$ に $\\varepsilon = x$ を入れる：`k : x < x by h(x, hx)`。$x < x$ は矛盾なので `linarith`。", "(3) `by_contra hn` で「$P$ でない」を仮定。$f(hn)$ が $Q$ なので、$g$ に渡して矛盾：`g(f(hn))`。"],
 parts=[("thm contra :\n  P : Prop, Q : Prop, f : Q => P, h : not P\n  |- not Q", "assume q : Q\n  h(f(q))"),
        ("thm small :\n  x : Real, h : forall eps:Real>0. x < eps\n  |- not (x > 0)", "assume hx : x > 0\n  k : x < x by h(x, hx)\n  linarith"),
        ("thm by_contra_use :\n  P : Prop, Q : Prop, f : not P => Q, g : not Q\n  |- P", "by_contra hn\n  g(f(hn))")],
 uses=["assume q : Q", "h(f(q))", "h(x, hx)", "by_contra hn"], ex_title="でないを使う・作る・背理法")

# ---------------------------------------------------------------- 10
lesson(10, "ε を任意にとる（大学の入口）", "ε", [
  {"p": "**ねらい**：大学の解析で最もよく出る形「任意の $\\varepsilon > 0$ に対して …」を書く。$\\forall \\varepsilon > 0$ は「$\\varepsilon$ を任意にとり、$\\varepsilon > 0$ と仮定する」の 2 つをまとめたもの。$\\exists \\delta > 0$ は「$\\delta$ を挙げ、$\\delta > 0$ も示す」。"},
  {"paper": ["**定理**　任意の $\\varepsilon > 0$ に対し、$\\delta < \\varepsilon$ となる $\\delta > 0$ がある。", "**証明**　$\\varepsilon > 0$ を任意にとる。$\\delta = \\varepsilon/2$ とすればよい。$\\blacksquare$"]},
  {"code": "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith"},
  {"steps": [["Fix eps | h_{eps} : eps > 0", "$\\varepsilon$ を任意にとり、$\\varepsilon > 0$ という仮定に $h_\\varepsilon$ と名前を付ける。`|` は「〜であって」"], ["choose eps/2, linarith", "$\\delta$ として $\\varepsilon/2$ を挙げる。`,` の後ろは「$\\varepsilon/2 > 0$」の根拠"], ["linarith", "残りの $\\varepsilon/2 < \\varepsilon$"]]},
  {"type": [["eps", "ε（空白で変わる）。`delta` は δ"], ["h_{eps}", "添字つきの名前 $h_\\varepsilon$"], ["/", "分数（直前の項が分子になる）"], ["forall eps:Real>0.", "∀ε > 0,"]]},
], task="(1) 任意の $\\varepsilon > 0$ に対し、$\\delta + \\delta < \\varepsilon$ となる $\\delta > 0$ がある（$\\forall \\varepsilon > 0$ を**作る**）。(2) 「すべての $\\varepsilon > 0$ で $x \\le \\varepsilon$」ならば $x \\le 1/2$（$\\forall \\varepsilon > 0$ を**使う**）。",
 hints=["(1) `Fix eps | h_{eps} : eps > 0` から。$\\delta = \\varepsilon/2$ だとぎりぎり足りない。$\\varepsilon/3$ にする：`choose eps/3, linarith` のあと `linarith`。", "(2) $h$ に $\\varepsilon = 1/2$ を入れる。そのためには「$1/2 > 0$」の根拠が要る：`k : 1/2 > 0 by decide`。", "(2) あとは `h(1/2, k)` で閉じる。"],
 parts=[("thm third :\n  |- forall eps:Real>0. exists d:Real>0. d + d < eps", "Fix eps | h_{eps} : eps > 0\n  choose eps/3, linarith\n  linarith"),
        ("thm below_half :\n  x : Real, h : forall eps:Real>0. x <= eps\n  |- x <= 1/2", "k : 1/2 > 0 by decide\nh(1/2, k)")],
 uses=["Fix eps |", "choose eps/3", "h(1/2, k)"], ex_title="ε を作る・使う")

# ---------------------------------------------------------------- 11
lesson(11, "定義を書く・使う", "定義", [
  {"p": "**ねらい**：自分で言葉を定義する（`def`）。「偶数」「有界」のような性質は `def 名前(引数) :⇔ 命題` と書く（`:⇔` は「〜のことと定める」）。定義した言葉は、証明の中で**必要に応じて自動で開かれる**（中身の命題として扱われる）。"},
  {"code": "def even(n : Nat) :<=> exists k:Nat. n = 2k\n\nthm even_add :\n  m : Nat, n : Nat, hm : even(m), hn : even(n)\n  |- even(m + n)\n\nObtain a | ha by hm\nObtain b | hb by hn\nchoose a + b\nm + n\n  = 2a + 2b       by ha, hb\n  = 2(a + b)      by ring"},
  {"steps": [["def even(n : Nat) :<=> exists k:Nat. n = 2k", "「$n$ が偶数」を「$n = 2k$ となる $k$ がある」と定める"], ["Obtain a | ha by hm", "$hm$ は even(m)。定義を開くと「ある」なので、`Obtain` で $a$ と $ha : m = 2a$ を取り出せる"], ["choose a + b", "示す even(m + n) も、開くと「ある」。例として $a + b$"], ["= 2a + 2b       by ha, hb", "根拠を `,` で並べると、両方の等式で書き換える"]]},
  {"p": "**値の定義**は `def f(x : Real) : Real := 式`（`:=` は「〜と定める」。値を返すもの）。性質の定義は `:⇔`、値の定義は `:=` と使い分ける。"},
  {"p": "**記法**：定義の下に字下げして `notation 型紙` と書くと、教科書の書き方で使える（例：`notation a_n -> alpha (n -> \\infty)`。レッスン 13）。"},
  {"type": [[":<=>", ":⇔（性質を定める）"], [":=", "値を定める"], ["(n:Nat |-> a_n + 1)", "「$n$ を $a_n + 1$ に移す数列」そのもの。`|->` は ↦"]]},
], task="数列 $a$ が $M$ で上から抑えられる（すべての $n$ で $a_n \\le M$）とき、数列 $a_n + 1$ は $M + 1$ で上から抑えられることを示す。",
 hints=["示す upper(…, M + 1) は、開くと「すべての $n$ について …」。`Fix n`。", "$h$ に $n$ を入れる：`k : a_n <= M by h(n)`。", "あとは `linarith`（示すべきものは $a_n + 1 \\le M + 1$）。"],
 pre="def upper(a : Nat -> Real, M : Real) :<=> forall n:Nat. a_n <= M",
 stmt="thm upper_shift :\n  a : Nat -> Real, M : Real, h : upper(a, M)\n  |- upper((n:Nat |-> a_n + 1), M + 1)",
 proof="Fix n\n  k : a_n <= M by h(n)\n  linarith", uses=["Fix n", "h(n)"], ex_title="上から抑えられる数列")

# ---------------------------------------------------------------- 12
lesson(12, "∀∃ と ∃∀（量化子の順番）", "量化子の順番", [
  {"p": "**ねらい**：「すべての」と「ある」が重なった命題を書く・使う。**順番を入れ替えると意味が変わる**。ε-δ・ε-N 論法でつまずく所の多くは、ここにある。"},
  {"paper": ["**∀x∃y 型**（どの $x$ にも、それに合う $y$ がある）：「どの実数 $x$ にも、$x$ より大きい実数 $y$ がある」は**正しい**。$x$ を見てから $y = x + 1$ と選べばよい。",
             "**∃y∀x 型**（1 つの $y$ が、どの $x$ にも通用する）：「どの実数 $x$ よりも大きい実数 $y$ がある」は**正しくない**。そういう $y$ があったとすると、$x = y + 1$ とおいて $y > y + 1$ となり矛盾。"]},
  {"p": "違いは、**選ぶときに相手がもう決まっているかどうか**（$y$ を選ぶとき、$x$ はもう決まっているか）。$\\forall x\\ \\exists y$ では $x$ が先なので、$y$ は $x$ を使って選んでよい（$y$ は $x$ に依存する）。$\\exists y\\ \\forall x$ では $y$ を先に 1 つ決め、そのあとどんな $x$ が来ても成り立たないといけない。"},
  {"p": "Narfi では、**書く順番がそのまま量化子の順番**になる。goal の先頭から順に、∀ なら `Fix`、∃ なら `choose` を書く。"},
  {"code": "thm bigger :\n  |- forall x:Real. exists y:Real. y > x\n\nFix x\n  choose x + 1\n  linarith\n\nthm no_biggest :\n  |- not (exists y:Real. forall x:Real. y > x)\n\nassume h : exists y:Real. forall x:Real. y > x\n  Obtain y | hy by h\n  k : y > y + 1 by hy(y + 1)\n  linarith"},
  {"steps": [["Fix x", "∀x：まず $x$ を任意にとる"], ["choose x + 1", "∃y：$y$ として $x + 1$ を挙げる。$x$ はもう決まっているので、使ってよい"],
             ["Obtain y | hy by h", "「1 つの $y$ がどの $x$ にも通用する」から、その $y$ を取り出す"],
             ["k : y > y + 1 by hy(y + 1)", "$hy$ はどの $x$ にも使えるので、$x = y + 1$ を入れる（$y$ を取り出したあとなので、$y$ を使った値を入れてよい）"],
             ["linarith", "$y > y + 1$ は矛盾。`not` を示すには、矛盾を出せばよい"]]},
  {"h": "使う側：仮定が ∀∃ か ∃∀ か"},
  {"p": "仮定 $h : \\forall x\\ \\exists y.\\ P$ は、**先に x を渡してから** $y$ を取り出す：`Obtain y | hy by h(x)`。取り出した $y$ はその $x$ 用のもの（$x$ を変えれば $y$ も変わりうる）。依存を `Obtain y(x) | hy by h(x)` と書いておくと、検査器が確かめる。"},
  {"p": "仮定 $h : \\exists y\\ \\forall x.\\ P$ は、**先に** $y$ を 1 つ取り出す：`Obtain y | hy by h`。その $y$ はどの $x$ にも使える（`hy(x)`）。だから $\\exists y\\ \\forall x$ から $\\forall x\\ \\exists y$ は出る（逆は出ない。上の例が反例）。"},
  {"code": "thm ex_all_to_all_ex :\n  f : Real -> Real, h : exists M:Real. forall x:Real. f(x) <= M\n  |- forall x:Real. exists M:Real. f(x) <= M\n\nObtain M | hM by h\nFix x\n  choose M\n  hM(x)"},
  {"h": "ε-N 論法では"},
  {"p": "$a_n \\to \\alpha$ は「$\\forall \\varepsilon > 0\\ \\exists N\\ \\forall n \\ge N.\\ |a_n - \\alpha| < \\varepsilon$」。$N$ は $\\varepsilon$ のあとなので **ε ごとに選んでよい**（$\\varepsilon$ が小さいほど $N$ は大きくなるのがふつう）。$n$ は $N$ のあとなので、$N$ を $n$ を使って選んではいけない。順番を入れ替えた「$\\exists N\\ \\forall \\varepsilon > 0\\ \\forall n \\ge N$」は、「ある番号から先はずっと $a_n = \\alpha$」というずっと強い（ふつうは成り立たない）主張になる。"},
  {"p": "証明では `Obtain N(eps) | hN by …` と書くと、$N$ が $\\varepsilon$ にだけ依ることを検査器が確かめる（次の 2 つのレッスンで使う）。"},
  {"type": [["forall x:Real. exists y:Real. …", "∀x∃y（$y$ は $x$ ごと）"], ["exists y:Real. forall x:Real. …", "∃y∀x（1 つの $y$ がすべての $x$ に）"], ["Obtain y(x) | hy by h(x)", "$y$ が $x$ に依ることを書いて取り出す"]]},
  {"pitfalls": [
    ["「Fix できない：goal … は ∀ の形ではない」", "goal が ∃ で始まっている。∃y∀x なら、先に `choose`（$y$ を決める）、それから `Fix x`"],
    ["「`x` は文脈にない」（choose の行で）", "∃y∀x で、まだとっていない $x$ を使って $y$ を選ぼうとした。$y$ は $x$ によらない値で選ぶ"],
    ["「依存関係の宣言が合わない」", "`Obtain N(eps)` と書いたのに、$n$ をとったあと（`Fix n` の中）で取り出している。取り出す行を `Fix n` より前に置く"]]},
], task="(1) どの実数 $x$ にも、$x + y = 0$ となる $y$ がある（∀∃ を**作る**）。(2) ある実数 $m$ があって、どの $x$ でも $x^2 + 1 > m$（∃∀ を**作る**）。(3) どの $x$ にも $f(x)$ より大きい $y$ があるなら、どの $x$ にも $f(x) + 1$ より大きい $y$ がある（∀∃ を**使う**）。",
 hints=["(1) goal は ∀x から始まる：`Fix x`。次は ∃y：$x$ を使って $y$ を選んでよい（$x + y = 0$ になる $y$ は？）。最後は `ring`。",
        "(2) goal は ∃m から始まる：先に `choose`。$m$ は $x$ を使わずに選ぶ（$x^2 + 1$ はいつも 1 以上）。`choose 0` のあと `Fix x`、`h : x^2 >= 0 by sq_nonneg`、`linarith`。",
        "(3) `Fix x` のあと、仮定に $x$ を渡して取り出す：`Obtain y(x) | hy by h(x)`。$y + 1$ を挙げて（`choose y + 1`）、`linarith`。"],
 pre="axiom sq_nonneg : x : Real |- x^2 >= 0",
 parts=[("thm neg_inverse :\n  |- forall x:Real. exists y:Real. x + y = 0", "Fix x\n  choose -x\n  ring"),
        ("thm lower_bound :\n  |- exists m:Real. forall x:Real. x^2 + 1 > m", "choose 0\nFix x\n  h : x^2 >= 0 by sq_nonneg\n  linarith"),
        ("thm above_shift :\n  f : Real -> Real, h : forall x:Real. exists y:Real. y > f(x)\n  |- forall x:Real. exists y:Real. y > f(x) + 1", "Fix x\n  Obtain y(x) | hy by h(x)\n  choose y + 1\n  linarith")],
 uses=["Fix x\n  choose -x", "choose 0\nFix x", "Obtain y(x) | hy by h(x)"], ex_title="∀∃ と ∃∀ を作る・使う")

# ---------------------------------------------------------------- 13
LIM = "def is_lim(a : Nat -> Real, alpha : Real) :<=> forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n  notation a_n -> alpha (n -> \\infty)"
lesson(13, "数列の極限", "極限", [
  {"p": "**ねらい**：数列 $a_n$ が $\\alpha$ に収束する（$\\varepsilon$-$N$ 論法）を定義し、使う。数列は $a : \\mathbb{N} \\to \\mathbb{R}$ と宣言すると $a_n$ と書ける。"},
  {"code": LIM},
  {"p": "読み方：「任意の $\\varepsilon > 0$ に対し、ある $N$ があって、$n \\ge N$ なら $|a_n - \\alpha| < \\varepsilon$」。下の `notation` は**記法**で、教科書と同じ $a_n \\to \\alpha\\ (n \\to \\infty)$ の形で書けるようにする。$a$ の所には $n$ を含む式が入るので、$a_{n+1} \\to \\alpha\\ (n \\to \\infty)$ とも書ける。"},
  {"paper": ["**定理**　$a_n \\to \\alpha$ ならば $a_{n+1} \\to \\alpha$。", "**証明**　$\\varepsilon > 0$ をとる。$n \\ge N$ で $|a_n - \\alpha| < \\varepsilon$ となる $N$ をとる。$n \\ge N$ なら $n + 1 \\ge N$ なので、$|a_{n+1} - \\alpha| < \\varepsilon$。$\\blacksquare$"]},
  {"code": LIM + "\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : a_n -> alpha (n -> \\infty)\n  |- a_{n+1} -> alpha (n -> \\infty)\n\nFix eps | h_{eps} : eps > 0\n  Obtain N | hN by h(eps, h_{eps})\n  choose N\n  Fix n | h_n : n >= N\n    k : n + 1 >= N by linarith\n    hN(n + 1, k)"},
  {"steps": [["Fix eps | h_{eps} : eps > 0", "$\\varepsilon > 0$ をとる（示す収束の定義が開かれる）"], ["Obtain N | hN by h(eps, h_{eps})", "仮定 $h$ に $\\varepsilon$ と $h_\\varepsilon$ を渡すと「ある $N$ が …」。その $N$ を取り出す"], ["choose N", "同じ $N$ を挙げる"], ["Fix n | h_n : n >= N", "$n \\ge N$ をとる"], ["k : n + 1 >= N by linarith", "$n + 1 \\ge N$ を書き留める"], ["hN(n + 1, k)", "$hN$ を $n + 1$ で使うと $|a_{n+1} - \\alpha| < \\varepsilon$"]]},
  {"type": [["a_n, a_{n+1}", "数列の項"], ["abs( ) または |x|", "絶対値"], ["-> と \\infty", "→ と ∞"]]},
], task="$a_n \\to \\alpha$ ならば、ある番号 $N$ から先は $a_n < \\alpha + 1$ であることを示す（収束する数列は、いずれ上から抑えられる）。",
 hints=["定義の $\\varepsilon$ に 1 を入れる。$1 > 0$ の根拠を `one : 1 > 0 by decide` と書き留め、`Obtain N | hN by h(1, one)`。", "`choose N` のあと `Fix n | h_n : n >= N`。`k : abs(a_n - alpha) < 1 by hN(n, h_n)`。", "絶対値をはずすのに `abs_lt` を使う：`l : -1 < a_n - alpha and a_n - alpha < 1 by abs_lt(k)`。あとは `linarith`。"],
 pre=LIM + "\n\naxiom abs_lt : x : Real, e : Real, h : abs(x) < e |- -e < x and x < e",
 stmt="thm eventually_below :\n  a : Nat -> Real, alpha : Real, h : a_n -> alpha (n -> \\infty)\n  |- exists N:Nat. forall n:Nat>=N. a_n < alpha + 1",
 proof="one : 1 > 0 by decide\nObtain N | hN by h(1, one)\nchoose N\nFix n | h_n : n >= N\n  k : abs(a_n - alpha) < 1 by hN(n, h_n)\n  l : -1 < a_n - alpha and a_n - alpha < 1 by abs_lt(k)\n  linarith", uses=["Obtain N | hN by h", "choose N", "Fix n |", "hN(n, h_n)"], ex_title="いずれ上から抑えられる")

# ---------------------------------------------------------------- 14
LIM_AX = LIM + "\n\naxiom triangle : x : Real, y : Real |- abs(x + y) <= abs(x) + abs(y)\naxiom ge_max_left : n : Nat, h : n >= max{a, b} |- n >= a\naxiom ge_max_right : n : Nat, h : n >= max{a, b} |- n >= b"
ADD_CONST = "thm lim_add_const :\n  a : Nat -> Real, alpha : Real, c : Real, h : a_n -> alpha (n -> \\infty)\n  |- a_n + c -> alpha + c (n -> \\infty)\n\nFix eps | h_{eps} : eps > 0\n  Obtain N(eps) | hN by h(eps, h_{eps})\n  choose N\n  Fix n | h_n : n >= N\n    abs(a_n + c - (alpha + c))\n      = abs(a_n - alpha)   by ring\n      < eps                by hN(n, h_n)"
lesson(14, "極限の証明を自分で書く（実践）", "極限の証明", [
  {"p": "**ねらい**：ε-N の証明を、最初から自分で書く。収束の証明は**型が決まっている**ので、型どおりに書けば半分は終わる。残りは「仮定に何を入れるか」を下書きで決めること。"},
  {"h": "証明の型"},
  {"keys": [
    ["Fix eps | h_{eps} : eps > 0", "∀ε>0：示したい収束の $\\varepsilon$ をとる"],
    ["Obtain N(eps) | hN by h(○, 根拠)", "仮定の収束に、$\\varepsilon$ から作った ○（$\\varepsilon$ そのもの、$\\varepsilon/2$ など）を入れて $N$ を取り出す。$N$ は $\\varepsilon$ ごと（レッスン 12）"],
    ["choose N", "∃N：$N$ を挙げる（いくつかの $N$ をまとめるなら $\\max\\{N_1, N_2\\}$）"],
    ["Fix n | h_n : n >= N", "∀n≥N：$n$ をとる"],
    ["abs(…) の連鎖", "$|… - …| < \\varepsilon$ を、等式・不等式の連鎖で示す（紙の証明の最後の 1 行）"]]},
  {"p": "いちばん簡単な例：$a_n \\to \\alpha$ なら $a_n + c \\to \\alpha + c$。○ は $\\varepsilon$ そのもので足りる（$|(a_n + c) - (\\alpha + c)| = |a_n - \\alpha|$ なので）。"},
  {"code": LIM + "\n\n" + ADD_CONST},
  {"h": "下書き：○ と N を逆算する"},
  {"p": "○ に何を入れるかは、最後の連鎖から**逆に**決める。和 $a_n + b_n \\to \\alpha + \\beta$ なら、三角不等式で $|(a_n + b_n) - (\\alpha + \\beta)| \\le |a_n - \\alpha| + |b_n - \\beta|$。これを $\\varepsilon$ 未満にしたいので、それぞれを $\\varepsilon/2$ 未満にすればよい → ○ は $\\varepsilon/2$。$N$ は $N_1$（$a$ 用）と $N_2$（$b$ 用）の両方より先、つまり $\\max\\{N_1, N_2\\}$。"},
  {"paper": ["**定理**　$a_n \\to \\alpha$、$b_n \\to \\beta$ ならば $a_n + b_n \\to \\alpha + \\beta$。",
             "**証明**　$\\varepsilon > 0$ をとる。$n \\ge N_1$ で $|a_n - \\alpha| < \\varepsilon/2$、$n \\ge N_2$ で $|b_n - \\beta| < \\varepsilon/2$ となる $N_1, N_2$ をとり、$N = \\max\\{N_1, N_2\\}$ とおく。$n \\ge N$ なら $|(a_n + b_n) - (\\alpha + \\beta)| \\le |a_n - \\alpha| + |b_n - \\beta| < \\varepsilon/2 + \\varepsilon/2 = \\varepsilon$。$\\blacksquare$"]},
  {"p": "教科書の証明は、下書きを消して清書したもの。「$\\varepsilon/2$ とおく」が天下りに見えるのは、逆算の跡が消えているから。練習では、Goal タブで $\\varepsilon$ と示すべきものを見ながら、紙に逆算を書いてから始めるとよい。"},
  {"p": "使う道具（この練習では公理として置く）：三角不等式 `triangle`（$|x + y| \\le |x| + |y|$）と、`ge_max_left(h_n)`（$n \\ge \\max\\{N_1, N_2\\}$ から $n \\ge N_1$）・`ge_max_right(h_n)`。"},
  {"h": "具体的な数列：1/(n+1) → 0"},
  {"p": "$n$ は自然数だが、$1/(n+1)$ のように**実数の式の中で使える**（自然数は実数に含まれる）。自然数どうしの不等式（$n \\ge N$）と実数の不等式を、`linarith` はまとめて扱う（$n \\ge 0$ も自動で使う）。"},
  {"paper": ["**定理**　$\\dfrac{1}{n+1} \\to 0$。",
             "**証明**　$\\varepsilon > 0$ をとる。アルキメデス性（どんな実数よりも大きい自然数がある）で $N > 1/\\varepsilon$ となる $N$ をとる。$n \\ge N$ なら $n + 1 > 1/\\varepsilon$ なので $\\dfrac{1}{n+1} < \\varepsilon$。よって $\\left|\\dfrac{1}{n+1} - 0\\right| = \\dfrac{1}{n+1} < \\varepsilon$。$\\blacksquare$"]},
  {"p": "ここでの $N$ は $\\varepsilon$ の式では書けない（「$1/\\varepsilon$ より大きい自然数」としか言えない）。だから、存在を言う定理 `archimedes` から `Obtain` で取り出す。使う道具（公理として置く）：`archimedes`（どんな $x$ にも $N > x$ となる自然数 $N$ がある）、`inv_lt`（$x > 0$、$\\varepsilon > 0$、$x > 1/\\varepsilon$ なら $1/x < \\varepsilon$）、`inv_pos`（$x > 0$ なら $1/x > 0$）、`abs_of_pos`（$x > 0$ なら $|x| = x$）。"},
  {"h": "定理を使って定理を示す"},
  {"p": "一度示した定理は、ほかの証明の根拠に使える。$a_n \\to \\alpha$ なら $a_n + a_n \\to \\alpha + \\alpha$ は、和の定理に $h$ を 2 回渡すだけ：`lim_add(h, h)`。ε をとり直す必要はない。"},
  {"type": [["N_1, N_2", "添字つきの名前 $N_1, N_2$"], ["max{N_1, N_2}", "$\\max\\{N_1, N_2\\}$"], ["eps/2", "$\\varepsilon/2$"]]},
  {"pitfalls": [
    ["「linarith では … を示せない」（連鎖の最後）", "○ の選び方が合っていない（$\\varepsilon/2$ を 2 つ足すと $\\varepsilon$。$\\varepsilon$ を 2 つ足すと $2\\varepsilon$ で多すぎる）。下書きをやり直す"],
    ["hN_1(n, h_n) で「… が合わない」", "$hN_1$ に渡すのは「$n \\ge N_1$」の根拠。$h_n$ は「$n \\ge \\max\\{N_1, N_2\\}$」なので、`ge_max_left(h_n)` にして渡す"],
    ["「依存関係の宣言が合わない」", "`Obtain N_1(eps)` を `Fix n` の中に書いている。$N$ を取り出す行は、`choose` より前に置く"]]},
], task="(1) $a_n \\to \\alpha$、$b_n \\to \\beta$ ならば $a_n + b_n \\to \\alpha + \\beta$ を、最初から書く。(2) $a_n \\to \\alpha$ ならば $a_n + a_n \\to \\alpha + \\alpha$（(1) を使う）。(3) さらに $a_n + b_n + c \\to \\alpha + \\beta + c$（(1) と上の lim_add_const を使う）。(4) $\\dfrac{1}{n+1} \\to 0$（具体的な数列）。",
 hints=["(1) 型どおり：`Fix eps | h_{eps} : eps > 0`。下書きで ○ = $\\varepsilon/2$。まず `h_2 : eps/2 > 0 by linarith` と書き留める。",
        "(1) `Obtain N_1(eps) | hN_1 by ha(eps/2, h_2)`、同じく $N_2$。`choose max{N_1, N_2}`、`Fix n | h_n : n >= max{N_1, N_2}`。",
        "(1) `k_1 : abs(a_n - alpha) < eps/2 by hN_1(n, ge_max_left(h_n))`、同じく $k_2$。",
        "(1) 連鎖：`abs(a_n + b_n - (alpha + beta))`、`= abs((a_n - alpha) + (b_n - beta)) by ring`、`<= abs(a_n - alpha) + abs(b_n - beta) by triangle`、`< eps/2 + eps/2 by k_1, k_2`、`= eps by ring`。",
        "(2) `lim_add(h, h)` の 1 行。(3) 内側から：`lim_add(ha, hb)` が $a_n + b_n \\to \\alpha + \\beta$。それを lim_add_const に渡す。",
        "(4) `Fix eps | h_{eps} : eps > 0` のあと、`hA : exists N:Nat. N > 1/eps by archimedes`、`Obtain N | hN by hA`、`choose N`、`Fix n | h_n : n >= N`。",
        "(4) `p : n + 1 > 0 by linarith`、`q : n + 1 > 1/eps by linarith`、`r : 1/(n + 1) < eps by inv_lt(p, h_{eps}, q)`、`s : 1/(n + 1) > 0 by inv_pos(p)`。",
        "(4) 連鎖：`abs(1/(n + 1) - 0)`、`= abs(1/(n + 1)) by ring`、`= 1/(n + 1) by abs_of_pos(s)`、`< eps by r`。"],
 pre=LIM_AX + "\naxiom archimedes : x : Real |- exists N:Nat. N > x\naxiom inv_lt : x : Real, e : Real, hx : x > 0, he : e > 0, h : x > 1/e |- 1/x < e\naxiom inv_pos : x : Real, hx : x > 0 |- 1/x > 0\naxiom abs_of_pos : x : Real, h : x > 0 |- abs(x) = x\n\n" + ADD_CONST,
 parts=[("thm lim_add :\n  a : Nat -> Real, b : Nat -> Real, alpha : Real, beta : Real,\n  ha : a_n -> alpha (n -> \\infty), hb : b_n -> beta (n -> \\infty)\n  |- a_n + b_n -> alpha + beta (n -> \\infty)",
         "Fix eps | h_{eps} : eps > 0\n  h_2 : eps/2 > 0 by linarith\n  Obtain N_1(eps) | hN_1 by ha(eps/2, h_2)\n  Obtain N_2(eps) | hN_2 by hb(eps/2, h_2)\n  choose max{N_1, N_2}\n  Fix n | h_n : n >= max{N_1, N_2}\n    k_1 : abs(a_n - alpha) < eps/2 by hN_1(n, ge_max_left(h_n))\n    k_2 : abs(b_n - beta) < eps/2 by hN_2(n, ge_max_right(h_n))\n    abs(a_n + b_n - (alpha + beta))\n      = abs((a_n - alpha) + (b_n - beta))     by ring\n      <= abs(a_n - alpha) + abs(b_n - beta)   by triangle\n      < eps/2 + eps/2                         by k_1, k_2\n      = eps                                   by ring"),
        ("thm lim_double :\n  a : Nat -> Real, alpha : Real, h : a_n -> alpha (n -> \\infty)\n  |- a_n + a_n -> alpha + alpha (n -> \\infty)", "lim_add(h, h)"),
        ("thm lim_add3 :\n  a : Nat -> Real, b : Nat -> Real, alpha : Real, beta : Real, c : Real,\n  ha : a_n -> alpha (n -> \\infty), hb : b_n -> beta (n -> \\infty)\n  |- a_n + b_n + c -> alpha + beta + c (n -> \\infty)", "lim_add_const(lim_add(ha, hb))"),
        ("thm lim_inv :\n  |- 1/(n + 1) -> 0 (n -> \\infty)",
         "Fix eps | h_{eps} : eps > 0\n  hA : exists N:Nat. N > 1/eps by archimedes\n  Obtain N | hN by hA\n  choose N\n  Fix n | h_n : n >= N\n    p : n + 1 > 0 by linarith\n    q : n + 1 > 1/eps by linarith\n    r : 1/(n + 1) < eps by inv_lt(p, h_{eps}, q)\n    s : 1/(n + 1) > 0 by inv_pos(p)\n    abs(1/(n + 1) - 0)\n      = abs(1/(n + 1))   by ring\n      = 1/(n + 1)        by abs_of_pos(s)\n      < eps              by r")],
 uses=["Obtain N_1(eps) | hN_1 by ha(eps/2, h_2)", "choose max{N_1, N_2}", "ge_max_left(h_n)", "lim_add(h, h)", "lim_add_const(lim_add(ha, hb))", "by archimedes", "inv_lt(p, h_{eps}, q)"], ex_title="極限の証明を書く")

# ---------------------------------------------------------------- 15
lesson(15, "数学的帰納法", "帰納法", [
  {"p": "**ねらい**：自然数 $n$ についての命題を、$n = 0$ のときと「$k$ で成り立てば $k + 1$ でも成り立つ」の 2 つで示す（`induction n`）。漸化式で定めた数列（`rec`）について示すときによく使う。"},
  {"code": "rec double(n : Nat) : Nat\n  double(0) = 0\n  double(n + 1) = double(n) + 2\n\nthm double_eq :\n  |- forall n:Nat. double(n) = 2n\n\nFix n\n  induction n\n    Case zero\n      double(0)\n        = 0       by double.zero\n        = 2*0     by ring\n    Case succ k, IH : double(k) = 2k\n      s : S(k) = k + 1 by ring\n      double(S(k))\n        = double(k + 1)     by s\n        = double(k) + 2     by double.succ(k)\n        = 2k + 2            by IH\n        = 2(k + 1)          by ring\n        = 2S(k)             by s"},
  {"steps": [["rec double(n : Nat) : Nat", "漸化式で数列を定める。`double(0) = 0`（初項）と `double(n + 1) = …`（漸化式）。2 つの等式は、それぞれ `double.zero`・`double.succ` という名前で使える"], ["induction n", "$n$ についての帰納法。下に `Case zero` と `Case succ k, IH : …` を書く"], ["Case zero", "$n = 0$ の場合"], ["Case succ k, IH : double(k) = 2k", "$k$ で成り立つ（帰納法の仮定 $IH$）として、次の数で示す。$IH$ の中身は省略できない"], ["s : S(k) = k + 1 by ring", "「$k$ の次の数」は $S(k)$ と書かれる。$k + 1$ と同じことを書き留めて、`by s` で書き換える"]]},
  {"type": [["rec", "漸化式による定義"], ["induction n", "数学的帰納法"], ["S(k)", "$k$ の次の数（$k + 1$）"]]},
  {"pitfalls": [["「… と … が合わない」（S(k) と k + 1）", "帰納法の段では $k + 1$ が $S(k)$ の形で出る。`s : S(k) = k + 1 by ring` を書き、連鎖の最初と最後で `by s` を使う"]]},
], task="$f(0) = 0$、$f(n+1) = f(n) + 2n + 1$ で定めた数列について、$f(n) = n^2$ を示す（$1 + 3 + 5 + \\dots + (2n-1) = n^2$）。",
 hints=["上の例と同じ形。`Fix n` のあと `induction n`。", "`Case zero` は `odd_sum(0) = 0 by odd_sum.zero`、`= 0^2 by ring` の連鎖。", "`Case succ k, IH : odd_sum(k) = k^2`。連鎖：`= odd_sum(k + 1) by s`、`= odd_sum(k) + 2k + 1 by odd_sum.succ(k)`、`= k^2 + 2k + 1 by IH`、`= (k + 1)^2 by ring`、`= S(k)^2 by s`。"],
 pre="rec odd_sum(n : Nat) : Nat\n  odd_sum(0) = 0\n  odd_sum(n + 1) = odd_sum(n) + 2n + 1",
 stmt="thm odd_sum_sq :\n  |- forall n:Nat. odd_sum(n) = n^2",
 proof="Fix n\n  induction n\n    Case zero\n      odd_sum(0)\n        = 0     by odd_sum.zero\n        = 0^2   by ring\n    Case succ k, IH : odd_sum(k) = k^2\n      s : S(k) = k + 1 by ring\n      odd_sum(S(k))\n        = odd_sum(k + 1)          by s\n        = odd_sum(k) + 2k + 1     by odd_sum.succ(k)\n        = k^2 + 2k + 1            by IH\n        = (k + 1)^2               by ring\n        = S(k)^2                  by s", uses=["induction n", "by IH"], ex_title="奇数の和は平方数")

# ---------------------------------------------------------------- 16
lesson(16, "エディタの使い方", "", [
  {"keys": [
    ["\\fr + Tab, /", "分数"], ["_ , ^", "添字・上付き（$a_n$・$a_{i,j}$・$x^2$）"], ["abs( ) , |x|", "絶対値"],
    ["[[ ", "行列（成分の中で Enter で行、& で列を足す）"],
    ["<= >= != => <=>", "≤ ≥ ≠ ⇒ ⇔"], ["\\|- , \\vdash", "⊢"], ["|-> , \\mapsto", "↦"], ["forall exists eps …", "∀ ∃ ε …（空白で変換）"],
    ["\\ + 名前", "記号の補完（Tab か Enter で決定）"], ["Tab（行末）", "エラーに出た直し方・根拠の候補を入れる"], ["Tab / Shift+Tab（複数行を選んで）", "まとめて字下げ・戻す"],
    ["⌘F / ⌘⌥F", "検索 / 置換（正規表現も使える）"], ["⇧⌥F", "整形（連鎖の by をそろえる など）"], ["⌘S / ⌘Z", "保存 / 元に戻す"]]},
  {"p": "右の **Goal** タブには、カーソルの行で使える仮定と、示すべきものが出る。困ったら「次の一手」のボタンを押すと、いま書けるものが入る。"},
  {"p": "**Prose** タブで証明が文章として、**LaTeX** タブで論文に貼れる形で読める。下の `JA` を押すと、エディタの中も日本語の証明文の形になる（ファイルは変わらない）。"},
  {"p": "証明の行を右クリック →「証明木を見る」で、証明が論理の規則（自然演繹）の組み合わせとしてどう組み立てられているかが見られる。"},
  {"p": "古い書き方のファイルは、開くと「今の書き方に直すか」を聞かれる（File → Update Old Syntax でも直せる）。"},
])

# ---------------------------------------------------------------- 付録
L.append({"title": "付録：早見表", "blocks": [
  {"h": "goal の形から、書くものを選ぶ"},
  {"keys": [
    ["P => Q（ならば）", "`assume h : P`（下に字下げして Q を示す）"],
    ["forall x. P（すべての）", "`Fix x`（`forall eps>0` なら `Fix eps | h : eps > 0`）"],
    ["exists x. P（ある）", "`choose t`（範囲つきなら `choose t, 根拠`）"],
    ["forall x. exists y. P", "`Fix x` のあと `choose t`（t は x を使ってよい）"],
    ["exists y. forall x. P", "`choose t` のあと `Fix x`（t は x を使えない）"],
    ["P and Q（かつ）", "`根拠1, 根拠2`"],
    ["P or Q（または）", "`left` か `right`"],
    ["not P（でない）", "`assume h : P`（矛盾を示す）"],
    ["等式・不等式", "連鎖、`ring`、`linarith`、仮定の名前"],
    ["何でも", "`by_contra hn`（背理法）"]]},
  {"h": "仮定の形から、使い方を選ぶ"},
  {"keys": [
    ["h : P => Q", "`h(p)` で Q"],
    ["h : forall x. P", "`h(t)` で P(t)（条件つきなら `h(t, 根拠)`）"],
    ["h : exists x. P", "`Obtain x | hx by h`"],
    ["h : forall x. exists y. P", "`Obtain y(x) | hy by h(x)`（y は x ごと）"],
    ["h : exists y. forall x. P", "`Obtain y | hy by h` のあと、どの x にも `hy(x)`"],
    ["h : P and Q", "`h.left`・`h.right`"],
    ["h : P or Q", "`cases h` の下に `Case left h1`・`Case right h2`"],
    ["h : not P", "`h(p)` で矛盾"],
    ["h : a = b", "連鎖の根拠 `by h`（a を b に書き換える）"]]},
  {"h": "書き方の決まり"},
  {"keys": [
    ["名前 : 右辺", "名前を導入する。右辺は型（もの）か命題"],
    ["by 根拠", "根拠はいつも by の右"],
    ["|", "「〜であって」：左がもの、右がその仮定（Fix・Obtain）"],
    [",", "同じ種類のものを並べる"]]},
]})

header = "// Narfi のチュートリアル（エディタ右側の Learn タブ）。対象：理系の高校生でもわかるように。\n// 各レッスン：本文（p・paper：紙の証明・code：エディタと同じ見た目で描く・steps：1 行ずつ・type：打ち方・check・pitfalls・keys・h）、\n// 練習（file：自分のファイルに作る練習のファイル・task・hints・exercise・answer）。番号とファイル名の番号はそろえる。\n// 例と答えが通ることは tests/ui.rs（tutorial_answers_check）で確かめる。このファイルは scripts/learn/tutorial.py で作る（直接直さない）。\n\n"
open(os.path.join(HERE, "../../src/tutorial.js"), "w").write(header + "window.NARFI_TUTORIAL = " + json.dumps(L, ensure_ascii=False, indent=2) + ";\n")
print(len(L), "lessons")
