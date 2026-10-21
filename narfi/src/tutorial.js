// Narfi のチュートリアル（エディタ右側の Learn タブ）。対象：理系の高校生でもわかるように。
// 各レッスン：本文（p・paper：紙の証明・code：エディタと同じ見た目で描く・steps：1 行ずつ・type：打ち方・check・pitfalls・keys・h）、
// 練習（task・hints・exercise・answer）。答えが通ることは tests/ui.rs（tutorial_answers_check）で確かめる。

window.NARFI_TUTORIAL = [
  {
    "title": "1. はじめての証明",
    "blocks": [
      {
        "p": "**ねらい**：Narfi で定理を書いて、証明が正しいかを検査器に確かめてもらう。"
      },
      {
        "paper": [
          "**定理**　実数 $x$ が $x > 1$ を満たすとき、$2x > 2$ である。",
          "**証明**　$x > 1$ の両辺を 2 倍すればよい。$\\blacksquare$"
        ]
      },
      {
        "p": "Narfi では、同じことをこう書きます。"
      },
      {
        "code": "thm double_gt :\n  x : Real, h : x > 1\n  |- 2x > 2\n\nlinarith"
      },
      {
        "steps": [
          [
            "thm double_gt :",
            "「定理を書きます。名前は double_gt」という宣言"
          ],
          [
            "x : Real, h : x > 1",
            "**仮定**。$x$ は実数、$x > 1$ が成り立つ。この仮定に $h$ という名前を付けている（あとで使うため）"
          ],
          [
            "|- 2x > 2",
            "⊢ の右が**示したいこと**（結論）"
          ],
          [
            "linarith",
            "**証明**。`linarith` は「仮定から不等式の計算で分かる」という意味。検査器がその計算を実際に確かめる"
          ]
        ]
      },
      {
        "type": [
          [
            "Real",
            "ℝ（実数）。`Nat` は ℕ"
          ],
          [
            "\\|-",
            "⊢（「〜のとき、〜が成り立つ」の区切り）"
          ],
          [
            ">=  <=  !=",
            "≥　≤　≠"
          ]
        ]
      },
      {
        "check": "「練習を開く」を押すと、証明の所が `sorry`（まだ書いていない、の印）になっています。右上が **1 incomplete**（黄色）。`sorry` の行にカーソルを置いて右の **Goal** タブを見ると、使える仮定と、示すべきもの（⊢ の右）が出ています。`sorry` を消して `linarith` と書くと、右上が **1 theorem verified**（緑）になります。"
      },
      {
        "pitfalls": [
          [
            "「linarith では … を示せない」",
            "仮定から一次の不等式の計算だけでは出ない。仮定が足りないか、$x^2$ のような 2 次の式が入っている"
          ]
        ]
      }
    ],
    "task": "$x > 1$、$y > 2$ のとき、$x + y > 3$ を示す。",
    "hints": [
      "Goal タブで、仮定 2 つと示すべき $x + y > 3$ を確かめる。",
      "2 つの不等式を足せば出る。`linarith` がその計算をしてくれる。"
    ],
    "exercise": "-- 練習 1：sorry を消して証明を書く\n\nthm sum_gt :\n  x : Real, y : Real, h : x > 1, k : y > 2\n  |- x + y > 3\n\nsorry\n",
    "answer": "thm sum_gt :\n  x : Real, y : Real, h : x > 1, k : y > 2\n  |- x + y > 3\n\nlinarith\n"
  },
  {
    "title": "2. 式変形をつなげる",
    "blocks": [
      {
        "p": "**ねらい**：紙と同じように、式を縦に並べて変形する。各行に「なぜそう変形できるか」（根拠）を `by` の後ろに書く。"
      },
      {
        "paper": [
          "$a \\le b$ のとき　$a + 1 \\le b + 1 \\le b + 2$"
        ]
      },
      {
        "code": "thm chain :\n  a : Real, b : Real, h : a <= b\n  |- a + 1 <= b + 2\n\na + 1\n  <= b + 1   by linarith\n  <= b + 2   by linarith"
      },
      {
        "steps": [
          [
            "a + 1",
            "変形を始める式"
          ],
          [
            "<= b + 1   by linarith",
            "1 行目の変形。根拠は「仮定 $h$ からの不等式の計算」"
          ],
          [
            "<= b + 2   by linarith",
            "2 行目。最後まで来ると、全体として $a + 1 \\le b + 2$ が示された"
          ]
        ]
      },
      {
        "p": "根拠には、仮定の名前（`by h`）、計算（`by ring`：多項式の計算、`by linarith`：不等式の計算）が書けます。"
      },
      {
        "p": "**根拠がわからないとき**は、`by …` を書かずに `<= b + 1` とだけ書いてみてください。エラーになって、検査器が見つけた根拠の候補が出ます。行末で **Tab** を押すと入ります。"
      },
      {
        "type": [
          [
            "<=",
            "≤（打つと自動で ≤ になる）"
          ],
          [
            "by",
            "根拠を書く前の区切り"
          ]
        ]
      }
    ],
    "task": "$x \\le y$、$y < z$ から $x < z$ を、変形の連鎖で示す。",
    "hints": [
      "`x` から始めて、`<= y` と `< z` の 2 行。",
      "1 行目の根拠は仮定 `h`、2 行目は仮定 `k`。"
    ],
    "exercise": "-- 練習 2：式変形の連鎖\n\nthm chain2 :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nsorry\n",
    "answer": "thm chain2 :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nx\n  <= y   by h\n  < z    by k\n"
  },
  {
    "title": "3. 「ならば」を示す・使う",
    "blocks": [
      {
        "p": "**ねらい**：「$P$ ならば $Q$」（$P \\to Q$）を示すには、$P$ を仮定して $Q$ を示す。高校の数学と同じ。"
      },
      {
        "paper": [
          "**定理**　$x > 2$ ならば $x > 1$。",
          "**証明**　$x > 2$ と仮定する。すると $x > 1$。$\\blacksquare$"
        ]
      },
      {
        "code": "thm gt_two :\n  x : Real\n  |- x > 2 -> x > 1\n\nassume h : x > 2\n  linarith"
      },
      {
        "steps": [
          [
            "assume h : x > 2",
            "「$x > 2$ と仮定する」。仮定の名前を $h$ にする"
          ],
          [
            "  linarith",
            "字下げした所では $h$ が使える。示すべきものは $x > 1$ に変わっている"
          ]
        ]
      },
      {
        "p": "**字下げ**が「仮定が使える範囲」です。`assume` の下は 1 段（スペース 2 つ）下げて書きます。"
      },
      {
        "p": "逆に「ならば」の仮定 $f : P \\to Q$ を**使う**ときは、$P$ の根拠 $p$ を渡して `f(p)` と書くと $Q$ になります（三段論法）。"
      },
      {
        "code": "thm syllogism :\n  P : Prop, Q : Prop, f : P -> Q, p : P\n  |- Q\n\nf(p)"
      },
      {
        "type": [
          [
            "->",
            "→（ならば）"
          ],
          [
            "Prop",
            "命題（正しいか正しくないかが決まる文）"
          ]
        ]
      },
      {
        "pitfalls": [
          [
            "「仮定 h の中身が書かれていない」",
            "`assume h` だけでなく `: x > 2` まで書く（行末で Tab を押すと入る）"
          ]
        ]
      }
    ],
    "task": "$P \\to Q$、$Q \\to R$ ならば $P \\to R$ を示す。",
    "hints": [
      "示すのは「$P$ ならば $R$」。まず `assume p : P`。",
      "$f(p)$ で $Q$ が手に入る。それを $g$ に渡すと $R$。`g(f(p))` と一度に書いてもよい。"
    ],
    "exercise": "-- 練習 3：ならば を 2 回使う\n\nthm imp_trans :\n  P : Prop, Q : Prop, R : Prop, f : P -> Q, g : Q -> R\n  |- P -> R\n\nsorry\n",
    "answer": "thm imp_trans :\n  P : Prop, Q : Prop, R : Prop, f : P -> Q, g : Q -> R\n  |- P -> R\n\nassume p : P\n  g(f(p))\n"
  },
  {
    "title": "4. 「かつ」",
    "blocks": [
      {
        "p": "**ねらい**：「$P$ かつ $Q$」（$P \\land Q$）の仮定 $h$ からは、`h.left` で $P$、`h.right` で $Q$ が取り出せる。$P \\land Q$ を示すには、2 つの根拠を `,` で並べる。"
      },
      {
        "paper": [
          "**定理**　$x > 0$ かつ $y > 0$ ならば $x + y > 0$。",
          "**証明**　$x > 0$ と $y > 0$ を足せばよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm pos_add :\n  x : Real, y : Real\n  |- x > 0 and y > 0 -> x + y > 0\n\nassume h : x > 0 and y > 0\n  hx : x > 0 by h.left\n  hy : y > 0 by h.right\n  linarith"
      },
      {
        "steps": [
          [
            "hx : x > 0 by h.left",
            "$h$ の左側を取り出して、名前 $hx$ を付ける。「名前 : 命題 by 根拠」は**途中で分かったことを書き留める行**"
          ],
          [
            "hy : y > 0 by h.right",
            "右側も同じ"
          ],
          [
            "linarith",
            "$hx$ と $hy$ を足して $x + y > 0$"
          ]
        ]
      },
      {
        "type": [
          [
            "and",
            "∧（かつ）"
          ],
          [
            "h.left / h.right",
            "∧ の左側・右側を取り出す"
          ]
        ]
      }
    ],
    "task": "$P \\land Q$ ならば $Q \\land P$ を示す。",
    "hints": [
      "`assume h : P and Q`。",
      "`h.right` が $Q$、`h.left` が $P$。2 つを `,` で並べると $Q \\land P$ になる（`h.right, h.left`）。"
    ],
    "exercise": "-- 練習 4：かつ の順番を入れ替える\n\nthm and_swap :\n  P : Prop, Q : Prop\n  |- P and Q -> Q and P\n\nsorry\n",
    "answer": "thm and_swap :\n  P : Prop, Q : Prop\n  |- P and Q -> Q and P\n\nassume h : P and Q\n  h.right, h.left\n"
  },
  {
    "title": "5. 「または」",
    "blocks": [
      {
        "p": "**ねらい**：「$P$ または $Q$」（$P \\lor Q$）を**示す**には、どちらを示すか選ぶ（`choose left` / `choose right`）。$P \\lor Q$ の仮定を**使う**には、場合分けする（`cases`）。"
      },
      {
        "paper": [
          "**定理**　$P$ または $Q$ ならば、$Q$ または $P$。",
          "**証明**　$P$ の場合は右側、$Q$ の場合は左側を示せばよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm or_swap :\n  P : Prop, Q : Prop, h : P or Q\n  |- Q or P\n\ncases h\n  Case left hp\n    choose right\n    hp\n  Case right hq\n    choose left\n    hq"
      },
      {
        "steps": [
          [
            "cases h",
            "$h$ で場合分けする"
          ],
          [
            "Case left hp",
            "$P$ の場合。そのとき分かっていること（$P$）に $hp$ と名前を付ける"
          ],
          [
            "choose right",
            "示したい $Q \\lor P$ のうち、右（$P$）を示すと決める"
          ],
          [
            "hp",
            "$P$ は $hp$ そのもの"
          ]
        ]
      },
      {
        "type": [
          [
            "or",
            "∨（または）"
          ],
          [
            "cases h",
            "場合分け。下に `Case left …` と `Case right …` を同じ字下げで"
          ]
        ]
      }
    ],
    "task": "$P \\lor Q$、$P \\to R$、$Q \\to R$ から $R$ を示す。",
    "hints": [
      "`cases h` で 2 つの場合に分ける。",
      "左の場合は `f(hp)`、右の場合は `g(hq)`。"
    ],
    "exercise": "-- 練習 5：場合分け\n\nthm or_elim :\n  P : Prop, Q : Prop, R : Prop, h : P or Q, f : P -> R, g : Q -> R\n  |- R\n\nsorry\n",
    "answer": "thm or_elim :\n  P : Prop, Q : Prop, R : Prop, h : P or Q, f : P -> R, g : Q -> R\n  |- R\n\ncases h\n  Case left hp\n    f(hp)\n  Case right hq\n    g(hq)\n"
  },
  {
    "title": "6. 「すべての」",
    "blocks": [
      {
        "p": "**ねらい**：「すべての $x$ について …」（$\\forall x$）を**示す**には、$x$ を 1 つ任意にとって（`Fix x`）、その $x$ で示す。**使う**ときは、具体的な値を入れる（`h(3)` のように）。"
      },
      {
        "paper": [
          "**定理**　すべての実数 $x$ について $x + 1 > x$。",
          "**証明**　$x$ を任意にとる。$x + 1 > x$ は明らか。$\\blacksquare$"
        ]
      },
      {
        "code": "thm add_one :\n  |- forall x:Real. x + 1 > x\n\nFix x\n  linarith"
      },
      {
        "steps": [
          [
            "Fix x",
            "「$x$ を任意にとって固定する」。ここから先、示すべきものは $x + 1 > x$"
          ],
          [
            "linarith",
            "その $x$ について示す"
          ]
        ]
      },
      {
        "p": "**使う**例：「すべての $x$ で $f(x) \\ge 0$」という仮定 $h$ があれば、`h(2)` が「$f(2) \\ge 0$」の根拠になります。"
      },
      {
        "type": [
          [
            "forall x:Real.",
            "∀x ∈ ℝ,（すべての実数 x について）。`forall` は空白を打つと ∀ になる"
          ]
        ]
      }
    ],
    "task": "すべての $x$ で $f(x) \\ge 0$ のとき、$f(2) + 1 > 0$ を示す。",
    "hints": [
      "まず「$f(2) \\ge 0$」を書き留める：`k : f(2) >= 0 by h(2)`。",
      "あとは `linarith`。"
    ],
    "exercise": "-- 練習 6：すべての を使う\n\nthm f_two :\n  f : Real -> Real, h : forall x:Real. f(x) >= 0\n  |- f(2) + 1 > 0\n\nsorry\n",
    "answer": "thm f_two :\n  f : Real -> Real, h : forall x:Real. f(x) >= 0\n  |- f(2) + 1 > 0\n\nk : f(2) >= 0 by h(2)\nlinarith\n"
  },
  {
    "title": "7. 「ある」",
    "blocks": [
      {
        "p": "**ねらい**：「… となる $x$ がある」（$\\exists x$）を**示す**には、例を 1 つ挙げる（`choose 2` のように）。仮定の「ある」を**使う**には、その $x$ を取り出す（`Obtain`）。"
      },
      {
        "paper": [
          "**定理**　$x + 3 = 5$ となる実数 $x$ がある。",
          "**証明**　$x = 2$ とすればよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm solve :\n  |- exists x:Real. x + 3 = 5\n\nchoose 2\nring"
      },
      {
        "steps": [
          [
            "choose 2",
            "例として $x = 2$ を挙げる。示すべきものは $2 + 3 = 5$ になる"
          ],
          [
            "ring",
            "計算で確かめる"
          ]
        ]
      },
      {
        "p": "**使う**例：仮定 $h$ が「$a > 5$ となる $a$ がある」なら、`Obtain a, ha : h` でその $a$ と性質 $ha : a > 5$ が手に入ります。"
      },
      {
        "type": [
          [
            "exists x:Real.",
            "∃x ∈ ℝ,（ある実数 x が存在して）"
          ],
          [
            "choose 2",
            "例として 2 を挙げる"
          ],
          [
            "Obtain a, ha : h",
            "h から a と、a の性質 ha を取り出す"
          ]
        ]
      }
    ],
    "task": "「$x > 5$ となる $x$ がある」ならば「$y > 4$ となる $y$ がある」。",
    "hints": [
      "まず `Obtain a, ha : h` で $a$ と $ha : a > 5$ を取り出す。",
      "例として同じ $a$ を挙げる（`choose a`）。あとは `linarith`。"
    ],
    "exercise": "-- 練習 7：ある を使って、ある を示す\n\nthm exists_gt :\n  h : exists x:Real. x > 5\n  |- exists y:Real. y > 4\n\nsorry\n",
    "answer": "thm exists_gt :\n  h : exists x:Real. x > 5\n  |- exists y:Real. y > 4\n\nObtain a, ha : h\nchoose a\nlinarith\n"
  },
  {
    "title": "8. ε を任意にとる（大学の入口）",
    "blocks": [
      {
        "p": "**ねらい**：大学の解析で最もよく出る形「任意の $\\varepsilon > 0$ に対して …」を書く。$\\forall \\varepsilon > 0$ は「$\\varepsilon$ を任意にとり、$\\varepsilon > 0$ と仮定する」の 2 つをまとめたもの。"
      },
      {
        "paper": [
          "**定理**　任意の $\\varepsilon > 0$ に対し、$\\delta < \\varepsilon$ となる $\\delta > 0$ がある。",
          "**証明**　$\\varepsilon > 0$ を任意にとる。$\\delta = \\varepsilon/2$ とすればよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith"
      },
      {
        "steps": [
          [
            "Fix eps | h_{eps} : eps > 0",
            "$\\varepsilon$ を任意にとり、$\\varepsilon > 0$ という仮定に名前 $h_\\varepsilon$ を付ける"
          ],
          [
            "choose eps/2, linarith",
            "$\\delta$ として $\\varepsilon/2$ を挙げる。`,` の後ろは「$\\varepsilon/2 > 0$」の根拠"
          ],
          [
            "linarith",
            "残りの $\\varepsilon/2 < \\varepsilon$"
          ]
        ]
      },
      {
        "type": [
          [
            "eps",
            "ε（空白を打つと変わる）。`delta` は δ"
          ],
          [
            "h_{eps}",
            "添字つきの名前 $h_\\varepsilon$。`_` で添字の欄ができる"
          ],
          [
            "/",
            "分数（直前の項が分子になる）"
          ]
        ]
      }
    ],
    "task": "上の half_pos を、見ないで書いてみる。",
    "hints": [
      "`Fix eps | h_{eps} : eps > 0` で始める。",
      "$\\delta$ として $\\varepsilon/2$ を選ぶと、$> 0$ も $< \\varepsilon$ も `linarith` で出る。"
    ],
    "exercise": "-- 練習 8：ε を任意にとる\n\nthm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nsorry\n",
    "answer": "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith\n"
  },
  {
    "title": "9. 数列の極限",
    "blocks": [
      {
        "p": "**ねらい**：数列 $a_n$ が $\\alpha$ に収束する（$\\varepsilon$-$N$ 論法）を `def` で定義し、使う。数列は $a : \\mathbb{N} \\to \\mathbb{R}$ と宣言すると $a_n$ と書ける。"
      },
      {
        "code": "def is_lim(a : Nat -> Real, alpha : Real) :=\n  forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\nnotation a -> alpha (n -> \\infty) := is_lim((n : Nat |-> a), alpha)"
      },
      {
        "p": "読み方：「任意の $\\varepsilon > 0$ に対し、ある $N$ があって、$n \\ge N$ なら $|a_n - \\alpha| < \\varepsilon$」。"
      },
      {
        "p": "2 行目の `notation` は**略記**：`is_lim(a, alpha)` を、教科書と同じ $a_n \\to \\alpha\\ (n \\to \\infty)$ の形で書けるようにする。右辺の $(n \\mapsto a)$ の $n$ は束縛変数なので、使うときはどの文字でもよい（$a_k \\to \\alpha\\ (k \\to \\infty)$）。$a$ の所には $n$ を含む式が入るので、$a_{n+1} \\to \\alpha\\ (n \\to \\infty)$ も書ける。"
      },
      {
        "paper": [
          "**定理**　$a_n \\to \\alpha$ ならば $a_{n+1} \\to \\alpha$。",
          "**証明**　$\\varepsilon > 0$ をとる。$n \\ge N$ で $|a_n - \\alpha| < \\varepsilon$ となる $N$ をとる。$n \\ge N$ なら $n + 1 \\ge N$ なので、$|a_{n+1} - \\alpha| < \\varepsilon$。$\\blacksquare$"
        ]
      },
      {
        "steps": [
          [
            "Fix eps | h_{eps} : eps > 0",
            "$\\varepsilon > 0$ をとる（定義は自動で開かれる）"
          ],
          [
            "Obtain N, hN : h(eps, h_{eps})",
            "仮定 $h$ に $\\varepsilon$ と $h_\\varepsilon$ を渡すと「ある $N$ が…」が出る。その $N$ を取り出す"
          ],
          [
            "choose N",
            "同じ $N$ を挙げる"
          ],
          [
            "Fix n | h_n : n >= N",
            "$n \\ge N$ をとる"
          ],
          [
            "k : n + 1 >= N by linarith",
            "$n + 1 \\ge N$ を書き留める"
          ],
          [
            "hN(n + 1, k)",
            "$hN$ を $n + 1$ で使う"
          ]
        ]
      },
      {
        "type": [
          [
            "a_n, a_{n+1}",
            "数列の項 $a_n$・$a_{n+1}$"
          ],
          [
            "abs( ) または |x|",
            "絶対値"
          ],
          [
            "a_{n+1} -> alpha (n -> \\infty)",
            "$a_{n+1} \\to \\alpha\\ (n \\to \\infty)$。`->` は →、`\\infty` は ∞"
          ],
          [
            "(n:Nat |-> a_{n+1})",
            "「$n$ を $a_{n+1}$ に移す数列」そのもの。`|->` は ↦（略記の右辺で使う）"
          ]
        ]
      }
    ],
    "task": "上の証明を書く。",
    "hints": [
      "形は練習 8 と同じ。$N$ は $h$ から `Obtain` で取り出したものを、そのまま使う。",
      "最後に要るのは $|a_{n+1} - \\alpha| < \\varepsilon$。$hN$ は「$n + 1 \\ge N$」の根拠があれば $n + 1$ で使える。"
    ],
    "exercise": "-- 練習 9：1 つずらした数列の極限\n\ndef is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\nnotation a -> alpha (n -> \\infty) := is_lim((n : Nat |-> a), alpha)\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : a_n -> alpha (n -> \\infty)\n  |- a_{n+1} -> alpha (n -> \\infty)\n\nsorry\n",
    "answer": "def is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\nnotation a -> alpha (n -> \\infty) := is_lim((n : Nat |-> a), alpha)\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : a_n -> alpha (n -> \\infty)\n  |- a_{n+1} -> alpha (n -> \\infty)\n\nFix eps | h_{eps} : eps > 0\n  Obtain N, hN : h(eps, h_{eps})\n  choose N\n  Fix n | h_n : n >= N\n    k : n + 1 >= N by linarith\n    hN(n + 1, k)\n"
  },
  {
    "title": "10. 背理法",
    "blocks": [
      {
        "p": "**ねらい**：「$P$ でないと仮定して矛盾を導く」（背理法）。`by_contra hn` で「$P$ でない」を仮定し、矛盾（$\\bot$）を示す。"
      },
      {
        "paper": [
          "**定理**　「$P$ でない、ということはない」ならば $P$。",
          "**証明**　$P$ でないと仮定する。これは仮定に矛盾する。$\\blacksquare$"
        ]
      },
      {
        "code": "thm dne :\n  P : Prop, h : not not P\n  |- P\n\nby_contra hn\n  h(hn)"
      },
      {
        "steps": [
          [
            "by_contra hn",
            "「$P$ でない」と仮定し、名前 $hn$ を付ける。示すべきものは矛盾（$\\bot$）"
          ],
          [
            "h(hn)",
            "「$P$ でない、ということはない」は「$P$ でないなら矛盾」という意味。$hn$ を渡すと矛盾になる"
          ]
        ]
      },
      {
        "p": "「でない」（$\\lnot P$）は Narfi の中では「$P$ ならば矛盾」（$P \\to \\bot$）として扱われます。だから「$P$ でない」を示すには `assume p : P` として矛盾を示し、使うには `hn(p)` と $P$ の根拠を渡します。"
      },
      {
        "type": [
          [
            "not",
            "¬（でない）"
          ],
          [
            "by_contra hn",
            "背理法：結論の否定を hn として仮定する"
          ]
        ]
      }
    ],
    "task": "$P$ ならば「$P$ でない、ということはない」。",
    "hints": [
      "示すのは $\\lnot\\lnot P$、つまり「$\\lnot P$ ならば矛盾」。`assume hn : not P`。",
      "$hn$ に $P$ の根拠 $h$ を渡すと矛盾：`hn(h)`。"
    ],
    "exercise": "-- 練習 10：でない、ということはない\n\nthm dni :\n  P : Prop, h : P\n  |- not not P\n\nsorry\n",
    "answer": "thm dni :\n  P : Prop, h : P\n  |- not not P\n\nassume hn : not P\n  hn(h)\n"
  },
  {
    "title": "11. エディタの使い方",
    "blocks": [
      {
        "keys": [
          [
            "\\fr + Tab, /",
            "分数"
          ],
          [
            "_ , ^",
            "添字・上付き"
          ],
          [
            "abs( ) , |x|",
            "絶対値"
          ],
          [
            "<= >= != -> <->",
            "≤ ≥ ≠ → ↔"
          ],
          [
            "\\|- , \\vdash",
            "⊢"
          ],
          [
            "|-> , \\mapsto",
            "↦"
          ],
          [
            "forall exists eps …",
            "∀ ∃ ε …（空白で変換）"
          ],
          [
            "\\ + 名前",
            "記号の補完（Tab か Enter で決定）"
          ],
          [
            "Tab（行末）",
            "エラーに出た直し方・根拠の候補を入れる"
          ],
          [
            "Tab / Shift+Tab（複数行を選んで）",
            "まとめて字下げ・戻す"
          ],
          [
            "ダブルクリック",
            "名前（添字ごと）を選ぶ"
          ],
          [
            "⌥ + ←→",
            "単語ごとに動く"
          ],
          [
            "⌘S / ⌘Z",
            "保存 / 元に戻す"
          ]
        ]
      },
      {
        "p": "右の **Goal** タブには、カーソルの行で使える仮定と、示すべきものが出ます。困ったら「次の一手」のボタンを押すと、いま書けるものが入ります。"
      },
      {
        "p": "**Prose** タブで証明が文章として、**LaTeX** タブで論文に貼れる形で読めます。下の `JA` を押すと、エディタの中も日本語の証明文の形になります（ファイルは変わりません）。言語は Preferences（右上のアイコンのメニュー、または ⌘,）で選べます。"
      },
      {
        "p": "証明の行を右クリック →「証明木を見る」で、証明が論理の規則（自然演繹）の組み合わせとしてどう組み立てられているかが見られます。"
      }
    ]
  },
  {
    "title": "付録：早見表",
    "blocks": [
      {
        "p": "証明は「いま示すべきもの」（Goal タブの ⊢ の右）の形を見て、1 行ずつ書きます。"
      },
      {
        "h": "示すべきものの形で選ぶ"
      },
      {
        "keys": [
          [
            "∀x. φ（すべての）",
            "Fix x（条件つき ∀ε>0 なら Fix ε | hε : ε > 0）"
          ],
          [
            "φ → ψ（ならば）、¬φ",
            "assume h : φ"
          ],
          [
            "φ ∧ ψ（かつ）",
            "根拠1, 根拠2"
          ],
          [
            "φ ∨ ψ（または）",
            "choose left / choose right"
          ],
          [
            "∃x. φ（ある）",
            "choose 例"
          ],
          [
            "= < ≤",
            "ring・linarith・式変形の連鎖"
          ],
          [
            "何でも",
            "by_contra h（背理法）、根拠 1 つで閉じる"
          ]
        ]
      },
      {
        "h": "仮定の形で選ぶ"
      },
      {
        "keys": [
          [
            "h : ∃x. φ",
            "Obtain x, hx : h"
          ],
          [
            "h : φ ∨ ψ",
            "cases h（Case left h1 / Case right h2）"
          ],
          [
            "h : φ ∧ ψ",
            "h.left・h.right"
          ],
          [
            "h : ∀x. φ",
            "h(具体的な値)"
          ],
          [
            "h : φ → ψ",
            "h(φ の根拠)"
          ]
        ]
      },
      {
        "h": "途中で分かったことを書き留める"
      },
      {
        "p": "`名前 : 命題 by 根拠`。根拠が長ければ `名前 : 命題` の下に字下げして書く。"
      },
      {
        "p": "書き方の完全な一覧は [docs/language/syntax.md](https://github.com/Narfidort/Narfi/blob/main/docs/language/syntax.md)。"
      }
    ]
  }
];
