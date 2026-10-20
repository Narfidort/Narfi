// Narfi のチュートリアル（エディタ右側の Learn タブ）。
// 各レッスン：本文（p・paper：紙の証明・code・steps：1 行ずつ・check：確かめよう・pitfalls：よくあるつまずき・keys・h）、
// 練習（task・hints・exercise・answer）。答えが通ることは tests/ui.rs（tutorial_answers_check）で確かめる。
// このファイルは手で直してよい。

window.NARFI_TUTORIAL = [
  {
    "title": "1. はじめての証明と画面の見方",
    "blocks": [
      {
        "p": "**ねらい**：定理の形（仮定 ⊢ 結論）と、証明が「通る」とはどういうことかを知る。画面のどこを見ればよいかを覚える。"
      },
      {
        "paper": [
          "**定理**　命題 $P$ が成り立つと仮定する。このとき $P$ が成り立つ。",
          "**証明**　仮定そのものである。$\\blacksquare$"
        ]
      },
      {
        "code": "thm first :\n  P : Prop, h : P\n  |- P\n\nh"
      },
      {
        "steps": [
          [
            "thm first :",
            "定理の名前は first。名前には英数字と `.`・`_` が使える"
          ],
          [
            "  P : Prop, h : P",
            "仮定の並び。$P$ は命題（`Prop`）、$h$ は「$P$ が成り立つ」という仮定の名前"
          ],
          [
            "  |- P",
            "`⊢` の右が示すこと（結論）。`|-` と打つ（エディタでは `\\|-` で ⊢ が入る）"
          ],
          [
            "h",
            "証明。結論 $P$ は仮定 $h$ そのものなので、名前 `h` を書くだけで閉じる"
          ]
        ]
      },
      {
        "check": "「練習を開く」で開いたら、最後の `sorry` の行にカーソルを置き、右の **Goal** タブを見る。文脈に $h : P$、下に $\\vdash P$（示すべきもの）が出ている。`sorry` を `h` に書き換えると、右上が **1 theorem verified** になる。"
      },
      {
        "pitfalls": [
          [
            "右上が「1 incomplete」（黄色）",
            "`sorry` が残っている。`sorry` は「あとで書く」の印で、そこを埋めると通る"
          ],
          [
            "「`k` が見つからない」",
            "名前の打ち間違い。Goal タブの文脈にある名前（ここでは `h`）を使う"
          ]
        ]
      },
      {
        "p": "困ったら Goal タブの **次の一手** を見る。いま書けるものがボタンで出ていて、押すとその行に入る。"
      }
    ],
    "task": "`sorry` を消して、証明を書く。",
    "hints": [
      "Goal タブで、示すべきもの（$\\vdash$ の右）と、文脈の仮定を見比べる。",
      "示すべき $P$ が、仮定 `h : P` とまったく同じ。名前を 1 つ書けば閉じる。"
    ],
    "exercise": "-- 練習 1：sorry を消して証明を書く\n\nthm first :\n  P : Prop, h : P\n  |- P\n\nsorry\n",
    "answer": "thm first :\n  P : Prop, h : P\n  |- P\n\nh\n"
  },
  {
    "title": "2. ならば（→）：仮定する・当てはめる",
    "blocks": [
      {
        "p": "**ねらい**：$P \\to Q$ を**示す**には $P$ を仮定する（`assume`）。$P \\to Q$ を**使う**には $P$ の根拠を渡す（`f(p)`）。"
      },
      {
        "paper": [
          "**定理**　$P \\to Q$ かつ $Q \\to R$ ならば $P \\to R$。",
          "**証明**　$P$ を仮定する（$p$）。$f$ より $Q$ が成り立つ。$g$ より $R$ が成り立つ。$\\blacksquare$"
        ]
      },
      {
        "code": "thm imp_trans :\n  P : Prop, Q : Prop, R : Prop, f : P -> Q, g : Q -> R\n  |- P -> R\n\nassume p : P\n  q : Q by f(p)\n  g(q)"
      },
      {
        "steps": [
          [
            "assume p : P",
            "→ を剥がす。$P$ を仮定し、名前を $p$ にする。ここから先（字下げした所）の Goal は $R$ になる"
          ],
          [
            "  q : Q by f(p)",
            "$f : P \\to Q$ に $p : P$ を渡すと $Q$ が出る（→ の除去）。それに名前 $q$ を付けて覚える"
          ],
          [
            "  g(q)",
            "$g : Q \\to R$ に $q$ を渡すと $R$。Goal と同じなので閉じる"
          ]
        ]
      },
      {
        "p": "字下げが「仮定 $p$ が使える範囲」。`assume` の下を字下げして書く。"
      },
      {
        "check": "`q : Q by f(p)` の行にカーソルを置くと、Goal タブの文脈に $p : P$ があり、示すべきものが $R$ になっている。"
      },
      {
        "pitfalls": [
          [
            "「仮定 p の中身が書かれていない」",
            "`assume p` だけでは何を仮定したか読めない。`: P` を書く（行末で Tab を押すと入る）"
          ],
          [
            "「根拠 g(p) が示すのは … だが、必要なのは …」",
            "$g$ に渡せるのは $Q$ の根拠。$p$ は $P$ の根拠なので、先に $f(p)$ で $Q$ を作る"
          ]
        ]
      }
    ],
    "task": "$P \\to (Q \\to P)$ を示す（$Q$ は使わなくてよい）。",
    "hints": [
      "→ が 2 つある。外側の → を `assume p : P` で剥がすと、Goal は $Q \\to P$ になる。",
      "もう 1 回 `assume q : Q` で剥がすと Goal は $P$。手元に $p : P$ がある。"
    ],
    "exercise": "-- 練習 2：P → (Q → P)\n\nthm k_comb :\n  P : Prop, Q : Prop\n  |- P -> (Q -> P)\n\nsorry\n",
    "answer": "thm k_comb :\n  P : Prop, Q : Prop\n  |- P -> (Q -> P)\n\nassume p : P\n  assume q : Q\n    p\n"
  },
  {
    "title": "3. かつ（∧）：取り出す・まとめる",
    "blocks": [
      {
        "p": "**ねらい**：$P \\land Q$ の仮定 $h$ から `h.left`（$P$）・`h.right`（$Q$）を取り出す。$P \\land Q$ を示すには 2 つの根拠を `,` で並べる。"
      },
      {
        "paper": [
          "**定理**　$P \\land Q$ ならば $Q \\land P$。",
          "**証明**　$P \\land Q$ を仮定する。そこから $Q$ と $P$ がわかる。よって $Q \\land P$。$\\blacksquare$"
        ]
      },
      {
        "code": "thm and_swap :\n  P : Prop, Q : Prop\n  |- P and Q -> Q and P\n\nassume h : P and Q\n  q : Q by h.right\n  p : P by h.left\n  Q and P by q, p"
      },
      {
        "steps": [
          [
            "assume h : P and Q",
            "→ を剥がす。`and` と打つと ∧"
          ],
          [
            "  q : Q by h.right",
            "∧ の右側を取り出す（∧ の除去）"
          ],
          [
            "  p : P by h.left",
            "∧ の左側"
          ],
          [
            "  Q and P by q, p",
            "2 つの根拠を並べると ∧ ができる（∧ の導入）。最後の行なので Goal と同じことを確かめて閉じる"
          ]
        ]
      },
      {
        "p": "途中の行 `q : Q by h.right` は「事実の行」：示したことに名前を付けて、あとで使えるようにする。紙の「よって $Q$（これを $q$ とする）」にあたる。"
      },
      {
        "check": "右クリック →「証明木を見る」で、∧E と ∧I が使われた自然演繹の木が見られる。"
      },
      {
        "pitfalls": [
          [
            "「根拠が書かれていない」",
            "事実の行には `by 根拠` が要る。エラーに出た候補（`by h.right` など）を Tab で入れられる"
          ]
        ]
      }
    ],
    "task": "$P \\land (Q \\land R)$ から $(P \\land Q) \\land R$ を示す。",
    "hints": [
      "`assume h : P and (Q and R)` のあと、`h.left` が $P$、`h.right` が $Q \\land R$。",
      "$Q \\land R$ からさらに `.left`・`.right` で $Q$ と $R$ を取り出せる（いったん名前を付けると楽）。",
      "最後は `(P and Q) and R by (p, q), r` のように、まとめを入れ子にする。"
    ],
    "exercise": "-- 練習 3：∧ の組み替え\n\nthm and_assoc :\n  P : Prop, Q : Prop, R : Prop\n  |- P and (Q and R) -> (P and Q) and R\n\nsorry\n",
    "answer": "thm and_assoc :\n  P : Prop, Q : Prop, R : Prop\n  |- P and (Q and R) -> (P and Q) and R\n\nassume h : P and (Q and R)\n  qr : Q and R by h.right\n  pq : P and Q by h.left, qr.left\n  (P and Q) and R by pq, qr.right\n"
  },
  {
    "title": "4. または（∨）：選ぶ・場合分けする",
    "blocks": [
      {
        "p": "**ねらい**：$P \\lor Q$ を**示す**には、どちらを示すかを `choose left`・`choose right` で選ぶ。$P \\lor Q$ を**使う**には `cases` で場合分けする。"
      },
      {
        "paper": [
          "**定理**　$P \\lor Q$ ならば $Q \\lor P$。",
          "**証明**　$P$ の場合、右側の $P$ を示せばよい。$Q$ の場合、左側の $Q$ を示せばよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm or_swap :\n  P : Prop, Q : Prop, h : P or Q\n  |- Q or P\n\ncases h\n  Case left hp\n    choose right\n    hp\n  Case right hq\n    choose left\n    hq"
      },
      {
        "steps": [
          [
            "cases h",
            "$h : P \\lor Q$ で場合分け。下に 2 つの場合を書く"
          ],
          [
            "  Case left hp",
            "$P$ の場合。その仮定の名前が $hp$"
          ],
          [
            "    choose right",
            "Goal $Q \\lor P$ の右側（$P$）を示すと決める。Goal が $P$ になる"
          ],
          [
            "    hp",
            "$P$ は $hp$ そのもの"
          ],
          [
            "  Case right hq",
            "$Q$ の場合"
          ]
        ]
      },
      {
        "check": "`Case left hp` の下の行で Goal タブを見ると、文脈に $hp : P$ がある。`Case right hq` の下では $hq : Q$。"
      },
      {
        "pitfalls": [
          [
            "「Case left か Case right が必要」",
            "`cases` の下には、2 つの場合をちょうど同じ字下げで書く"
          ]
        ]
      }
    ],
    "task": "$P \\lor Q$ と $P \\to R$、$Q \\to R$ から $R$ を示す（場合分けの基本形）。",
    "hints": [
      "`cases h` で 2 つの場合に分ける。",
      "左の場合は `f(hp)`、右の場合は `g(hq)` で $R$ が出る。"
    ],
    "exercise": "-- 練習 4：場合分け\n\nthm or_elim :\n  P : Prop, Q : Prop, R : Prop, h : P or Q, f : P -> R, g : Q -> R\n  |- R\n\nsorry\n",
    "answer": "thm or_elim :\n  P : Prop, Q : Prop, R : Prop, h : P or Q, f : P -> R, g : Q -> R\n  |- R\n\ncases h\n  Case left hp\n    f(hp)\n  Case right hq\n    g(hq)\n"
  },
  {
    "title": "5. すべての（∀）：任意にとる・代入する",
    "blocks": [
      {
        "p": "**ねらい**：$\\forall x.\\ \\varphi(x)$ を**示す**には、$x$ を任意にとって固定し（`Fix x`）、$\\varphi(x)$ を示す。$\\forall$ を**使う**には、具体的なものを代入する（`h(t)`）。これが「量化子を剥がす」操作。"
      },
      {
        "paper": [
          "**定理**　すべての $x$ で $P(x) \\to Q(x)$、すべての $x$ で $P(x)$ ならば、すべての $x$ で $Q(x)$。",
          "**証明**　$x$ を任意にとる。$P(x)$ が成り立つので、$Q(x)$ が成り立つ。$\\blacksquare$"
        ]
      },
      {
        "code": "thm all_mp :\n  P : Nat -> Prop, Q : Nat -> Prop,\n  f : forall x:Nat. P(x) -> Q(x), h : forall x:Nat. P(x)\n  |- forall x:Nat. Q(x)\n\nFix x\n  px : P(x) by h(x)\n  f(x, px)"
      },
      {
        "steps": [
          [
            "Fix x",
            "∀ を剥がす。$x$ を任意にとる。Goal は $Q(x)$ になる"
          ],
          [
            "  px : P(x) by h(x)",
            "$h$ の $\\forall$ に $x$ を代入（∀ の除去）"
          ],
          [
            "  f(x, px)",
            "$f$ に $x$ を代入し、続けて $P(x)$ の根拠 $px$ を渡す。引数は ∀ と → の順に並べる"
          ]
        ]
      },
      {
        "check": "`Fix x` の次の行で Goal タブを見ると、文脈に $x \\in \\mathbb{N}$（Fix）があり、Goal が $Q(x)$。"
      },
      {
        "pitfalls": [
          [
            "「Fix できない：goal は ∀ の形ではない」",
            "Goal が ∀ のときだけ `Fix` が使える。Goal タブで形を確かめる"
          ]
        ]
      }
    ],
    "task": "すべての $x$ で $P(x) \\land Q(x)$ ならば、すべての $x$ で $P(x)$。",
    "hints": [
      "まず `Fix x`。",
      "`h(x)` が $P(x) \\land Q(x)$。その左側が欲しい。"
    ],
    "exercise": "-- 練習 5：∀ と ∧\n\nthm all_left :\n  P : Nat -> Prop, Q : Nat -> Prop, h : forall x:Nat. P(x) and Q(x)\n  |- forall x:Nat. P(x)\n\nsorry\n",
    "answer": "thm all_left :\n  P : Nat -> Prop, Q : Nat -> Prop, h : forall x:Nat. P(x) and Q(x)\n  |- forall x:Nat. P(x)\n\nFix x\n  pq : P(x) and Q(x) by h(x)\n  pq.left\n"
  },
  {
    "title": "6. ある（∃）：例を挙げる・取り出す",
    "blocks": [
      {
        "p": "**ねらい**：$\\exists x.\\ \\varphi(x)$ を**示す**には、例 $t$ を挙げて（`choose t`）$\\varphi(t)$ を示す。仮定の $\\exists$ を**使う**には、その $x$ と性質を取り出す（`Obtain x, hx : e`）。"
      },
      {
        "paper": [
          "**定理**　$P(x)$ となる $x$ があり、すべての $x$ で $P(x) \\to Q(x)$ ならば、$Q(x)$ となる $x$ がある。",
          "**証明**　$P(a)$ となる $a$ をとる。すると $Q(a)$。よって $a$ が例になる。$\\blacksquare$"
        ]
      },
      {
        "code": "thm ex_mp :\n  P : Nat -> Prop, Q : Nat -> Prop,\n  e : exists x:Nat. P(x), f : forall x:Nat. P(x) -> Q(x)\n  |- exists x:Nat. Q(x)\n\nObtain a, ha : e\nchoose a\nf(a, ha)"
      },
      {
        "steps": [
          [
            "Obtain a, ha : e",
            "$e$ から、$P(a)$ となる $a$ と、その性質 $ha : P(a)$ を取り出す（∃ の除去）"
          ],
          [
            "choose a",
            "Goal $\\exists x.\\ Q(x)$ の例として $a$ を挙げる（∃ の導入）。Goal は $Q(a)$ になる"
          ],
          [
            "f(a, ha)",
            "$Q(a)$ の根拠"
          ]
        ]
      },
      {
        "check": "`choose a` の次の行で、Goal が $Q(a)$ になっている。"
      },
      {
        "pitfalls": [
          [
            "`choose 0` などで別の値を挙げてしまう",
            "その値で $\\varphi$ が示せなくなる。Goal タブで、何を示すことになったかを確かめる"
          ]
        ]
      }
    ],
    "task": "どんな自然数 $n$ にも、$m = n + n$ となる $m$ がある。",
    "hints": [
      "`Fix n` のあと、例として何を挙げればよいか考える。",
      "`choose n + n` とすると、Goal は $n + n = n + n$。`refl`（反射律）で閉じる。"
    ],
    "exercise": "-- 練習 6：∃ の例を挙げる\n\nthm double :\n  |- forall n:Nat. exists m:Nat. m = n + n\n\nsorry\n",
    "answer": "thm double :\n  |- forall n:Nat. exists m:Nat. m = n + n\n\nFix n\n  choose n + n\n  refl\n"
  },
  {
    "title": "7. 計算：式変形の連鎖",
    "blocks": [
      {
        "p": "**ねらい**：等式・不等式は、紙と同じように縦に並べて変形する。各行の `by` の右がその一歩の根拠。計算は `ring`（多項式として等しい）・`linarith`（仮定からの一次不等式）に任せられる。"
      },
      {
        "paper": [
          "$a \\le b$ のとき　$a + 1 \\le b + 1 \\le b + 2$。"
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
            "  <= b + 1   by linarith",
            "1 歩目。$h : a \\le b$ から一次不等式で出る"
          ],
          [
            "  <= b + 2   by linarith",
            "2 歩目。最後の式まで来たら、全体として $a + 1 \\le b + 2$ が示された"
          ]
        ]
      },
      {
        "p": "**根拠がわからないとき**：`by …` を書かずに `<= b + 1` とだけ書くと、エラーになり、検査器が見つけた根拠の候補（`by linarith` など）が出る。行末で Tab を押すと入る。検査器が勝手に補うことはない。"
      },
      {
        "check": "`<= b + 1` の行の `by linarith` を消すと、Goal タブに「根拠の候補」のボタンが出る。"
      },
      {
        "pitfalls": [
          [
            "「連鎖の中で不等号の向きが混ざっている」",
            "$\\le$ と $\\ge$ を 1 つの連鎖に混ぜない。向きをそろえる"
          ]
        ]
      }
    ],
    "task": "$x \\le y$、$y < z$ から $x < z$ を、連鎖で示す。",
    "hints": [
      "`x` から始めて、`<= y` と `< z` の 2 段。",
      "根拠は仮定そのもの（`by h`・`by k`）。"
    ],
    "exercise": "-- 練習 7：式変形の連鎖\n\nthm chain2 :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nsorry\n",
    "answer": "thm chain2 :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nx\n  <= y   by h\n  < z    by k\n"
  },
  {
    "title": "8. ε を任意にとる",
    "blocks": [
      {
        "p": "**ねらい**：解析でいちばん使う形 $\\forall \\varepsilon > 0.\\ \\cdots$ を扱う。これは $\\forall \\varepsilon.\\ \\varepsilon > 0 \\to \\cdots$ の略記なので、`Fix ε | hε : ε > 0` で ∀ と → を一度に剥がす。"
      },
      {
        "paper": [
          "**定理**　任意の $\\varepsilon > 0$ に対し、$\\delta < \\varepsilon$ となる $\\delta > 0$ がある。",
          "**証明**　$\\varepsilon > 0$ を任意にとる。$\\delta = \\varepsilon / 2$ とすればよい。$\\blacksquare$"
        ]
      },
      {
        "code": "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith"
      },
      {
        "steps": [
          [
            "Fix eps | h_{eps} : eps > 0",
            "$\\varepsilon$ と仮定 $h_\\varepsilon : \\varepsilon > 0$ を導入。`eps` は ε と表示される"
          ],
          [
            "  choose eps/2, linarith",
            "$\\delta$ として $\\varepsilon/2$ を挙げる。`,` の後ろは「$\\varepsilon/2 > 0$」の根拠"
          ],
          [
            "  linarith",
            "残った Goal $\\varepsilon/2 < \\varepsilon$ を一次不等式で"
          ]
        ]
      },
      {
        "check": "`choose eps/2, linarith` の次の行で、Goal が $\\varepsilon/2 < \\varepsilon$ になっている。"
      }
    ],
    "task": "上の half_pos を、自分で書いてみる。",
    "hints": [
      "`Fix eps | h_{eps} : eps > 0` で始める。",
      "$\\delta$ として何を選ぶか。$\\varepsilon/2$ なら、$> 0$ も $< \\varepsilon$ も `linarith` で出る。"
    ],
    "exercise": "-- 練習 8：ε を任意にとる\n\nthm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nsorry\n",
    "answer": "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith\n"
  },
  {
    "title": "9. 数列と極限",
    "blocks": [
      {
        "p": "**ねらい**：定義（`def`）を使って、数列の極限を書く。数列 $a : \\mathbb{N} \\to \\mathbb{R}$ は $a_n$ と添字で書ける。定義は必要な所で自動的に開かれる。"
      },
      {
        "code": "def is_lim(a : Nat -> Real, alpha : Real) :=\n  forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps"
      },
      {
        "paper": [
          "**定理**　$a_n \\to \\alpha$ ならば $a_{n+1} \\to \\alpha$。",
          "**証明**　$\\varepsilon > 0$ をとる。$n \\ge N$ で $|a_n - \\alpha| < \\varepsilon$ となる $N$ をとる。$n \\ge N$ なら $n + 1 \\ge N$ なので $|a_{n+1} - \\alpha| < \\varepsilon$。$\\blacksquare$"
        ]
      },
      {
        "steps": [
          [
            "Fix eps | h_{eps} : eps > 0",
            "定義が開かれて、Goal の先頭が ∀ε>0 になっている"
          ],
          [
            "  Obtain N, hN : h(eps, h_{eps})",
            "仮定 $h$ に $\\varepsilon$ とその条件を渡し、$N$ を取り出す"
          ],
          [
            "  choose N",
            "同じ $N$ でよい"
          ],
          [
            "  Fix n | h_n : n >= N",
            "$n \\ge N$ をとる"
          ],
          [
            "    k : n + 1 >= N by linarith",
            "$n + 1 \\ge N$"
          ],
          [
            "    hN(n + 1, k)",
            "$hN$ を $n + 1$ で使う"
          ]
        ]
      }
    ],
    "task": "上の証明を書く（$(n \\mapsto a_{n+1})$ は「$n$ を $a_{n+1}$ に移す数列」。`|->` で ↦）。",
    "hints": [
      "形は練習 8 と同じ。$\\exists N$ は $h$ から `Obtain` で取り出した $N$ をそのまま使う。",
      "最後に必要なのは $|a_{n+1} - \\alpha| < \\varepsilon$。$hN$ は $n + 1 \\ge N$ の根拠があれば $n + 1$ で使える。"
    ],
    "exercise": "-- 練習 9：1 つずらした数列の極限\n\ndef is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : is_lim(a, alpha)\n  |- is_lim((n:Nat |-> a_{n+1}), alpha)\n\nsorry\n",
    "answer": "def is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : is_lim(a, alpha)\n  |- is_lim((n:Nat |-> a_{n+1}), alpha)\n\nFix eps | h_{eps} : eps > 0\n  Obtain N, hN : h(eps, h_{eps})\n  choose N\n  Fix n | h_n : n >= N\n    k : n + 1 >= N by linarith\n    hN(n + 1, k)\n"
  },
  {
    "title": "10. 背理法と帰納法",
    "blocks": [
      {
        "p": "**ねらい**：`by_contra h` で結論の否定 $h$ を仮定し、矛盾 $\\bot$ を示す（背理法）。自然数の性質は `induction n` で $0$ の場合と $k \\to k+1$ の場合に分ける（帰納法）。"
      },
      {
        "paper": [
          "**定理**　$\\lnot\\lnot P$ ならば $P$。",
          "**証明**　$P$ でないと仮定する。これは $\\lnot\\lnot P$ に矛盾する。$\\blacksquare$"
        ]
      },
      {
        "code": "thm dne :\n  P : Prop, h : not not P\n  |- P\n\nby_contra hn\n  h(hn)"
      },
      {
        "steps": [
          [
            "by_contra hn",
            "$hn : \\lnot P$ を仮定する。Goal は $\\bot$（矛盾）"
          ],
          [
            "  h(hn)",
            "$\\lnot\\lnot P$ は「$\\lnot P \\to \\bot$」なので、$hn$ を渡すと $\\bot$"
          ]
        ]
      },
      {
        "p": "帰納法の形：\n"
      },
      {
        "code": "induction n\n  Case zero\n    （n = 0 のときの証明）\n  Case succ k, IH : φ(k)\n    （φ(k) を仮定して φ(k + 1) の証明）"
      }
    ],
    "task": "$P$ ならば $\\lnot\\lnot P$（上の逆向き）。",
    "hints": [
      "$\\lnot\\lnot P$ は $\\lnot P \\to \\bot$。→ を剥がすので `assume hn : not P`。",
      "$hn : \\lnot P$ は $P \\to \\bot$。$P$ の根拠を渡せば $\\bot$。"
    ],
    "exercise": "-- 練習 10：二重否定の導入\n\nthm dni :\n  P : Prop, h : P\n  |- not not P\n\nsorry\n",
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
          ],
          [
            "⌘,",
            "Preferences（読みの言語）"
          ]
        ]
      },
      {
        "p": "右の **Prose** で証明が文章として、**LaTeX** で論文に貼れる形で読める。下の言語のボタン（`JA`）でエディタの中も読みの形になる（ファイルは変わらない）。言語は右下の歯車（Preferences）で選ぶ。"
      },
      {
        "p": "証明の行を右クリック →「証明木を見る」で、自然演繹の木（Gentzen 式・Fitch 式）が見られる。"
      }
    ]
  },
  {
    "title": "付録：早見表（goal の形から書き方を選ぶ）",
    "blocks": [
      {
        "p": "証明は「いま示すべきもの（Goal）」と仮定の形を見て、1 行ずつ書く。Goal タブの「次の一手」にも同じ候補が出る。"
      },
      {
        "h": "Goal の形で選ぶ（Goal を小さくする）"
      },
      {
        "keys": [
          [
            "∀x. φ",
            "Fix x（条件つき ∀ε>0 なら Fix ε | hε : ε > 0）"
          ],
          [
            "φ → ψ、¬φ",
            "assume h : φ"
          ],
          [
            "φ ∧ ψ",
            "根拠1, 根拠2"
          ],
          [
            "φ ∨ ψ",
            "choose left / choose right"
          ],
          [
            "∃x. φ",
            "choose 項"
          ],
          [
            "= < ≤",
            "ring・linarith・連鎖"
          ],
          [
            "何でも",
            "by_contra h・根拠 1 つで閉じる"
          ]
        ]
      },
      {
        "h": "仮定の形で選ぶ（仮定を使う）"
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
            "h(t)"
          ],
          [
            "h : φ → ψ",
            "h(p)（p は φ の根拠）"
          ]
        ]
      },
      {
        "h": "途中で示したことを増やす"
      },
      {
        "p": "`k : φ by 根拠`（名前は省略できる）。証明が長ければ `k : φ` の下に字下げして書く。"
      },
      {
        "p": "書き方の完全な一覧は [docs/language/syntax.md](https://github.com/Narfidort/Narfi/blob/main/docs/language/syntax.md)。"
      }
    ]
  }
];
