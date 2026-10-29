// Narfi のコース「公理へ向かって」（Learn タブの後半）。章ごとに、定理が頼る公理を減らしていく。
// 各章：本文（チュートリアルと同じ部品）・file（自分のファイルに作る：course/番号-名前.narfi。番号は章の番号）・task・hints・exercise・answer。
// 答えが通ることは tests/ui.rs（tutorial_answers_check）で確かめる。このファイルは scripts/learn/course.py で作る（直接直さない）。

window.NARFI_COURSE = [
  {
    "title": "コース 0. 限りなく近づく",
    "blocks": [
      {
        "p": "**ねらい**：数列の極限を ε-N で定義し、「収束する数列の和は、和に収束する」を証明する。チュートリアルのレッスン 12〜14 の続き（レッスン 14 で書いた和の定理を、ここでは「何に頼っているか」から見直す）。"
      },
      {
        "paper": [
          "**定理**　$a_n \\to \\alpha$、$b_n \\to \\beta$ ならば $a_n + b_n \\to \\alpha + \\beta$。",
          "**証明**　$\\varepsilon > 0$ をとる。$n \\ge N_1$ で $|a_n - \\alpha| < \\varepsilon/2$、$n \\ge N_2$ で $|b_n - \\beta| < \\varepsilon/2$ となる $N_1, N_2$ をとる。$N = \\max\\{N_1, N_2\\}$ とすると、$n \\ge N$ のとき",
          "$|(a_n + b_n) - (\\alpha + \\beta)| \\le |a_n - \\alpha| + |b_n - \\beta| < \\varepsilon/2 + \\varepsilon/2 = \\varepsilon$。$\\blacksquare$"
        ]
      },
      {
        "p": "証明で使う 4 つの事実（三角不等式・$\\varepsilon > 0$ なら $\\varepsilon/2 > 0$・$n \\ge \\max\\{N_1, N_2\\}$ なら $n \\ge N_1$ と $n \\ge N_2$）は、この章ではまだ**公理**（証明なしに認めるもの）として置く。中身は次の章から開けていく。"
      },
      {
        "steps": [
          [
            "Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))",
            "$a$ の収束の定義に $\\varepsilon/2$ を入れて $N_1$ を取り出す。`pos_half(hε)` が「$\\varepsilon/2 > 0$」の根拠"
          ],
          [
            "choose max{N_1, N_2}",
            "示す側の $N$ として $\\max\\{N_1, N_2\\}$ を挙げる"
          ],
          [
            "Fix n | hn : n ≥ max{N_1, N_2}",
            "$n \\ge N$ をとる。ここから下が、紙の証明の最後の 1 行"
          ]
        ]
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの宣言の一覧にも出る）が、その定理が頼っている公理。**このコースの目標は、章ごとにこの一覧を短く・弱くしていくこと**。最後に残るのは、数学の土台の公理だけになる。"
      }
    ],
    "file": "course/0-極限.narfi",
    "task": "最後の `sorry` を、紙の証明の最後の 1 行と同じ不等式の連鎖で埋める。",
    "hints": [
      "$|(a_n + b_n) - (\\alpha + \\beta)|$ から始める連鎖。1 段目は `= |(a_n - α) + (b_n - β)|   by ring`。",
      "2 段目は三角不等式：`≤ |a_n - α| + |b_n - β|   by triangle(a_n - α, b_n - β)`。",
      "3 段目：`< ε/2 + ε/2   by h_1(n, ge.max.left(hn)), h_2(n, ge.max.right(hn))`（$h_1$ に「$n \\ge N_1$」の根拠を渡す）。",
      "最後は `= ε   by ring`。"
    ],
    "exercise": "-- コース 0：限りなく近づく\n--\n-- 「数列 a_n が α に限りなく近づく」を ε-N で書き、和の極限を証明する。\n-- 上の 4 つの axiom は、まだ中身を問わない「ブラックボックス」。\n-- 定理 lim.add が頼っている公理は、右の Goal タブの一覧（または検査の結果）に出る。\n-- このコースの目標：章ごとに、この一覧を短く・弱くしていく。\n--\n-- 練習：最後の sorry を、不等式の連鎖で埋める。\n\naxiom triangle     : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\naxiom pos_half     : x : ℝ, h : x > 0 ⊢ x/2 > 0\naxiom ge.max.left  : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ a\naxiom ge.max.right : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ b\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose max{N_1, N_2}\n  Fix n | hn : n ≥ max{N_1, N_2}\n    sorry\n",
    "answer": "-- コース 0：限りなく近づく\n--\n-- 「数列 a_n が α に限りなく近づく」を ε-N で書き、和の極限を証明する。\n-- 上の 4 つの axiom は、まだ中身を問わない「ブラックボックス」。\n-- 定理 lim.add が頼っている公理は、右の Goal タブの一覧（または検査の結果）に出る。\n-- このコースの目標：章ごとに、この一覧を短く・弱くしていく。\n--\n-- 練習：最後の sorry を、不等式の連鎖で埋める。\n\naxiom triangle     : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\naxiom pos_half     : x : ℝ, h : x > 0 ⊢ x/2 > 0\naxiom ge.max.left  : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ a\naxiom ge.max.right : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ b\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose max{N_1, N_2}\n  Fix n | hn : n ≥ max{N_1, N_2}\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.max.left(hn)), h_2(n, ge.max.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 1. ブラックボックスを開ける",
    "blocks": [
      {
        "p": "**ねらい**：第 0 章の 4 つの公理のうち 3 つを証明して、和の極限が頼る公理を三角不等式だけにする。"
      },
      {
        "p": "**pos_half**（$x > 0$ なら $x/2 > 0$）は一次の不等式なので `linarith` で出る。"
      },
      {
        "p": "**max** の 2 つは、少し工夫する。$N$ として $\\max\\{N_1, N_2\\}$ の代わりに $N_1 + N_2$ をとってもよい（大きくとる分には困らない）。すると必要なのは「$n \\ge a + b$ なら $n \\ge a$」で、これは自然数が 0 以上であること（`nat.nonneg(b) : b ≥ 0`）と一次の不等式で出る。"
      },
      {
        "paper": [
          "**補題**　自然数 $a, b, n$ について、$n \\ge a + b$ ならば $n \\ge a$。",
          "**証明**　$b \\ge 0$ なので $n \\ge a + b \\ge a$。$\\blacksquare$"
        ]
      },
      {
        "type": [
          [
            "nat.nonneg(b)",
            "自然数 $b$ について $b \\ge 0$（組み込みの定理）"
          ]
        ]
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの宣言の一覧にも出る）が、その定理が頼っている公理。**このコースの目標は、章ごとにこの一覧を短く・弱くしていくこと**。最後に残るのは、数学の土台の公理だけになる。"
      }
    ],
    "file": "course/1-箱を開ける.narfi",
    "task": "3 つの `sorry`（pos_half・ge.add.left・ge.add.right）を埋める。lim.add の右の〔公理: …〕が triangle だけになれば完成。",
    "hints": [
      "pos_half は `linarith` だけ。",
      "ge.add.left：`k : b ≥ 0 by nat.nonneg(b)` と書き留めてから `linarith`。",
      "ge.add.right も同じ（今度は $a \\ge 0$ を使う）。"
    ],
    "exercise": "-- コース 1：ブラックボックスを開ける（pos_half と max）\n--\n-- 第 0 章の lim.add は 4 つの公理に頼っていた。そのうち 3 つは証明できる：\n--   pos_half：x > 0 なら x/2 > 0 は、一次不等式（linarith）で出る\n--   ge.max.left / right：N として max{N₁, N₂} の代わりに N₁ + N₂ をとれば、\n--     自然数が 0 以上であること（nat.nonneg）と一次不等式で出る\n--\n-- 練習：3 つの sorry を埋める。lim.add の頼る公理が triangle だけになる。\n\naxiom triangle : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nsorry\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nsorry\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nsorry\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n",
    "answer": "-- コース 1：ブラックボックスを開ける（pos_half と max）\n--\n-- 第 0 章の lim.add は 4 つの公理に頼っていた。そのうち 3 つは証明できる：\n--   pos_half：x > 0 なら x/2 > 0 は、一次不等式（linarith）で出る\n--   ge.max.left / right：N として max{N₁, N₂} の代わりに N₁ + N₂ をとれば、\n--     自然数が 0 以上であること（nat.nonneg）と一次不等式で出る\n--\n-- 練習：3 つの sorry を埋める。lim.add の頼る公理が triangle だけになる。\n\naxiom triangle : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 2. 三角不等式を分解する",
    "blocks": [
      {
        "p": "**ねらい**：残った公理 triangle（$|x + y| \\le |x| + |y|$）を、絶対値のもっと基本的な 3 つの性質から証明する。"
      },
      {
        "keys": [
          [
            "abs.ge",
            "$|x| \\ge x$"
          ],
          [
            "abs.ge_neg",
            "$|x| \\ge -x$"
          ],
          [
            "abs.cases",
            "$|x| = x$ または $|x| = -x$"
          ]
        ]
      },
      {
        "paper": [
          "**定理**　$|x + y| \\le |x| + |y|$。",
          "**証明**　$|x + y| = x + y$ のとき：$x \\le |x|$、$y \\le |y|$ を足せばよい。$|x + y| = -(x + y)$ のとき：$-x \\le |x|$、$-y \\le |y|$ を足せばよい。$\\blacksquare$"
        ]
      },
      {
        "p": "「または」の仮定で場合分けする（チュートリアルのレッスン 6）。それぞれの場合で、使う性質を事実の行で書き留めてから `linarith`。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの宣言の一覧にも出る）が、その定理が頼っている公理。**このコースの目標は、章ごとにこの一覧を短く・弱くしていくこと**。最後に残るのは、数学の土台の公理だけになる。"
      }
    ],
    "file": "course/2-三角不等式.narfi",
    "task": "triangle の `sorry` を埋める。",
    "hints": [
      "`Fix x, y` のあと、`c : |x + y| = x + y ∨ |x + y| = -(x + y) by abs.cases(x + y)`。",
      "`cases c` で 2 つの場合に分ける。",
      "左の場合：`p : |x| ≥ x by abs.ge(x)`、`q : |y| ≥ y by abs.ge(y)`、`linarith`。右の場合は abs.ge_neg を使う。"
    ],
    "exercise": "-- コース 2：三角不等式を分解する\n--\n-- 残った公理 triangle（|x + y| ≤ |x| + |y|）を、絶対値のもっと基本的な 3 つの性質から証明する：\n--   abs.ge：|x| ≥ x　　abs.ge_neg：|x| ≥ -x　　abs.cases：|x| = x か |x| = -x\n--\n-- 練習：triangle を証明する。\n-- ヒント：abs.cases(x + y) で場合分けし、それぞれ abs.ge・abs.ge_neg を「p : |x| ≥ x by abs.ge(x)」のように並べて linarith。\n\naxiom abs.ge     : ∀x:ℝ. |x| ≥ x\naxiom abs.ge_neg : ∀x:ℝ. |x| ≥ -x\naxiom abs.cases  : ∀x:ℝ. |x| = x ∨ |x| = -x\n\nthm triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\nsorry\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n",
    "answer": "-- コース 2：三角不等式を分解する\n--\n-- 残った公理 triangle（|x + y| ≤ |x| + |y|）を、絶対値のもっと基本的な 3 つの性質から証明する：\n--   abs.ge：|x| ≥ x　　abs.ge_neg：|x| ≥ -x　　abs.cases：|x| = x か |x| = -x\n--\n-- 練習：triangle を証明する。\n-- ヒント：abs.cases(x + y) で場合分けし、それぞれ abs.ge・abs.ge_neg を「p : |x| ≥ x by abs.ge(x)」のように並べて linarith。\n\naxiom abs.ge     : ∀x:ℝ. |x| ≥ x\naxiom abs.ge_neg : ∀x:ℝ. |x| ≥ -x\naxiom abs.cases  : ∀x:ℝ. |x| = x ∨ |x| = -x\n\nthm triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\nFix x, y\n  c : |x + y| = x + y ∨ |x + y| = -(x + y) by abs.cases(x + y)\n  cases c\n    Case left h\n      p : |x| ≥ x by abs.ge(x)\n      q : |y| ≥ y by abs.ge(y)\n      linarith\n    Case right h\n      p : |x| ≥ -x by abs.ge_neg(x)\n      q : |y| ≥ -y by abs.ge_neg(y)\n      linarith\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1 | h_1 by ha(ε/2, pos_half(hε))\n  Obtain N_2 | h_2 by hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 3. 絶対値を作る",
    "blocks": [
      {
        "p": "**ねらい**：第 2 章で公理として置いた絶対値の 3 つの性質を、絶対値を**定義**して証明する。頼る公理は、順序の公理 1 つ（「$x < 0$ か $x \\ge 0$」）だけになる。"
      },
      {
        "p": "絶対値 $|x|$ を「$x \\ge 0$ なら $x$、$x < 0$ なら $-x$」を満たす数として定める。そういう数を **1 つ選ぶ**には、選択（`some`）を使う：`some({y | 条件})` は「条件を満たす $y$ が存在するなら、その 1 つ」。存在を示せば（ab.exists）、選んだものが条件を満たす（ab.spec、組み込みの `choice` による）。"
      },
      {
        "code": "def isabs(x : ℝ, y : ℝ) :⇔ (x ≥ 0 ∧ y = x) ∨ (x < 0 ∧ y = -x)\ndef ab(x : ℝ) : ℝ := some({y : ℝ | isabs(x, y)})"
      },
      {
        "p": "組み込みの $|x|$ と区別するため、ここでは `ab(x)` という名前で作る。ab.ge の証明（ファイルの中にある）が、ab.spec を場合分けして使うお手本。"
      },
      {
        "type": [
          [
            "some({y | φ})",
            "φ を満たす y を 1 つ選んだもの（選択）"
          ],
          [
            "choice(集合, 存在の証明)",
            "選んだものが条件を満たす（組み込みの公理）"
          ]
        ]
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの宣言の一覧にも出る）が、その定理が頼っている公理。**このコースの目標は、章ごとにこの一覧を短く・弱くしていくこと**。最後に残るのは、数学の土台の公理だけになる。"
      }
    ],
    "file": "course/3-絶対値を作る.narfi",
    "task": "ab.exists・ab.ge_neg・ab.cases の 3 つの `sorry` を埋める。ab.triangle の右の〔公理: …〕が lt_or_ge だけになれば完成。",
    "hints": [
      "ab.exists：`Fix x` のあと、`t : x < 0 ∨ x ≥ 0 by lt_or_ge(x)` を書き留めて `cases t`。",
      "$x < 0$ の場合（`Case left hn`）：`choose -x`、`right`（isabs の右側を示す）、`hn, refl`（$x < 0$ と $-x = -x$）。",
      "$x \\ge 0$ の場合（`Case right hp`）：`choose x`、`left`、`hp, refl`。",
      "ab.ge_neg は ab.ge と同じ形（`s : isabs(x, ab(x)) by ab.spec(x)` を場合分けして `linarith`）。",
      "ab.cases も同じ形。左の場合は `left` のあと `a.right`、右の場合は `right` のあと `b.right`。"
    ],
    "exercise": "-- コース 3：絶対値を作る\n--\n-- 第 2 章で残った abs.ge・abs.ge_neg・abs.cases を、絶対値を「定義」して証明する。\n-- |x| は組み込みの記号なので、ここでは ab(x) という名前で作る：\n--   ab(x) は「x ≥ 0 なら x、x < 0 なら -x」を満たす y（そういう y を 1 つ選ぶ：選択 some）\n-- そのために使うのは、順序の公理 lt_or_ge（x < 0 か x ≥ 0）だけ。\n-- （some は HOL の選択公理による。土台の公理なので、頼る公理の一覧には出ない）\n--\n-- 練習：ab.exists・ab.ge_neg・ab.cases を証明する。ab.triangle の頼る公理が lt_or_ge だけになる。\n\naxiom lt_or_ge : ∀x:ℝ. x < 0 ∨ x ≥ 0\n\ndef isabs(x : ℝ, y : ℝ) :⇔ (x ≥ 0 ∧ y = x) ∨ (x < 0 ∧ y = -x)\ndef ab(x : ℝ) : ℝ := some({y : ℝ | isabs(x, y)})\n\nthm ab.exists :\n  ⊢ ∀x:ℝ. ∃y:ℝ. isabs(x, y)\n\nsorry\n\nthm ab.spec :\n  ⊢ ∀x:ℝ. isabs(x, ab(x))\n\nFix x\n  choice({y : ℝ | isabs(x, y)}, ab.exists(x))\n\nthm ab.ge :\n  ⊢ ∀x:ℝ. ab(x) ≥ x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      n : x < 0 by b.left\n      linarith\n\nthm ab.ge_neg :\n  ⊢ ∀x:ℝ. ab(x) ≥ -x\n\nsorry\n\nthm ab.cases :\n  ⊢ ∀x:ℝ. ab(x) = x ∨ ab(x) = -x\n\nsorry\n\nthm ab.triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. ab(x + y) ≤ ab(x) + ab(y)\n\nFix x, y\n  c : ab(x + y) = x + y ∨ ab(x + y) = -(x + y) by ab.cases(x + y)\n  cases c\n    Case left h\n      p : ab(x) ≥ x by ab.ge(x)\n      q : ab(y) ≥ y by ab.ge(y)\n      linarith\n    Case right h\n      p : ab(x) ≥ -x by ab.ge_neg(x)\n      q : ab(y) ≥ -y by ab.ge_neg(y)\n      linarith\n",
    "answer": "-- コース 3：絶対値を作る\n--\n-- 第 2 章で残った abs.ge・abs.ge_neg・abs.cases を、絶対値を「定義」して証明する。\n-- |x| は組み込みの記号なので、ここでは ab(x) という名前で作る：\n--   ab(x) は「x ≥ 0 なら x、x < 0 なら -x」を満たす y（そういう y を 1 つ選ぶ：選択 some）\n-- そのために使うのは、順序の公理 lt_or_ge（x < 0 か x ≥ 0）だけ。\n-- （some は HOL の選択公理による。土台の公理なので、頼る公理の一覧には出ない）\n--\n-- 練習：ab.exists・ab.ge_neg・ab.cases を証明する。ab.triangle の頼る公理が lt_or_ge だけになる。\n\naxiom lt_or_ge : ∀x:ℝ. x < 0 ∨ x ≥ 0\n\ndef isabs(x : ℝ, y : ℝ) :⇔ (x ≥ 0 ∧ y = x) ∨ (x < 0 ∧ y = -x)\ndef ab(x : ℝ) : ℝ := some({y : ℝ | isabs(x, y)})\n\nthm ab.exists :\n  ⊢ ∀x:ℝ. ∃y:ℝ. isabs(x, y)\n\nFix x\n  t : x < 0 ∨ x ≥ 0 by lt_or_ge(x)\n  cases t\n    Case left hn\n      choose -x\n      right\n      hn, refl\n    Case right hp\n      choose x\n      left\n      hp, refl\n\nthm ab.spec :\n  ⊢ ∀x:ℝ. isabs(x, ab(x))\n\nFix x\n  choice({y : ℝ | isabs(x, y)}, ab.exists(x))\n\nthm ab.ge :\n  ⊢ ∀x:ℝ. ab(x) ≥ x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      n : x < 0 by b.left\n      linarith\n\nthm ab.ge_neg :\n  ⊢ ∀x:ℝ. ab(x) ≥ -x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      p : x ≥ 0 by a.left\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      linarith\n\nthm ab.cases :\n  ⊢ ∀x:ℝ. ab(x) = x ∨ ab(x) = -x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      left\n      a.right\n    Case right b\n      right\n      b.right\n\nthm ab.triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. ab(x + y) ≤ ab(x) + ab(y)\n\nFix x, y\n  c : ab(x + y) = x + y ∨ ab(x + y) = -(x + y) by ab.cases(x + y)\n  cases c\n    Case left h\n      p : ab(x) ≥ x by ab.ge(x)\n      q : ab(y) ≥ y by ab.ge(y)\n      linarith\n    Case right h\n      p : ab(x) ≥ -x by ab.ge_neg(x)\n      q : ab(y) ≥ -y by ab.ge_neg(y)\n      linarith\n"
  },
  {
    "title": "コース 4. ring を使わずに計算する",
    "blocks": [
      {
        "p": "**ねらい**：ここまでの証明は `ring`・`linarith`（自動の計算）に頼っていた。その中身は**体の公理**。ここでは体の公理の一部を公理として置き、`ring` を使わずに式を 1 歩ずつ変形する。"
      },
      {
        "keys": [
          [
            "F.add_comm",
            "$a + b = b + a$"
          ],
          [
            "F.add_zero",
            "$a + 0 = a$"
          ],
          [
            "F.mul_comm",
            "$ab = ba$"
          ],
          [
            "F.distrib",
            "$a(b + c) = ab + ac$"
          ],
          [
            "F.add_cancel",
            "$a + b = a + c$ ならば $b = c$"
          ]
        ]
      },
      {
        "p": "連鎖の各段の根拠には、その変形に使う公理を、具体的な値を入れて書く（`F.add_comm(0, a)` は「$0 + a = a + 0$」）。式の**一部だけ**を書き換えるときは `EQ2(等式, refl)`。"
      },
      {
        "paper": [
          "**定理**　$a \\cdot 0 = 0$。",
          "**証明**　$a \\cdot 0 + a \\cdot 0 = a(0 + 0) = a \\cdot 0 = a \\cdot 0 + 0$。両辺から $a \\cdot 0$ を簡約して $a \\cdot 0 = 0$。$\\blacksquare$（ファイルの F.mul_zero）"
        ]
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの宣言の一覧にも出る）が、その定理が頼っている公理。**このコースの目標は、章ごとにこの一覧を短く・弱くしていくこと**。最後に残るのは、数学の土台の公理だけになる。"
      }
    ],
    "file": "course/4-体の公理.narfi",
    "task": "F.zero_add（$0 + a = a$）と F.distrib_right（$(a + b)c = ac + bc$）を、ring を使わずに証明する。",
    "hints": [
      "F.zero_add：`0 + a` から始めて、`= a + 0   by F.add_comm(0, a)`、`= a   by F.add_zero(a)`。",
      "F.distrib_right：掛け算の順番を入れ替えて分配法則に持ち込む。`(a + b) * c = c * (a + b)   by F.mul_comm(a + b, c)`。",
      "続けて `= c * a + c * b   by F.distrib(c, a, b)`、`= a * c + c * b   by EQ2(F.mul_comm(c, a), refl)`、`= a * c + b * c   by EQ2(F.mul_comm(c, b), refl)`。"
    ],
    "exercise": "-- コース 4：ring を使わずに計算する\n--\n-- ここまでの証明は ring・linarith（自動の計算）に頼っていた。その中身は体と順序の公理。\n-- ここでは体の公理の一部を axiom として置き、ring を使わずに式を変形する。\n--   連鎖の各行 `= … by 根拠` の根拠は、その等式そのもの（F.add_comm(0, a) など）\n--   式の一部だけを書き換えるときは EQ2(等式, refl)\n--\n-- 例：F.mul_zero（a · 0 = 0）は、分配法則と簡約法則だけで示せる（下にある）。\n-- 練習：F.zero_add と F.distrib_right を証明する。\n\naxiom F.add_comm   : ∀a:ℝ. ∀b:ℝ. a + b = b + a\naxiom F.add_zero   : ∀a:ℝ. a + 0 = a\naxiom F.mul_comm   : ∀a:ℝ. ∀b:ℝ. a * b = b * a\naxiom F.distrib    : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a * (b + c) = a * b + a * c\naxiom F.add_cancel : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a + b = a + c ⇒ b = c\n\nthm F.zero_add :\n  a : ℝ\n  ⊢ 0 + a = a\n\nsorry\n\nthm F.distrib_right :\n  a : ℝ, b : ℝ, c : ℝ\n  ⊢ (a + b) * c = a * c + b * c\n\nsorry\n\nthm F.mul_zero :\n  a : ℝ\n  ⊢ a * 0 = 0\n\ne1 : a * (0 + 0) = a * 0 + a * 0 by F.distrib(a, 0, 0)\ne3 : a * (0 + 0) = a * 0 by EQ2(F.add_zero(0), refl)\na * 0 + a * 0\n  = a * (0 + 0)   by eq.symm(e1)\n  = a * 0         by e3\n  = a * 0 + 0     by eq.symm(F.add_zero(a * 0))\nF.add_cancel(a * 0, a * 0, 0, this)\n",
    "answer": "-- コース 4：ring を使わずに計算する\n--\n-- ここまでの証明は ring・linarith（自動の計算）に頼っていた。その中身は体と順序の公理。\n-- ここでは体の公理の一部を axiom として置き、ring を使わずに式を変形する。\n--   連鎖の各行 `= … by 根拠` の根拠は、その等式そのもの（F.add_comm(0, a) など）\n--   式の一部だけを書き換えるときは EQ2(等式, refl)\n--\n-- 例：F.mul_zero（a · 0 = 0）は、分配法則と簡約法則だけで示せる（下にある）。\n-- 練習：F.zero_add と F.distrib_right を証明する。\n\naxiom F.add_comm   : ∀a:ℝ. ∀b:ℝ. a + b = b + a\naxiom F.add_zero   : ∀a:ℝ. a + 0 = a\naxiom F.mul_comm   : ∀a:ℝ. ∀b:ℝ. a * b = b * a\naxiom F.distrib    : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a * (b + c) = a * b + a * c\naxiom F.add_cancel : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a + b = a + c ⇒ b = c\n\nthm F.zero_add :\n  a : ℝ\n  ⊢ 0 + a = a\n\n0 + a\n  = a + 0   by F.add_comm(0, a)\n  = a       by F.add_zero(a)\n\nthm F.distrib_right :\n  a : ℝ, b : ℝ, c : ℝ\n  ⊢ (a + b) * c = a * c + b * c\n\n(a + b) * c\n  = c * (a + b)       by F.mul_comm(a + b, c)\n  = c * a + c * b     by F.distrib(c, a, b)\n  = a * c + c * b     by EQ2(F.mul_comm(c, a), refl)\n  = a * c + b * c     by EQ2(F.mul_comm(c, b), refl)\n\nthm F.mul_zero :\n  a : ℝ\n  ⊢ a * 0 = 0\n\ne1 : a * (0 + 0) = a * 0 + a * 0 by F.distrib(a, 0, 0)\ne3 : a * (0 + 0) = a * 0 by EQ2(F.add_zero(0), refl)\na * 0 + a * 0\n  = a * (0 + 0)   by eq.symm(e1)\n  = a * 0         by e3\n  = a * 0 + 0     by eq.symm(F.add_zero(a * 0))\nF.add_cancel(a * 0, a * 0, 0, this)\n"
  },
  {
    "title": "コース 5〜. この先",
    "blocks": [
      {
        "p": "第 4 章で置いた体の公理と、第 3 章の順序の公理は、ℝ を作れば証明できる。標準ライブラリの `reals/` には、ℝ を有理数のコーシー列の同値類として作るところまである（Standard Library → reals）。"
      },
      {
        "p": "この先の章（準備中）：ℝ の足し算・掛け算を作って体の公理を証明する → ℚ を ℤ から、ℤ を ℕ から作る → 最後に残るのは、ペアノの公理・等号（反射律と代入）・自然演繹の規則・HOL の公理（外延性と選択）だけ。"
      }
    ]
  }
];
