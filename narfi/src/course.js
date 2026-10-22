// Narfi のコース「公理へ」（エディタ右側の Learn タブ）。
// 各章：本文、作るファイル（file）、練習（exercise）、答え（answer）。答えが通ることは tests/ui.rs で確かめる。

window.NARFI_COURSE = [
  {
    "title": "コース 0. 限りなく近づく",
    "blocks": [
      {
        "p": "ε-N で極限を定義し、和の極限を証明します。三角不等式などの 4 つの性質は、まだ中身を問わない公理（axiom）として置きます。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの一覧にも出ます）が、その定理が頼っている公理です。章が進むごとに、この一覧が短く・弱くなっていきます。"
      },
      {
        "p": "「コースのファイルを開く」で、自分のファイル一覧に `course/0-極限.narfi` が作られて開きます（すでにあれば、続きから開きます）。"
      }
    ],
    "file": "course/0-極限.narfi",
    "exercise": "-- コース 0：限りなく近づく\n--\n-- 「数列 a_n が α に限りなく近づく」を ε-N で書き、和の極限を証明する。\n-- 上の 4 つの axiom は、まだ中身を問わない「ブラックボックス」。\n-- 定理 lim.add が頼っている公理は、右の Goal タブの一覧（または検査の結果）に出る。\n-- このコースの目標：章ごとに、この一覧を短く・弱くしていく。\n--\n-- 練習：最後の sorry を、不等式の連鎖で埋める。\n\naxiom triangle     : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\naxiom pos_half     : x : ℝ, h : x > 0 ⊢ x/2 > 0\naxiom ge.max.left  : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ a\naxiom ge.max.right : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ b\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose max{N_1, N_2}\n  Fix n | hn : n ≥ max{N_1, N_2}\n    sorry\n",
    "answer": "-- コース 0：限りなく近づく\n--\n-- 「数列 a_n が α に限りなく近づく」を ε-N で書き、和の極限を証明する。\n-- 上の 4 つの axiom は、まだ中身を問わない「ブラックボックス」。\n-- 定理 lim.add が頼っている公理は、右の Goal タブの一覧（または検査の結果）に出る。\n-- このコースの目標：章ごとに、この一覧を短く・弱くしていく。\n--\n-- 練習：最後の sorry を、不等式の連鎖で埋める。\n\naxiom triangle     : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\naxiom pos_half     : x : ℝ, h : x > 0 ⊢ x/2 > 0\naxiom ge.max.left  : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ a\naxiom ge.max.right : a : ℕ, b : ℕ, n : ℕ, h : n ≥ max{a, b} ⊢ n ≥ b\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose max{N_1, N_2}\n  Fix n | hn : n ≥ max{N_1, N_2}\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.max.left(hn)), h_2(n, ge.max.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 1. ブラックボックスを開ける",
    "blocks": [
      {
        "p": "第 0 章の公理のうち 3 つを証明して、和の極限が頼る公理を triangle だけにします。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの一覧にも出ます）が、その定理が頼っている公理です。章が進むごとに、この一覧が短く・弱くなっていきます。"
      },
      {
        "p": "「コースのファイルを開く」で、自分のファイル一覧に `course/1-箱を開ける.narfi` が作られて開きます（すでにあれば、続きから開きます）。"
      }
    ],
    "file": "course/1-箱を開ける.narfi",
    "exercise": "-- コース 1：ブラックボックスを開ける（pos_half と max）\n--\n-- 第 0 章の lim.add は 4 つの公理に頼っていた。そのうち 3 つは証明できる：\n--   pos_half：x > 0 なら x/2 > 0 は、一次不等式（linarith）で出る\n--   ge.max.left / right：N として max{N₁, N₂} の代わりに N₁ + N₂ をとれば、\n--     自然数が 0 以上であること（nat.nonneg）と一次不等式で出る\n--\n-- 練習：3 つの sorry を埋める。lim.add の頼る公理が triangle だけになる。\n\naxiom triangle : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nsorry\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nsorry\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nsorry\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n",
    "answer": "-- コース 1：ブラックボックスを開ける（pos_half と max）\n--\n-- 第 0 章の lim.add は 4 つの公理に頼っていた。そのうち 3 つは証明できる：\n--   pos_half：x > 0 なら x/2 > 0 は、一次不等式（linarith）で出る\n--   ge.max.left / right：N として max{N₁, N₂} の代わりに N₁ + N₂ をとれば、\n--     自然数が 0 以上であること（nat.nonneg）と一次不等式で出る\n--\n-- 練習：3 つの sorry を埋める。lim.add の頼る公理が triangle だけになる。\n\naxiom triangle : ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 2. 三角不等式を分解する",
    "blocks": [
      {
        "p": "三角不等式を、絶対値のもっと基本的な 3 つの性質から証明します。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの一覧にも出ます）が、その定理が頼っている公理です。章が進むごとに、この一覧が短く・弱くなっていきます。"
      },
      {
        "p": "「コースのファイルを開く」で、自分のファイル一覧に `course/2-三角不等式.narfi` が作られて開きます（すでにあれば、続きから開きます）。"
      }
    ],
    "file": "course/2-三角不等式.narfi",
    "exercise": "-- コース 2：三角不等式を分解する\n--\n-- 残った公理 triangle（|x + y| ≤ |x| + |y|）を、絶対値のもっと基本的な 3 つの性質から証明する：\n--   abs.ge：|x| ≥ x　　abs.ge_neg：|x| ≥ -x　　abs.cases：|x| = x か |x| = -x\n--\n-- 練習：triangle を証明する。\n-- ヒント：abs.cases(x + y) で場合分けし、それぞれ abs.ge・abs.ge_neg を「p : |x| ≥ x by abs.ge(x)」のように並べて linarith。\n\naxiom abs.ge     : ∀x:ℝ. |x| ≥ x\naxiom abs.ge_neg : ∀x:ℝ. |x| ≥ -x\naxiom abs.cases  : ∀x:ℝ. |x| = x ∨ |x| = -x\n\nthm triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\nsorry\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n",
    "answer": "-- コース 2：三角不等式を分解する\n--\n-- 残った公理 triangle（|x + y| ≤ |x| + |y|）を、絶対値のもっと基本的な 3 つの性質から証明する：\n--   abs.ge：|x| ≥ x　　abs.ge_neg：|x| ≥ -x　　abs.cases：|x| = x か |x| = -x\n--\n-- 練習：triangle を証明する。\n-- ヒント：abs.cases(x + y) で場合分けし、それぞれ abs.ge・abs.ge_neg を「p : |x| ≥ x by abs.ge(x)」のように並べて linarith。\n\naxiom abs.ge     : ∀x:ℝ. |x| ≥ x\naxiom abs.ge_neg : ∀x:ℝ. |x| ≥ -x\naxiom abs.cases  : ∀x:ℝ. |x| = x ∨ |x| = -x\n\nthm triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. |x + y| ≤ |x| + |y|\n\nFix x, y\n  c : |x + y| = x + y ∨ |x + y| = -(x + y) by abs.cases(x + y)\n  cases c\n    Case left h\n      p : |x| ≥ x by abs.ge(x)\n      q : |y| ≥ y by abs.ge(y)\n      linarith\n    Case right h\n      p : |x| ≥ -x by abs.ge_neg(x)\n      q : |y| ≥ -y by abs.ge_neg(y)\n      linarith\n\ndef is_lim(a : ℕ → ℝ, α : ℝ) :⇔ ∀ε:ℝ>0. ∃N:ℕ. ∀n:ℕ≥N. |a_n - α| < ε\n\nthm pos_half :\n  x : ℝ, h : x > 0\n  ⊢ x/2 > 0\n\nlinarith\n\nthm ge.add.left :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ a\n\nk : b ≥ 0 by nat.nonneg(b)\nlinarith\n\nthm ge.add.right :\n  a : ℕ, b : ℕ, n : ℕ, h : n ≥ a + b\n  ⊢ n ≥ b\n\nk : a ≥ 0 by nat.nonneg(a)\nlinarith\n\nthm lim.add :\n  a : ℕ → ℝ, b : ℕ → ℝ, α : ℝ, β : ℝ,\n  ha : is_lim(a, α), hb : is_lim(b, β)\n  ⊢ is_lim((n : ℕ ↦ a_n + b_n), α + β)\n\nFix ε | hε : ε > 0\n  Obtain N_1, h_1 : ha(ε/2, pos_half(hε))\n  Obtain N_2, h_2 : hb(ε/2, pos_half(hε))\n  choose N_1 + N_2\n  Fix n | hn : n ≥ N_1 + N_2\n    |(a_n + b_n) - (α + β)|\n      = |(a_n - α) + (b_n - β)|   by ring\n      ≤ |a_n - α| + |b_n - β|     by triangle(a_n - α, b_n - β)\n      < ε/2 + ε/2                 by h_1(n, ge.add.left(hn)), h_2(n, ge.add.right(hn))\n      = ε                         by ring\n"
  },
  {
    "title": "コース 3. 絶対値を作る",
    "blocks": [
      {
        "p": "絶対値を「x ≥ 0 なら x、そうでなければ −x を満たすもの」として選択で定義し、第 2 章の 3 つの性質を、順序の公理 1 つから証明します。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの一覧にも出ます）が、その定理が頼っている公理です。章が進むごとに、この一覧が短く・弱くなっていきます。"
      },
      {
        "p": "「コースのファイルを開く」で、自分のファイル一覧に `course/3-絶対値を作る.narfi` が作られて開きます（すでにあれば、続きから開きます）。"
      }
    ],
    "file": "course/3-絶対値を作る.narfi",
    "exercise": "-- コース 3：絶対値を作る\n--\n-- 第 2 章で残った abs.ge・abs.ge_neg・abs.cases を、絶対値を「定義」して証明する。\n-- |x| は組み込みの記号なので、ここでは ab(x) という名前で作る：\n--   ab(x) は「x ≥ 0 なら x、x < 0 なら -x」を満たす y（そういう y を 1 つ選ぶ：選択 some）\n-- そのために使うのは、順序の公理 lt_or_ge（x < 0 か x ≥ 0）だけ。\n-- （some は HOL の選択公理による。土台の公理なので、頼る公理の一覧には出ない）\n--\n-- 練習：ab.exists・ab.ge_neg・ab.cases を証明する。ab.triangle の頼る公理が lt_or_ge だけになる。\n\naxiom lt_or_ge : ∀x:ℝ. x < 0 ∨ x ≥ 0\n\ndef isabs(x : ℝ, y : ℝ) :⇔ (x ≥ 0 ∧ y = x) ∨ (x < 0 ∧ y = -x)\ndef ab(x : ℝ) : ℝ := some({y : ℝ | isabs(x, y)})\n\nthm ab.exists :\n  ⊢ ∀x:ℝ. ∃y:ℝ. isabs(x, y)\n\nsorry\n\nthm ab.spec :\n  ⊢ ∀x:ℝ. isabs(x, ab(x))\n\nFix x\n  choice({y : ℝ | isabs(x, y)}, ab.exists(x))\n\nthm ab.ge :\n  ⊢ ∀x:ℝ. ab(x) ≥ x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      n : x < 0 by b.left\n      linarith\n\nthm ab.ge_neg :\n  ⊢ ∀x:ℝ. ab(x) ≥ -x\n\nsorry\n\nthm ab.cases :\n  ⊢ ∀x:ℝ. ab(x) = x ∨ ab(x) = -x\n\nsorry\n\nthm ab.triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. ab(x + y) ≤ ab(x) + ab(y)\n\nFix x, y\n  c : ab(x + y) = x + y ∨ ab(x + y) = -(x + y) by ab.cases(x + y)\n  cases c\n    Case left h\n      p : ab(x) ≥ x by ab.ge(x)\n      q : ab(y) ≥ y by ab.ge(y)\n      linarith\n    Case right h\n      p : ab(x) ≥ -x by ab.ge_neg(x)\n      q : ab(y) ≥ -y by ab.ge_neg(y)\n      linarith\n",
    "answer": "-- コース 3：絶対値を作る\n--\n-- 第 2 章で残った abs.ge・abs.ge_neg・abs.cases を、絶対値を「定義」して証明する。\n-- |x| は組み込みの記号なので、ここでは ab(x) という名前で作る：\n--   ab(x) は「x ≥ 0 なら x、x < 0 なら -x」を満たす y（そういう y を 1 つ選ぶ：選択 some）\n-- そのために使うのは、順序の公理 lt_or_ge（x < 0 か x ≥ 0）だけ。\n-- （some は HOL の選択公理による。土台の公理なので、頼る公理の一覧には出ない）\n--\n-- 練習：ab.exists・ab.ge_neg・ab.cases を証明する。ab.triangle の頼る公理が lt_or_ge だけになる。\n\naxiom lt_or_ge : ∀x:ℝ. x < 0 ∨ x ≥ 0\n\ndef isabs(x : ℝ, y : ℝ) :⇔ (x ≥ 0 ∧ y = x) ∨ (x < 0 ∧ y = -x)\ndef ab(x : ℝ) : ℝ := some({y : ℝ | isabs(x, y)})\n\nthm ab.exists :\n  ⊢ ∀x:ℝ. ∃y:ℝ. isabs(x, y)\n\nFix x\n  t : x < 0 ∨ x ≥ 0 by lt_or_ge(x)\n  cases t\n    Case left hn\n      choose -x\n      choose right\n      hn, refl\n    Case right hp\n      choose x\n      choose left\n      hp, refl\n\nthm ab.spec :\n  ⊢ ∀x:ℝ. isabs(x, ab(x))\n\nFix x\n  choice({y : ℝ | isabs(x, y)}, ab.exists(x))\n\nthm ab.ge :\n  ⊢ ∀x:ℝ. ab(x) ≥ x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      n : x < 0 by b.left\n      linarith\n\nthm ab.ge_neg :\n  ⊢ ∀x:ℝ. ab(x) ≥ -x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      k : ab(x) = x by a.right\n      p : x ≥ 0 by a.left\n      linarith\n    Case right b\n      k : ab(x) = -x by b.right\n      linarith\n\nthm ab.cases :\n  ⊢ ∀x:ℝ. ab(x) = x ∨ ab(x) = -x\n\nFix x\n  s : isabs(x, ab(x)) by ab.spec(x)\n  cases s\n    Case left a\n      choose left\n      a.right\n    Case right b\n      choose right\n      b.right\n\nthm ab.triangle :\n  ⊢ ∀x:ℝ. ∀y:ℝ. ab(x + y) ≤ ab(x) + ab(y)\n\nFix x, y\n  c : ab(x + y) = x + y ∨ ab(x + y) = -(x + y) by ab.cases(x + y)\n  cases c\n    Case left h\n      p : ab(x) ≥ x by ab.ge(x)\n      q : ab(y) ≥ y by ab.ge(y)\n      linarith\n    Case right h\n      p : ab(x) ≥ -x by ab.ge_neg(x)\n      q : ab(y) ≥ -y by ab.ge_neg(y)\n      linarith\n"
  },
  {
    "title": "コース 4. ring を使わずに計算する",
    "blocks": [
      {
        "p": "自動の計算（ring）の中身である体の公理を明示して、式の変形を 1 歩ずつ書きます。"
      },
      {
        "p": "定理の右に出る〔公理: …〕（Goal タブの一覧にも出ます）が、その定理が頼っている公理です。章が進むごとに、この一覧が短く・弱くなっていきます。"
      },
      {
        "p": "「コースのファイルを開く」で、自分のファイル一覧に `course/4-体の公理.narfi` が作られて開きます（すでにあれば、続きから開きます）。"
      }
    ],
    "file": "course/4-体の公理.narfi",
    "exercise": "-- コース 4：ring を使わずに計算する\n--\n-- ここまでの証明は ring・linarith（自動の計算）に頼っていた。その中身は体と順序の公理。\n-- ここでは体の公理の一部を axiom として置き、ring を使わずに式を変形する。\n--   連鎖の各行 `= … by 根拠` の根拠は、その等式そのもの（F.add_comm(0, a) など）\n--   式の一部だけを書き換えるときは EQ2(等式, refl)\n--\n-- 例：F.mul_zero（a · 0 = 0）は、分配法則と簡約法則だけで示せる（下にある）。\n-- 練習：F.zero_add と F.distrib_right を証明する。\n\naxiom F.add_comm   : ∀a:ℝ. ∀b:ℝ. a + b = b + a\naxiom F.add_zero   : ∀a:ℝ. a + 0 = a\naxiom F.mul_comm   : ∀a:ℝ. ∀b:ℝ. a * b = b * a\naxiom F.distrib    : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a * (b + c) = a * b + a * c\naxiom F.add_cancel : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a + b = a + c ⇒ b = c\n\nthm F.zero_add :\n  a : ℝ\n  ⊢ 0 + a = a\n\nsorry\n\nthm F.distrib_right :\n  a : ℝ, b : ℝ, c : ℝ\n  ⊢ (a + b) * c = a * c + b * c\n\nsorry\n\nthm F.mul_zero :\n  a : ℝ\n  ⊢ a * 0 = 0\n\ne1 : a * (0 + 0) = a * 0 + a * 0 by F.distrib(a, 0, 0)\ne3 : a * (0 + 0) = a * 0 by EQ2(F.add_zero(0), refl)\na * 0 + a * 0\n  = a * (0 + 0)   by eq.symm(e1)\n  = a * 0         by e3\n  = a * 0 + 0     by eq.symm(F.add_zero(a * 0))\nF.add_cancel(a * 0, a * 0, 0, this)\n",
    "answer": "-- コース 4：ring を使わずに計算する\n--\n-- ここまでの証明は ring・linarith（自動の計算）に頼っていた。その中身は体と順序の公理。\n-- ここでは体の公理の一部を axiom として置き、ring を使わずに式を変形する。\n--   連鎖の各行 `= … by 根拠` の根拠は、その等式そのもの（F.add_comm(0, a) など）\n--   式の一部だけを書き換えるときは EQ2(等式, refl)\n--\n-- 例：F.mul_zero（a · 0 = 0）は、分配法則と簡約法則だけで示せる（下にある）。\n-- 練習：F.zero_add と F.distrib_right を証明する。\n\naxiom F.add_comm   : ∀a:ℝ. ∀b:ℝ. a + b = b + a\naxiom F.add_zero   : ∀a:ℝ. a + 0 = a\naxiom F.mul_comm   : ∀a:ℝ. ∀b:ℝ. a * b = b * a\naxiom F.distrib    : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a * (b + c) = a * b + a * c\naxiom F.add_cancel : ∀a:ℝ. ∀b:ℝ. ∀c:ℝ. a + b = a + c ⇒ b = c\n\nthm F.zero_add :\n  a : ℝ\n  ⊢ 0 + a = a\n\n0 + a\n  = a + 0   by F.add_comm(0, a)\n  = a       by F.add_zero(a)\n\nthm F.distrib_right :\n  a : ℝ, b : ℝ, c : ℝ\n  ⊢ (a + b) * c = a * c + b * c\n\n(a + b) * c\n  = c * (a + b)       by F.mul_comm(a + b, c)\n  = c * a + c * b     by F.distrib(c, a, b)\n  = a * c + c * b     by EQ2(F.mul_comm(c, a), refl)\n  = a * c + b * c     by EQ2(F.mul_comm(c, b), refl)\n\nthm F.mul_zero :\n  a : ℝ\n  ⊢ a * 0 = 0\n\ne1 : a * (0 + 0) = a * 0 + a * 0 by F.distrib(a, 0, 0)\ne3 : a * (0 + 0) = a * 0 by EQ2(F.add_zero(0), refl)\na * 0 + a * 0\n  = a * (0 + 0)   by eq.symm(e1)\n  = a * 0         by e3\n  = a * 0 + 0     by eq.symm(F.add_zero(a * 0))\nF.add_cancel(a * 0, a * 0, 0, this)\n"
  },
  {
    "title": "コース 5〜. この先",
    "blocks": [
      {
        "p": "第 4 章で置いた体の公理と、第 3 章の順序の公理は、ℝ を作れば証明できます。標準ライブラリの `reals/` には、ℝ を有理数のコーシー列の同値類として作るところまであります（Standard Library → reals）。"
      },
      {
        "p": "この先の章（準備中）：ℝ の足し算・掛け算を作って体の公理を証明する → ℚ を ℤ から、ℤ を ℕ から作る → 最後に残るのは、ペアノの公理・等号（反射律と代入）・自然演繹の規則・HOL の公理（外延性と選択）だけ。"
      }
    ]
  }
];
