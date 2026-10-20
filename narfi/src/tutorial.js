// Narfi のチュートリアル（エディタ右側の Learn タブ）。
// 各レッスン：本文（p：文。$…$ は数式・`…` はコード、code：コードの例、keys：キーの表）、練習（exercise）と答え（answer）。
// 答えが検査を通ることは tests/ui.rs（tutorial_answers_check）で確かめる。

window.NARFI_TUTORIAL = [
  {
    title: "0. 早見表：goal の形から書き方を選ぶ",
    blocks: [
      { p: "証明は「いま示すべきもの（Goal）」の形を見て、1 行ずつ書きます。迷ったら右の Goal タブを見てください。Goal の下の「次の一手」に、いま書けるものが出ます（押すと入ります）。" },
      { p: "**Goal の形で選ぶ**（Goal を小さくする）" },
      { keys: [
        ["∀x. φ", "Fix x（条件つき ∀ε>0 なら Fix ε | hε : ε > 0）"],
        ["φ → ψ、¬φ", "assume h : φ"],
        ["φ ∧ ψ", "根拠1, 根拠2"],
        ["φ ∨ ψ", "choose left / choose right"],
        ["∃x. φ", "choose 項"],
        ["= < ≤", "ring・linarith・連鎖（下に = … by 根拠 を並べる）"],
        ["何でも", "by_contra h（背理法）・根拠 1 つで閉じる（h、h(t)、定理）"]
      ] },
      { p: "**仮定の形で選ぶ**（仮定を使う）" },
      { keys: [
        ["h : ∃x. φ", "Obtain x, hx : h"],
        ["h : φ ∨ ψ", "cases h（下に Case left h1 と Case right h2）"],
        ["h : φ ∧ ψ", "h.left・h.right"],
        ["h : ∀x. φ", "h(t)（x に t を入れる）"],
        ["h : φ → ψ", "h(p)（p は φ の根拠）"]
      ] },
      { p: "**途中で示したことを増やす**：`k : φ by 根拠`（名前は省略できる）。証明が長ければ `k : φ` の下に字下げして書きます。根拠を書かずに `φ` だけ書くとエラーになり、見つかった根拠が候補として出ます（Tab で入る）。" },
      { p: "書き方の完全な一覧は [docs/language/syntax.md](https://github.com/Narfidort/Narfi/blob/main/docs/language/syntax.md) にあります。" }
    ]
  },
  {
    title: "1. はじめての証明",
    blocks: [
      { p: "Narfi では、定理を `thm 名前 :` の下に「仮定 ⊢ 結論」の形で書き、その下に証明を書きます。証明は 1 行ずつ検査され、右上に結果が出ます。" },
      { code: "thm first :\n  P : Prop, h : P\n  |- P\n\nh" },
      { p: "仮定 `h : P` は「命題 $P$ が成り立つ」という仮定に $h$ という名前を付けたものです。結論 $P$ は仮定 $h$ そのものなので、証明は `h` の 1 行です。" },
      { p: "カーソルのある行で何が分かっていて何を示すべきか（Goal）は、右の Goal タブに出ます。まだ書けない所には `sorry` と書いておけます（その定理は「incomplete」になります）。" },
      { p: "⊢ は `\\|-` と打つか、`\\vdash` を補完で選ぶと入ります。ファイルの中では `|-` と保存されます。" }
    ],
    exercise: "-- 練習 1：sorry を消して、証明を書いてください\n\nthm first :\n  P : Prop, h : P\n  |- P\n\nsorry\n",
    answer: "thm first :\n  P : Prop, h : P\n  |- P\n\nh\n"
  },
  {
    title: "2. ならば（→）とかつ（∧）",
    blocks: [
      { p: "$P \\to Q$ を示すには、`assume h : P` で $P$ を仮定し、その下（字下げした所）で $Q$ を示します。仮定の中身 `: P` は省略できません（書かないと、入れるべき式がエラーに出て、行末で Tab を押すと入ります）。" },
      { p: "$P \\land Q$ の仮定 $h$ からは `h.left` で $P$、`h.right` で $Q$ が取り出せます。これは自然演繹の ∧除去の規則で、規則の名前で `and.left(h)`・`and.right(h)` とも書けます。$P \\land Q$ を示すには、根拠を 2 つカンマで並べます（∧導入。`and.intro(p, q)` とも書けます）。" },
      { p: "証明の中で右クリックして「証明木を見る」を選ぶと、その行の証明が自然演繹の木（Gentzen 式・Fitch 式）として見られます。" },
      { code: "assume h : P and Q\n  h.right, h.left" },
      { p: "何を示したのかを書いておきたいときは、命題を書いて `by` の後に根拠を書けます：`Q and P by h.right, h.left`。書いた命題が Goal と違えばエラーになります。" },
      { p: "記号は英単語でも打てます：`->`（→）、`and`（∧）、`or`（∨）、`not`（¬）。" }
    ],
    exercise: "-- 練習 2：P ∧ Q ならば Q ∧ P\n\nthm and_swap :\n  P : Prop, Q : Prop\n  |- P and Q -> Q and P\n\nsorry\n",
    answer: "thm and_swap :\n  P : Prop, Q : Prop\n  |- P and Q -> Q and P\n\nassume h : P and Q\n  h.right, h.left\n"
  },
  {
    title: "3. すべての（∀）とある（∃）",
    blocks: [
      { p: "$\\forall n.\\ \\varphi(n)$ を示すには、`Fix n` で $n$ を任意にとって固定し、その下で $\\varphi(n)$ を示します。" },
      { p: "$\\exists m.\\ \\varphi(m)$ を示すには、`choose t` で $m$ として項 $t$ をとり、その下で $\\varphi(t)$ を示します。" },
      { p: "仮定 $e : \\exists x.\\ \\varphi(x)$ を使うときは、`Obtain x, hx : e` で $x$ と $hx : \\varphi(x)$ を取り出します。" },
      { p: "`refl` は $t = t$ の形の等式を示します。" }
    ],
    exercise: "-- 練習 3：どんな n にも、m = n + n となる m がある\n\nthm double :\n  |- forall n:Nat. exists m:Nat. m = n + n\n\nsorry\n",
    answer: "thm double :\n  |- forall n:Nat. exists m:Nat. m = n + n\n\nFix n\n  choose n + n\n  refl\n"
  },
  {
    title: "4. 計算：等式・不等式の連鎖",
    blocks: [
      { p: "式の変形は、黒板と同じように縦に並べて書けます。各行の `by` の右に、その一歩の根拠を書きます。" },
      { code: "x\n  <= y   by h\n  < z    by k" },
      { p: "根拠には、仮定や定理のほかに自動証明が使えます：`ring`（多項式としての等式）、`linarith`（仮定からの一次不等式）、`decide`（数の計算）。自動証明の結果も、小さな核（kernel）が証明書を検算しています。" },
      { p: "積は `*` で書きます（表示では記号なしで並びます）。数のあとは `*` を省けます：`2x`、`2(a + b)`、`3a_n`。`ab` は a と b の積ではなく、ab という 1 つの名前です。" },
      { p: "`<=` と打つと ≤、`>=` は ≥、`!=` は ≠ になります。分数は `/`（直前の項が分子になります）か `\\fr` + Tab で入ります。" }
    ],
    exercise: "-- 練習 4：x ≤ y と y < z から x < z（連鎖で書いてみる）\n\nthm chain :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nsorry\n",
    answer: "thm chain :\n  x : Real, y : Real, z : Real, h : x <= y, k : y < z\n  |- x < z\n\nx\n  <= y   by h\n  < z    by k\n"
  },
  {
    title: "5. ε を任意にとる",
    blocks: [
      { p: "範囲付きの量化子 $\\forall \\varepsilon > 0.\\ \\varphi$ は、$\\forall \\varepsilon.\\ \\varepsilon > 0 \\to \\varphi$ の略記です。`Fix eps | h_eps : eps > 0` で、$\\varepsilon$ と仮定 $h_\\varepsilon : \\varepsilon > 0$ を一度に導入します。" },
      { p: "$\\exists \\delta > 0.\\ \\varphi$ を示すときは、`choose t, 根拠` で $\\delta$ として $t$ をとり、$t > 0$ の根拠をカンマの後に書きます。" },
      { p: "`eps`・`delta`・`alpha` などは ε・δ・α と表示されます。`_` で添字が入ります（`h_eps` は $h_\\varepsilon$）。" }
    ],
    exercise: "-- 練習 5：どんな ε > 0 にも、それより小さい δ > 0 がある\n\nthm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nsorry\n",
    answer: "thm half_pos :\n  |- forall eps:Real>0. exists d:Real>0. d < eps\n\nFix eps | h_{eps} : eps > 0\n  choose eps/2, linarith\n  linarith\n"
  },
  {
    title: "6. 数列と極限",
    blocks: [
      { p: "数列は ℕ から ℝ への関数として宣言します：`a : Nat -> Real`。こう宣言した $a$ については、$a_n$・$a_{n+1}$ と添字で書けます（`a(n)` と書いても同じです）。" },
      { p: "よく使う述語は `def` で定義できます。定義は、証明の中で必要な所で自動的に展開されます。" },
      { code: "def is_lim(a : Nat -> Real, alpha : Real) :=\n  forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps" },
      { p: "仮定 $h$ が $\\forall \\varepsilon > 0.\\ \\cdots$ の形なら、`h(eps, h_eps)` のように引数と条件の根拠を渡して使えます。$(n \\mapsto a_{n+1})$ は「$n$ を $a_{n+1}$ に移す数列」（λ）で、`|->` か `\\mapsto` で ↦ が入ります。" }
    ],
    exercise: "-- 練習 6：a が α に収束するなら、1 つずらした数列も α に収束する\n\ndef is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : is_lim(a, alpha)\n  |- is_lim((n:Nat |-> a_{n+1}), alpha)\n\nsorry\n",
    answer: "def is_lim(a : Nat -> Real, alpha : Real) := forall eps:Real>0. exists N:Nat. forall n:Nat>=N. abs(a_n - alpha) < eps\n\nthm shift :\n  a : Nat -> Real, alpha : Real, h : is_lim(a, alpha)\n  |- is_lim((n:Nat |-> a_{n+1}), alpha)\n\nFix eps | h_{eps} : eps > 0\n  Obtain N, hN : h(eps, h_{eps})\n  choose N\n  Fix n | h_n : n >= N\n    k : n + 1 >= N by linarith\n    hN(n + 1, k)\n"
  },
  {
    title: "7. 場合分け・背理法・帰納法",
    blocks: [
      { p: "仮定 $h : P \\lor Q$ で場合分けするには `cases h` と書き、その下に `Case left hp` と `Case right hq` を並べます。$P \\lor Q$ を示すときは `choose left` か `choose right` でどちらを示すか選びます。" },
      { p: "背理法は `by_contra hn` です（$\\lnot$ 結論を仮定して矛盾 ⊥ を示します）。" },
      { p: "自然数の帰納法は `induction n` の下に `Case zero` と `Case succ k, IH : φ(k)` を書きます。" }
    ],
    exercise: "-- 練習 7：P ∨ Q ならば Q ∨ P\n\nthm or_swap :\n  P : Prop, Q : Prop, h : P or Q\n  |- Q or P\n\nsorry\n",
    answer: "thm or_swap :\n  P : Prop, Q : Prop, h : P or Q\n  |- Q or P\n\ncases h\n  Case left hp\n    choose right\n    hp\n  Case right hq\n    choose left\n    hq\n"
  },
  {
    title: "8. エディタの使い方",
    blocks: [
      { keys: [
        ["\\fr + Tab, /", "分数"],
        ["_ , ^", "添字・上付き"],
        ["abs( ) , |x|", "絶対値"],
        ["<= >= != -> <->", "≤ ≥ ≠ → ↔"],
        ["\\|- , \\vdash", "⊢"],
        ["|-> , \\mapsto", "↦"],
        ["forall exists eps …", "∀ ∃ ε …（空白で変換）"],
        ["\\ + 名前", "記号の補完（Tab か Enter で決定）"],
        ["Tab（行末）", "エラーに出た直し方を入れる"],
        ["⌘S / ⌘Z", "保存 / 元に戻す"]
      ] },
      { p: "右の Prose タブでは証明が日本語の文章として、LaTeX タブでは論文に貼れる形で読めます。下の `JP` を押すと、エディタの中も日本語の証明文の形で表示されます（ファイルの中身は変わりません）。" },
      { p: "書き方の完全な一覧（すべての文・根拠・規則の名前）は [docs/language/syntax.md](https://github.com/Narfidort/Narfi/blob/main/docs/language/syntax.md) にあります。" },
      { p: "ファイルは左の一覧で作れます（右クリックでフォルダ・名前の変更・削除）。GitHub でログインすると、ほかの端末でも同じファイルが開けます。" }
    ]
  }
];
