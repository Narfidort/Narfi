/**
 * Narfi の tree-sitter 文法（色分け用）。
 *
 * 書きかけの証明でも崩れないように、構造は最小限にして「トークンの並び」として読む。
 * 意味のある塊は、宣言の見出し（thm 名前）と、名前を導入する命令（Fix x、have h など）だけ。
 */
const IDENT = /[\p{L}_][\p{L}\p{Nd}_'₀-₉]*(\.[\p{L}_][\p{L}\p{Nd}_'₀-₉]*)*/;

module.exports = grammar({
  name: 'narfi',
  extras: $ => [/\s/, $.comment],
  word: $ => $.identifier,

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.declaration_head,
      $.unknown_intro,
      $.intro,
      $.case_head,
      $.keyword,
      $.builtin,
      $.sorry,
      $.type,
      $.quantifier,
      $.logical,
      $.turnstile,
      $.relation,
      $.assign,
      $.operator,
      $.number,
      $.identifier,
      $.punctuation,
    ),

    comment: _ => token(seq('--', /.*/)),

    declaration_head: $ => seq(field('kind', choice('thm', 'axiom')), field('name', $.identifier)),

    // 未定の対象を導入する大文字の命令（仕様書 §9.2）
    unknown_intro: $ => seq(field('keyword', choice('Fix', 'Obtain')), field('name', $.identifier)),
    case_head: $ => seq(field('keyword', 'Case'), field('kind', choice('left', 'right', 'zero', 'succ'))),

    intro: $ => seq(field('keyword', choice('assume', 'have', 'let', 'by_contra')), field('name', $.identifier)),

    keyword: _ => choice('choose', 'suffices', 'contradiction', 'induction', 'cases', 'by', 'left', 'right'),
    builtin: _ => choice('ring', 'linarith', 'decide', 'refl', 'EQ1', 'EQ2', 'or.left', 'or.right'),
    sorry: _ => 'sorry',

    type: _ => choice(token(prec(2, /[ℕℤℚℝℂ]/)), 'Prop'),
    quantifier: _ => token(prec(2, /[∀∃λ]/)),
    logical: _ => choice('→', '∧', '∨', '¬', '⊥', '↔', '->', '/\\', '\\/'),
    turnstile: _ => choice('⊢', '∴', '⇐', '|-'),
    relation: _ => choice('=', '≠', '<', '≤', '>', '≥', '∈', '<=', '>=', '!='),
    assign: _ => ':=',
    operator: _ => choice('+', '-', '−', '·', '*', '/', '^', '²', '³', '|'),
    number: _ => /\d+/,
    punctuation: _ => choice('(', ')', ',', ':', '.'),

    identifier: _ => IDENT,
  },
});
