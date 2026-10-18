(comment) @comment

(declaration_head kind: _ @keyword)
(declaration_head name: (identifier) @function)

; 未定の対象を導入する大文字の命令（Fix / Obtain / Case）は、小文字の命令と別の色にする
(unknown_intro keyword: _ @constructor)
(unknown_intro name: (identifier) @variable.special)
(case_head keyword: _ @constructor)
(case_head kind: _ @keyword)

(intro keyword: _ @keyword)
(intro name: (identifier) @variable.special)

(keyword) @keyword
(builtin) @function.builtin
(sorry) @string.special

(type) @type
(quantifier) @keyword.operator
(logical) @operator
(turnstile) @punctuation.special
(relation) @operator
(assign) @operator
(operator) @operator
(number) @number
(punctuation) @punctuation.delimiter
