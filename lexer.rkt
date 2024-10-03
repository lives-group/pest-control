#lang racket

(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(define-tokens value-tokens
  (CHAR VAR STRING NAT))

(define-empty-tokens op-tokens
  (EOF OR
       LPAREN
       RPAREN
       STAR
       NOT
       SEMI
       EPSILON
       ARROW
       START
       REP
       ANY
       PLUS
       OPTION
       AND
       LBRACK
       RBRACK
       COMMA
       PUSH
       POP
       POPALL
       DROP
       PEEK
       PEEKALL
       DROPALL
       LEN
       TONAT
       INFTY
       LKEYS
       RKEYS
       CAT
       MINUS))

(define next-token
  (lexer-src-pos
   [(eof) (token-EOF)]
   [(:+ whitespace #\newline) (return-without-pos (next-token input-port))]
   ["," (token-COMMA)]
   ["[" (token-LBRACK)]
   ["]" (token-RBRACK)]
   ["{" (token-LKEYS)]
   ["}" (token-RKEYS)]
   ["/" (token-OR)]
   ["~" (token-CAT)]
   ["+" (token-PLUS)]
   ["?" (token-OPTION)]
   ["*" (token-STAR)]
   ["&" (token-AND)]
   ["<--" (token-ARROW)]
   ["!" (token-NOT)]
   ["^" (token-REP)]
   [";" (token-SEMI)]
   ["-" (token-MINUS)]
   ["epsilon" (token-EPSILON)]
   ["start:" (token-START)]
   ["push" (token-PUSH)]
   ["pop" (token-POP)]
   ["drop" (token-DROP)]
   ["peek" (token-PEEK)]
   ["peekall" (token-PEEKALL)]
   ["dropall" (token-DROPALL)]
   ["top.len" (token-LEN)]
   ["top.tonat" (token-TONAT)]
   ["infty" (token-INFTY)]
   ["." (token-ANY)]
   [#\( (token-LPAREN)]
   [#\) (token-RPAREN)]
   [(:seq #\" (complement (:seq any-string #\" any-string)) #\")
    (token-STRING (let* ([s lexeme]
                         [n (string-length s)])
                    (substring s 1 (- n 1))))]
   [(:seq alphabetic (:* (:+ alphabetic numeric)))
    (token-VAR lexeme)]
   [ (:+ numeric)  (token-NAT lexeme)]
   [(:seq #\' any-char #\') (token-CHAR (let* ([s lexeme]
                                               [n (string-length s)])
                                          (substring s 1 (- n 1))))]))


(provide value-tokens op-tokens next-token)
