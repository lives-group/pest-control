#lang racket

(require parser-tools/yacc
         "core.rkt"
         "lexer.rkt")

;; converting a string token into a tree of
;; characters concatenation

(define (string->tree s)
  (match s
    ['() (peps)]
    [(cons c '()) (pchr c)]
    [(cons c s1) (pcat (pchr c)
                       (string->tree s1))]))

(define core-parser
  (parser
   (start peg)
   (end EOF)
   (tokens value-tokens op-tokens)
   (src-pos)
   (error
    (lambda (a b c d e)
      (begin (printf "parse error:\na = ~a\nb = ~a\nc = ~a\nd = ~a\ne = ~a\n" a b c d e)
             (void))))
   (grammar
    (peg [(rules START expr) (peg-grammar $1 $3)])
    (rules [() '()]
           [(rule rules) (cons $1 $2)])
    (rule [(VAR ARROW expr SEMI) (cons $1 $3)])
    (expr [(cat OR expr) (pchoice $1 $3)]
          [(cat) $1])
    (cat [(cat CAT term) (pcat $1 $3)]
         [(term) $1])
    (term [(prefixop term) ($1 $2)]
          [(factor)   $1])
    (prefixop [(NOT) (lambda (e) (pneg e))]
              [(AND) (lambda (e) (pneg (pneg e)))])
    (factor [(factor postfix) ($2 $1)]
            [(atom) $1])
    (postfix ;[(STAR) (lambda (e) (pstar e))]
             ;[(PLUS) (lambda (e) (pcat e (pstar e)))]
             [(OPTION) (lambda (e) (pchoice e peps))]
             [(LBRACK aexpr COMMA aexpr RBRACK) (lambda (e) (prepeat-interval e $2 $4))]
             [(REP aexpr) (lambda (e) (prepeat-exact e $2))]
             )
    (char-list [(CHAR) (pchr (car (string->list $1)))]
               [(CHAR COMMA char-list) (pchoice $1 $3)])
    (atom [(EPSILON) (peps)]
          [(CHAR)    (pchr (car (string->list $1)))]
          [(STRING)  (string->tree (string->list $1))]
          [(LBRACK char-list RBRACK) $2]
          [(ANY)     (pany)]
          [(VAR)     (pvar $1)]
          [(LPAREN expr RPAREN) $2]
          [(PUSH LPAREN expr RPAREN) (ppush $3)]
          [(POP)     (ppop)]
          [(DROP)    (pdrop)]
          [(PEEK)    (ppeek)]
          [(PEEKALL) (ppeekall)]
          [(DROPALL) (pdropall)]
          )
    (aexpr [(aexpr op1 aterm) (ax-op $2 $1 $3)]
           [(aterm) $1])
    (aterm [(aterm op2 afactor) (ax-op $2 $1 $3)]
           [(afactor) $1])
    (afactor [(NAT) (ax-lit (string->number $1))]
             [(LEN) (ax-var 'len)]
             [(TONAT) (ax-var 'tonat)]
             [(INFTY) (ax-lit 'infty)]
             [(LPAREN aexpr RPAREN) $2])
    (op1 [(PLUS) '+]
         [(MINUS) '-])
    (op2 [(STAR) '*])
    )))

(define (parse ip)
  (port-count-lines! ip)  
  (core-parser (lambda () (next-token ip))))

(provide parse)
