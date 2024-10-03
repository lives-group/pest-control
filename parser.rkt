#lang racket

(require "core.rkt"
         "tree.rkt")

(provide (rename-out [parse peg-parse]))

#;(define (flattent t)
   (match t
      [(tunit)     '()]
      [(tchr c)    (list c)]
      [(tpair f s) (append (flattent f) (flattent s))]
      [(tleft t)   (flattent t)] 
      [(tright t)  (flattent t)]
      [(tlist xs)  (flatten (map flattent xs))]
      [(tpop xs)  (flatten (map flattent xs))]
      [(tpush xs)  (flatten (map flattent xs))]
      [(tdrop)  '()]
      [(tpeek xs)  (flatten (map flattent xs))]
      [(tpeek xs)  (flatten (map flattent xs))]
      [(tpeekall xs)  (flatten (map flattent xs))]
      [(tpopall xs)  (flatten (map flattent xs))]
     )
  )

(define (match-input x s)
      (cond [(null? x) s]
            [(null? s) #f]
            [(char=? (car x) (car s)) (match-input (cdr x) (cdr s))]
            [else #f]
            )
  )
;; definition of the top level parser

(define (parse g s)
  (match g
    [(peg-grammar rs p)
     (let* ([inp (string->list s)]
            [r (run-expr '() rs p inp)])
       (if (null? r)
           (displayln "Could not parse the input string!")
            r))]))

(define (run-eps stk s)
  (list '() s stk))

(define (run-chr stk c s)
  (match s
    ['() '()]
    [(cons c1 s1)
     (if (eq? c c1)
         (list (list c) stk s1)
         '())]))

(define (run-any stk s)
  (match s
    ['() '()]
    [(cons c s1) (list (list c) stk s1)]))

(define (run-var stk g v s)
  (match (assoc v g)
    [#f (begin
          (printf "Undefined variable: ~a\n~a\n" v g)
          '())]
    [(cons _ e1) (run-expr stk g e1 s)]))

(define (run-cat stk g e1 e2 s)
  (match (run-expr stk g e1 s)
    ['() '()]
    [(list p1 stk1 s1)
     (match (run-expr stk1 g e2 s1)
       ['() '()]
       [(list p2 stk2 s2)
        (list (append p1 p2) stk2 s2)])]))

(define (run-choice stk g e1 e2 s)
  (match (run-expr stk g e1 s)
    ['() (match (run-expr stk g e2 s)
           ['() '()]
           [(list p2 stk2 s2)
            (list p2 stk2 s2)])]
    [(list p1 stk1 s1)
     (list p1 stk1 s1)]))

(define (run-neg stk g e1 s)
  (match (run-expr stk g e1 s)
    ['() (list '() stk s)]
    [(list p stk s1) '()]))

(define (run-star stk g e s)
  (match (run-expr stk g e s)
    ['() (list '() stk s)]
    [(list p stk1 s1)
     (match (run-expr stk1 g (pstar e) s1)
       ['() (list p stk1 s1)]
       [(list p2 stk2 s2)
        (list  (append p p2) stk2 s2)])]))

(define (run-repeat-exact stk n g e s)
  (cond
    [(leq n 0) (list '() stk s)]
    [else (match (run-expr stk g e s)
               ['() '()]
               [(list p stk1 s1)
                    (match (run-repeat-exact stk1 (minus n 1) g e s1)
                           ['() '()]
                           [(list p2 stk2 s2)
                            (list (append p p2) stk2 s2)])])]))

(define (run-push stk g e s)
      (match (run-expr stk g e s)
             ['() '()]
             [(list p stk1 s1) (list p (cons  p stk1) s1) ]))

(define (run-pop stk g s)
     (if (null? stk)
         '()
          (match (match-input (car stk) s)
                [#f '()]
                [s1 (list (car stk) (cdr stk) s1)])))

(define (run-peekall stk g s)
     (if (null? stk)
         '()
          (let [(stks (flatten stk))]
               (match (match-input stks s)
                      [#f '()]
                      [s1 (list stks stk s1)]))))

(define (run-dropall stk g s)
      (list '() '() s))

(define (run-peek stk g s)
     (if (null? stk)
         '()
          (match (match-input (car stk) s)
                [#f '()]
                [s1 (list (car stk) stk s1)])))

(define (run-drop stk g s)
     (if (null? stk)
         '()
          (list '() (cdr stk) s)))

(define (run-repeat-while stk t f g e s)
   (cond [(leq f 0) (list t stk s)]
         [else (match (run-expr stk g e s)
                      ['()                       (list t stk s)]
                      [(list t1 stk1 s1) (run-repeat-while stk1
                                                          (append t t1)
                                                          (minus f 1)
                                                          g e s1)]) ])
  )

(define (run-repeat-interval stk i f g e s)
  (cond
    [(le f i) (list '() stk s)]
    [else (match (run-repeat-exact stk i g e s)
              ['() '()]
              [(list t stk1 s1) (run-repeat-while stk1 t f g e s1)])]))

(define (eval stk e)
    (match e
      [(ax-lit n)      n]
      [(ax-lit 'infty) 'infty]
      [(ax-var 'len) (length (car stk))]
      [(ax-var 'tonat) (let ([k (string->number (list->string (car stk)))])
                             (if (not k) (raise 'numberFormatFail) k))]
      [(ax-op '+ e d) (plus (eval stk e) (eval stk d))]
      [(ax-op '- e d) (max 0 (minus (eval stk e) (eval stk d)))]
      [(ax-op '* e d) (mult (eval stk e) (eval stk d))]
      )
  )


(define (le e1 e2)
     (match e1
        ['infty #f]
        [(? number?) (match e2
                      ['infty #t]
                      [(? number?) (< e1 e2)]) ]
       )
  )

(define (leq e1 e2)
     (match e1
        ['infty #f]
        [(? number?) (match e2
                      ['infty #t]
                      [(? number?) (<= e1 e2)]) ]
       )
  )

(define (minus e1 e2)
     (match e1
        ['infty 'infty]
        [(? number?) (match e2
                      ['infty 0]
                      [(? number?) (- e1 e2)]) ]
       )
  )

(define (plus e1 e2)
     (match e1
        ['infty 'infty]
        [(? number?) (match e2
                      ['infty 'infty]
                      [(? number?) (+ e1 e2)]) ]
       )
  )

(define (mult e1 e2)
     (match e1
        ['infty 'infty]
        [(? number?) (match e2
                      ['infty 'infty]
                      [(? number?) (* e1 e2)]) ]
       )
  )

(define (run-expr stk g e s)
  (match e
    [(peps) (run-eps stk s)]
    [(pchr c) (run-chr stk c s)]
    [(pany) (run-any stk s)]
    [(pvar v) (run-var stk g v s)]
    [(pcat e1 e2) (run-cat stk g e1 e2 s)]
    [(pchoice e1 e2) (run-choice stk g e1 e2 s)]
    [(pneg e1) (run-neg stk g e1 s)]
    [(pstar e1) (run-star stk g e1 s)]
    [(prepeat-exact e1 ae) (run-repeat-exact stk (eval stk ae) g e1 s)]
    [(prepeat-interval e1 ai af) (run-repeat-interval stk (eval stk ai) (eval stk af) g e1 s)]
    [(ppush e1) (run-push stk g e1 s)]
    [(ppeek)   (run-peek stk g s)]
    [(ppop)    (run-pop stk g s)]
    [(pdrop)   (run-drop stk g s)]
    [(ppeekall) (run-peekall stk g s)]
    [(pdropall) (run-dropall stk g s)]
  ))
