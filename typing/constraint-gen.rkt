#lang racket

(require "../core.rkt"
         "type.rkt"
         "constraint.rkt")

(provide gen-constr)

; interface for the constraint generation state

(define counter 0)

(define (norm e)
    (match e
      [(ax-lit 'infty) (val-infty)]
      [(ax-lit n)      (val-nat n)]
      [(ax-var 'len)   (val-nat 0)]
      [(ax-var 'tonat) (val-nat 0)]
      [(ax-op o e d) (match (cons (norm e) (norm d))
                        [(cons (val-infty) _) (val-infty)]
                        [(cons _ (val-infty)) (val-infty)]
                        [(cons e d) (val-nat (norm-op o e d))]
                        )]
      )
  )
(define (norm-op o e d)
     (match o
        ['+ (+ (val-nat-val e) (val-nat-val d))]
        ['- (- (val-nat-val e) (val-nat-val d))]
        ['* (* (val-nat-val e) (val-nat-val d))])
  )

(define (get-counter)
  counter)

(define (inc-counter)
  (set! counter (add1 counter)))

(define (fresh-var)
  (let ([v (get-counter)])
    (begin
      (inc-counter)
      (term-tyvar v))))

; definition of the constraint generation.

(define (gen-constr grammar)
  (match grammar
    [(peg-grammar rs st)
     (constr-and (gen-constr-rules rs)
                 (let ([tv (fresh-var)])
                   (constr-ex tv (gen-constr-expr st tv))))]))

(define (gen-constr-rule r)
  (match r
    [(cons v e) (let* ([tv (fresh-var)]
                       [c (gen-constr-expr e tv)])
                  (constr-def v tv c))]))

(define (gen-constr-rules rs)
  (match rs
    ['() (constr-T)]
    [(cons c cs) (constr-and (gen-constr-rule c)
                             (gen-constr-rules cs))]))

(define (gen-constr-expr e ty)
  (match e
    [(peps) (constr-eq ty (type #t '()))]
    [(pchr c) (constr-eq ty (type #f '()))]
    [(pany) (constr-eq ty (type #f '()))]
    [(pvar v) (constr-eq (pvar v)
                         ty)]
    [(ppush e1) (gen-constr-expr e1 ty)]
    [(ppop) (constr-eq ty (type #t '()))]
    [(pdrop) (constr-eq ty (type #t '()))]
    [(ppeek) (constr-eq ty (type #t '()))]
    [(pdropall) (constr-eq ty (type #t '()))]
    [(ppeekall) (constr-eq ty (type #t '()))]
    [(prepeat-exact e val) (let* ([tv1 (fresh-var)]
                                    [c1 (gen-constr-expr e tv1)]
                                    [n1 (norm val)])
                              (constr-and (constr-ex tv1 c1)
                                          (constr-and (constr-eq ty (term-pow tv1 n1))
                                                      (constr-diff n1 (val-infty))))
                             )]
    [(prepeat-interval e i f)
     (let* ([tv1 (fresh-var)]
            [c1 (gen-constr-expr e tv1)]
            [ni (norm i)]
            [nf (norm f)])
            (constr-and (constr-ex tv1 c1)
                        (constr-and (constr-eq ty (term-interval tv1 ni nf))
                                    (constr-diff ni (val-infty)))))
                             ]
    [(pchoice e1 e2)
     (let* ([tv1 (fresh-var)]
            [tv2 (fresh-var)]
            [c1  (gen-constr-expr e1 tv1)]
            [c2  (gen-constr-expr e2 tv2)])
       (constr-ex
        tv1
        (constr-ex
         tv2
         (constr-and
          c1
          (constr-and
           c2
           (constr-eq
            ty
            (term-plus tv1 tv2)))))))]
    [(pcat e1 e2)
     (let* ([tv1 (fresh-var)]
            [tv2 (fresh-var)]
            [c1 (gen-constr-expr e1 tv1)]
            [c2 (gen-constr-expr e2 tv2)])
       (constr-ex
        tv1
        (constr-ex
         tv2
         (constr-and
          c1
          (constr-and
           c2
           (constr-eq ty
                      (term-prod tv1 tv2)))))))]
    [(pstar e1)
     (let* ([tv1 (fresh-var)]
            [c1  (gen-constr-expr e1 tv1)])
       (constr-ex
        tv1
        (constr-and c1
                    (constr-eq ty
                               (term-star tv1)))))]
    [(pneg e1)
     (let* ([tv1 (fresh-var)]
            [c1 (gen-constr-expr e1 tv1)])
       (constr-ex
        tv1
        (constr-and
         c1
         (constr-eq ty
                    (term-not tv1)))))]))
