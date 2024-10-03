#lang racket

(require "core.rkt"
         "tree.rkt")

(provide (rename-out [pretty peg-pretty]))


(define (pretty g t)
  (match g
    [(peg-grammar rs p) (list->string (ppr rs p t))]))

(define (ppr-eps t)
  (match t
    [(tunit) '()]
    [t1 (raise 'type-error)]))

(define (ppr-chr c t)
  (match t
    [(tchr c1) (if (eq? c c1)
                   (list c)
                   (raise 'type-error))]
    [t1 (raise 'type-error)]))

(define (ppr-var g v t)
  (match (assoc v g)
    [#f (begin
          (printf "Undefined variable: ~a\n~a\n" v g)
          '())]
    [(cons _ e1)
     (ppr g e1 t)]))

(define (ppr-cat g e1 e2 t)
  (match t
    [(tpair t1 t2)
     (append (ppr g e1 t1)
             (ppr g e2 t2))]
    [t1 (raise 'type-error)]))

(define (ppr-choice g e1 e2 t)
  (match t
    [(tleft t1) (ppr g e1 t1)]
    [(tright t2) (ppr g e2 t2)]
    [t1 (raise 'type-error)]))

(define (ppr-star g e t)
  (match t
    [(tlist ts)
     (append-map
      (lambda (t1) (ppr g e t1))
      ts)]
    [t1 (raise 'type-error)]))

(define (ppr-neg g e t)
  (match t
    [(tunit) '()]
    [t1 (raise 'type-error)]))

(define (ppr-push g e t)
  (match t
    [(tpush t) (ppr g e t)]
    [t1 (raise 'type-error)]))

(define (ppr-drop g t)
  (match t
    [(tdrop) '()]
    [t1 (raise 'type-error)]))

(define (ppr-peekall g t)
  (match t
    [(tpeekall t) t]
    [t1 (raise 'type-error)]))

(define (ppr-popall g t)
  (match t
    [(tpopall t) t]
    [t1 (raise 'type-error)]))

(define (ppr-peek g t)
  (match t
    [(tpeek t) t]
    [t1 (raise 'type-error)]))

(define (ppr-poop g t)
  (match t
    [(tpeek t) t]
    [t1 (raise 'type-error)]))


(define (ppr g e t)
  (match e
    [(peps) (ppr-eps t)]
    [(pchr c) (ppr-chr c t)]
    [(pvar v) (ppr-var g v t)]
    [(pcat e1 e2) (ppr-cat g e1 e2 t)]
    [(pchoice e1 e2) (ppr-choice g e1 e2 t)]
    [(pstar e1) (ppr-star g e1 t)]
    [(pneg e1) (ppr-neg g e1 t)]
    [(ppop) (ppr-poop g t)]
    [(ppush e1) (ppr-push g e1 t)]
    [(pdrop) (ppr-drop g t)]
    [(ppeek) (ppr-peek g t)]
    [(ppopall) (ppr-popall g t)]
    [(ppeekall) (ppr-peekall g t)]))
