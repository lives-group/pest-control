#lang racket

;; main type inference driver

(require "../core.rkt"
         "type.rkt"
         "constraint-gen.rkt"
         "constraint-solver.rkt"
         "solver/model-parser.rkt")

(provide infer)

(define (infer g)
  (let* ([constr (gen-constr g)]
         [p (solver constr)]
         [result-string (cdr p)])
        (cons (car p) (parse (open-input-string result-string)))))
