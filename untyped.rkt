#lang racket

(module reader racket 
(require "grammar.rkt")


(provide (rename-out [peg-read read]
                     [peg-read-syntax read-syntax]))

(define (peg-read in)
  (syntax->datum
   (peg-read-syntax #f in)))

(define (peg-read-syntax path port)
  (define grammar (parse port))
  (datum->syntax
   #f
   `(module peg-mod racket
      (provide parser
               pretty
               (all-from-out "tree.rkt"))

      (require "parser.rkt"
               "pretty.rkt"
               "tree.rkt")
      
      (define (parser s)
        (peg-parse ,grammar s))
      (define (pretty t)
        (peg-pretty ,grammar t)))))
)
