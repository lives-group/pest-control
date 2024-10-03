#lang racket

(require "grammar.rkt"
         "typing/infer.rkt"
         "parser.rkt"
         "pretty.rkt"
         "tree.rkt"
         syntax/strip-context)

(provide (rename-out [peg-read read]
                     [peg-read-syntax read-syntax]))

(define (peg-read in)
  (syntax->datum
   (peg-read-syntax #f in)))

(define (peg-read-syntax path port)
  (define grammar (parse port))
  (let ([types (infer grammar)])
    (if (eq? (cdr types) 'unsat)
        (error "The grammar isn't well-typed! It can loop on some inputs.")
        (datum->syntax
         #f
         `(module peg-mod racket
            (provide parser
                     pretty
                     (all-from-out pest-control/tree))

            (require pest-control/parser
                     pest-control/pretty
                     pest-control/tree
                     pest-control/typing/infer)

            (define (parser s)
              (peg-parse ,grammar s))
            (define (pretty t)
              (peg-pretty ,grammar t)))))))
