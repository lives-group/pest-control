#lang racket

(require "core.rkt"
         "tree.rkt"
         "parser.rkt"
         "grammar.rkt")

(define (simpleParse peg)
       (parse (open-input-string peg))
  )

(define (simpleParseRun peg s)
       (peg-parse (parse (open-input-string peg)) s)
  )

