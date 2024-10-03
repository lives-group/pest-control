#lang racket

(provide (all-defined-out))

;; definition of the core expressions

(struct peps
  ()
  #:prefab)

(struct pchr
  (symb)
  #:prefab)

(struct pany
  ()
  #:prefab)

(struct pvar
  (name)
  #:prefab)

(struct pcat
  (left right)
  #:prefab)

(struct pchoice
  (left right)
  #:prefab)

(struct ppop
  ()
  #:prefab)

(struct pdrop
  ()
  #:prefab)

(struct ppeek
  ()
  #:prefab)

(struct ppeekall
  ()
  #:prefab)

(struct ppopall
  ()
  #:prefab)

(struct pdropall
  ()
  #:prefab)

(struct ppush
  (expr)
  #:prefab)

(struct prepeat-exact
  (expr val)
  #:prefab)

(struct prepeat-interval
  (expr val_i val_f)
  #:prefab)

(struct pneg
  (expr)
  #:prefab)

(struct pstar
  (expr)
  #:prefab)

(struct peg-grammar
  (rules start)
  #:prefab)

(struct ax-op ; ax stands for arithmetical expression
  (op left rgth)
  #:prefab)

(struct ax-lit 
  (val)
  #:prefab)

; We will use the symbols 'tonat for top.tonat and 'len for top.length  
(struct ax-var 
  (name)
  #:prefab)