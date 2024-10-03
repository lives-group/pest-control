#lang racket

(provide (all-defined-out))

;; definition of parse trees

(struct tunit
  ()
  #:prefab)

(struct tchr
  (symb)
  #:prefab)

(struct tpair
  (fst snd)
  #:prefab)

(struct tleft
  (tree)
  #:prefab)

(struct tright
  (tree)
  #:prefab)

(struct tlist
  (elems)
  #:prefab)

(struct tpop
  (t)
  #:prefab)

(struct tpush
  (t)
  #:prefab)

(struct tpeek
  (t)
  #:prefab)

(struct tdrop () #:prefab)
(struct tdropall () #:prefab)

(struct tpopall
  (xs)
  #:prefab)

(struct tpeekall
  (xs)
  #:prefab)
