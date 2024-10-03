#lang racket

(require redex)
(provide (all-defined-out))

;; definition of the index syntax

(define-language IdxL
  (n ::= v
         (op n n)
         infty
         t)
  (v ::= natural)
  (t ::= length
         to-nat)
  (op ::= add
          minus
          mul
          div
          mod)
  (vd ::= natural
          infty)
  (M ::= hole
         (op M n)
         (op vd M))
  (stk ::= (s stk)
           nil)
  (s ::= string)
  (conf ::= (n stk)))

(define-metafunction IdxL
  same-idx? : n n -> boolean
  [(same-idx? 0 to-nat) #t]
  [(same-idx? to-nat 0) #t]
  [(same-idx? length 0) #t]
  [(same-idx? 0 length) #t]
  [(same-idx? n_1 n_1) #t]
  [(same-idx? n_1 n_2) #f])

;; reduction used in type checking

(define-metafunction IdxL
  eval-op : op v v -> v
  [(eval-op add v_1 v_2)
   ,(+ (term v_1) (term v_2))]
  [(eval-op minus v_1 v_2)
   ,(- (term v_1) (term v_2))]
  [(eval-op mul v_1 v_2)
   ,(* (term v_1) (term v_2))]
  [(eval-op div v_1 v_2)
   ,(quotient (term v_1) (term v_2))]
  [(eval-op mod v_1 v_2)
   ,(modulo (term v_1) (term v_2))])  

(define ->s
  (reduction-relation IdxL
      #:domain n
      #:codomain n
      (--> (in-hole M (op infty n_1))
           (in-hole M infty)
           "S-infty-L")
      (--> (in-hole M (op v infty))
           (in-hole M infty)
           "S-infty-R")
      (--> (in-hole M (op to-nat n_1))
           (in-hole M (op 0 n_1))
           "S-tonat-L")
      (--> (in-hole M (op v_1 to-nat))
           (in-hole M (op v_1 0))
           "S-tonat-R")
      (--> (in-hole M (op v_1 length))
           (in-hole M (op v_1 0))
           "S-length-R")
      (--> (in-hole M (op v_1 v_2))
           (in-hole M (eval-op op v_1 v_2))
           "S-Op")))

(define ->s* (compatible-closure ->s IdxL n))

;; definition of tests of the reduction relation

(module+ tests
  (test--> ->s (term (add 1 infty))
               (term infty))
  (test--> ->s (term (mul 2 length))
               (term (mul 2 0)))
  (test--> ->s (term (add infty to-nat))
               (term infty))
  (test--> ->s (term (add 1 3))
               (term 4))
  (test--> ->s (term (div to-nat 2))
               (term (div 0 2)))
  (test-results))

;; defining the type checking normalization

(define-metafunction IdxL
  tc-norm : n -> vd
  [(tc-norm n_1) ,(car (apply-reduction-relation* ->s* (term n_1)))])

;; dynamic semantics

(define-metafunction IdxL
  eval-top : t stk -> v
  [(eval-top length (s_1 stk_1)) ,(string-length (term s_1))]
  [(eval-top to-nat (s_1 stk_1)) ,(string->number (term s_1))])

(define ->e
  (reduction-relation IdxL
      #:domain conf
      #:codomain conf
      (--> ((in-hole M (op infty n_1)) stk)
           ((in-hole M infty) stk)
           "E-infty-L")
      (--> ((in-hole M (op v_1 infty)) stk)
           ((in-hole M infty) stk)
           "E-infty-R")
      (--> ((in-hole M t_1) stk)
           ((in-hole M (eval-top t_1 stk)) stk)
           "E-Top")
      (--> ((in-hole M (op v_1 v_2)) stk)
           ((in-hole M (eval-op op v_1 v_2)) stk)
           "E-Op")))

(define ->e* (compatible-closure ->e IdxL n))

(define-metafunction IdxL
  norm : conf -> conf
  [(norm conf_1) ,(car (apply-reduction-relation* ->e* (term conf_1)))])
