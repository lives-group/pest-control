#lang racket

(require redex
         "idx.rkt")

(define-extended-language PegStackL IdxL
  (symb ::= natural)
  (nt ::= variable-not-otherwise-mentioned)
  (e ::= epsilon
         (chr symb)
         (cat e e)
         (choice e e)
         (not e)
         (rep e n)     -- exact repetition
         (inter e n n) -- interval repetition
         (push e)
         pop
         peek
         peek-all
         drop
         drop-all)
  (r ::= (nt e))
  (g ::= ((r ...) e))
  (inp ::= (symb ...))
  (b ::= boolean)
  (ty ::= (b H))
  (H  ::= (nt ...))
  (T ::= (nt ty))
  (G ::= (T ...))
  (res ::= (inp inp stk)
           F))


;; big step semantics

(define-metafunction PegStackL
  same? : symb symb -> boolean
  [(same? symb_1 symb_1) #t]
  [(same? symb_1 symb_2) #f])

(define-metafunction PegStackL
  concat : (symb ...) (symb ...) -> (symb ...)
  [(concat (symb_1 ...) (symb_2 ...)) (symb_1 ... symb_2 ...)])

(define-metafunction PegStackL
  union : (nt ...) (nt ...) -> (nt ...)
  [(union (nt_1 ...) ())  (nt_1 ...)]
  [(union () (nt_1 ...) )  (nt_1 ...)]
  [(union (nt_1 nt_2 ...) (nt_3 ... nt_1  nt_4 ...))
   (union (nt_1 nt_2 ...)
          (nt_3 ... nt_4 ...))]
  [(union (nt_1 nt_2 ...) (nt_3 nt_4 ...))
   (union (nt_1 nt_2 ... nt_3) (nt_4 ...))])

(define-metafunction PegStackL
  lt : n n -> boolean
  [(lt v_1 v_2) (< v_1 v_2)]
  [(lt n_1 infty) #t]
  [(lt infty n_2) #f]
  [(lt length n_1) #f]
  [(lt n_1 to-nat) #f]
  [(lt n_1 length) #f])

(define-metafunction PegStackL
  ty-prod : ty ty -> ty
  [(ty-prod (b_1 H_1) (b_2 H_2))
   (if b_1 (b_2 (union H_1 H_2))
           (b_2 H_1))])

(define-metafunction PegStackL
  ty-sum : ty ty -> ty
  [(ty-sum (b_1 H_1) (b_2 H_2))
   ((or b_1 b_2) (union H_1 H_2))])

(define-metafunction PegStackL
  ty-not : ty -> ty
  [(ty-not (b_1 H_1)) (#t H1)])

(define-judgment-form PegStackL
  #:contract (type-of G e ty)
  #:mode (type-of I I O)
  [
   -----------------------------------------"T-epsilon"
   (type-of G epsilon (#t ()))
  ]
  [
   -----------------------------------------"T-symb"
   (type-of G (chr symb_1) (#f ()))
  ]
  [
   (where #f (in-head-set nt H1))
   ----------------------------------------------------------"T-nt"
   (type-of (T_1 ... (nt (b_1 H_1)) T_2 ...) nt (b_1 H_1))
  ]
  [
   (type-of G e_1 ty_1)
   (type-of G e_2 ty_2)
   -----------------------------------------------------------"T-cat"
   (type-of G (cat e_1 e_2) (ty-prod ty_1 ty_2))
  ]
  [
   (type-of G e_1 ty_1)
   (type-of G e_2 ty_2)
   -----------------------------------------------------------"T-choice"
   (type-of G (cat e_1 e_2) (ty-sum ty_1 ty_2))
  ]
  [
   (type-of G e_1 ty)
   -----------------------------------------------------------"T-not"
   (type-of G (not e_1) (ty-not ty))
  ]
  [
   (where n_2 (tc-norm n_1))
   (where #t (same-idx? n_2 infty))
   (type-of G e_1 (#f H_1))
   --------------------------------------------------------"T-rep-infty"
   (type-of G (rep e_1 n_1) (#t H_1))
  ]
  [
   (where n_2 (tc-norm n_1))
   (where #f (same-idx? n_2 infty))
   (where b_2 (same-idx? n_2 0))
   (type-of G e_1 (b_1 H_1)) 
   --------------------------------------------------------"T-rep"
   (type-of G (rep e_1 n_1) ((or b_1 b_2) H_1))
  ]
  [
   (where n_3 (tc-norm n_1))
   (where n_4 (tc-norm n_2))
   (where #t (lt n_3 n_4))
   (type-of G e_1 (b_1 H_1))
   (where b_3 (or b_1 (same-idx? n_4 infty)))
   ---------------------------------------------------------"T-inter"
   (type-of G (inter n_1 n_2 e_1) (b_3 H_1))
  ]
  [
   (type-of G e_1 ty_1)
   ----------------------------------"T-push"
   (type-of G (push e_1) ty_1)
  ]
  [
   -----------------------------------"T-pop"
   (type-of G pop (#t ()))
  ]
  [
   -----------------------------------"T-peek"
   (type-of G peek (#t ()))
  ]
  [
   -----------------------------------"T-drop"
   (type-of G drop (#t ()))
  ]
  [
   -----------------------------------"T-peek_all"
   (type-of G peek-all (#t ()))
  ]
  [
   -----------------------------------"T-drop_all"
   (type-of G drop-all (#t ()))
  ]
)

; como garantir que todas as regras possuem o tipo correto
; na gramática?

(define-judgment-form PegStackL
  #:contract (typed-grammar G g)
  #:mode (typed-grammar I I)
  [
    ------------------------------------------"T-grammar"
    (typed-grammar G_1 g_1)
  ])

(define-judgment-form PegStackL
  #:contract (eval g e stk inp res)
  #:mode (eval I I I I O)
  [
   -----------------------------------------"E-epsilon"
   (eval g epsilon stk inp_1 (() inp_1 stk))
  ]
  [
   ---------------------------------------------------------------"E-symb-succ"
   (eval g (chr symb_1) stk (symb_1 symb_2 ...) ((symb_1) (symb_2 ...) stk))
  ]
  [
   (where #f (same symb_1 symb_2))
   ------------------------------------"E-symb-fail"
   (eval g (chr symb_1) stk (symb_2 symb_3 ...) F)
  ]
  [
    (eval (r_1 ... (nt e) r_2 ...) e stk inp res_1)
    ----------------------------------------------------"E-nt"
    (eval (r_1 ... (nt e) r_2 ...) nt stk inp res_1)
  ]
  [
    (eval g e_1 stk inp (inp_1 inp_2 stk_1))
    (eval g e_2 stk_1 inp_2 (inp_3 inp_4 stk_2))
    -----------------------------------------------------"E-cat-succ"
    (eval g (cat e_1 e_2) stk inp ((concat inp_1 inp_3) inp_4 stk_2))
  ]
  [
    (eval g e_1 stk inp F)
    -----------------------------------------------------"E-cat-fail1"
    (eval g (cat e_1 e_2) stk inp F)     
  ]  
  [
    (eval g e_1 stk inp (inp_1 inp_2 stk_1))
    (eval g e_2 stk_1 inp_2 F)
    -----------------------------------------------------"E-cat-fail2"
    (eval g (cat e_1 e_2) stk inp F)     
  ]
  [
    (eval g e_1 stk inp (inp_1 inp_2 stk_1))
    -----------------------------------------------------"E-choice-succ1"
    (eval g (choice e_1 e_2) stk inp (inp_1 inp_2 stk_1))
  ]
  [
     (eval g e_1 stk inp F)
     (eval g e_2 stk inp res_1)
     ----------------------------------------------------"E-choice-succ2"
     (eval g (choice e_1 e_2) stk inp res_1)
  ]
  [
     (eval g e_1 stk inp F)
   ------------------------------------------------------"E-not-succ"
     (eval g (not e_1) stk inp (() inp stk))
  ]
  [
     (eval g e_1 stk inp (inp_1 inp_2 stk_1))
   ------------------------------------------------------"E-not-fail"
     (eval g (not e_1) stk inp F)
  ]
  [
     (where 0 (norm (n_1 stk)))
   ------------------------------------------------------"E-rep-zero"
   (eval g (rep e_1 n_1) stk inp (() inp stk))
  ]
  [
      (where (n_1 stk_1) (norm (n stk)))
      (where #t (lt 0 n_1))
   -------------------------------------------------------"E-rep-fail1"
      (eval g (rep e_1 n) stk inp (() inp stk))
  ]
  [
    (where (n_1 stk_1) (norm (n stk)))
    (where #t (lt 0 n_1))
    (eval g e_1 stk inp (inp_1 inp_2 stk_1))
    (eval g (rep e_1 (minus n_1 1)) stk_1 inp_2 F)
    ------------------------------------------------------"E-rep-fail2"
    (eval g (rep e_1 n) stk inp F)
  ]
  [
    (where (n_1 stk_1) (norm (n stk)))
    (where #t (lt 0 n_1))
    (eval g e_1 stk inp (inp_1 inp_2 stk_1))
    (eval g (rep e_1 (minus n_1 1)) stk_1 inp_2 (inp_3 inp_4 stk_2))
    -----------------------------------------------------------------"E-rep-succ"
    (eval g (rep e_1 n) stk inp ((concat inp_1 inp_3) inp_4 stk_2))
  ]
  [
   (where n_3 (norm (n_1 stk)))
   (where n_3 (norm (n_2 stk)))
   (eval g (rep e_1 n_3) stk inp res_1)
   --------------------------------------------------------------"E-inter-base1"
   (eval g (inter e_1 n_1 n_2) stk inp res_1)
  ]
  [
    (where n_3 (norm (n_1 stk)))
    (where n_4 (norm (n_2 stk)))
    (where #t (lt n_3 n_4))
    (eval g (rep e_1 n_4) stk inp_1 (inp_2 inp_3 stk_1))
    --------------------------------------------------------------"E-inter-base2"
    (eval g (inter e_1 n_1 n_2) stk inp_1 (inp_2 inp_3 stk_1))
  ]
  [
    (where n_3 (norm (n_1 stk)))
    (where n_4 (norm (n_2 stk)))
    (where #t (lt n_3 n_4))
    (eval g (rep e_1 n_4) stk inp_1 F)
    (eval g (inter e_1 n_3 (minus n_4 1)) stk inp_1 res_1)
    --------------------------------------------------------------"E-inter-rec"
    (eval g (inter e_1 n_1 n_2) stk inp_1 res_1)
  ]
)