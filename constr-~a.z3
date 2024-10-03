(declare-datatypes () ((NT Noob918)))


(define-fun empty () (Set NT)
  ((as const (Set NT)) false))

(define-fun singleton ((a NT)) (Set NT)
  (store empty a true))

(define-fun union ((a (Set NT)) (b (Set NT))) (Set NT)
  ((_ map or) a b))

(define-fun imp ((b Bool) (s (Set NT))) (Set NT)
  (ite b s empty))

(declare-datatypes () ((Type (mk-type (is-null Bool) (head-set (Set NT))))))
(declare-datatypes () ((INat (i (value Int))  Infty )) )

(define-fun lt ((a INat) (b INat)) (Bool)
  (match a
     (case (i n) (match b
                    (case (i m) (< n m))
                    (case Infty true) ))
     (case Infty (match b
                    (case (i m) false)
                    (case Infty false)))))

(define-fun gt ((a INat) (b INat)) (Bool)
  (match a
     (case (i n) (match b
                    (case (i m) (> n m))
                    (case Infty false) ))
     (case Infty (match b
                    (case (i m) true)
                    (case Infty false)))))

(define-fun isZero ((a INat)) (Bool)
  (match a
     (case (i n) (= n 0))
     (case Infty false)))

(define-fun isInfty ((a INat)) (Bool)
  (match a
     (case (i n) false)
     (case Infty true)))

(define-fun prod ((a Type) (b Type)) (Type)
  (mk-type (and (is-null a) (is-null b))
           (union (head-set a) (imp (is-null a) (head-set b)))))

(define-fun sum ((a Type) (b Type)) (Type)
  (mk-type (or (is-null a)
               (is-null b))
           (union (head-set a)
                  (head-set b))))

(define-fun star ((a Type)) (Type)
  (mk-type true
           (head-set a)))

(define-fun neg ((a Type)) (Type)
  (mk-type true
           (head-set a)))

(define-fun member ((a NT) (t Type)) (Bool)
  (select (head-set t) a))

(define-fun typow ((a Type) (i INat)) (Type)
  (mk-type (or (isZero i) (is-null a))
           (head-set a)))

(define-fun tyinter ((a Type) (i INat) (j INat)) (Type)
  (mk-type (or (isZero i) (is-null a))
           (head-set a)))
(declare-const t7 Type)
(declare-const t6 Type)
(declare-const t5 Type)
(declare-const t4 Type)
(declare-const t3 Type)
(declare-const t2 Type)
(declare-const t1 Type)
(declare-const t0 Type)
;v3 = <#f,{}>
(assert (= t3 (mk-type false empty)))
;v4 = <#f,{}>
(assert (= t4 (mk-type false empty)))
;v1 = ( v3 * v4 )
(assert (= t1 (prod t3 t4)))
;v6 = <#f,{}>
(assert (= t6 (mk-type false empty)))
;v7 = <#t,{}>
(assert (= t7 (mk-type true empty)))
;v5 = ( v6 + v7 )
(assert (= t5 (sum t6 t7)))
;v2 = v5 [ 0 ,  infty ]
(assert (= t2 (tyinter t5 (i 0) Infty)))
(assert (not (and (= Infty Infty ) (is-null t5) )))
(assert (lt (i 0) Infty))
;0 != infty
(assert (not (= (i 0) Infty)))
;v0 = ( v1 * v2 )
(assert (= t0 (prod t1 t2)))
(check-sat)
(get-model)
