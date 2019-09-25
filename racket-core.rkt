#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (p1 e) (p2 e e)
       (set! x e) (begin e e ...)
       (var-ref x) (var-ref/no-check x) (var-set! x e) (var-set/check-undef! x e)
       (lambda (x_!_ ...) e) (let-values (((x_!_) e) ...) e)
       (raises e)] ;; expressiosn
  [v   ::= n b c (void) uninit] ;; values
  [c   ::= (closure x ... e ρ)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [p1  ::= add1]
  [p2  ::= + * <]
  [o   ::= p1 p2]
  [E   ::= hole (v ... E e ...) (o v ... E e ...) (if E e e)
       (var-set! x E) (var-set/check-undef! x E)
       (begin v ... E e ...) (set! x E)
       (let-values (((x) v) ... ((x) E) ((x) e) ...) e)] ;; eval context

  [ρ   ::= ((x any) ...)] ;; environment
  [σ   ::= ((x any) ...)] ;; store

  [e-test ::= x n b (void)
          (e-test e-test ...) (lambda (x_!_ ...) e-test) (if e-test e-test e-test)
          (p2 e-test e-test) (p1 e-test) (set! x e-test) (begin e-test e-test ...)
          (let-values (((x) e-test) ...) e-test) (raises e-test)] ;; to be used to generate test cases (i.e. exclude closures)
  )

; (render-language RC "RC.pdf" #:nts '(e v c n b x p1 p2 o E ρ σ))

(define-metafunction RC
  δ : (o any ...) -> v or true or false or (raises e)
  [(δ (add1 n)) ,(add1 (term n))]
  [(δ (< n_1 n_2)) ,(if (< (term n_1) (term n_2)) (term true) (term false))]
  [(δ (+ n_1 n_2)) ,(+ (term n_1) (term n_2))]
  [(δ (* n_1 n_2)) ,(* (term n_1) (term n_2))]
  [(δ (o any_1 any_2 ...)) (raises (o any_1 any_2 ...))])

(define-metafunction RC
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction RC
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   (raises any_1)])

;; standard reduction
(define -->βs
  (reduction-relation
   RC
   #:domain (e ρ σ)
   (--> [(in-hole E (raises e)) ρ σ]
        [(raises e) ρ σ] "error")
   (--> [(in-hole E x) ρ σ]
        [(in-hole E (lookup σ x_1)) ρ σ] "lookup"
        (where x_1 ,(term (lookup ρ x))))

   (--> [(in-hole E (var-ref x)) ρ σ]
        [(in-hole E v) ρ σ]
        (where (variable x_var v) (lookup σ (lookup ρ x)))
        "var-ref")
   (--> [(in-hole E (var-ref/no-check x)) ρ σ]
        [(in-hole E v) ρ σ]
        (where (variable x_var v) (lookup σ (lookup ρ x)))
        "var-ref/no-check") ; for now the same with var-ref
   (--> [(in-hole E (var-set! x v)) ρ σ]
        [(in-hole E (void)) ρ (extend σ (cell_var) ((variable x_var v)))]
        (where cell_var (lookup ρ x))
        (where (variable x_var v_var) (lookup σ cell_var))
        "var-set!")
   (--> [(in-hole E (var-set/check-undef! x v)) ρ σ]
        [(in-hole E (void)) ρ (extend σ (cell_var) ((variable x_var v)))]
        (where cell_var (lookup ρ x))
        (where (variable x_var v_var) (lookup σ cell_var))
        "var-set/check-undef!") ; for now the same with var-set!

   (--> [(in-hole E (lambda (x ...) e)) ρ σ]
        [(in-hole E (closure x ... e ρ)) ρ σ] "closure")
   (--> [(in-hole E (set! x v)) ρ σ]
        [(in-hole E (void)) ρ (extend σ (x_1) (v))]
        (side-condition (not (equal? (term (raises ,(term x))) (term (lookup ρ x)))))
        (where x_1 ,(term (lookup ρ x))) "set!")
   (--> [(in-hole E (begin v_1 ... v_n)) ρ σ]
        [(in-hole E v_n) ρ σ] "begin")
   (--> [(in-hole E (let-values (((x) v) ...) e)) ρ σ]
        [(in-hole E e) (extend ρ (x ...) (x_2 ...)) (extend σ (x_2 ...) (v ...))] "let"
        (where (x_2 ...) ,(variables-not-in (term e) (term (x ...)))))
   (--> [(in-hole E (if v_0 e_1 e_2)) ρ σ]
        [(in-hole E e_1) ρ σ]
        (side-condition (not (equal? (term v_0) (term false)))) "if-true")
   (--> [(in-hole E (if false e_1 e_2)) ρ σ]
        [(in-hole E e_2) ρ σ] "if-false")
   (--> [(in-hole E (o v_1 v_2 ...)) ρ σ]
        [(in-hole E (δ (o v_1 v_2 ...))) ρ σ] "δ")
   (--> [(in-hole E ((closure x ..._n e ρ_1) v ..._n)) ρ_2 σ]
        [(in-hole E e) (extend ρ_1 (x ...) (x_2 ...)) (extend σ (x_2 ...) (v ...))] "βv"
        (where (x_2 ...) ,(variables-not-in (term e) (term (x ...)))))))

(define -->βss ;; just for pictures (render-reduction-relation)
  (reduction-relation
   RC
   #:domain (e ρ σ)
   (--> [(in-hole E (raises e)) ρ σ]
        [(raises e) ρ σ] "error")
   (--> [(in-hole E x) ρ σ]
        [(in-hole E (lookup σ x_1)) ρ σ] "lookup"
        (where x_1 ,(term (lookup ρ x))))
   (--> [(in-hole E (lambda (x ...) e)) ρ σ]
        [(in-hole E (closure x ... e ρ)) ρ σ] "closure")
   (--> [(in-hole E (set! x v)) ρ σ]
        [(in-hole E (void)) ρ (extend σ (c_1) (v))]
        (side-condition (term ((lookup ρ x) ≠ (raises x))))
        (where c_1 ,(term (lookup ρ x))) "set!")
   (--> [(in-hole E (begin v_1 ... v_n)) ρ σ]
        [(in-hole E v_n) ρ σ] "begin")
   (--> [(in-hole E (let-values (((x) v) ...) e)) ρ σ]
        [(in-hole E e) (extend ρ (x ...) (x_2 ...)) (extend σ (x_2 ...) (v ...))] "let"
        (where (x_2 ...) ,(term (variables-not-in e (x ...)))))
   (--> [(in-hole E (if v_0 e_1 e_2)) ρ σ]
        [(in-hole E e_1) ρ σ]
        (side-condition (term (v_0 ≠ false))) "if-true")
   (--> [(in-hole E (if false e_1 e_2)) ρ σ]
        [(in-hole E e_2) ρ σ] "if-false")
   (--> [(in-hole E (o v_1 v_2 ...)) ρ σ]
        [(in-hole E (δ (o v_1 v_2 ...))) ρ σ] "δ")
   (--> [(in-hole E ((closure x ..._n e ρ_1) v ..._n)) ρ_2 σ]
        [(in-hole E e) (extend ρ_1 (x ...) (c_2 ...)) (extend σ (c_2 ...) (v ...))] "βv"
        (where (c_2 ...) ,(term (variables-not-in e (x ...)))))))


(define-metafunction RC
  eval-rc : e -> v or closure or stuck
  [(eval-rc e) (run-rc (e () ()))])

(define-metafunction RC
  ;run-rc : (e Σ σ) -> v or closure or stuck
  [(run-rc (n ρ σ)) n]
  [(run-rc (b ρ σ)) b]
  [(run-rc (c ρ σ)) closure]
  [(run-rc ((void) ρ σ)) (void)]
  [(run-rc ((raises e) ρ σ)) stuck]
  [(run-rc any_1)
   (run-rc any_again)
   (where (any_again) ,(apply-reduction-relation -->βs (term any_1)))]
  [(run-rc any_1) stuck])

(define-metafunction RC
  ;rc-api : (e Σ σ) -> (rc-out Σ σ)
  [(rc-api (n ρ σ)) (n ρ σ)]
  [(rc-api (b ρ σ)) (b ρ σ)]
  [(rc-api (c ρ σ)) (c ρ σ)]
  [(rc-api ((void) ρ σ)) ((void) ρ σ)]
  [(rc-api ((raises e) ρ σ)) ((raises e) ρ σ)]
  [(rc-api any_1)
   (rc-api any_again)
   (where (any_again) ,(apply-reduction-relation -->βs (term any_1)))]
  [(rc-api (any_e any_ρ any_σ)) ((raises any_e) any_ρ any_σ)])
