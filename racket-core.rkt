#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (o e e)
       (set! x e) (begin e e ...)
       (var-ref x) (var-ref/no-check x) (var-set! x e) (var-set/check-undef! x e)
       (lambda (x_!_ ...) e)
       (raises e)] ;; expressiosn
  [v   ::= n b c (void) uninit] ;; values
  [c   ::= (closure x ... e ρ)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [o   ::= + * <]
  [EL   ::= hole (v ... EL e ...) (o EL e) (o v EL) (if EL e e)
       (var-set! x EL) (var-set/check-undef! x EL)
       (begin v ... EL e ...) (set! x EL)] ;; eval context

  [ρ   ::= ((x any) ...)] ;; environment
  [σ   ::= ((x any) ...)] ;; store

  [e-test ::= x n b (void)
          (e-test e-test ...) (lambda (x_!_ ...) e-test) (if e-test e-test e-test)
          (p2 e-test e-test) (p1 e-test) (set! x e-test) (begin e-test e-test ...)
          (raises e-test)] ;; to be used to generate test cases (i.e. exclude closures)
  )

; (render-language RC "RC.pdf" #:nts '(e v c n b x p1 p2 o EL ρ σ))

(define-metafunction RC
  [(let-values (((x) e) ...) e_body)
   ((lambda (x ...) e_body) e ...)])

(define-metafunction RC
  δ : (o any any) -> v or true or false or (raises e)
  [(δ (< n_1 n_2)) ,(if (< (term n_1) (term n_2))
                        (term true) (term false))]
  [(δ (+ n_1 n_2)) ,(+ (term n_1) (term n_2))]
  [(δ (* n_1 n_2)) ,(* (term n_1) (term n_2))]
  [(δ (o any_1 any_2)) (raises (o any_1 any_2))])

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
   (--> [(in-hole EL (raises e)) ρ σ]
        [(raises e) ρ σ] "error")
   (--> [(in-hole EL x) ρ σ]
        [(in-hole EL (lookup σ x_1)) ρ σ] "lookup"
        (where x_1 ,(term (lookup ρ x))))

   (--> [(in-hole EL (var-ref x)) ρ σ]
        [(in-hole EL v) ρ σ]
        (where v (lookup σ (lookup ρ x)))
        "var-ref")
   (--> [(in-hole EL (var-ref/no-check x)) ρ σ]
        [(in-hole EL v) ρ σ]
        (where v (lookup σ (lookup ρ x)))
        "var-ref/no-check") ; for now the same with var-ref
   (--> [(in-hole EL (var-set! x v)) ρ σ]
        [(in-hole EL (void)) ρ (extend σ (cell_var) (v))]
        (where cell_var (lookup ρ x))
        "var-set!")
   (--> [(in-hole EL (var-set/check-undef! x v)) ρ σ]
        [(in-hole EL (void)) ρ (extend σ (cell_var) (v))]
        (where cell_var (lookup ρ x))
        (where v_var (lookup σ cell_var)) ; to make sure it's there
        "var-set/check-undef!") ; for now the same with var-set!

   (--> [(in-hole EL (lambda (x ...) e)) ρ σ]
        [(in-hole EL (closure x ... e ρ)) ρ σ] "closure")
   (--> [(in-hole EL (set! x v)) ρ σ]
        [(in-hole EL (void)) ρ (extend σ (x_1) (v))]
        (side-condition (not (equal? (term (raises ,(term x))) (term (lookup ρ x)))))
        (where x_1 ,(term (lookup ρ x))) "set!")
   (--> [(in-hole EL (begin v_1 ... v_n)) ρ σ]
        [(in-hole EL v_n) ρ σ] "begin")
   (--> [(in-hole EL (if v_0 e_1 e_2)) ρ σ]
        [(in-hole EL e_1) ρ σ]
        (side-condition (not (equal? (term v_0) (term false)))) "if-true")
   (--> [(in-hole EL (if false e_1 e_2)) ρ σ]
        [(in-hole EL e_2) ρ σ] "if-false")
   (--> [(in-hole EL (o v_1 v_2 ...)) ρ σ]
        [(in-hole EL (δ (o v_1 v_2 ...))) ρ σ] "δ")
   (--> [(in-hole EL ((closure x ..._n e ρ_1) v ..._n)) ρ_2 σ]
        [(in-hole EL e) (extend ρ_1 (x ...) (x_2 ...)) (extend σ (x_2 ...) (v ...))] "βv"
        (where (x_2 ...) ,(variables-not-in (term e) (term (x ...)))))))

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
