#lang racket

(require redex "lang.rkt")

(provide (all-defined-out))

; (render-language RC "RC.pdf" #:nts '(e v c n b x p1 p2 o E ρ σ))

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
(define -->βr
  (reduction-relation
   Linklets
   #:domain (p ρ σ)
   (--> [(in-hole EP (in-hole E (raises e))) ρ σ]
        [(in-hole EP (raises e)) ρ σ] "error")

   (--> [(in-hole EP (in-hole E x)) ρ σ]
        [(in-hole EP (in-hole E (lookup σ x_1))) ρ σ] "lookup"
        (where x_1 ,(term (lookup ρ x))))

   (--> [(in-hole EP (in-hole E (var-ref x))) ρ σ]
        [(in-hole EP (in-hole E v)) ρ σ]
        (where v (lookup σ (lookup ρ x)))
        "var-ref")
   (--> [(in-hole EP (in-hole E (var-ref/no-check x))) ρ σ]
        [(in-hole EP (in-hole E v)) ρ σ]
        (where v (lookup σ (lookup ρ x)))
        "var-ref/no-check") ; for now the same with var-ref
   (--> [(in-hole EP (in-hole E (var-set! x v))) ρ σ]
        [(in-hole EP (in-hole E (void))) ρ (extend σ (cell_var) (v))]
        (where cell_var (lookup ρ x))
        "var-set!")
   (--> [(in-hole EP (in-hole E (var-set/check-undef! x v))) ρ σ]
        [(in-hole EP (in-hole E (void))) ρ (extend σ (cell_var) (v))]
        (where cell_var (lookup ρ x))
        (where v_var (lookup σ cell_var)) ; to make sure it's there
        "var-set/check-undef!") ; for now the same with var-set!

   (--> [(in-hole EP (in-hole E (lambda (x ...) e))) ρ σ]
        [(in-hole EP (in-hole E (closure (x ...) e ρ))) ρ σ] "closure")
   (--> [(in-hole EP (in-hole E (set! x v))) ρ σ]
        [(in-hole EP (in-hole E (void))) ρ (extend σ (x_1) (v))]
        (side-condition (not (equal? (term (raises ,(term x))) (term (lookup ρ x)))))
        (where x_1 ,(term (lookup ρ x))) "set!")
   (--> [(in-hole EP (in-hole E (begin v_1 ... v_n))) ρ σ]
        [(in-hole EP (in-hole E v_n)) ρ σ] "begin")
   (--> [(in-hole EP (in-hole E (if v_0 e_1 e_2))) ρ σ]
        [(in-hole EP (in-hole E e_1)) ρ σ]
        (side-condition (not (equal? (term v_0) (term false)))) "if-true")
   (--> [(in-hole EP (in-hole E (if false e_1 e_2))) ρ σ]
        [(in-hole EP (in-hole E e_2)) ρ σ] "if-false")
   (--> [(in-hole EP (in-hole E (o v_1 v_2))) ρ σ]
        [(in-hole EP (in-hole E (δ (o v_1 v_2)))) ρ σ] "δ")
   (--> [(in-hole EP (in-hole E ((closure (x ..._n) e ρ_1) v ..._n))) ρ_2 σ]
        [(in-hole EP (in-hole E e)) (extend ρ_1 (x ...) (x_2 ...)) (extend σ (x_2 ...) (v ...))] "βv"
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
   (where (any_again) ,(apply-reduction-relation -->βr (term any_1)))]
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
   (where (any_again) ,(apply-reduction-relation -->βr (term any_1)))]
  [(rc-api (any_e any_ρ any_σ)) ((raises any_e) any_ρ any_σ)])
