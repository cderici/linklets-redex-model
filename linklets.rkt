#lang racket

(require redex
         "racket-core.rkt"
         "lang.rkt"
         "util.rkt")

(provide (all-defined-out))

(define -->βp
  (reduction-relation
   Linklets
   #:domain (p ρ σ)
   #;(--> [(in-hole EP (raises e)) ω Ω ρ σ]
          [(raises e) ω Ω ρ σ] "error")
   (--> [(in-hole EP (make-instance)) ρ σ]
        [(in-hole EP ((void) x_li)) ρ σ_1]
        (where x_li ,(variable-not-in (term σ) (term li)))
        (where σ_1 (extend σ (x_li) ((linklet-instance))))
        "make-instance")
   (--> [(in-hole EP (instance-variable-value x_li x)) ρ σ]
        [(in-hole EP (v x_li)) ρ σ]
        (where v (lookup σ (get-var-from-instance x x_li σ)))
        "instance variable value")
   (--> [(in-hole EP (let-inst x (v x_i) p-top)) ρ σ]
        [(in-hole EP p-top) ρ (extend σ (x) (LI))]
        (where LI (lookup σ x_i)) "let-inst")

   (--> [(in-hole EP (seq v_1 ... v_n)) ρ σ]
        [(in-hole EP v_n) ρ σ] "seq")

   (--> [(in-hole EP (instantiate-linklet (Lβ x_target v ... v_last) LI ...)) ρ σ]
        [(in-hole EP (v_last x_target)) ρ σ] "return instance/value")
   (--> [(in-hole EP (instantiate-linklet (Lβ x_target) LI ...)) ρ σ]
        [(in-hole EP ((void) x_target)) ρ σ] "return instance/no-value")

   (--> [(in-hole EP (define-values (x) e)) ρ σ]
        [(in-hole EP (void)) ρ_2 σ_2]
        (where (v ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (where cell ,(variable-not-in (term (x ρ_1 σ_1)) (term cell_1)))
        (where (ρ_2 σ_2) ((extend ρ_1 (x) (cell)) (extend σ_1 (cell) (v))))  "define-values")
   (--> [(in-hole EP e) ρ σ]
        [(in-hole EP v) ρ_1 σ_1]
        (where (v ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (side-condition (not (redex-match? Linklets v (term e)))) "expression")

   (--> [(in-hole EP (instantiate-linklet (Lα c-imps c-exps l-top ...) LI ...)) ρ σ]
        [(in-hole EP (instantiate-linklet (Lα c-imps c-exps l-top ...) LI ... #:target x_target)) ρ σ_1]
        (where x_target ,(variable-not-in (term σ) (term li)))
        (where σ_1 (extend σ (x_target) ((linklet-instance)))))

   (--> [(in-hole EP (instantiate-linklet (Lα c-imps c-exps l-top ...) LI ... #:target x_target)) ρ σ]
        [(in-hole EP (instantiate-linklet (Lβ x_target l-top ...))) ρ_2 σ_1]
        ; set the stage for target/imports/exports
        (where ρ_1 (instantiate-imports c-imps (LI ...) ρ σ))
        (where (ρ_2 σ_1) (instantiate-exports c-exps x_target ρ_1 σ))
        "set the stage for evaluation")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instantiation Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utils for Imports
(define-metafunction Linklets
  get-var-from-instance : x x σ -> cell
  [(get-var-from-instance x x_li σ)
   cell
   (where (linklet-instance (x_bef cell_bef) ... (x cell) (x_aft cell_aft) ...)
          (lookup σ x_li))]
  [(get-var-from-instance x LI σ) (raises not-found)])

(define-metafunction Linklets
  get-instance : n n (LI ...) -> LI
  [(get-instance n n (LI LI_rest ...)) LI]
  [(get-instance n_1 n_2 (LI LI_rest ...))
   (get-instance ,(add1 (term n_1)) n_2 (LI_rest ...))])

(define-metafunction Linklets
  process-import-group : (imp-obj ...) (LI ...) ρ σ -> ρ
  [(process-import-group () (LI ...) ρ σ) ρ]
  [(process-import-group ((Import n x_id x_int x_ext) imp-obj_rest ...)
                             (LI ...) ρ σ)
   (process-import-group (imp-obj_rest ...) (LI ...) ρ_1 σ)
   (where LI_inst (get-instance 0 n (LI ...)))
   (where cell_var (get-var-from-instance x_ext LI_inst σ))
   (where ρ_1 (extend ρ (x_id) (cell_var)))])

(define-metafunction Linklets
  instantiate-imports : c-imps (LI ...) ρ σ -> ρ
  [(instantiate-imports () (LI ...) ρ σ) ρ]
  [(instantiate-imports ((imp-obj ...) (imp-obj_rest ...) ...)
                               (LI ...) ρ σ)
   (instantiate-imports ((imp-obj_rest ...) ...) (LI ...) ρ_1 σ)
   (where ρ_1 (process-import-group (imp-obj ...) (LI ...) ρ σ))])

; Utils for Exports
(define-metafunction Linklets
  process-one-export : exp-obj x ρ σ -> (ρ σ)
  ; target has it
  [(process-one-export (Export x_gen x_id x_ext) x_target ρ σ)
   (ρ_1 σ) ; <- same store (σ) and instances (Ω), i.e. don't create new variable
   (where (linklet-instance (x_bef cell_bef) ... (x_ext cell) (x_aft cell_aft) ...)
          (lookup σ x_target))
   (where ρ_1 (extend ρ (x_gen) (cell)))]
  ; target doesn't have it
  [(process-one-export (Export x_gen x_id x_ext) x_target ρ σ)
   (ρ_1 (extend σ_1 (x_target) ((linklet-instance (x cell) ... (x_ext cell_new)))))
   ; create a new variable and put a reference to it within the target
   (where (linklet-instance (x cell) ...) (lookup σ x_target))
   (where cell_new ,(variable-not-in (term (ρ σ x ... cell ...)) (term cell_1)))
   (where (ρ_1 σ_1) ((extend ρ (x_gen) (cell_new)) (extend σ (cell_new) (uninit))))])

(define-metafunction Linklets
  instantiate-exports : c-exps x ρ σ -> (ρ σ)
  [(instantiate-exports () x ρ σ) (ρ σ)]
  [(instantiate-exports ((Export x_gen x_id x_ext) exp-obj ...) x_target ρ σ)
   (instantiate-exports (exp-obj ...) x_target ρ_1 σ_1)
   (where (ρ_1 σ_1) (process-one-export (Export x_gen x_id x_ext) x_target ρ σ))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instantiation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

Instantiating a linklet is basically getting the imported vars into
the env and evaluating all the forms in the body in the presence of
a "target" linklet instance.

If a target instance is not provided to the instantiation (as an
initial argument), then it's a regular instantiation, we will create a
new instance and evaluate all the forms in the linklet body and the
instantiation will return the created linklet instance (the variables
inside the created instance depends on the evaluated forms within the
linklet body).

If a target is provided to the instantiation, then the instantiation
will take place similarly, but the result will be the result of
evaluating the last expression in the linklet body, i.e. the
instantiation will return a value instead of an instance. This is what
we call "evaluating a linklet".

|#

(define -->βi
  (reduction-relation
   Linklets
   #:domain (L-obj ρ σ)
   (--> [(in-hole EI (define-values (x) e)) ρ σ]
        [(in-hole EI (void)) ρ_2 σ_2]
        (where (v_1 ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (where (ρ_2 σ_2) ((extend ρ_1 (x) (cell)) (extend σ_1 (cell) (v_1))))
        (where cell ,(variable-not-in (term (x ρ_1 σ_1)) (term cell))) "inst-def-val")
   (--> [(in-hole EI e) ρ σ]
        [(in-hole EI v) ρ_1 σ_1]
        (where (v ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (side-condition (not (redex-match? Linklets v (term e))))
        "inst-expr")))
