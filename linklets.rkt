#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language LinkletSource RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]

  [l-top ::= d e] ; linklet body expressions
  [d ::= (define-values (x) e)]

  ;; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  ;; (internal-exported-id external-exported-id)
  [exp-id ::= x (x x)])

(define-extended-language Linklets LinkletSource
  ;; compile
  [CL ::= (compile-linklet L)]
  [L-obj ::= (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top ...)]
  ;; import & export objects
  [imp-obj ::= (Import n x x x)] ; group-index id(<-gensymed) int_id ext_id
  [exp-obj ::= (Export x x x)] ; int_id int_gensymed ext_id

  ;; instantiate
  [LI ::= (linklet-instance (x cell) ...)] ;; note that an instance have no exports
  [I ::= v LI (instantiate-linklet linkl-ref inst-ref ...)
     (instantiate-linklet linkl-ref inst-ref ... #:target inst-ref)]

  [linkl-ref ::= x L-obj (raises e)]
  [inst-ref ::= x LI (raises e)]

  ;; program-stuff
  [p ::= (program (use-linklets (x_!_ L) ...) p-top ... final-expr)]
  [p-top :== I (let-inst x I) (instance-variable-value inst-ref x)]
  [final-expr ::= p-top v]

  ;; environments
  [ω   ::= ((x L-obj) ...)] ; linklet env
  [Ω   ::= ((x LI) ...)] ; instance env

  [V ::= v LI]
  ; extend the evaluation context of Racket Core with the new var-set!s

  ;; evaluation-context for the programs
  [EP ::= hole
          (program (use-linklets) V ... (let-inst x EL) p-top ... final-expr)
          (program (use-linklets) V ... EL p-top ... final-expr)
          (program (use-linklets) V ... EL)]
  [EL ::= hole
          (instantiate-linklet EL inst-ref ...) ;; resolve the linklet
          (instantiate-linklet L-obj LI ... EL inst-ref ...) ;; resolve the imported instances
          (instantiate-linklet EL inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate-linklet L-obj LI ... EL inst-ref ... #:target inst-ref) ;; resolve the imported instances
          (instance-variable-value EL x)]

  ;; evaluation-context for the linklet body
  [EI ::= hole (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) v ... EI l-top ...)]
  )

(define-extended-language LinkletProgramTest Linklets
  [p-test ::= (program (use-linklets (x_!_ L) ...) p-top-test ... final-expr)]
  [p-top-test ::= (instantiate-linklet x x ... #:target I-test)
                  (let-inst x (instantiate-linklet x x ...))
                  (instance-variable-value inst-ref x)
                  n b (void)]
  [I-test ::= x (linklet-instance)]
  [final-expr-test ::= p-top-test v])

(define -->βp
  (reduction-relation
   Linklets
   #:domain (p ω Ω ρ σ)
   (--> [(in-hole EP (raises e)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ] "error")
   (--> [(in-hole EL (raises e)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ] "error in EL")
   (--> [(in-hole EP x) ω Ω ρ σ]
        [(in-hole EP L-obj_found) ω Ω ρ σ]
        (where L-obj_found (lookup ω x))
        "linklet-lookup")
   (--> [(in-hole EP x) ω Ω ρ σ]
        [(in-hole EP LI_found) ω Ω ρ σ]
        (where LI_found (lookup Ω x))
        "instance-lookup")
   (--> [(in-hole EP (instance-variable-value LI x)) ω Ω ρ σ]
        [(in-hole EP v) ω Ω ρ σ]
        (where (variable x_var v) (lookup σ (get-var-from-instance x LI)))
        "instance variable value")
   (--> [(in-hole EP (instance-variable-value L-obj x)) ω Ω ρ σ]
        [(raises instance-expected) ω Ω ρ σ] "instance variable value error")
   (--> [(in-hole EP (let-inst x LI)) ω Ω ρ σ]
        [(in-hole EP (void)) ω (extend Ω (x) (LI)) ρ σ] "let-inst")
   (--> [(in-hole EP (instantiate-linklet L-obj LI ...)) ω Ω ρ σ]
        [(in-hole EP LI_1) ω_1 Ω_1 ρ σ_1]
        (where (LI_1 ω_1 Ω_1 ρ_1 σ_1)
               (instantiate-entry ω Ω ρ σ L-obj LI ...)) "instantiate linklet")
   (--> [(in-hole EP (instantiate-linklet L-obj LI ... #:target inst-ref_80)) ω Ω ρ σ]
        [(in-hole EP v_1) ω_1 Ω_1 ρ_1 σ_1]
        (where (v_1 ω_1 Ω_1 ρ_1 σ_1)
               (instantiate-entry ω Ω ρ σ L-obj LI ... #:target inst-ref_80)) "eval linklet")
   (--> [(in-hole EP (instantiate-linklet L-obj LI ...)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ]
        (where (raises e) (instantiate-entry ω Ω ρ σ L-obj LI ...)) "error in instantiation")
   (--> [(in-hole EP (instantiate-linklet L-obj LI ... #:target inst-ref_80)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ]
        (where (raises e) (instantiate-entry ω Ω ρ σ L-obj LI ... #:target inst-ref_80)) "error in evaluation")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instantiation Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utils for Imports
(define-metafunction Linklets
  get-var-from-instance : x LI -> cell
  [(get-var-from-instance
    x (linklet-instance (x_bef cell_bef) ... (x cell) (x_aft cell_aft) ...)) cell]
  [(get-var-from-instance x LI) (raises not-found)])

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
   (where cell_var (get-var-from-instance x_ext LI_inst))
   (where ρ_1 (extend ρ (x_id) (cell_var)))])

(define-metafunction Linklets
  instantiate-imports : ((imp-obj ...) ...) (LI ...) ρ σ -> ρ
  [(instantiate-imports () (LI ...) ρ σ) ρ]
  [(instantiate-imports ((imp-obj ...) (imp-obj_rest ...) ...)
                               (LI ...) ρ σ)
   (instantiate-imports ((imp-obj_rest ...) ...) (LI ...) ρ_1 σ)
   (where ρ_1 (process-import-group (imp-obj ...) (LI ...) ρ σ))])

; Utils for Exports
(define-metafunction Linklets
  process-one-export : exp-obj x Ω ρ σ -> (Ω ρ σ)
  ; target has it
  [(process-one-export (Export x_id x_gen x_ext) x_target Ω ρ σ)
   (Ω ρ_1 σ) ; <- same store (σ) and instances (Ω), i.e. don't create new variable
   (where (linklet-instance (x_bef cell_bef) ... (x_ext cell) (x_aft cell_aft) ...)
          (lookup Ω x_target))
   (where ρ_1 (extend ρ (x_gen) (cell)))]
  ; target doesn't have it
  [(process-one-export (Export x_id x_gen x_ext) x_target Ω ρ σ)
   ((extend Ω (x_target) ((linklet-instance (x cell) ... (x_ext cell_new)))) ρ_1 σ_1)
   ; create a new variable and put a reference to it within the target
   (where (linklet-instance (x cell) ...) (lookup Ω x_target))
   (where cell_new ,(variable-not-in (term (ρ σ x ... cell ...)) (term cell_1)))
   (where (ρ_1 σ_1) ((extend ρ (x_gen) (cell_new)) (extend σ (cell_new) ((variable x_ext uninit)))))])

(define-metafunction Linklets
  instantiate-exports : (exp-obj ...) x Ω ρ σ -> (Ω ρ σ)
  [(instantiate-exports () x Ω ρ σ) (Ω ρ σ)]
  [(instantiate-exports ((Export x_id x_gen x_ext) exp-obj ...) x_target Ω ρ σ)
   (instantiate-exports (exp-obj ...) x_target Ω_1 ρ_1 σ_1)
   (where (Ω_1 ρ_1 σ_1) (process-one-export (Export x_id x_gen x_ext) x_target Ω ρ σ))])

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

(define-metafunction Linklets
  ;instantiate-entry : ω Ω ρ σ L-obj LI ... (#:target x) -> (LI ω Ω ρ σ) or (v ω Ω ρ σ)

  ;; (No forms in the linklet body)
  ;;    -> no reason to deal with imports exports
  ;;    -> no reason to go into the instantiate-loop

  ;;   either
  ;;    - return void (if target is provided)
  ;;    - return target (if target is not provided)

  ;; prepare inputs case-lambda style
  ; instantiate without target
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ...)
   (instantiate-entry ω (extend Ω (x_target) ((linklet-instance))) ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target #:result instance)
   (where x_target ,(variable-not-in (term Ω) (term x)))]
  ; instantiate with a reference to target instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target #:result value)]
  ; instantiate with an explicit target instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target)
   (instantiate-entry ω (extend Ω (x_target) (LI_target)) ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target #:result value)
   (where x_target ,(variable-not-in (term Ω) (term x)))]
  ; return void
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target #:result value)
   ((void) ω Ω ρ σ)]
  ; return instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target #:result instance)
   ((lookup Ω x_target) ω Ω ρ σ)]

  ;; (There are forms in the linklet body)
  ;; prepare inputs case-lambda style
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ...)
   (instantiate-entry ω (extend Ω (x_target) ((linklet-instance))) ρ σ
                      (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target #:result instance)
   (where x_target ,(variable-not-in (term Ω) (term x)))]
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target #:result value)]

  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target LI_target)
   (instantiate-entry ω (extend Ω (x_target) (LI_target)) ρ σ
                      (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target #:result value)
   (where x_target ,(variable-not-in (term Ω) (term x)))]
  ;; ready - get the imported variables (l-var ...) and put them into the environment
  ;;         (?) instance-variable-reference
  ;; set   - for each exported variable,
  ;;          - either get it from the target, or create one (and put it in the target)
  ;;          - put it in the environment
  ;; go    - start the instantiation loop
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target #:result x_result)
   (instantiate-loop (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...)
                     ω Ω_1 ρ_2 σ_1 #:target x_target #:result x_result)
   (where ρ_1 (instantiate-imports ((imp-obj ...) ...) (LI ...) ρ σ))
   (where (Ω_1 ρ_2 σ_1) (instantiate-exports (exp-obj ...) x_target Ω ρ_1 σ))])

(define-metafunction Linklets
  instantiate-loop : L-obj ω Ω ρ σ #:target x #:result x -> (LI ω Ω ρ σ) or (v ω Ω ρ σ)
  ;; return value/instance after all the body is evaluated
  [(instantiate-loop (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) v ...)
                     ω Ω ρ σ #:target x_target #:result instance)
   ((lookup Ω x_target) ω Ω ρ σ)]
  [(instantiate-loop (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) v ... v_last)
                     ω Ω ρ σ #:target x_target #:result value)
   (v_last ω Ω ρ σ)]
  ;; repeatedly one-step reduce
  [(instantiate-loop L-obj ω Ω ρ σ #:target x_target #:result x_result)
   (instantiate-loop L-obj_new ω Ω ρ_1 σ_1 #:target x_target #:result x_result)
   (where ((L-obj_new ρ_1 σ_1))
          ,(apply-reduction-relation -->βi (term (L-obj ρ σ))))])

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

(define -->βi-render
  (reduction-relation
   Linklets
   #:domain (L-obj ρ σ)
   (--> [(in-hole EI (define-values (x) e)) ρ σ]
        [(in-hole EI (void)) ρ_2 σ_2]
        (where (v_1 ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (where (ρ_2 σ_2) ((extend ρ_1 (x) (cell)) (extend σ_1 (cell) (v_1))))
        (side-condition (term (cell ∉ (x ρ_1 σ_1))))  "inst-def-val")
   (--> [(in-hole EI e) ρ σ]
        [(in-hole EI v) ρ_1 σ_1]
        (where (v ρ_1 σ_1) ,(term (rc-api (e ρ σ))))
        (side-condition (term (e ∉ v))) "inst-expr")))
