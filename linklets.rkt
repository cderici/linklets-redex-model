#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  [LI ::= (linklet-instance (x l-var) ...)] ;; note that an instance have no exports

  [L-obj ::= (compiled-linklet ((imp-obj ...) ...)
                               (exp-obj ...)
                               l-top ...)]

  [l-top ::= d e] ; linklet body expressions
  [l-var ::= (variable x v constance)] ; linklet variables
  [d ::= (define-values (x) e)]
  [e ::= .... (var-ref x) (var-ref/no-check x) (var-set! x x) (var-set/check-undef! x v)]

  ; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  [imp-obj ::= (Import n x x x)] ; group-index id int_id ext_id
  ; (internal-exported-id external-exported-id)
  [exp-id ::= x (x x)]
  [exp-obj ::= (Export x x x)] ; int_id int_gensymed ext_id

  [constance ::= #f constant consistent]

  ;; compile-instantiate expressions
  [CL ::= (compile-linklet L)]
  [I ::= LI (make-instance (exp-id ...) (x v) ...)
         (instantiate-linklet linkl-ref inst-ref ...)] ; instantiate
  [T ::= v (instantiate-linklet linkl-ref inst-ref ... #:target x)] ; evaluate

  [linkl-ref ::= x L-obj (raises e)]
  [inst-ref ::= x LI (raises e)]

  #;[v/i ::= value instance]

  ;; program-stuff
  [p-top :== I T (let-inst x I) (instance-variable-value x x)]
  [p ::= (program (use-linklets (x_!_ L) ...) p-top ... final-expr)]
  [final-expr ::= p-top v]

  [ω   ::= ((x L-obj) ...)] ; linklet env
  [Ω   ::= ((x LI) ...)] ; linklet instance env

  [V ::= v LI]
  [EP ::= hole
          (program (use-linklets) V ... (let-inst x EL) p-top ... final-expr)
          (program (use-linklets) V ... EL p-top ... final-expr)
          (program (use-linklets) V ... EL)]

  [EL ::= hole
          (instantiate-linklet EL x ...) ;; resolve the linklet
          (instantiate-linklet L-obj LI ... EL inst-ref ...) ;; resolve the imported instances

          (instantiate-linklet EL inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate-linklet L-obj LI ... EL inst-ref ... #:target inst-ref) ;; resolve the imported instances

          (instance-variable-value EL x)])

(define -->βp
  (reduction-relation
   Linklets
   #:domain (p ω Ω ρ σ)
   (--> [(in-hole EP (raises e)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ] "error")
   (--> [(in-hole EL (raises e)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ] "error in EL")
   (--> [(in-hole EP x) ω Ω ρ σ]
        [(in-hole EP (lookup ω x)) ω Ω ρ σ] "linklet-lookup")
   (--> [(in-hole EP (instance-variable-value LI x)) ω Ω ρ σ]
        [(in-hole EP (get-var-val LI x σ)) ω Ω ρ σ] "instance variable value")
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
        (where (raises e) (instantiate-entry ω Ω ρ σ L-obj LI ... #:target inst-ref_80)) "error in evaluation")

   ))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  ;instantiate-entry : ω Ω ρ σ L-obj LI ... (#:target x) -> (LI ω Ω ρ σ) or (v ω Ω ρ σ)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 1) get the imported variables (l-var ...) and put them into the environment
  ;; 2) create a target if it's not given
  ;; (?) instance-variable-reference
  ;; 3) for each exported variable,
  ;;        - either get it from the target, or create one
  ;;        - put it in the environment
  ;; 4) if there's no form in the body, either
  ;;        - return void (if target is provided)
  ;;        - return target (if target is not provided)
  ;; 5) if there are forms in the body, start the instantiation loop

  ;; (No forms in the linklet body) -> no reason to deal with imports exports
  ;; prepare inputs case-lambda style
  ; instantiate without target
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ...)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target (linklet-instance) #:result instance)]
  ; instantiate with a reference to target instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target x_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target #:result value)
   (where LI_target (lookup Ω x_target))]
  ; instantiate with an explicit target instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target #:result value)]
  ; return void
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target #:result value)
   ((void) ω Ω ρ σ)]
  ; return instance
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...)) LI ... #:target LI_target #:result instance)
   (LI_target ω Ω ρ σ)])

#|

  ;; (There are forms in the linklet body)
  ;; prepare inputs case-lambda style
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ...)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target (linklet-instance) #:result instance)]
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target x_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target LI_target #:result value)
   (where LI_target (lookup Ω x_target))]
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target LI_target)
   (instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target LI_target #:result value)]
  ; start the loop
  [(instantiate-entry ω Ω ρ σ (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_1 l-top ...) LI ... #:target LI_target #:result value)
  |#
