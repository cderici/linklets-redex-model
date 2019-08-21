#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  [LI ::= (linklet-instance (exp-id ...) (x l-var) ...)] ;; (sym-var pairs)

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
  [I ::= (make-instance (exp-id ...) (x v) ...)
         (instantiate-linklet linkl-ref inst-ref ...)] ; instantiate
  [T ::= (instantiate-linklet linkl-ref inst-ref ... #:target x)] ; evaluate

  [linkl-ref ::= x L-obj (raises e)]
  [inst-ref ::= x LI (raises e)]

  ;; program-stuff
  [p-top :== I T (let-inst x I) (instance-variable-value x x)]
  [p ::= (program (use-linklets (x_!_ L) ...) p-top ... final-expr)]
  [final-expr ::= p-top v]

  [ω   ::= ((x L) ...)] ; linklet env
  [Ω   ::= ((x LI) ...)] ; linklet instance env

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
   (--> [(in-hole EP (instantiate L-obj LI ...)) ω Ω ρ σ]
        [(in-hole EP LI_1) Ω_1 ρ σ_1]
        (where (LI_1 ω_1 Ω_1 ρ_1 σ_1)
               (instantiate-entry ω Ω ρ σ L-obj LI ...)) "instantiate linklet")
   (--> [(in-hole EP (instantiate L-obj LI ... #:target x_80)) ω Ω ρ σ]
        [(in-hole EP e_1) ω_1 Ω_1 ρ_1 σ_1]
        (where (e_1 ω_1 Ω_1 ρ_1 σ_1)
               (instantiate-entry ω Ω ρ σ L-obj LI ... #:target x_80)) "eval linklet")
   (--> [(in-hole EP (instantiate L-obj LI ...)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ]
        (where (raises e) (instantiate-entry ω Ω ρ σ L-obj LI ...)) "error in instantiation")
   (--> [(in-hole EP (instantiate L-obj LI ... #:target x_80)) ω Ω ρ σ]
        [(raises e) ω Ω ρ σ]
        (where (raises e) (instantiate-entry ω Ω ρ σ L-obj LI ... #:target x_80)) "error in evaluation")

   ))

(define-metafunction Linklets
  ;; return
  [(run-prog ((program (use-linklets) V ... n) ω Ω ρ σ)) n] ;; number
  [(run-prog ((program (use-linklets) V ... b) ω Ω ρ σ)) b] ;; boolean
  [(run-prog ((program (use-linklets) V ... (void)) ω Ω ρ σ)) (void)] ;; void
  [(run-prog ((raises e) ω Ω ρ σ)) stuck] ;; stuck

  ;; load the linklets
  [(run-prog ((program (use-linklets (x_1 L-obj_1) (x L-obj) ...) p-top ...) ω Ω ρ σ))
   (run-prog ((program (use-linklets) p-top ...)
              (extend ω (x_1 x ...) (L-obj_1 L-obj ...)) Ω ρ σ))]

  ;; problem in intermediate steps
  [(run-prog ((program (use-linklets (x L-obj) ...) p-top_1 ... stuck p-top_2 ...)
              ω Ω ρ σ)) stuck]

  ;; reduce
  [(run-prog any_1)
   (run-prog any_again)
   (where (any_again) ,(apply-reduction-relation -->βp (term any_1)))]
  [(run-prog any_1) stuck])


(define-metafunction Linklets
  ;eval-prog :Linklets-> v or closure or stuck or void
  [(eval-prog (program (use-linklets (x_L L) ...) p-top ...))
   (run-prog ((program (use-linklets (x_L L-obj) ...) p-top ...) () () () ()))
   (where (L-obj ...) ((compile-linklet L) ...))
   #;(side-condition (and (term (check-free-varss L ...))
                        (term (no-exp/imp-duplicates L ...))
                        (term (no-export-rename-duplicates L ...))
                        (term (no-non-definable-variables L ...))
                        (term (no-duplicate-binding-namess L ...))
                        (term (linklet-refs-check-out
                               (p-top ...)
                               (x_L ...)
                               (get-defined-instance-ids (p-top ...) ())))))]
  [(eval-prog p) stuck])
