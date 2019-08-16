#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  [LI ::= (linklet-instance (exp-id ...) (x l-var) ...)] ;; (var-sym cell)
  
  [l-top ::= d e] ; linklet body expressions
  [l-var ::= (variable x v constance)] ; linklet variables
  [d ::= (define-values (x) e)]
  
  ; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  [exp-id ::= x (x x)]

  [constance ::= #f constant consistent]

  ;; compile-instantiate expressions
  [CL ::= (compile-linklet L)]
  [I ::= (make-instance (exp-id ...) (x v) ...)
         (instantiate-linklet linkl-ref inst-ref ...)] ; instantiate
  [T ::= (instantiate-linklet linkl-ref inst-ref ... #:target x)] ; evaluate

  [linkl-ref ::= x L (raises e)]
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
          (instantiate-linklet L LI ... EL inst-ref ...) ;; resolve the imported instances

          (instantiate-linklet EL inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate-linklet L LI ... EL inst-ref ... #:target inst-ref) ;; resolve the imported instances

          (instance-variable-value EL x)])
