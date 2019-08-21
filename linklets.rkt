#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  [LI ::= (linklet-instance (exp-id ...) (x l-var) ...)] ;; (var-sym cell)

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
