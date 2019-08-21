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

; A separate pass
(define-metafunction Linklets
  all-toplevels : (l-top ...) (x ...) -> (x ...)
  [(all-toplevels () (x ...)) (x ...)]
  [(all-toplevels ((define-values (x) e) l-top ...) (x_tops ...))
   (all-toplevels (l-top ...) (x_tops ... x))]
  [(all-toplevels (l-top_1 l-top ...) (x ...))
   (all-toplevels (l-top ...) (x ...))])

; A separate (slightly deeper) pass
(define-metafunction Linklets
  get-mutated-vars-expr : l-top (x ...) -> (x ...)
  [(get-mutated-vars-expr (set! x v) (x_muts ...)) (x x_muts ...)]
  [(get-mutated-vars-expr (begin l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ...))]
  [(get-mutated-vars-expr l-top (x ...)) (x ...)])

(define-metafunction Linklets
  get-all-mutated-vars : (l-top ...) (x ...) -> (x ...)
  [(get-all-mutated-vars () (x ...)) (x ...)]
  [(get-all-mutated-vars (l-top_1 l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ... x_new_muts ... ))
   (where (x_new_muts ...) (get-mutated-vars-expr l-top_1 ()))])

; Process Imports
(define-metafunction Linklets
  process-import : n (imp-id ...) (imp-obj ...) -> (imp-obj ...)
  [(process-import n () (imp-obj ...)) (imp-obj ...)]
  [(process-import n (x imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x x) ))
   (where x_gen ,(variable-not-in (term (x imp-id ...)) (term x)))]
  [(process-import n ((x_ext x_int) imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x_int x_ext)))
   (where x_gen ,(variable-not-in (term ((x_ext x_int) imp-id ...)) (term x)))])

(define-metafunction Linklets
  process-importss : n ((imp-id ...) ...) ((imp-obj ...) ...) -> ((imp-obj ...) ...)
  [(process-importss n () ((imp-obj ...) ...)) ((imp-obj ...) ...)]
  [(process-importss n ((imp-id_1 ...) (imp-id ...) ...) ((imp-obj ...) ...))
   (process-importss ,(add1 (term n))
                     ((imp-id ...) ...)
                     ((imp-obj ...) ... (imp-obj_1 ...)))
   (where (imp-obj_1 ...) (process-import n (imp-id_1 ...) ()))])

; Process Exports
(define-metafunction Linklets
  process-exports : (exp-id ...) (exp-obj ...) -> (exp-obj ...)
  [(process-exports () (exp-obj ...)) (exp-obj ...)]
  [(process-exports (x exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x x_gen x)))
   (where x_gen ,(variable-not-in (term (x exp-id ...)) (term x)))]
  [(process-exports ((x_int x_ext) exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x_int x_gen x_ext)))
   (where x_gen ,(variable-not-in (term ((x_int x_ext) exp-id ...)) (term x)))])