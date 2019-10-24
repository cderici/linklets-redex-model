#lang racket/base

;; Language Grammars

(require redex)

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Racket Core
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (o e e)
       (begin e e ...) (lambda (x_!_ ...) e)
       (raises e) (set! x e)
       (var-ref x) (var-ref/no-check x)
       (var-set! x e) (var-set/check-undef! x e)] ;; expressiosn
  [v   ::= n b c (void) uninit] ;; values
  [c   ::= (closure (x ...) e ρ)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [o   ::= + * <]
  [E   ::= hole (v ... E e ...) (o E e) (o v E)
       (var-set! x E) (var-set/check-undef! x E)
       (begin v ... E e ...) (set! x E) (if E e e)] ;; eval context

  [ρ   ::= ((x any) ...)] ;; environment
  [σ   ::= ((x any) ...)] ;; store

  [e-test ::= x n b (void)
          (e-test e-test ...) (lambda (x_!_ ...) e-test) (if e-test e-test e-test)
          (p2 e-test e-test) (p1 e-test) (set! x e-test) (begin e-test e-test ...)
          (raises e-test)] ;; to be used to generate test cases (i.e. exclude closures)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklet Source
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language LinkletSource RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]

  [l-top ::= (define-values (x) e) e] ; linklet body expressions

  ;; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  ;; (internal-exported-id external-exported-id)
  [exp-id ::= x (x x)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language Linklets LinkletSource
  ;; compile
  [CL ::= (compile-linklet L)]
  [L-obj ::= (Lα c-imps c-exps l-top ...) (Lβ x l-top ...)]
  [c-imps ::= ((imp-obj ...) ...)]
  [c-exps ::= (exp-obj ...)]
  ;; import & export objects
  [imp-obj ::= (Import n x x x)] ; group-index id(<-gensymed) int_id ext_id
  [exp-obj ::= (Export x x x)] ; int_gensymed int_id ext_id

  ;; instantiate
  [LI ::= x (linklet-instance (x cell) ...)] ;; note that an instance have no exports
  [I ::= (make-instance)
         (instantiate-linklet linkl-ref inst-ref ...)
         (instantiate-linklet linkl-ref inst-ref ... #:target inst-ref)]

  [linkl-ref ::= x L-obj (raises e)]
  [inst-ref ::= x LI (raises e)]
  [v ::= .... V]
  ;; program-stuff
  [p ::= (program (use-linklets (x_!_ L) ...) p-top) v]
  [p-top ::= v I (let-inst x I p-top) (let-inst x V p-top) (seq p-top ...)
             (instance-variable-value inst-ref x)]

  [V ::= (v x)]

  ;; evaluation-context for the programs
  [EP ::= hole
          (instantiate-linklet EP inst-ref ...) ;; resolve the linklet
          (instantiate-linklet EP inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate-linklet (Lβ x v ... EP l-top ...) inst-ref ...) ;; instantiate

          (let-inst x EP p-top)
          (seq v ... EP p-top ...)

          (program (use-linklets) EP)]
  ;; evaluation-context for the linklet body
  [EI ::= hole (Lα ((imp-obj ...) ...) (exp-obj ...) v ... EI l-top ...)]
  )

(define-extended-language LinkletProgramTest Linklets
  [p-test ::= (program (use-linklets (x_!_ L) ...) p-top-test ...)]
  [p-top-test ::= (instantiate-linklet x x ... #:target I-test)
                  (instantiate-linklet x x ...)
                  (let-inst x (instantiate-linklet x x ...) p-top-test)
                  (instance-variable-value inst-ref x)
                  v-test]
  [I-test ::= x (linklet-instance)]
  [v-test ::= n b (void)])
