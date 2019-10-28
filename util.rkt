#lang racket/base

(require redex "lang.rkt")

(provide (all-defined-out))

;; substitute linklet

(define-metafunction Linklets
  substitute-one : x L-obj p-top -> p-top
  [(substitute-one x L-obj (instantiate-linklet x x_imp_inst ...))
   (instantiate-linklet L-obj x_imp_inst ...)]
  [(substitute-one x L-obj (instantiate-linklet x x_imp_inst ... #:target x_t))
   (instantiate-linklet L-obj x_imp_inst ... #:target x_t)]
  [(substitute-one x L-obj (let-inst x_1 I p-top))
   (let-inst x_1 I_s p-top_new)
   (where I_s (substitute-one x L-obj I))
   (where p-top_new (substitute-one x L-obj p-top))]
  [(substitute-one x L-obj (let-inst x_1 LI p-top))
   (let-inst x_1 LI p-top_new)
   (where p-top_new (substitute-one x L-obj p-top))]
  [(substitute-one x L-obj (seq p-top ...))
   (seq p-top_new ...)
   (where (p-top_new ...) ((substitute-one x L-obj p-top) ...))]
  [(substitute-one x L-obj p-top) p-top])

(define-metafunction Linklets
  [(substitute-linklet x L-obj (p-top ...))
   (p-top_new ...)
   (where (p-top_new ...) ((substitute-one x L-obj p-top) ...))])

;; substitute instance

#;(define-metafunction Linklets
  substitute-instance : x LI p-top -> p-top
  [(substitute-instance x LI (instantiate-linklet linkl-ref x_bef ... x x_aft ...))
   (instantiate-linklet linkl-ref x_bef ... LI x_aft ...)]
  [(substitute-instance x LI (instantiate-linklet linkl-ref x_bef ... x x_aft ... #:target x_tar))
   (instantiate-linklet linkl-ref x_bef ... LI x_aft ... #:target x_tar)]
  [(substitute-instance x LI (instantiate-linklet linkl-ref x ... #:target x))
   (instantiate-linklet linkl-ref x ... #:target LI)]
  [(substitute-instance x LI (let-inst x_1 I p-top))
   (let-inst x_1 I_s p-top_1)
   (where I_s (substitute-instance x LI I))
   (where p-top_1 (substitute-instance x LI p-top))]
  [(substitute-instance x LI (instance-variable-value x x_var))
   (instance-variable-value LI x_var)]
  [(substitute-instance x LI p-top) p-top])

#;(define-metafunction Linklets
  [(substitute-instance-multi x LI () (p-top ...)) (p-top ...)]
  [(substitute-instance-multi x LI (p-top_1 p-top ...) (p-top_new ...))
   (substitute-instance-multi x LI (p-top ...) (p-top_new ... p-top_new1))
   (where p-top_new1 (substitute-instance x LI p-top_1))])
