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
