#lang racket/base

(require redex "lang.rkt")

(provide (all-defined-out))

;; substitute linklet

(define-metafunction Linklets
  substitute-one : x L-obj p-top -> p-top
  [(substitute-one x L-obj (instantiate-linklet x inst-ref ...))
   (instantiate-linklet L-obj inst-ref ...)]
  [(substitute-one x L-obj (instantiate-linklet x inst-ref ... #:target inst-ref_1))
   (instantiate-linklet L-obj inst-ref ... #:target inst-ref_1)]
  [(substitute-one x L-obj (let-inst x_1 I p-top))
   (let-inst x_1 I_s p-top_1)
   (where I_s (substitute-one x L-obj I))
   (where p-top_1 (substitute-one x L-obj p-top))]
  [(substitute-one x L-obj p-top) p-top])

(define-metafunction Linklets
  [(substitute-linklet x L-obj () (p-top ...)) (p-top ...)]
  [(substitute-linklet x L-obj (p-top_1 p-top ...) (p-top_new ...))
   (substitute-linklet x L-obj (p-top ...) (p-top_new ... p-top_new1))
   (where p-top_new1 (substitute-one x L-obj p-top_1))])

;; substitute instance

(define-metafunction Linklets
  subst-inst-one : x LI p-top -> p-top
  [(subst-inst-one x LI (instantiate-linklet linkl-ref inst-ref_bef ... x inst-ref_aft ...))
   (instantiate-linklet linkl-ref inst-ref_bef ... LI inst-ref_aft ...)]
  [(subst-inst-one x LI (instantiate-linklet linkl-ref inst-ref_bef ... x inst-ref_aft ... #:target inst-ref_tar))
   (instantiate-linklet linkl-ref inst-ref_bef ... LI inst-ref_aft ... #:target inst-ref_tar)]
  [(subst-inst-one x LI (instantiate-linklet linkl-ref inst-ref ... #:target x))
   (instantiate-linklet LI inst-ref ... #:target LI)]
  [(subst-inst-one x LI (let-inst x_1 I p-top))
   (let-inst x_1 I_s p-top_1)
   (where I_s (subst-inst-one x LI I))
   (where p-top_1 (substitute-one x L-obj p-top))]
  [(subst-inst-one x LI p-top) p-top])

(define-metafunction Linklets
  [(subst-inst x LI () (p-top ...)) (p-top ...)]
  [(subst-inst x LI (p-top_1 p-top ...) (p-top_new ...))
   (subst-inst x LI (p-top ...) (p-top_new ... p-top_new1))
   (where p-top_new1 (subst-inst-one x LI p-top_1))])
