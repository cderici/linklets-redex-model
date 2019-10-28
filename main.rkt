#lang racket/base

(require redex
         "lang.rkt"
         "linklets.rkt"
         "racket-core.rkt")

(provide (all-defined-out))

(define-metafunction Linklets
  ;; return
  [(run-prog ((program (use-linklets) (n _)) ρ σ)) n] ;; number
  [(run-prog ((program (use-linklets) (b _)) ρ σ)) b] ;; boolean
  [(run-prog ((program (use-linklets) ((void) _)) ρ σ)) (void)] ;; void
  [(run-prog ((raises e) ρ σ)) stuck] ;; stuck

  ;; problem in intermediate steps
  [(run-prog ((program (use-linklets (x L) ...) stuck) ρ σ)) stuck]

  ;; reduce
  [(run-prog any_1)
   (run-prog any_again)
   (where (any_again) ,(apply-reduction-relation -->βp (term any_1)))]
  [(run-prog any_1)
   (run-prog any_again)
   (where (any_again) ,(apply-reduction-relation -->βr (term any_1)))]

  #;[(run-prog any_1) stuck])


(define-metafunction Linklets
  ;eval-prog :Linklets-> v or closure or stuck or void
  [(eval-prog (program (use-linklets (x_L L) ...) p-top))
   (run-prog ((program (use-linklets (x_L L) ...) p-top) () ()))
   #;(where ((x_L L-obj) ...) ((x_L (compile-linklet L)) ...))
   #;(side-condition (and (term (check-free-varss L ...))
                        (term (no-exp/imp-duplicates L ...))
                        (term (no-export-rename-duplicates L ...))
                        (term (no-non-definable-variables L ...))
                        (term (no-duplicate-binding-namess L ...))
                        (term (linklet-refs-check-out
                               (p-top ...)
                               (x_L ...)
                               (get-defined-instance-ids (p-top ...) ())))))]
  #;[(eval-prog p) stuck])
