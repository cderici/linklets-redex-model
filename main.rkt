#lang racket/base

(require redex
         "linklets.rkt"
         "compile-linklets.rkt"
         "racket-core.rkt")

(provide (all-defined-out))

(define-metafunction Linklets
  ;; return
  [(run-prog ((program (use-linklets) V ... n) ω Ω ρ σ)) n] ;; number
  [(run-prog ((program (use-linklets) V ... b) ω Ω ρ σ)) b] ;; boolean
  [(run-prog ((program (use-linklets) V ... (void)) ω Ω ρ σ)) (void)] ;; void
  [(run-prog ((raises e) ω Ω ρ σ)) stuck] ;; stuck

  ;; compile and load the linklets
  [(run-prog ((program (use-linklets (x_1 L_1) (x L) ...) p-top ... final-expr) ω Ω ρ σ))
   (run-prog ((program (use-linklets (x L) ...) p-top ... final-expr)
              (extend ω (x_1) (L-obj_1)) Ω ρ σ))
   (where L-obj_1 (compile-linklet L_1))]

  ;; problem in intermediate steps
  [(run-prog ((program (use-linklets (x L) ...) p-top_1 ... stuck p-top_2 ... final-expr)
              ω Ω ρ σ)) stuck]

  ;; reduce
  [(run-prog any_1)
   (run-prog any_again)
   (where (any_again) ,(apply-reduction-relation -->βp (term any_1)))]
  #;[(run-prog any_1) stuck])


(define-metafunction Linklets
  ;eval-prog :Linklets-> v or closure or stuck or void
  [(eval-prog (program (use-linklets (x_L L) ...) p-top ... final-expr))
   (run-prog ((program (use-linklets (x_L L) ...) p-top ... final-expr) () () () ()))
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
