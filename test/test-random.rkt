#lang racket

(require redex
         "../lang.rkt"
         "../main.rkt"
         "test-utils.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; meta-test area
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets) (make-instance)))) (term (void)))
#;(eval-prog=racket-linklets? (program (use-linklets) (make-instance)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; random testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#;(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)



#;(redex-check Linklets (program (use-linklets (x_!_ L) ...) p-top)
 (equal? (term (eval-prog=racket-linklets? p)) #true)
 #:attempts 10)
