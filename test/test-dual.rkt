#lang racket

(require redex
         "../test-utils.rkt")

(eval-rc=racket-core? 1)
(eval-rc=racket-core? ((lambda (x) x) 1))
(eval-rc=racket-core? (+ x 1))
(eval-rc=racket-core? (void))
(eval-rc=racket-core? (+ 1 (void)))
(eval-rc=racket-core? (if (< 1 2) 1 2))
(eval-rc=racket-core? (if (< 1 2) (< 1 2) 2))
(eval-rc=racket-core? (set! q (void)))
(eval-rc=racket-core? ((lambda (x) x) (+ a b)))
(eval-rc=racket-core? (if (void) (void) (void)))
(eval-rc=racket-core? (if (void) 3 (< qw F)))
(eval-rc=racket-core? ((lambda () (void))))

(eval-prog=racket-linklets? (program (use-linklets) 3))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () 2)]) 3))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () ())])
                                     (let-inst t1 (instantiate-linklet l1))
                                     (instantiate-linklet l1 #:target t1)))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () 3)])
                                     (instantiate-linklet l1 #:target (linklet-instance))))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () (+ 1 2))])
                                     (instantiate-linklet l1 #:target (linklet-instance))))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l (linklet () () 2 1)]
                                      [t (linklet () ())])
                                     (let-inst ti (instantiate-linklet t))
                                     (instantiate-linklet l #:target ti)))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l1 (linklet () ())]
                                      [l2 (linklet () () (define-values (a) 5) a)])
                                     (let-inst t1 (instantiate-linklet l1))
                                     (instantiate-linklet l2 #:target t1)))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l2 (linklet () (a) (define-values (a) 5) a)])
                                     (let-inst t1 (instantiate-linklet l2))
                                     (instance-variable-value t1 a)))



(eval-prog=racket-linklets? (program (use-linklets
                                      [l1 (linklet () ())]
                                      [l2 (linklet ((b)) () (define-values (a) 5) (+ a b))]
                                      [l3 (linklet () (b) (define-values (b) 3))])
                                     (let-inst t1 (instantiate-linklet l1))
                                     (let-inst t3 (instantiate-linklet l3))
                                     (instantiate-linklet l2 t3 #:target t1)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; random testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Random Testing for Racket-Core

#;(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)

;(redex-check Linklets (term (eval-programs=racket-linklets e)) #:attempts 1000)
