#lang racket

(require redex
         "test-utils.rkt")

(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () 1)])
                                     (let-inst t1 (instantiate-linklet l1)
                                               (instantiate-linklet l1 #:target t1))))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () 3)])
                                     (let-inst t (make-instance)
                                               (instantiate-linklet l1 #:target t))))
(eval-prog=racket-linklets? (program (use-linklets [l1 (linklet () () (+ 1 2))])
                                     (let-inst t (make-instance)
                                               (instantiate-linklet l1 #:target t))))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l (linklet () () 2 1)])
                                     (let-inst ti (make-instance)
                                               (instantiate-linklet l #:target ti))))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l2 (linklet () () (define-values (a) 5) a)])
                                     (let-inst t1 (make-instance)
                                               (instantiate-linklet l2 #:target t1))))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l1 (linklet () () 1)]
                                      [l2 (linklet () (a) (define-values (a) 5) a)])
                                     (let-inst t2 (instantiate-linklet l2)
                                               (instance-variable-value t2 a))))
(eval-prog=racket-linklets? (program (use-linklets
                                      [l2 (linklet () (a) (define-values (a) 5) a)])
                                     (let-inst t1 (instantiate-linklet l2)
                                               (instance-variable-value t1 a))))

(eval-prog=racket-linklets? (program (use-linklets
                                      [l2 (linklet ((b)) () (define-values (a) 5) (+ a b))]
                                      [l3 (linklet () (b) (define-values (b) 3) 1)])
                                     (let-inst t1 (make-instance)
                                               (let-inst t3 (instantiate-linklet l3)
                                                         (instantiate-linklet l2 t3 #:target t1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; random testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Random Testing for Racket-Core

#;(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)

;(redex-check Linklets (term (eval-programs=racket-linklets e)) #:attempts 1000)
