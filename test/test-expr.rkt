#lang racket

(require redex "../lang.rkt")

;; Source Language Expression Validity Tests


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Racket-Core
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicates for testing
(define RC? (redex-match? RC e))
(define not-RC? (compose not RC?))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simple Expressions : Values and Vars
(test-predicate RC? (term 1))
(test-predicate RC? (term (lambda (x) x)))
(test-predicate RC? (term (lambda () x)))

(test-predicate not-RC? (term (lambda (x))))

; Basic Core Expressions
(test-predicate RC? (term (define x 4)))
(test-predicate RC? (term (func x y z)))
(test-predicate RC? (term (func-nullary)))
(test-predicate RC? (term (if true x y)))
(test-predicate RC? (term (+ 1 2)))
(test-predicate RC? (term (+ x 1)))
(test-predicate RC? (term (+ 1 (+ 1 1))))
(test-predicate RC? (term (set! x 42)))
(test-predicate RC? (term (begin 1)))
(test-predicate RC? (term (begin x y 3)))
(test-predicate RC? (term (begin (begin 1 2) 3))) ; nested begins are possible
; let-values is desugared into lambda application
(test-predicate RC? (term (let-values (((x) 1)) x)))


(test-predicate not-RC? (term (begin)))
(test-predicate not-RC? (term (lambda (x) x x)))
(test-predicate not-RC? (term (+)))
(test-predicate not-RC? (term (+ 1)))
(test-predicate not-RC? (term (+ 1 2 3)))
(test-predicate not-RC? (term (set! 3 5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklet Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define L? (redex-match? Linklets L))
(define not-L? (compose not L?))


(test-predicate L? (term (linklet () ())))
(test-predicate L? (term (linklet () () (define-values (x) 1))))
(test-predicate L? (term (linklet () () (define-values (x) 1) (define-values (x) 5))))
(test-predicate L? (term (linklet () (x))))
(test-predicate L? (term (linklet () (x) (define-values (x) 1))))
(test-predicate L? (term (linklet () (x) (define-values (x) 1) (+ x x))))
(test-predicate L? (term (linklet (()) (x) (define-values (x) 1))))
(test-predicate L? (term (linklet ((a)) (x) (define-values (x) a))))
(test-predicate L? (term (linklet ((a)) ((x x1)) (define-values (x) a))))

(test-predicate not-L? (term (linklet ()))) ; no imports (or exports)
(test-predicate not-L? (term (linklet (x) ()))) ; imports are listof-listof-ids

(test-predicate L? (term (linklet ((a)) ((x x1)) (define-values (x) a))))

; compiled (linklet () (x) (define-values (x) 4) (+ x x))
(test-predicate L? (term
                    (linklet () ((x x1))
                             (define-values (x) 1)
                             (var-set! x1 x)
                             (+ x x))))
; compiled (linklet () (x) (define-values (x) 4) (set! x 5) (+ x x))
(test-predicate L? (term
                    (linklet () ((x x1))
                             (define-values (x) 4)
                             (var-set! x1 x)
                             (var-set/check-undef! x1 5)
                             (+ (var-ref x1) (var-ref x1)))))

(define program? (redex-match? Linklets p))
(define not-program? (compose not program?))

#;(test-predicate
 program? (term (program (use-linklets))))
(test-predicate
 program? (term (program (use-linklets) 3)))
(test-predicate
 program? (term (program (use-linklets [l1 (linklet () ())])
                         (let-inst t1 (instantiate-linklet l1)
                                   (instantiate-linklet l1 #:target t1)))))

(test-predicate
 program? (term (program (use-linklets)
                         (let-inst ti (instantiate-linklet t)
                                   (instantiate-linklet l #:target ti)))))
(test-predicate
 program? (term (program (use-linklets
                          [l (linklet () () 1)]
                          [t (linklet () ())])
                         (let-inst ti (instantiate-linklet t)
                                   (instantiate-linklet l #:target ti)))))
(test-predicate
 program? (term (program (use-linklets
                          [l1 (linklet () ())]
                          [l2 (linklet () () (define-values (x) 5) x)])
                         (let-inst t1 (instantiate-linklet l1)
                                   (instantiate-linklet l2 #:target t1)))))
