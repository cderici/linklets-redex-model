#lang racket

(require redex
         "../linklets.rkt"
         "../racket-core.rkt"
         "../compile-linklets.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-linklet
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; get all toplevel variables
(test-equal (term (all-toplevels () ())) (term ()))
(test-equal (term (all-toplevels (3 4) ())) (term ()))
(test-equal (term (all-toplevels ((set! x 14)) ())) (term ()))
(test-equal (term (all-toplevels ((define-values (x) 3) (set! x 14)) ())) (term (x)))
(test-equal (term (all-toplevels ((define-values (x) 3) (set! x 14) (define-values (y) 3)) ())) (term (x y)))

; get all mutated variables
(test-equal (term (get-all-mutated-vars () ())) (term ()))
(test-equal (term (get-mutated-vars-expr (set! x 15) ())) (term (x)))
(test-equal (term (get-all-mutated-vars ((set! x 15)) ())) (term (x)))
(test-equal (term (get-mutated-vars-expr 3 ())) (term ()))
(test-equal (term (get-mutated-vars-expr (begin 3) ()))
            (term ()))
(test-equal (term (get-mutated-vars-expr (begin 3 (set! x 15)) ()))
            (term (x)))
(test-equal (term (get-mutated-vars-expr (begin 3
                                                (set! x 15)
                                                (set! y 15)) ()))
            (term (x y)))
(test-equal (term (get-mutated-vars-expr (define-values (x) 15) ()))
            (term ()))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15)
                                         (set! x 15)) ()))
            (term (x)))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15)
                                         (set! x 15)
                                         (set! y 14)) ()))
            (term (x y)))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15)
                                         (begin (set! x 15)
                                                (set! y 14))
                                         (set! z 14)) ()))
            (term (x y z)))

; process imports
; CAUTION: the gensym-ed symbols in expected results
; are hardcoded, may brake if gensym method of redex changes
(test-equal (term (process-importss 0 ((x)) ()))
            (term (((Import 0 x1 x x)))))
(test-equal (term (process-importss 0 ((x) (y)) ()))
            (term (((Import 0 x1 x x))
                   ((Import 1 y1 y y)))))
(test-equal (term (process-importss 0 ((x z) (y)) ()))
            (term (((Import 0 x1 x x) (Import 0 z1 z z))
                   ((Import 1 y1 y y)))))
; process exports
(test-equal (term (process-exports () ())) (term ()))
(test-equal (term (process-exports (a) ()))
            (term ((Export a a1 a))))
(test-equal (term (process-exports ((a-int a-ext) b) ()))
            (term ((Export a-int x a-ext)
                   (Export b b1 b))))

; compile-pre-tests
(test-equal (term (process-importss 0 () ())) (term ()))
(test-equal (term (process-exports () ())) (term ()))
(test-equal (term (get-all-mutated-vars () ())) (term ()))
(test-equal (term (all-toplevels () ())) (term ()))
(test-equal (term (c-body () () () () () () ())) (term ()))
; compile tests
(test-equal (term (compile-linklet (linklet () ())))
            (term (Lα () ())))
(test-equal (term (compile-linklet (linklet () () 3 4)))
            (term (Lα () () 3 4)))
(test-equal (term (compile-linklet (linklet () () (begin 3 4))))
            (term (Lα () () (begin 3 4))))
(test-equal (term (compile-linklet
                   (linklet () () (begin (set! x 3) 4))))
            (term (Lα () () (begin (set! x 3) 4))))
(test-equal (term (compile-linklet
                   (linklet () () (let-values (((x) 3)) x))))
            (term (Lα () () (let-values (((x) 3)) x))))
(test-equal (term (compile-linklet
                   (linklet () () (lambda (x) x))))
            (term (Lα () () (lambda (x) x))))
(test-equal (term (compile-linklet
                   (linklet () () (if (lambda (x) x) 3 4))))
            (term (Lα () () (if (lambda (x) x) 3 4))))
(test-equal (term (compile-linklet
                   (linklet () () (+ x x))))
            (term (Lα () () (+ x x))))
(test-equal (term (compile-linklet
                   (linklet () () 3 (+ x x))))
            (term (Lα () () 3 (+ x x))))

; compile-linklet important cases:
; no extra asts
(test-equal (term (compile-linklet
                   (linklet () () (define-values (x) 5) (+ x x))))
            (term (Lα () () (define-values (x) 5) (+ x x))))

(test-equal (term (compile-linklet
                   (linklet ((c)) () (define-values (x) 4) (+ x c))))
            (term (Lα (((Import 0 c1 c c))) ()
                                    (define-values (x) 4)
                                    (+ x (var-ref/no-check c1)))))

; inside lambda
#;(test-equal (term (compile-linklet
                   (linklet ((c)) ()
                            c
                            (lambda (y) c)
                            )))
            (term (Lα (((Import 0 c1 c c))) ()
                                    (var-ref/no-check c1)
                                    (lambda (y) (var-ref/no-check c1))
                                    )))

(test-equal (term (compile-linklet
                   (linklet ((cc)) (w)
                            cc
                            (lambda (p) w)
                            )))
            (term (Lα (((Import 0 cc1 cc cc))) ((Export w w1 w))
                                    (var-ref/no-check cc1)
                                    (lambda (p) (var-ref w1)))))
; slightly more realistic lambda
(test-equal (term (compile-linklet
                   (linklet ((c)) ()
                            (define-values (a) (+ c c))
                            (define-values (x) (lambda (y) c))
                            )))
            (term (Lα (((Import 0 c1 c c))) ()
                                    (define-values (a) (+ (var-ref/no-check c1) (var-ref/no-check c1)))
                                    (define-values (x) (lambda (y) (var-ref/no-check c1))))))

; create a variable for export
(test-equal (term (compile-linklet
                   (linklet () (x) (define-values (x) 5) (+ x x))))
            (term (Lα () ((Export x x1 x))
                                    (define-values (x) 5)
                                    (var-set! x1 x)
                                    (+ x x))))

; don't create a variable (even though it's set!
(test-equal (term (compile-linklet
                   (linklet () ()
                            (define-values (x) 5)
                            (set! x 6) (+ x x))))
            (term (Lα () ()
                                    (define-values (x) 5)
                                    (set! x 6) (+ x x))))

; create a variable for export, set! and use that one
(test-equal (term (compile-linklet
                   (linklet () (x)
                            (define-values (x) 5)
                            (set! x 6) (+ x x))))
            (term (Lα () ((Export x x1 x))
                                    (define-values (x) 5)
                                    (var-set! x1 x)
                                    (var-set/check-undef! x1 6)
                                    (+ (var-ref x1) (var-ref x1)))))
