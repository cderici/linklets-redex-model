#lang racket

(require redex
         "linklets.rkt"
         "racket-core.rkt"
         "compile-linklets.rkt"
         "main.rkt"
         syntax/parse/define
         "test-utils.rkt")



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
(test-predicate RC? (term (let-values (((x) 1)) x)))


(test-predicate not-RC? (term (begin)))
(test-predicate not-RC? (term (lambda (x) x x)))
(test-predicate not-RC? (term (+)))
(test-predicate not-RC? (term (+ 1)))
(test-predicate not-RC? (term (+ 1 2 3)))
(test-predicate not-RC? (term (set! 3 5)))

;; primitive δ tests
(test-equal (term (δ (+ 12 8))) (term 20))
(test-equal (term (δ (* 2 10))) (term 20))

;; testing the transitive closure of -->βs
;; (testing the single-step -->βs would require to write down all possible results)
(test-->> -->βs (term ((if true 2 3) () ())) (term (2 () ())))
(test-->> -->βs (term ((if false -1 (* 21 2)) () ())) (term (42 () ())))

;; evaluation tests

(test-equal (term (eval-rc 42)) 42)
(test-equal (term (eval-rc ((lambda (x) x) 42))) 42)
(test-equal (term (eval-rc (lambda (x) x))) 'closure)
(test-equal (term (eval-rc (+ 20 22))) 42)
(test-equal (term (eval-rc (* 21 2))) 42)
(test-equal (term (eval-rc 42)) 42)

(test-equal (term (eval-rc (begin 1 42))) 42)
(test-equal (term (eval-rc (begin 1 2 3 4 42))) 42)
(test-equal (term (eval-rc (begin (+ 2 3) 1 42))) 42)
(test-equal (term (eval-rc (begin 1 (+ 2 3) (+ 2 3) 42))) 42)
(test-equal (term (eval-rc (if true 42 -1))) 42)
(test-equal (term (eval-rc (if 1 -1 42))) -1)
(test-equal (term (eval-rc (if (< 2 1) -1 42))) 42)
(test-equal (term (eval-rc (if (< 2 1) -1 (* 21 2)))) 42)
(test-equal (term (eval-rc (let-values (((x) 42)) x))) 42)
(test-equal (term (eval-rc (let-values (((x) (+ 21 21))) x))) 42)
(test-equal (term (eval-rc (let-values (((x) 22) ((y) 20)) (+ x y)))) 42)
(test-equal (term (eval-rc (let-values (((x) 4))
                             (let-values (((c) (lambda (a) x)))
                               (let-values (((x) 10))
                                 (c 1)))))) 4)
(test-equal (term (eval-rc (let-values (((x) 4)) (begin (set! x 42) x)))) 42)
(test-equal (term (eval-rc (let-values (((x) 4))
                             (let-values (((c) (lambda (a) x)))
                               (begin
                                 (set! x 10)
                                 (c 1)))))) 10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklet Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicates and tools for testing

(define-simple-macro (linklet? p)
  (test-predicate (redex-match? Linklets L) (term p)))

(define L? (redex-match? Linklets L))
(define not-L? (compose not L?))

(define-simple-macro (program? p)
  (test-predicate (redex-match? Linklets p) (term p)))

(define not-program? (compose not (redex-match? Linklets p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet? (linklet () ()))
(linklet? (linklet () () (define-values (x) 1)))
(linklet? (linklet () () (define-values (x) 1) (define-values (x) 5)))
(linklet? (linklet () (x)))
(linklet? (linklet () (x) (define-values (x) 1)))
(linklet? (linklet () (x) (define-values (x) 1) (+ x x)))
(linklet? (linklet (()) (x) (define-values (x) 1)))
(linklet? (linklet ((a)) (x) (define-values (x) a)))
(linklet? (linklet ((a)) ((x x1)) (define-values (x) a)))

(test-predicate not-L? (term (linklet ()))) ; no imports (or exports)
(test-predicate not-L? (term (linklet (x) ()))) ; imports are listof-listof-ids

(linklet? (linklet ((a)) ((x x1)) (define-values (x) a)))

; compiled (linklet () (x) (define-values (x) 4) (+ x x))
(linklet? (linklet () ((x x1)) (define-values (x) 1) (var-set! x1 x) (+ x x)))
; compiled (linklet () (x) (define-values (x) 4) (set! x 5) (+ x x))
(linklet? (linklet () ((x x1))
                   (define-values (x) 4)
                   (var-set! x1 x)
                   (var-set/check-undef! x1 5)
                   (+ (var-ref x1) (var-ref x1))))

; "program" acts like a begin, the last result is returned, where
; result is either a linklet instance or a value

(program? (program (use-linklets)))
(program? (program (use-linklets) 3))
(program? (program (use-linklets [l1 (linklet () ())])
                   (let-inst t1 (instantiate-linklet l1))
                   (instantiate-linklet l1 #:target t1)))

(program? (program (use-linklets)
                   (let-inst ti (instantiate-linklet t))
                   (instantiate-linklet l #:target ti)))
(program? (program (use-linklets
                    [l (linklet () () 1)]
                    [t (linklet () ())])
                   (let-inst ti (instantiate-linklet t))
                   (instantiate-linklet l #:target ti)))
(program? (program (use-linklets
                    [l1 (linklet () ())]
                    [l2 (linklet () () (define-values (x) 5) x)])
                   (let-inst t1 (instantiate-linklet l1))
                   (instantiate-linklet l2 #:target t1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compile-linklet
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (substitute-linklet l1 (Lα () ()) (3) ())) (term (3)))
(test-equal (term (substitute-linklet l1 (Lα () ()) (3 4) ())) (term (3 4)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instantiation side tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (get-var-from-instance c (linklet-instance (c cell1)))) (term cell1))

; put-imported-vars-into-env
#;(test-equal (term (instantiate-imports () () ())) (term (())))
#;(test-equal (term (instantiate-imports (((Import 0 c1 c c))) ((linklet-instance (c cell))) () ())) (term (((c1 cell)))))
#;(test-equal (term (instantiate-imports (((Import 0 c1 c c))
                                        ((Import 1 a1 a a)(Import 1 b1 b b)))
                                       ((linklet-instance (c (variable v1 5)))
                                        (linklet-instance (a (variable v2 2))(b (variable v3 3))))
                                       () ()))
            (term (((b1 cell2)(a1 cell1)(c1 cell))
                   ((cell2 (variable v3 3)) (cell1 (variable v2 2)) (cell (variable v1 5))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eval-prog/run-prog side tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (compile-linklet (linklet () ())))
            (term (Lα () ())))
(test-equal (term (run-prog ((program (use-linklets) 3)
                             () () ()))) 3)

(test-equal (term (run-prog ((program (use-linklets (l1 (linklet () ()))) 3)
                             () () ()))) 3)
(program? (program (use-linklets)
                   (let-inst t1 (linklet-instance))
                   (instantiate-linklet l1 #:target t1)))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (void)
                             (instantiate-linklet (Lα () ()) #:target t1))
                    ((t1 (linklet-instance)))
                    () ())))
            (term (((program (use-linklets) (void) (instantiate-linklet (Lγ)))
                    ((t1 (linklet-instance)))
                    ()
                    ()))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) (void) (instantiate-linklet (Lγ)))
                    ((t1 (linklet-instance)))
                    ()
                    ())))
            (term (((program (use-linklets)
                             (void)
                             (void))
                    ((t1 (linklet-instance)))
                    () ()))))

(test-equal (term (run-prog ((program (use-linklets)
                                      (void)
                                      (instantiate-linklet (Lα () ()) #:target t1))
                             ((t1 (linklet-instance)))
                             () ())))
            (term (void)))

(test-equal
 (term
  (instantiate-exports ((Export a a1 a)) target ((target (linklet-instance))) () ()))
 (term (((target (linklet-instance (a cell_1))) (target (linklet-instance)))
        ((a1 cell_1))
        ((cell_1 uninit)))))
; (term ((linklet-instance (a cell_1)) ((a1 cell_1)) ((cell_1 (variable a uninit))))))

(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (+ 1 2)) () ())))
            (term (((Lα () () 3) () ()))))

(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (define-values (a) 5) a) () ())))
            (term (((Lα () () (void) a) ((a cell)) ((cell 5))))))

(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () 3 a) ((a cell)) ((cell 5)))))
            (term (((Lα () () 3 5) ((a cell)) ((cell 5))))))

(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (void) a) ((a cell)) ((cell 5)))))
            (term (((Lα () () (void) 5) ((a cell)) ((cell 5))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eval-prog main tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-simple-macro (linklet-test p v)
  (test-equal (term (eval-prog p)) (term v)))

(linklet-test (program (use-linklets) 3) 3)

(linklet-test (program (use-linklets [l1 (linklet () () 2)])
                       3)
              3)
(linklet-test (program (use-linklets [l1 (linklet () ())])
                                      (let-inst t1 (instantiate-linklet l1))
                                      (instantiate-linklet l1 #:target t1))
              (void))

(linklet-test (program (use-linklets [l1 (linklet () () 3)])
                       (instantiate-linklet l1 #:target (linklet-instance)))
              3)

(linklet-test (program (use-linklets [l1 (linklet () () (+ 1 2))])
                       (instantiate-linklet l1 #:target (linklet-instance)))
              3)

(linklet-test (program (use-linklets
                        [l (linklet () () 2 1)]
                        [t (linklet () ())])
                       (let-inst ti (instantiate-linklet t))
                       (instantiate-linklet l #:target ti))
              1)

(linklet-test (program (use-linklets
                        [l1 (linklet () ())]
                        [l2 (linklet () () (define-values (a) 5) a)])
                       (let-inst t1 (instantiate-linklet l1))
                       (instantiate-linklet l2 #:target t1))
              5)

(linklet-test (program (use-linklets
                        [l2 (linklet () (a) (define-values (a) 5) a)])
                       (let-inst t1 (instantiate-linklet l2))
                       (instance-variable-value t1 a))
              5)

(linklet-test (program (use-linklets
                        [l1 (linklet () ())]
                        [l2 (linklet ((b)) () (define-values (a) 5) (+ a b))]
                        [l3 (linklet () (b) (define-values (b) 3))])
                       (let-inst t1 (instantiate-linklet l1))
                       (let-inst t3 (instantiate-linklet l3))
                       (instantiate-linklet l2 t3 #:target t1))
              8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; PYCKET LINKLET TESTS BEGIN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(linklet-test (program (use-linklets
                        [l (linklet () (x) (define-values (x) 4) (+ x x))]
                        [t (linklet () () (define-values (x) 1) (define-values (y) 2))])
                       (let-inst t1 (instantiate-linklet t))
                       (instantiate-linklet l #:target t1))
              8)


; even if linklet doesn't export, def goes into target if it doesn't already have it
; skipped in pycket
; @pytest.mark.skip(reason="this behavior is different btw Racket and Chez")
#;(linklet-test (program (use-linklets
                        [l2 (linklet () () (define-values (x) 4) (+ x x))])
                       (let-inst t2 (linklet-instance))
                       (instantiate-linklet l2 #:target t2)
                       (instance-variable-value t2 x)) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target_transfer_set_banged
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(linklet-test (program (use-linklets
                        [l (linklet () (y) (define-values (y) 10) (set! y 50))])
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t y))
              50)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target_def_overwrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () (x) (define-values (x) 4) (+ x x))]
                        [tl (linklet () (x) (define-values (x) 1))])
                       (let-inst t (instantiate-linklet tl))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target always overwrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; "if target doesn't have it, then it doesn't matter if linklet exports or not, put the variable in the target"
; @pytest.mark.skip(reason="this behavior is different btw Racket and Chez")
#;(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (z) 4) z)])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l #:target t)
                                      (instance-variable-value t z)))) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target def stays the same
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; "if linklet doesn't export, then target's def stay the same"

(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 4) (+ x x))]
                        [tl (linklet () (x) (define-values (x) 1))])
                       (let-inst t (instantiate-linklet tl))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              1)

; "use the local var, don't change target's var if you don't export"

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                        [tl (linklet () (x) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet tl))
                       (instantiate-linklet l #:target t))
              8)

(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 4) (+ x x))]
                        [tl (linklet () (x) (define-values (x) 10))]); <------------|
                       (let-inst t (instantiate-linklet tl));                       |
                       (instantiate-linklet l #:target t);                          |
                       (instance-variable-value t x));                              |
              10);                                                                  |
; t1  exports here   >--------------------------------------------------------------|

;  "imported variables doesn't get into target at all ... let alone overwrite any var inside the target"

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) () (+ x x))])
                       (let-inst li-1 (instantiate-linklet l1))
                       (let-inst t1 (linklet-instance))
                       (instantiate-linklet l2 li-1 #:target t1))
              8) ; t1 doesn't have x

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) () (+ x x))]
                        [tl-2 (linklet () (x) (define-values (x) 1))])
                       (let-inst li-1 (instantiate-linklet l1))
                       (let-inst t2 (instantiate-linklet tl-2))
                       (instantiate-linklet l2 li-1 #:target t2)
                       (instance-variable-value t2 x))
              1)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; defs_export_names
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4))])
                       (let-inst i (instantiate-linklet l))
                       (instance-variable-value i x15))
              4)

; "LinkletVars will be referred by the external name (e.g. (+ x15 x15)"
(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))])
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x15)) ; t doesn't have x
              4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; discarding_defs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15))
                                    (define-values (x) 4)
                                    (define-values (x15) 75))])
                       (let-inst i (instantiate-linklet l))
                       (instance-variable-value i x15))
              4) ; not 75

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15) k)
                                    (define-values (x) 4)
                                    (define-values (x15) 75)
                                    (define-values (k) x15))])
                       (let-inst i (instantiate-linklet l))
                       (instance-variable-value i x15)
                       (instance-variable-value i k))
              75) ; not 4

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; use targets def
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () (x) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              20)

; "use linklet's definition if both linklet and target have it"
; tests the compile linklet, the x's in the (+ x x) should be toplevel
; defined ids (not linklet vars)
(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 4) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              8)

(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 4) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; imports & exports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) () (+ x x))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t))
              8)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet (((x x2))) () (+ x2 x2))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t))
              8)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) (y) (define-values (y) (+ x x)) (+ y y))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t))
              16)

; "target's defs are overwritten only if the linklet has a definition not with an imported variable"
; (whether or not the linklet exports it)
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) (x) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 1000))])

                       (let-inst L1 (instantiate-linklet l1)) ; x 4
                       (let-inst t (instantiate-linklet t-l)) ; x 1000

                       (instantiate-linklet l2 L1 #:target t)
                       (instance-variable-value t x))
              1000)

; "same thing with the import renaming"
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet (((x x2))) () (+ x2 x2))]
                        [t-l (linklet () (x2) (define-values (x) 1000) (define-values (x2) 2000))])

                       (let-inst L1 (instantiate-linklet l1)) ; x 4
                       (let-inst t (instantiate-linklet t-l)) ; x 1000

                       (instantiate-linklet l2 L1 #:target t)
                       (instance-variable-value t x2))
              2000)
;;;; FIXME : create a way to check multiple things at once
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet (((x x2))) () (+ x2 x2))]
                        [t-l (linklet () (x) (define-values (x) 1000) (define-values (x2) 2000))])

                       (let-inst L1 (instantiate-linklet l1)) ; x 4
                       (let-inst t (instantiate-linklet t-l)) ; x 1000

                       (instantiate-linklet l2 L1 #:target t)
                       (instance-variable-value t x))
              1000)

; "slightly trickier"
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet (((x x2))) () (define-values (x) 14) (+ x2 x))]
                        [t-l (linklet () (x x2) (define-values (x) 1000) (define-values (x2) 2000))])

                       (let-inst L1 (instantiate-linklet l1)) ; x 4
                       (let-inst t (instantiate-linklet t-l)) ; x 1000

                       (instantiate-linklet l2 L1 #:target t))
              18)

(linklet-test (program (use-linklets
                        [l1 (linklet () (a) (define-values (a) 4))]
                        [l2 (linklet ((a)) () (+ a a))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t))
              8)
; "export-rename"
(linklet-test (program (use-linklets
                        [l1 (linklet () ((a1 a)) (define-values (a1) 4))]
                        [l2 (linklet ((a)) () (+ a a))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t))
              8)

; these may be redundant
(linklet-test (program (use-linklets
                        [l1 (linklet () ((x1 x)) (define-values (x1) 4))]
                        [l2 (linklet ((x)) ((y1 y)) (define-values (y1) x) (+ x y1))])
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l2 L1 #:target t))
              8)

(linklet-test (program (use-linklets
                        [l1 (linklet () ((x1 x)) (define-values (x1) 4))]
                        [l2 (linklet ((x)) ((y1 y)) (define-values (y1) x) (+ x y1))])
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l2 L1 #:target t)
                       (instance-variable-value t y))
              4)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet () (x) (define-values (x) 10))]
                        [l3 (linklet (((x x1))((x x2))) () (+ x1 x2))])
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst L2 (instantiate-linklet l2))
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l3 L1 L2 #:target t))
              14)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uninitialize undefine-valuesd exports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; "don't touch if target has it"
(linklet-test (program (use-linklets
                        [l (linklet () (x))]
                        [t-l (linklet () (x) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              10)

(linklet-test (program (use-linklets
                        [l (linklet () (x) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 30))]
                        [k (linklet () (x) (define-values (x) 20))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet k)
                       (instantiate-linklet l #:target t))
              60)

; "target exports the same var with another external name"
(linklet-test (program (use-linklets
                        [l (linklet () (x2) (+ x2 x2))]
                        [t-l (linklet () ((x x2)) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              20)

(linklet-test (program (use-linklets
                        [l (linklet () (x2) (+ x2 x2))]
                        [t-l (linklet () ((x x2)) (define-values (x) 10))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x2))
              10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eval define values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                        [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              8)

; these two below are actually an export rename test
(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                        [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x15))
              4)

(linklet-test (program (use-linklets
                        [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                        [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x16))
              1000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; closures and variables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; find the closure in the target and apply it
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) (g) (define-values (g) (lambda (y) x)))]
                        [l3 (linklet () (g) (g 5))])
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst t (linklet-instance))
                       (instantiate-linklet l2 L1 #:target t)
                       (instantiate-linklet l3 #:target t))
              4)

; import the closure and apply it
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 4))]
                        [l2 (linklet ((x)) (g) (define-values (g) (lambda (y) x)))]
                        [l4 (linklet ((g)) () (g 3))])
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst t (linklet-instance))
                       (let-inst L5 (instantiate-linklet l2 L1))
                       (instantiate-linklet l4 L5 #:target t))
              4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; set!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 3) (set! x 5) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 6))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              10)

(linklet-test (program (use-linklets
                        [l (linklet () () (define-values (x) 3) (set! x 5) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 6))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              6)

(linklet-test (program (use-linklets
                        [l (linklet () (x) (set! x 5) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 3))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t))
              10)

; the real thing is this one below
(linklet-test (program (use-linklets
                        [l (linklet () (x) (set! x 5) (+ x x))]
                        [t-l (linklet () (x) (define-values (x) 3))])
                       (let-inst t (instantiate-linklet t-l))
                       (instantiate-linklet l #:target t)
                       (instance-variable-value t x))
              5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; closure capture and reset
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) -1))]
                        [l2 (linklet ((x)) (g) (define-values (g) (lambda (p) x)))]
                        [l3 (linklet ((g)) (x) (set! x 5) (g 1000))]
                        [t-l (linklet () (x) (define-values (x) 2000))])
                       (let-inst t (instantiate-linklet t-l))
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst L2 (instantiate-linklet l2 L1))
                       (instantiate-linklet l3 L2 #:target t))
              -1)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) -1))]
                        [l2 (linklet ((x)) (g) (define-values (g) (lambda (p) x)))]
                        [l3 (linklet ((g)) (x) (set! x 5) (g 1000))]
                        [t-l (linklet () (x) (define-values (x) 2000))])
                       (let-inst t (instantiate-linklet t-l))
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst L2 (instantiate-linklet l2 L1))
                       (instantiate-linklet l3 L2 #:target t)
                       (instance-variable-value t x))
              5)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) -11))]
                        [l2 (linklet ((x)) (g)
                                     (define-values (y) 131)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 71))]
                        [l3 (linklet ((g)) () (g -1))])
                       (let-inst t (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (let-inst L2 (instantiate-linklet l2 L1))
                       (instantiate-linklet l3 L2 #:target t))
              60)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; slightly more complex tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 3 --- 1

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l3 (linklet () (y g)
                                     (set! y 200)
                                     (g -1))])
                       (let-inst t1 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t1) ; fill in the target
                       (instantiate-linklet l3 #:target t1))
              201)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l3 (linklet () (y g) (set! y 200) (g -1))])
                       (let-inst t1 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t1) ; fill in the target
                       (instantiate-linklet l3 #:target t1)
                       (instance-variable-value t1 y))
              200)
;; 3 --- 2

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l4 (linklet () (y g)
                                     (set! y 200)
                                     (define-values (y) 90)
                                     (g -1))])
                       (let-inst t2 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t2) ; fill in the target
                       (instantiate-linklet l4 #:target t2))
              91)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l4 (linklet () (y g)
                                     (set! y 200)
                                     (define-values (y) 90)
                                     (g -1))])
                       (let-inst t2 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t2) ; fill in the target
                       (instantiate-linklet l4 #:target t2)
                       (instance-variable-value t2 y))
              90)

;; 3 --- 3
(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l5 (linklet () (g)
                                     (define-values (y) 90)
                                     (+ y (g -1)))])
                       (let-inst t3 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t3) ; fill in the target
                       (instantiate-linklet l5 #:target t3))
              141)

(linklet-test (program (use-linklets
                        [l1 (linklet () (x) (define-values (x) 1))]
                        [l2 (linklet ((x)) (y g)
                                     (define-values (y) 10)
                                     (define-values (g) (lambda (p) (+ x y)))
                                     (set! y 50))]
                        [l5 (linklet () (g)
                                     (define-values (y) 90)
                                     (+ y (g -1)))])
                       (let-inst t3 (linklet-instance))
                       (let-inst L1 (instantiate-linklet l1))
                       (instantiate-linklet l2 L1 #:target t3) ; fill in the target
                       (instantiate-linklet l5 #:target t3)
                       (instance-variable-value t3 y))
              50)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; random testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Random Testing for Racket-Core

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
(eval-rc=racket-core? (if (void) (let-values () (void)) (< qw F)))
(eval-rc=racket-core? ((lambda () (void))))

#;(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)

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


;(redex-check Linklets (term (eval-programs=racket-linklets e)) #:attempts 1000)
