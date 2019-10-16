#lang racket

(require redex
         "../lang.rkt"
         "../linklets.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instantiation side tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (get-var-from-instance c (linklet-instance (c cell1)))) (term cell1))

(test-equal
 (term
  (instantiate-exports ((Export a a1 a)) target ((target (linklet-instance))) () ()))
 (term (((target (linklet-instance (a cell_1))) (target (linklet-instance)))
        ((a1 cell_1))
        ((cell_1 uninit)))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lα () ()) #:target t1))
                    ((t1 (linklet-instance)))
                    () ())))
            (term (((program (use-linklets) (instantiate-linklet (Lγ)))
                    ((t1 (linklet-instance)))
                    ()
                    ()))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) (instantiate-linklet (Lγ)))
                    ((t1 (linklet-instance)))
                    ()
                    ())))
            (term (((program (use-linklets) (void))
                    ((t1 (linklet-instance)))
                    () ()))))


(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t1 (linklet-instance)
                                       (instantiate-linklet (Lα () ()) #:target t1)))
                    () () ())))
            (term (((program (use-linklets)
                             (seq (instantiate-linklet (Lα () ()) #:target t1)))
                    ((t1 (linklet-instance))) () ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Instantiation Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lα () ((Export y y1 y))
                                                                  (define-values (y) 10)
                                                                  (var-set! y1 y)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    () () ())))
            (term (((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (define-values (y) 10)
                                                                  (var-set! y1 y)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance))) ((y1 cell_1)) ((cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (define-values (y) 10)
                                                                  (var-set! y1 y)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y1 cell_1))
                    ((cell_1 uninit)))))
            (term (((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (var-set! y1 y)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (var-set! y1 y) ; y : 10
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (void)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (void)
                                                                  (var-set/check-undef! y1 50)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (void)
                                                                  (void)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (instantiate-linklet (Lβ x
                                                                  (void)
                                                                  (void)
                                                                  (void)))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (let-inst t (linklet-instance (y cell_1))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation ;; let-inst extend environment
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (linklet-instance (y cell_1))
                                       (instance-variable-value t y)))
                    ((x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets) (seq (instance-variable-value t y)))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) (seq (instance-variable-value t y)))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets) (seq (instance-variable-value (linklet-instance (y cell_1)) y)))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) (seq (instance-variable-value (linklet-instance (y cell_1)) y)))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets) (seq 50))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) (seq 50))
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit)))))
            (term (((program (use-linklets) 50)
                    ((t (linklet-instance (y cell_1))) (x (linklet-instance (y cell_1))) (x (linklet-instance)))
                    ((y cell_2) (y1 cell_1))
                    ((cell_1 50) (cell_1 10) (cell_2 10) (cell_1 uninit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Evaluation Example (instantiation with target)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lα () ((Export x x1 x))
                                                      (define-values (x) 5)
                                                      (var-set! x1 x)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))
                                                  #:target (linklet-instance)))
                    () () ())))
            (term (((program (use-linklets)
                             (instantiate-linklet (Lγ (define-values (x) 5)
                                                      (var-set! x1 x)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x1 cell_1))
                    ((cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lγ (define-values (x) 5)
                                                      (var-set! x1 x)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x1 cell_1))
                    ((cell_1 uninit)))))
            (term (((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (var-set! x1 x)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lγ (var-set! x1 x) ; 5
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                            (instantiate-linklet (Lγ (void)
                                                     (var-set/check-undef! x1 6)
                                                     (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (void)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (void)
                                                      (+ (var-ref x1) (var-ref x1)))))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (void)
                                                      12)))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (instantiate-linklet (Lγ (void)
                                                      (void)
                                                      12)))
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets) 12)
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets) 12)
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term ((12
                    ((t (linklet-instance (x cell_1))) (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Evaluation Example (instantiation with target) with let-inst extend vs substitute
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (let-inst t (linklet-instance)
                                       (instantiate-linklet (Lα () ((Export x x1 x))
                                                                (define-values (x) 5)
                                                                (var-set! x1 x)
                                                                (var-set/check-undef! x1 6)
                                                                (+ (var-ref x1) (var-ref x1)))
                                                            #:target t)
                                       (instance-variable-value t x)))
                    () () ())))
            (term (((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lα () ((Export x x1 x))
                                                       (define-values (x) 5)
                                                       (var-set! x1 x)
                                                       (var-set/check-undef! x1 6)
                                                       (+ (var-ref x1) (var-ref x1)))
                                                   #:target t)
                              (instance-variable-value t x)))
                    ((t (linklet-instance))) () ()))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lα () ((Export x x1 x))
                                                       (define-values (x) 5)
                                                       (var-set! x1 x)
                                                       (var-set/check-undef! x1 6)
                                                       (+ (var-ref x1) (var-ref x1)))
                                                   #:target t)
                              (instance-variable-value t x)))
                    ((t (linklet-instance))) () ())));  <------------------------------|
            (term (((program (use-linklets) ;;; TARGET IS BEING MODIFIED --------------|
                             (seq;                                                     |
                              (instantiate-linklet (Lγ (define-values (x) 5);          |
                                                       (var-set! x1 x);                |
                                                       (var-set/check-undef! x1 6);    |
                                                       (+ (var-ref x1) (var-ref x1))));|
                              (instance-variable-value t x)));                         |
                    ((t (linklet-instance (x cell_1)));   <----------------------------|
                     (t (linklet-instance)))
                    ((x1 cell_1))
                    ((cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (define-values (x) 5)
                                                       (var-set! x1 x)
                                                       (var-set/check-undef! x1 6)
                                                       (+ (var-ref x1) (var-ref x1))))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x1 cell_1))
                    ((cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (var-set! x1 x)
                                                       (var-set/check-undef! x1 6)
                                                       (+ (var-ref x1) (var-ref x1))))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                             (instantiate-linklet (Lγ (void)
                                                      (var-set! x1 x) ; x : 5
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1))))
                             (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                            (seq
                             (instantiate-linklet (Lγ (void)
                                                      (void)
                                                      (var-set/check-undef! x1 6)
                                                      (+ (var-ref x1) (var-ref x1))))
                             (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (void)
                                                       (var-set/check-undef! x1 6)
                                                       (+ (var-ref x1) (var-ref x1))))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (void)
                                                       (void)
                                                       (+ (var-ref x1) (var-ref x1))))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (void)
                                                       (void)
                                                       (+ (var-ref x1) (var-ref x1))))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (void)
                                                       (void)
                                                       12))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              (instantiate-linklet (Lγ (void)
                                                       (void)
                                                       (void)
                                                       12))
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq
                              12
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              12
                              (instance-variable-value t x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq 12
                                  (instance-variable-value (linklet-instance (x cell_1)) x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq
                              12
                              (instance-variable-value (linklet-instance (x cell_1)) x)))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets)
                             (seq 12
                                  6))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

(test-equal (apply-reduction-relation
             -->βp
             (term ((program (use-linklets)
                             (seq 12 6))
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit)))))
            (term (((program (use-linklets) 6)
                    ((t (linklet-instance (x cell_1)))
                     (t (linklet-instance)))
                    ((x cell_2) (x1 cell_1))
                    ((cell_1 6) (cell_1 5) (cell_2 5) (cell_1 uninit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;,




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
