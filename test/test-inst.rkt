#lang racket

(require redex
         "../lang.rkt"
         "../linklets.rkt"
         "../racket-core.rkt"
         (for-syntax syntax/parse))

(define-syntax (test-step-reduce stx)
  (syntax-parse stx #:datum-literals (-->p -->r)
    [(_ t1 -->p t2)
     #'(test-equal (apply-reduction-relation -->βp (term t1)) (term (t2)))]
    [(_ t1 -->r t2)
     #'(test-equal (apply-reduction-relation -->βr (term t1)) (term (t2)))]))

(define-syntax (test-multi-step stx)
  (syntax-parse stx
    [(_) #'()]
    [(_ t2 red t3)
     #'(test-step-reduce t2 red t3)]
    [(_ t1 red_1 t2 red_2 t3 ...)
     #'(begin (test-step-reduce t1 red_1 t2)
              (test-multi-step t2 red_2 t3 ...))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instantiation side tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (get-var-from-instance c t ((t (linklet-instance (c cell1)))))) (term cell1))

(test-equal
 (term
  (instantiate-exports ((Export a1 a a)) target () ((target (linklet-instance)))))
 (term (((a1 cell_1))
        ((target (linklet-instance (a cell_1))) (cell_1 uninit) (target (linklet-instance))))))



(test-step-reduce
 ((program (use-linklets) (instantiate-linklet (Lα () () 1) #:target t1)) () ((t1 (linklet-instance))))
 -->p
 ((program (use-linklets) (instantiate-linklet (Lβ t1 1))) () ((t1 (linklet-instance)))))


(test-step-reduce
 ((program (use-linklets) (instantiate-linklet (Lβ t1 1))) () ((t1 (linklet-instance))))
 -->p
 ((program (use-linklets) (1 t1)) () ((t1 (linklet-instance)))))


(test-step-reduce
 ((program (use-linklets) (let-inst t1 (make-instance) (instantiate-linklet (Lα () () 1) #:target t1))) () ())
 -->p
 ((program (use-linklets) (let-inst t1 ((void) li) (instantiate-linklet (Lα () () 1) #:target t1))) () ((li (linklet-instance)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Instantiation Example (without target)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-multi-step
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lα () ((Export y1 y y)) (define-values (y) 10) (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  () ())
 -->p
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lα () ((Export y1 y y)) (define-values (y) 10) (var-set! y1 y) (var-set/check-undef! y1 50)) #:target li)
                     (instance-variable-value t y)))
  () ((li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (define-values (y) 10) (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y1 cell_1))
  ((li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (var-set! y1 10) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (void) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit)  (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (void) (void)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_1 50) (cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t
                     ((void) li)
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_1 50) (cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets) (instance-variable-value t y))
  ((y cell_2) (y1 cell_1))
  ((t (linklet-instance (y cell_1))) (cell_1 50) (cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets) (50 t))
  ((y cell_2) (y1 cell_1))
  ((t (linklet-instance (y cell_1))) (cell_1 50) (cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Evaluation Example (instantiation with target)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-multi-step
 ((program (use-linklets)
           (let-inst t (make-instance)
                     (seq
                      (instantiate-linklet (Lα () ((Export x1 x x)) (define-values (x) 5) (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))) #:target t)
                      (instance-variable-value t x))))
  () ())
 -->p
 ((program (use-linklets)
           (let-inst t ((void) li)
                     (seq
                      (instantiate-linklet (Lα () ((Export x1 x x)) (define-values (x) 5) (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))) #:target t)
                      (instance-variable-value t x))))
  () ((li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lα () ((Export x1 x x)) (define-values (x) 5) (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))) #:target t)
            (instance-variable-value t x)))
  () ((t (linklet-instance)) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (define-values (x) 5) (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x1 cell_1))
  ((t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (void) (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (void) (var-set! x1 5) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (void) (void) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (void) (+ (var-ref x1) (var-ref x1))))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (void) (+ 6 (var-ref x1))))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (void) (+ 6 6)))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq (instantiate-linklet (Lβ t (void) (void) (void) 12))
                               (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->p
 ((program (use-linklets) (seq (12 t)
                               (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->p
 ((program (use-linklets) (seq (12 t) (6 t)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->p
 ((program (use-linklets) (6 t))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; MISC
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-multi-step
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (define-values (y) (+ 7 3)) (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y1 cell_1))
  ((li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (define-values (y) 10) (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y1 cell_1))
  ((li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance)))))


#;(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (+ 1 2)) () ())))
            (term (((Lα () () 3) () ()))))

#;(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (define-values (a) 5) a) () ())))
            (term (((Lα () () (void) a) ((a cell)) ((cell 5))))))

#;(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () 3 a) ((a cell)) ((cell 5)))))
            (term (((Lα () () 3 5) ((a cell)) ((cell 5))))))

#;(test-equal (apply-reduction-relation
             -->βi
             (term ((Lα () () (void) a) ((a cell)) ((cell 5)))))
            (term (((Lα () () (void) 5) ((a cell)) ((cell 5))))))

