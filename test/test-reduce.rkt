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
                     (instantiate-linklet (Lβ li (var-set! y1 y) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (var-set! y1 10) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (var-set/check-undef! y1 50)))
                     (instance-variable-value t y)))
  ((y cell_2) (y1 cell_1))
  ((cell_1 10) (cell_2 10) (li (linklet-instance (y cell_1))) (cell_1 uninit)  (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t
                     (instantiate-linklet (Lβ li (void) (void)))
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
            (instantiate-linklet (Lβ t (var-set! x1 x) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (var-set! x1 5) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (seq
            (instantiate-linklet (Lβ t (void) (var-set/check-undef! x1 6) (+ (var-ref x1) (var-ref x1))))
            (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (+ (var-ref x1) (var-ref x1))))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (+ 6 (var-ref x1))))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq
                           (instantiate-linklet (Lβ t (void) (void) (+ 6 6)))
                           (instance-variable-value t x)))
  ((x cell_2) (x1 cell_1))
  ((cell_1 6) (cell_1 5) (cell_2 5) (t (linklet-instance (x cell_1))) (cell_1 uninit) (t (linklet-instance)) (li (linklet-instance))))
 -->r
 ((program (use-linklets) (seq (instantiate-linklet (Lβ t (void) (void) 12))
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
;;;; Evaluation Example 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-multi-step
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a)))
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  () ())
 -->p
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a)) #:target li)
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  () ((li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lβ li (define-values (a) 10) (var-set! a1 a)))
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  ((a1 cell_1)) ((li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lβ li (var-set! a1 a)))
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  ((a cell_2) (a1 cell_1)) ((cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lβ li (var-set! a1 10)))
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  ((a cell_2) (a1 cell_1)) ((cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (let-inst t (instantiate-linklet (Lβ li (void)))
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  ((a cell_2) (a1 cell_1)) ((cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (let-inst t ((void) li)
                     (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t)))
  ((a cell_2) (a1 cell_1)) ((cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (instantiate-linklet (Lα () () (define-values (x) 5) (+ x a)) #:target t))
  ((a cell_2) (a1 cell_1)) ((t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (instantiate-linklet (Lβ t (define-values (x) 5) (+ x a))))
  ((a cell_2) (a1 cell_1)) ((t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (instantiate-linklet (Lβ t (+ x a))))
  ((x cell_3) (a cell_2) (a1 cell_1)) ((cell_3 5) (t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (instantiate-linklet (Lβ t (+ 5 a))))
  ((x cell_3) (a cell_2) (a1 cell_1)) ((cell_3 5) (t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (instantiate-linklet (Lβ t (+ 5 10))))
  ((x cell_3) (a cell_2) (a1 cell_1)) ((cell_3 5) (t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->r
 ((program (use-linklets)
           (instantiate-linklet (Lβ t 15)))
  ((x cell_3) (a cell_2) (a1 cell_1)) ((cell_3 5) (t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 -->p
 ((program (use-linklets)
           (15 t))
  ((x cell_3) (a cell_2) (a1 cell_1)) ((cell_3 5) (t (linklet-instance (a cell_1))) (cell_1 10) (cell_2 10) (li (linklet-instance (a cell_1))) (cell_1 uninit) (li (linklet-instance))))
 )

;; Top-level repl example

#|
> (define k (lambda () a))
> (define a 10)
> (k)
10
|#

(test-multi-step
 ((program
   (use-linklets
    (l1 (linklet () (a k) (define-values (k) (lambda () a)) 1))
    (l2 (linklet () (a) (define-values (a) 10) 1))
    (l3 (linklet () (k) (k))))
   (let-inst t (make-instance)
             (seq
              (instantiate-linklet l1 #:target t)
              (instantiate-linklet l2 #:target t)
              (instantiate-linklet l3 #:target t))))
  () ())
 -->p
 ((program
   (use-linklets
    (l2 (linklet () (a) (define-values (a) 10) 1))
    (l3 (linklet () (k) (k))))
   (let-inst t (make-instance)
             (seq
              (instantiate-linklet (Lα () ((Export a1 a a) (Export k1 k k))
                                       (define-values (k) (lambda () (var-ref a1)))
                                       (var-set! k1 k) 1) #:target t)
              (instantiate-linklet l2 #:target t)
              (instantiate-linklet l3 #:target t))))
  () ())
 -->p
 ((program
   (use-linklets
    (l3 (linklet () (k) (k))))
   (let-inst t (make-instance)
             (seq
              (instantiate-linklet (Lα () ((Export a1 a a) (Export k1 k k))
                                       (define-values (k) (lambda () (var-ref a1))) (var-set! k1 k) 1) #:target t)
              (instantiate-linklet (Lα () ((Export a1 a a))
                                       (define-values (a) 10) (var-set! a1 a) 1) #:target t)
              (instantiate-linklet l3 #:target t))))
  () ())
 -->p
 ((program
   (use-linklets)
   (let-inst t (make-instance)
             (seq
              (instantiate-linklet (Lα () ((Export a1 a a) (Export k1 k k))
                                       (define-values (k) (lambda () (var-ref a1))) (var-set! k1 k) 1) #:target t)
              (instantiate-linklet (Lα () ((Export a1 a a))
                                       (define-values (a) 10) (var-set! a1 a) 1) #:target t)
              (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t))))
  () ())
 -->p
 ((program
   (use-linklets)
   (let-inst t ((void) li)
             (seq
              (instantiate-linklet (Lα () ((Export a1 a a) (Export k1 k k))
                                       (define-values (k) (lambda () (var-ref a1))) (var-set! k1 k) 1) #:target t)
              (instantiate-linklet (Lα () ((Export a1 a a))
                                       (define-values (a) 10) (var-set! a1 a) 1) #:target t)
              (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t))))
  () ((li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lα () ((Export a1 a a) (Export k1 k k))
                             (define-values (k) (lambda () (var-ref a1))) (var-set! k1 k) 1) #:target t)
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  () ((t (linklet-instance)) (li (linklet-instance))))
 -->p ;;; (define k (lambda () a)) start
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lβ t (define-values (k) (lambda () (var-ref a1))) (var-set! k1 k) 1))
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k1 cell_2) (a1 cell_1))
  ((t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lβ t (define-values (k) (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1)))) (var-set! k1 k) 1))
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k1 cell_2) (a1 cell_1))
  ((t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lβ t (var-set! k1 k) 1))
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k cell_3) (k1 cell_2) (a1 cell_1))
  ((cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lβ t (var-set! k1 (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1)))) 1))
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k cell_3) (k1 cell_2) (a1 cell_1))
  ((cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (instantiate-linklet (Lβ t (void) 1))
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k cell_3) (k1 cell_2) (a1 cell_1))
  ((cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (1 t)
    (instantiate-linklet (Lα () ((Export a1 a a)) (define-values (a) 10) (var-set! a1 a) 1) #:target t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((k cell_3) (k1 cell_2) (a1 cell_1))
  ((cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p ;;; (define a 10) start
 ((program
   (use-linklets)
   (seq
    (1 t)
    (instantiate-linklet (Lβ t (define-values (a) 10) (var-set! a1 a) 1))
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((a1 cell_1) (k cell_3) (k1 cell_2) (a1 cell_1))
  ((cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (1 t)
    (instantiate-linklet (Lβ t (var-set! a1 a) 1))
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (1 t)
    (instantiate-linklet (Lβ t (var-set! a1 10) 1))
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (1 t)
    (instantiate-linklet (Lβ t (void) 1))
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (instantiate-linklet (Lα () ((Export k1 k k)) ((var-ref k1))) #:target t)))
  ((a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p ;; (k) starts
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (instantiate-linklet (Lβ t ((var-ref k1))))))
  ((k1 cell_2)
   (a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (instantiate-linklet (Lβ t ((closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))))))
  ((k1 cell_2)
   (a cell_4)
   (a1 cell_1)
   (k cell_3)
   (k1 cell_2)
   (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (instantiate-linklet (Lβ t (var-ref a1)))))
  ((k1 cell_2) (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->r
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (instantiate-linklet (Lβ t 10))))
  ((k1 cell_2) (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (seq
    (1 t)
    (1 t)
    (10 t)))
  ((k1 cell_2) (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))
 -->p
 ((program
   (use-linklets)
   (10 t))
  ((k1 cell_2) (a1 cell_1))
  ((cell_1 10)
   (cell_4 10)
   (cell_2
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (cell_3
    (closure () (var-ref a1) ((k1 cell_2) (a1 cell_1))))
   (t (linklet-instance (a cell_1) (k cell_2)))
   (cell_2 uninit)
   (t (linklet-instance (a cell_1)))
   (cell_1 uninit)
   (t (linklet-instance))
   (li (linklet-instance))))

 )

#;

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
