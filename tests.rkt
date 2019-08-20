#lang racket

(require redex
         "linklets.rkt"
         "racket-core.rkt"
         syntax/parse/define)



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
(test-predicate RC? (term (add1 x)))
(test-predicate RC? (term (+ 1 (add1 1))))
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
(test-predicate not-RC? (term (add1)))
(test-predicate not-RC? (term (set! 3 5)))

;; primitive δ tests
(test-equal (term (δ (add1 0))) (term 1))
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

;; random testing

(define-namespace-anchor A)
(define N (namespace-anchor->namespace A))

; Lambda.e -> Number or 'closure or exn or 'true or 'false or (void)
(define (racket-evaluator t0)
  (define result
    (with-handlers ((exn:fail? values) ((lambda (x) #t) values))
      (let ((C (make-base-namespace)))
        (parameterize ((current-namespace C))
          (begin
            (namespace-require 'racket/bool)
            (namespace-require 'racket/linklet)
            (eval t0))))))
  (cond
    [(number? result) result] ;; Number
    [(boolean? result) (if result 'true 'false)] ;; 'true or 'false
    [(procedure? result) (term closure)] ;; 'closure
    [(void? result) '(void)] ;; (void)
    [(exn? result) (make-exn (exn-message result) (current-continuation-marks))]
    ;; exn
    [else (make-exn (format "check the result type : ~a" result) (current-continuation-marks))]))

(define-metafunction RC
  eval-rc=racket-core : e -> boolean
  [(eval-rc=racket-core e)
   ,(letrec ([rr (racket-evaluator (term e))]
             [vr (term (eval-rc e))])
      (begin 1 #;(printf "Trying e : ~a\n" (term e))
      (cond
        [(and (exn? rr) (eq? (term stuck) vr)) (begin 1 #;(printf "both stuck on : ~a" (term e)) #true)]
        [(exn? rr) (begin (printf "\n racket raised exn : ~a -- ~a\n\n" (term e) (exn-message rr)) #false)]
        [(and (void? rr) (eq? (term void) vr)) #true]
        [(eq? (term stuck) vr) (begin (printf "\n racket not stuck : ~a\n\n" (term e)) #false)]
        [else (let ((q (equal? vr rr)))
                (begin (unless q
                         (printf "\nTerm : ~a ==> racket : ~a -- eval-rc : ~a\n" (term e) rr vr))
                       q))])))])

(test-equal (term (eval-rc=racket-core 1)) #true)
(test-equal (term (eval-rc=racket-core ((lambda (x) x) 1))) #true)
(test-equal (term (eval-rc=racket-core (+ x 1))) #true)
(test-equal (term (eval-rc=racket-core (void))) #true)
(test-equal (term (eval-rc=racket-core (add1 (void)))) #true)
(test-equal (term (eval-rc=racket-core (if (< 1 2) 1 2))) #true)
(test-equal (term (eval-rc=racket-core (if (< 1 2) (< 1 2) 2))) #true)
(test-equal (term (eval-rc=racket-core (set! q (void)))) #true)
(test-equal (term (eval-rc=racket-core ((lambda (x) x) (+ a b)))) #true)
(test-equal (term (eval-rc=racket-core (if (void) (void) (void)))) #true)
(test-equal (term (eval-rc=racket-core (if (void) (let-values () (void)) (< qw F)))) #true)
(test-equal (term (eval-rc=racket-core ((lambda () (void))))) #true)

;; Random Testing for Racket-Core
;(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)

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

(test-predicate not-program? (term (program (use-linklets))))

(program? (program (use-linklets)
                     (let-inst ti (instantiate t))
                     (instantiate l #:target ti)))
(program? (program (use-linklets
                      [l (linklet () () 1)]
                      [t (linklet () ())])
                     (let-inst ti (instantiate t))
                     (instantiate l #:target ti)))
(program? (program (use-linklets
                      [l1 (linklet () ())]
                      [l2 (linklet () () (define-values (x) 5) x)])
                     (let-inst t1 (instantiate l1))
                     (instantiate l2 #:target t1)))

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
(test-equal (term (get-mutated-vars-expr (begin 3) ())) (term ()))
(test-equal (term (get-mutated-vars-expr (begin 3 (set! x 15)) ())) (term (x)))
(test-equal (term (get-mutated-vars-expr (begin 3 (set! x 15) (set! y 15)) ())) (term (x y)))
(test-equal (term (get-mutated-vars-expr (define-values (x) 15) ())) (term ()))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15) (set! x 15)) ())) (term (x)))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15) (set! x 15) (set! y 14)) ())) (term (x y)))
(test-equal (term (get-all-mutated-vars ((define-values (x) 15) (begin (set! x 15) (set! y 14)) (set! z 14)) ())) (term (x y z)))
