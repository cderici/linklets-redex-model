#lang racket

(require redex
         "linklets.rkt"
         "racket-core.rkt")



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

(redex-check RC e-test (term (eval-rc=racket-core e)) #:attempts 1000)

(define-metafunction Linklets
  [(IT-to-racket (instantiate x x_1 ...))
   (instantiate-linklet x (list x_1 ...))]
  [(IT-to-racket (instantiate L x ...))
   (instantiate-linklet (compile-linklet (quote L)) (list x ...))]
  [(IT-to-racket (instantiate x x_1 ... #:target x_T))
   (instantiate-linklet x (list x_1 ...) x_T)]
  [(IT-to-racket (instantiate L x ... #:target x_T))
   (instantiate-linklet (compile-linklet (quote L)) (list x ...) x_T)])

(define-metafunction Linklets
  [(prog-top-to-racket true) #t]
  [(prog-top-to-racket false) #f]
  [(prog-top-to-racket (raises e)) (error (quote e))]
  [(prog-top-to-racket rc-out) rc-out]
  [(prog-top-to-racket I-test) (IT-to-racket I-test)]
  [(prog-top-to-racket T-test) (IT-to-racket T-test)]
  [(prog-top-to-racket (define-values (x) e))
   (define-values (x) (prog-top-to-racket e))]
  [(prog-top-to-racket (let-inst x I-test))
   (define x (IT-to-racket I-test))]
  [(prog-top-to-racket (instance-variable-value x_1 x_2))
   (instance-variable-value x_1 (quote x_2))]
  [(prog-top-to-racket (lambda (x ...) e))
   (lambda (x ...) (prog-top-to-racket e))]
  [(prog-top-to-racket (begin e ...))
   (begin (prog-top-to-racket e) ...)]
  [(prog-top-to-racket (if e_1 e_2 e_3))
   (if (prog-top-to-racket e_1) (prog-top-to-racket e_2) (prog-top-to-racket e_3))]
  [(prog-top-to-racket (let-values (((x) e) ...) e_b))
   (let-values (((x) (prog-top-to-racket e)) ...) (prog-top-to-racket e_b))]
  [(prog-top-to-racket (p2 e_1 e_2))
   (p2 (prog-top-to-racket e_1) (prog-top-to-racket e_2))]
  [(prog-top-to-racket (p1 e_1))
   (p1 (prog-top-to-racket e_1))]
  [(prog-top-to-racket (set! x e))
   (set! x (prog-top-to-racket e))]
  [(prog-top-to-racket (closure x ... e ρ))
   (lambda (x ...) (prog-top-to-racket e))]
  [(prog-top-to-racket (e_1 e ...))
   ((prog-top-to-racket e_1) (prog-top-to-racket e) ...)]
  [(prog-top-to-racket any) any])

(define-metafunction Linklets
  [(to-actual-racket
    (program (use-linklets (x (linklet ((imp-id_r ...) ...) (exp-id ...) l-top ...)) ...) p-top-test ... final-expr-test))
   (let ((x (compile-linklet
             (quote
              (linklet ((imp-id_r ...) ...) (exp-id ...) (prog-top-to-racket l-top) ...)))) ...)
     (prog-top-to-racket p-top-test) ...
     (prog-top-to-racket final-expr-test))])

(define-metafunction Linklets
  eval-prog=racket-linklets : p-test -> boolean
  [(eval-prog=racket-linklets p-test)
   ,(letrec ([rr (racket-evaluator (term (to-actual-racket p-test)))]
             [vr (term (eval-prog p-test))])
      (begin 1 #;(printf "Trying e : ~a\n" (term p-test))
      (cond
        [(and (exn? rr) (eq? (term stuck) vr)) (begin 1 #;(printf "both stuck on : ~a" (term p-test)) #true)]
        [(exn? rr) (begin (printf "\n racket raised exn : ~a -- ~a\n\n" (term p-test) (exn-message rr)) #false)]
        [(and (void? rr) (eq? (term void) vr)) #true]
        [(eq? (term stuck) vr) (begin (printf "\n racket not stuck : ~a\n\n" (term p-test)) #false)]
        [else (let ((q (equal? vr rr)))
                (begin (unless q
                         (printf "\nTerm : ~a ==> racket : ~a -- eval-rc : ~a\n" (term p-test) rr vr))
                       q))])))])

(redex-check Linklets p-test (term (eval-prog=racket-linklets p-test)) #:attempts 2000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklet Expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicates for testing

(define L? (redex-match? Linklets L))
(define not-L? (compose not L?))

(define LI? (redex-match? Linklets LI))
(define not-LI? (compose not LI?))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linklet Program Expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program? (redex-match? Linklets p))
(define not-program? (compose not program?))

(test-predicate not-program? (term (program (use-linklets))))

(test-predicate program? (term (program (use-linklets) (let-inst ti (instantiate t)) (instantiate l #:target ti))))
(test-predicate program? (term (program (use-linklets
                                         [l (linklet () () 1)]
                                         [t (linklet () ())])
                                        (let-inst ti (instantiate t))
                                        (instantiate l #:target ti)))) ; 1
; "program" will act like begin, the last result is returned, where
; result is either a linklet instance or a value (i.e. targeted instantiation)
(test-predicate program? (term (program (use-linklets
                                         [l1 (linklet () ())]
                                         [t (linklet () ())])
                                        (let-inst ti (instantiate t))
                                        (instantiate l1 #:target ti)))) ;; (void)
(test-predicate program? (term (program (use-linklets
                                         [l1 (linklet () ())]
                                         [l2 (linklet () () (define-values (x) 5) x)])
                                        (let-inst t1 (instantiate l1))
                                        (instantiate l2 #:target t1)))) ;; 5

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () 2 1)]
                                       [t (linklet () ())])
                                      (let-inst ti (instantiate t))
                                      (instantiate l #:target ti)))) 1)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () ())]
                                       [l2 (linklet () () (define-values (a) 5) a)])
                                      (let-inst t1 (instantiate l1))
                                      (instantiate l2 #:target t1)))) 5)

(test-equal (term (eval-prog (program (use-linklets
                                       [l2 (linklet () () (define-values (a) 5) a)])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l2 #:target t)))) 5)

(test-equal (term (eval-prog (program (use-linklets
                                       [l2 (linklet () () (define-values (a) 5) (define-values (b) 10) a (+ a a))])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l2 #:target t)))) 10)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () ())]
                                       [l2 (linklet ((b)) () (define-values (a) 5) (+ a b))]
                                       [l3 (linklet () (b) (define-values (b) 3))])
                                      (let-inst t3 (instantiate l3))
                                      (let-inst t1 (instantiate l1))
                                      (instantiate l2 t3 #:target t1)))) 8)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; PYCKET LINKLET TESTS BEGIN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; (test-equal (term (eval-prog (program (use-linklets
;;                                        [(


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (define-values (x) 4) (+ x x))]
                                       [t (linklet () () (define-values (x) 1) (define-values (y) 2))])
                                      (let-inst t1 (instantiate t))
                                      (instantiate l #:target t1)))) 8)


(test-equal (term (eval-prog (program (use-linklets
                                       [l2 (linklet () () (define-values (x) 4) (+ x x))])
                                      (let-inst t2 (linklet-instance ()))
                                      (instantiate l2 #:target t2)
                                      (instance-variable-value t2 x)))) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target_transfer_set_banged
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (y) 10) (set! y 50))])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l #:target t)
                                      (instance-variable-value t y)))) 50)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target_def_overwrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (define-values (x) 4) (+ x x))]
                                       [tl (linklet () () (define-values (x) 1))])
                                      (let-inst t (instantiate tl))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 4)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target always overwrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; "if target doesn't have it, then it doesn't matter if linklet exports or not, put the variable in the target"

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (z) 4) z)])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l #:target t)
                                      (instance-variable-value t z)))) 4)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; target def stays the same
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; "if linklet doesn't export, then target's def stay the same"

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (x) 4) (+ x x))]
                                       [tl (linklet () () (define-values (x) 1))])
                                      (let-inst t (instantiate tl))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 1)

; "use the local var, don't change target's var if you don't export"

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                                       [tl (linklet () (x) (define-values (x) 10))])
                                      (let-inst t (instantiate tl))
                                      (instantiate l #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                                       [tl (linklet () () (define-values (x) 10))]); <--------------|
                                      (let-inst t (instantiate tl));                       |
                                      (instantiate l #:target t);                          |
                                      (instance-variable-value t x)))) 10);                |
; target exports here   -------------------------------------------------------------------|
(test-equal (term (eval-prog (program (use-linklets ;                                      |
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))];    |
                                       [tl (linklet () (x) (define-values (x) 10))]); <-------------|
                                      (let-inst t (instantiate tl))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 10)

;  "imported variables doesn't get into target at all ... let alone overwrite any var inside the target"

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) () (+ x x))])
                                      (let-inst li-1 (instantiate l1))
                                      (let-inst t1 (linklet-instance ()))
                                      (instantiate l2 li-1 #:target t1)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) () (+ x x))]
                                       [tl-2 (linklet () () (define-values (x) 1))])
                                      (let-inst li-1 (instantiate l1))
                                      (let-inst t2 (instantiate tl-2))
                                      (instantiate l2 li-1 #:target t2)
                                      (instance-variable-value t2 x)))) 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; defs_export_names
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4))])
                                      (let-inst i (instantiate l))
                                      (instance-variable-value i x15)))) 4)

; "LinkletVars will be referred by the external name (e.g. (+ x15 x15)"
(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))])
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x15)))) 4)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; discarding_defs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15))
                                                   (define-values (x) 4)
                                                   (define-values (x15) 75))])
                                      (let-inst i (instantiate l))
                                      (instance-variable-value i x15)))) 4)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15))
                                                   (define-values (x) 4)
                                                   (define-values (x15) 75)
                                                   (define-values (k) x15))])
                                      (let-inst i (instantiate l))
                                      (instance-variable-value i x15)
                                      (instance-variable-value i k)))) 75)

#;(test-case ""
  (define l (instantiate-linklet
             (compile-linklet
              '(linklet () ((x x15) k) (define-values (x) 4) (define-values (x15) 75) (define-values (k) x15))) null))
  (check-false (member 'x (instance-variable-names l)))
  (check-eq? (instance-variable-value l 'x15) 4)
  (check-eq? (instance-variable-value l 'k) 75)
  ;; uninterned symbol W_Symbol("str")
  (check-eq? (instance-variable-value l (list-ref (instance-variable-names l) 2)) 75))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; use targets def
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 20)

; "use linklet's definition if both linklet and target have it"
(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (x) 4) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (x) 4) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; basic import
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) () (+ x x))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet (((x x2))) () (+ x2 x2))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) (y) (define-values (y) (+ x x)) (+ y y))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t)))) 16)

; "target's defs are overwritten only if the linklet has a definition not with an imported variable"
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) () (+ x x))]
                                       [t-l (linklet () () (define-values (x) 1000))])

                                      (let-inst L1 (instantiate l1)) ; x 4
                                      (let-inst t (instantiate t-l)) ; x 1000

                                      (instantiate l2 L1 #:target t)
                                      (instance-variable-value t x)))) 1000)

; "same thing with the import renaming"
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet (((x x2))) () (+ x2 x2))]
                                       [t-l (linklet () () (define-values (x) 1000) (define-values (x2) 2000))])

                                      (let-inst L1 (instantiate l1)) ; x 4
                                      (let-inst t (instantiate t-l)) ; x 1000

                                      (instantiate l2 L1 #:target t)
                                      (instance-variable-value t x2)))) 2000)
;;;; FIXME : create a way to check multiple things at once
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet (((x x2))) () (+ x2 x2))]
                                       [t-l (linklet () () (define-values (x) 1000) (define-values (x2) 2000))])

                                      (let-inst L1 (instantiate l1)) ; x 4
                                      (let-inst t (instantiate t-l)) ; x 1000

                                      (instantiate l2 L1 #:target t)
                                      (instance-variable-value t x)))) 1000)

; "slightly trickier"
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet (((x x2))) () (define-values (x) 14) (+ x2 x))]
                                       [t-l (linklet () () (define-values (x) 1000) (define-values (x2) 2000))])

                                      (let-inst L1 (instantiate l1)) ; x 4
                                      (let-inst t (instantiate t-l)) ; x 1000

                                      (instantiate l2 L1 #:target t)))) 18)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; basic export
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (a) (define-values (a) 4))]
                                       [l2 (linklet ((a)) () (+ a a))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t)))) 8)
; "export-rename"
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () ((a1 a)) (define-values (a1) 4))]
                                       [l2 (linklet ((a)) () (+ a a))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t)))) 8)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uninitialize undefine-valuesd exports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;(test-case "uninitialize undefined exports"
  (define l (compile-linklet '(linklet () (x))))
  (define t (empty-target))
  (instantiate-linklet l null t)
  (check-not-false (member 'x (instance-variable-names t))))

; "don't touch if target has it"
(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x))]
                                       [t-l (linklet () () (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 10)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 10))]
                                       [k (linklet () () (define-values (x) 20))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate k)
                                      (instantiate l #:target t)))) 20)

; "target exports the same var with another external name"
(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x2) (+ x2 x2))]
                                       [t-l (linklet () ((x x2)) (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 20)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x2) (+ x2 x2))]
                                       [t-l (linklet () ((x x2)) (define-values (x) 10))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x2)))) 10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; export rename
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () ((x1 x)) (define-values (x1) 4))]
                                       [l2 (linklet ((x)) ((y1 y)) (define-values (y1) x) (+ x y1))])
                                      (let-inst L1 (instantiate l1))
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l2 L1 #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () ((x1 x)) (define-values (x1) 4))]
                                       [l2 (linklet ((x)) ((y1 y)) (define-values (y1) x) (+ x y1))])
                                      (let-inst L1 (instantiate l1))
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l2 L1 #:target t)
                                      (instance-variable-value t y)))) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; import rename
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet () (x) (define-values (x) 10))]
                                       [l3 (linklet (((x x1))((x x2))) () (+ x1 x2))])
                                      (let-inst L1 (instantiate l1))
                                      (let-inst L2 (instantiate l2))
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l3 L1 L2 #:target t)))) 14)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eval define values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                                       [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 8)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                                       [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x15)))) 4)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () ((x x15)) (define-values (x) 4) (+ x x))]
                                       [t-l (linklet () ((x x16)) (define-values (x) 1000))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x16)))) 1000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; closures and variables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) (g) (define-values (g) (lambda (y) x)))]
                                       [l3 (linklet () (g) (g 5))])
                                      (let-inst L1 (instantiate l1))
                                      (let-inst t (linklet-instance ()))
                                      (instantiate l2 L1 #:target t)
                                      (instantiate l3 #:target t)))) 4)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 4))]
                                       [l2 (linklet ((x)) (g) (define-values (g) (lambda (y) x)))]

                                       [l4 (linklet ((g)) () (g 3))])
                                      (let-inst L1 (instantiate l1))
                                      (let-inst t (linklet-instance ()))

                                      (let-inst L5 (instantiate l2 L1))
                                      (instantiate l4 L5 #:target t)))) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; set!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (x) 3) (set! x 5) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 6))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 10)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () () (define-values (x) 3) (set! x 5) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 6))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 6)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (set! x 5) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 3))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)))) 10)

(test-equal (term (eval-prog (program (use-linklets
                                       [l (linklet () (x) (set! x 5) (+ x x))]
                                       [t-l (linklet () () (define-values (x) 3))])
                                      (let-inst t (instantiate t-l))
                                      (instantiate l #:target t)
                                      (instance-variable-value t x)))) 5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; closure capture and reset
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) -1))]
                                       [l2 (linklet ((x)) (g) (define-values (g) (lambda (p) x)))]
                                       [l3 (linklet ((g)) (x) (set! x 5) (g 1000))]
                                       [t-l (linklet () () (define-values (x) 2000))])
                                      (let-inst t (instantiate t-l))
                                      (let-inst L1 (instantiate l1))
                                      (let-inst L2 (instantiate l2 L1))
                                      (instantiate l3 L2 #:target t)))) -1)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) -1))]
                                       [l2 (linklet ((x)) (g) (define-values (g) (lambda (p) x)))]
                                       [l3 (linklet ((g)) (x) (set! x 5) (g 1000))]
                                       [t-l (linklet () () (define-values (x) 2000))])
                                      (let-inst t (instantiate t-l))
                                      (let-inst L1 (instantiate l1))
                                      (let-inst L2 (instantiate l2 L1))
                                      (instantiate l3 L2 #:target t)
                                      (instance-variable-value t x)))) 5)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) -11))]
                                       [l2 (linklet ((x)) (g) (define-values (y) 131) (define-values (g) (lambda (p) (+ x y))) (set! y 71))]
                                       [l3 (linklet ((g)) () (g -1))])
                                      (let-inst t (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (let-inst L2 (instantiate l2 L1))
                                      (instantiate l3 L2 #:target t)))) 60)

;; 3 --- 1

   (test-equal
    (term
     (eval-prog
      (program (use-linklets
                [l1 (linklet () (x) (define-values (x) 1))]
                [l2 (linklet ((x)) (y g)
                             (define-values (y) 10)
                             (define-values (g) (lambda (p) (+ x y)))
                             (set! y 50))]
                [l3 (linklet () (y g)
                             (set! y 200)
                             (g -1))])
               (let-inst t1 (linklet-instance ()))
               (let-inst L1 (instantiate l1))
               (instantiate l2 L1 #:target t1) ; fill in the target
               (instantiate l3 #:target t1)))) 201)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 1))]
                                       [l2 (linklet ((x)) (y g) (define-values (y) 10) (define-values (g) (lambda (p) (+ x y))) (set! y 50))]
                                       [l3 (linklet () (y g) (set! y 200) (g -1))])
                                      (let-inst t1 (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t1) ; fill in the target
                                      (instantiate l3 #:target t1)
                                      (instance-variable-value t1 y)))) 200)
;; 3 --- 2


  (test-equal
   (term
    (eval-prog (program (use-linklets
                         [l1 (linklet () (x) (define-values (x) 1))]
                         [l2 (linklet ((x)) (y g)
                                      (define-values (y) 10)
                                      (define-values (g) (lambda (p) (+ x y)))
                                      (set! y 50))]
                         [l4 (linklet () (y g)
                                      (set! y 200)
                                      (define-values (y) 90)
                                      (g -1))])
                        (let-inst t2 (linklet-instance ()))
                        (let-inst L1 (instantiate l1))
                        (instantiate l2 L1 #:target t2) ; fill in the target
                        (instantiate l4 #:target t2)))) 91)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 1))]
                                       [l2 (linklet ((x)) (y g) (define-values (y) 10) (define-values (g) (lambda (p) (+ x y))) (set! y 50))]
                                       [l4 (linklet () (y g) (set! y 200) (define-values (y) 90) (g -1))])
                                      (let-inst t2 (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t2) ; fill in the target
                                      (instantiate l4 #:target t2)
                                      (instance-variable-value t2 y)))) 90)

;; 3 --- 3
(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 1))]
                                       [l2 (linklet ((x)) (y g) (define-values (y) 10) (define-values (g) (lambda (p) (+ x y))) (set! y 50))]
                                       [l5 (linklet () (g) (define-values (y) 90) (+ y (g -1)))])
                                      (let-inst t3 (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t3) ; fill in the target
                                      (instantiate l5 #:target t3)))) 141)

(test-equal (term (eval-prog (program (use-linklets
                                       [l1 (linklet () (x) (define-values (x) 1))]
                                       [l2 (linklet ((x)) (y g) (define-values (y) 10) (define-values (g) (lambda (p) (+ x y))) (set! y 50))]
                                       [l5 (linklet () (g) (define-values (y) 90) (+ y (g -1)))])
                                      (let-inst t3 (linklet-instance ()))
                                      (let-inst L1 (instantiate l1))
                                      (instantiate l2 L1 #:target t3) ; fill in the target
                                      (instantiate l5 #:target t3)
                                      (instance-variable-value t3 y)))) 50)

(test-results)
