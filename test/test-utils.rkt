#lang racket

(require redex
         "../lang.rkt"
         "../racket-core.rkt"
         "../linklets.rkt"
         syntax/parse/define
         "../main.rkt"
         "../util.rkt"
         (prefix-in model: "../compile-linklets.rkt"))

(provide (all-defined-out))

;; random testing

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For Racket Core
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


(define-simple-macro (eval-rc=racket-core? e)
  (test-equal (term (eval-rc=racket-core e)) #true))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For Linklets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction Linklets
  [(IT-to-racket (instantiate-linklet x x_1 ...))
   (instantiate-linklet x (list x_1 ...))]
  [(IT-to-racket (instantiate-linklet x x_1 ... #:target x_T))
   (instantiate-linklet x (list x_1 ...) x_T)]
  [(IT-to-racket (instantiate-linklet x x_1 ... #:target (linklet-instance)))
   (instantiate-linklet x (list x_1 ...) (make-instance #f #f))])

(define-metafunction LinkletProgramTest
  ; instance-variable-value
  [(prog-top-to-racket (instance-variable-value x_1 x_2))
   (instance-variable-value x_1 (quote x_2))]
  ; instantiate
  [(prog-top-to-racket (name ins (instantiate-linklet x_L x_LI ...))) (IT-to-racket ins)]
  ; evaluate
  [(prog-top-to-racket (name ins (instantiate-linklet x_L x_LI ... #:target I-test)))
   (IT-to-racket ins)]
  ; let-inst
  [(prog-top-to-racket (let-inst x (instantiate-linklet x_L x_LI ...) p-top))
   (let-values ([(x) (IT-to-racket (instantiate-linklet x_L x_LI ...))])
     (prog-top-to-racket p-top))]
  ; values
  [(prog-top-to-racket true) #t]
  [(prog-top-to-racket false) #f]
  [(prog-top-to-racket x) x]
  [(prog-top-to-racket v) v]
  ; below are for the linklet body
  [(prog-top-to-racket (o e_1 e_2))
   (o (prog-top-to-racket e_1) (prog-top-to-racket e_2))]
  [(prog-top-to-racket (define-values (x) e))
   (define-values (x) (prog-top-to-racket e))]
  [(prog-top-to-racket (lambda (x ...) e))
   (lambda (x ...) (prog-top-to-racket e))]
  [(prog-top-to-racket (begin e ...))
   (begin (prog-top-to-racket e) ...)]
  [(prog-top-to-racket (if e_1 e_2 e_3))
   (if (prog-top-to-racket e_1)
       (prog-top-to-racket e_2) (prog-top-to-racket e_3))]
  [(prog-top-to-racket (let-values (((x) e) ...) e_b))
   (let-values (((x) (prog-top-to-racket e)) ...) (prog-top-to-racket e_b))]
  [(prog-top-to-racket (set! x e))
   (set! x (prog-top-to-racket e))]
  [(prog-top-to-racket (e_1 e ...))
   ((prog-top-to-racket e_1) (prog-top-to-racket e) ...)]
  #;[(prog-top-to-racket any) any]
  )

(define-metafunction LinkletProgramTest
  [(to-actual-racket
    (program
     (use-linklets (x (linklet ((imp-id_r ...) ...) (exp-id ...) l-top ...)) ...)
     p-top-test ...))
   (let ((x (compile-linklet
             (quote
              (linklet ((imp-id_r ...) ...) (exp-id ...)
                       (prog-top-to-racket l-top) ...)))) ...)
     (prog-top-to-racket p-top-test) ...)])

(define-metafunction LinkletProgramTest
  eval-prog=racket-linklets : p-test -> boolean
  [(eval-prog=racket-linklets p-test)
   ,(letrec ([rr (racket-evaluator (term (to-actual-racket p-test)))]
             [vr (term (eval-prog p-test))])
      (begin 1 #;(printf "Trying e : ~a\n" (term p-test))
             (cond
               [(and (exn? rr) (eq? (term stuck) vr))
                (begin 1 #;(printf "both stuck on : ~a" (term p-test)) #true)]
               [(exn? rr)
                (begin (printf "\n racket raised exn : ~a -- ~a\n\n" (term p-test) (exn-message rr)) #false)]
               [(and (void? rr) (eq? (term void) vr)) #true]
               [(eq? (term stuck) vr) (begin (printf "\n racket not stuck : ~a\n\n" (term p-test)) #false)]
               [else (let ((q (equal? vr rr)))
                       (begin (unless q
                                (printf "\nTerm : ~a ==> racket : ~a -- eval-rc : ~a\n" (term p-test) rr vr))
                              q))])))])


(define-simple-macro (eval-prog=racket-linklets? e)
  (test-equal (term (eval-prog=racket-linklets e)) #true))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Also serves as a testing for the utilities themselves
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-equal (term (substitute-linklet l1 (Lα () ()) (3))) (term (3)))
(test-equal (term (substitute-linklet l1 (Lα () ()) (3 4))) (term (3 4)))

(test-equal
 (term
  (substitute-one l (Lα () ((Export y y1 y))
                        (define-values (y) 10)
                        (var-set! y1 y)
                        (var-set/check-undef! y1 50))
                  (instantiate-linklet l #:target t)))
 (term
  (instantiate-linklet (Lα () ((Export y y1 y))
                           (define-values (y) 10)
                           (var-set! y1 y)
                           (var-set/check-undef! y1 50)) #:target t)))

(test-equal
 (term
  (substitute-one l (Lα () ())
                  (let-inst t (linklet-instance)
                            (instantiate-linklet l #:target t))))
 (term
  (let-inst t (linklet-instance)
            (instantiate-linklet (Lα () ()) #:target t))))

(test-equal
 (term
  (substitute-one l (Lα () ((Export y y1 y))
                        (define-values (y) 10)
                        (var-set! y1 y)
                        (var-set/check-undef! y1 50))
                  (let-inst t (linklet-instance)
                            (instantiate-linklet l #:target t)
                            (instance-variable-value t y))))
 (term
  (let-inst t (linklet-instance)
            (instantiate-linklet (Lα () ((Export y y1 y))
                                     (define-values (y) 10)
                                     (var-set! y1 y)
                                     (var-set/check-undef! y1 50)) #:target t)
            (instance-variable-value t y))))

#;(test-equal
 (term
  (substitute-instance t1 (linklet-instance)
                       (instantiate-linklet (Lα () ()) #:target t1)))
 (term
  (instantiate-linklet (Lα () ()) #:target (linklet-instance))))
