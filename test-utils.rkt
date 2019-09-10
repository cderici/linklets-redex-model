#lang racket

(require redex
         "racket-core.rkt"
         "linklets.rkt"
         syntax/parse/define)

(provide (all-defined-out))

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


(define-simple-macro (eval-rc=racket-core? e)
  (test-equal (term (eval-rc=racket-core e)) #true))
