#lang racket

(require redex
         "../linklets.rkt"
         "../racket-core.rkt")

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
