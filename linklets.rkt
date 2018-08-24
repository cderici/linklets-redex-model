#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  
  [LI ::= (linklet-instance (exp-id ...) (x C) ...)] ;; (var-sym cell)

  [p ::= (program (use-linklets (x_!_ L) ...) p-top ... final-expr) (raises e)]
  [l-top ::= d e]
  [p-top ::= I T (let-inst x I) IV (raises e)]
  [d ::= (define-values (x) e)]
  [final-expr ::= n b (void) stuck IV T (raises e)]
  
  ; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  [exp-id ::= x (x x)]
  
  [I ::= LI stuck (instantiate linkl-ref inst-ref ...)] ; rc-out 
  [T ::= v stuck (instantiate linkl-ref inst-ref ... #:target inst-ref)]
  
  [IV ::= (instance-variable-value li-ref x)]
    
  [li-ref ::= linkl-ref inst-ref] ; we really should split Ω
  [linkl-ref ::= x L (raises e)]
  [inst-ref ::= x LI (raises e)]

  [V ::= v LI]

  [v/i ::= value instance]

  ; need to somehow express the linklet instances
  
  [var ::= (L-Var x V constance)]
  [constance ::= #f constant consistent]

  [Ω   ::= ((x any) ...)] ;; linklet environment

  [EP ::= hole
          (program (use-linklets) V ... (let-inst x EL) p-top ... final-expr)
          (program (use-linklets) V ... EL p-top ... final-expr)
          (program (use-linklets) V ... EL)]

  [EL ::= hole
          (instantiate EL inst-ref ...) ;; resolve the linklet
          (instantiate L LI ... EL inst-ref ...) ;; resolve the imported instances

          (instantiate EL inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate L LI ... EL inst-ref ... #:target inst-ref) ;; resolve the imported instances

          (instance-variable-value EL x)]

  [linkl-ref-test ::= x L]
  [p-test ::= (program (use-linklets (x_!_ L) ...) p-top-test ... final-expr-test)]
  [p-top-test ::= T-test n b (void) stuck (let-inst x I-test)] ; (instance-variable-value x x)
  [I-test ::= (instantiate linkl-ref-test x ...) ]
  [T-test ::= (instantiate linkl-ref-test x ... #:target x)]
  [final-expr-test ::= n b (void) stuck (instance-variable-value x x) T-test]
  )

#;(render-language
   Linklets
   "Linklets.ps"
   #:nts
   '(L LI p l-top p-top d final-expr imp-id exp-id I T IV linkl-ref inst-ref Ω EP EL))

(define-metafunction Linklets
  [(get-var-val (linklet-instance (exp-id ...) (x_0 cell_0) ... (x cell) (x_1 cell_1) ...) x σ)
   (lookup σ cell)]
  [(get-var-val LI x σ)
   (raises x)])

(define -->βp
  (reduction-relation
   Linklets
   #:domain (p Ω Σ σ)
   (--> [(in-hole EP (raises e)) Ω Σ σ]
        [(raises e) Ω Σ σ] "error")
   (--> [(in-hole EL (raises e)) Ω Σ σ]
        [(raises e) Ω Σ σ] "error in EL")
   (--> [(in-hole EP x) Ω Σ σ]
        [(in-hole EP (lookup Ω x)) Ω Σ σ] "linklet-lookup")
   (--> [(in-hole EP (instance-variable-value LI x)) Ω Σ σ]
        [(in-hole EP (get-var-val LI x σ)) Ω Σ σ] "instance variable value")
   (--> [(in-hole EP (instance-variable-value L x)) Ω Σ σ]
        [(raises instance-expected) Ω Σ σ] "instance variable value error")
   (--> [(in-hole EP (let-inst x LI)) Ω Σ σ]
        [(in-hole EP (void)) (extend Ω (x) (LI)) Σ σ] "let-inst")
   (--> [(in-hole EP (instantiate L LI ...)) Ω Σ σ]
        [(in-hole EP LI_1) Ω_1 Σ σ_1]
        (where (LI_1 Ω_1 Σ_1 σ_1) (instantiate-entry Ω Σ σ L LI ...)) "instantiate linklet")
   (--> [(in-hole EP (instantiate L LI ... #:target x_80)) Ω Σ σ]
        [(in-hole EP e_1) Ω_1 Σ_1 σ_1]
        (where (e_1 Ω_1 Σ_1 σ_1) (instantiate-entry Ω Σ σ L LI ... #:target x_80)) "eval linklet")
   (--> [(in-hole EP (instantiate L LI ...)) Ω Σ σ]
        [(raises e) Ω Σ σ]
        (where (raises e) (instantiate-entry Ω Σ σ L LI ...)) "error in instantiation")
   (--> [(in-hole EP (instantiate L LI ... #:target x_80)) Ω Σ σ]
        [(raises e) Ω Σ σ]
        (where (raises e) (instantiate-entry Ω Σ σ L LI ... #:target x_80)) "error in evaluation")

   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  collect-imports : (imp-id ...) LI #:env Σ #:store σ -> (Σ σ) or (raises e)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(collect-imports () (linklet-instance (exp-id ...) (x cell) ...) #:env Σ #:store σ) (Σ σ)]
  [(collect-imports (x imp-id ...)
                    (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x cell) (x_aft cell_aft) ...)
                    #:env Σ #:store σ)
   (collect-imports (imp-id ...)
                    (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x cell) (x_aft cell_aft) ...)
                    #:env (extend Σ (x) (x_fresh)) #:store (extend σ (x_fresh) (v)))
   (where x_fresh ,(variable-not-in
                    (term (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x cell) (x_aft cell_aft) ...))
                    (term x)))
   (where v ,(term (lookup σ cell)))]
  ; get the values of imports, don't worry about the cells
  [(collect-imports ((x_ext x_int) imp-id ...) ;; (external-id internal-id)
                    (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x_ext cell) (x_aft cell_aft) ...)
                    #:env Σ #:store σ)
   (collect-imports (imp-id ...)
                    (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x_ext cell) (x_aft cell_aft) ...)
                    ; match the external id, put into store the internal id
                    #:env (extend Σ (x_int) (cell_fresh)) #:store (extend σ (cell_fresh) (v)))
   (where cell_fresh ,(variable-not-in
                       (term (linklet-instance (exp-id ...) (x_bef cell_bef) ... (x_ext cell) (x_aft cell_aft) ...))
                       (term x_int)))
   (where v ,(term (lookup σ cell)))]
  ; error : given instance doesn't have that id
  [(collect-imports (imp-id_current imp-id ...) ;; (external-id internal-id)
                    (linklet-instance (exp-id ...) (x cell) ...)
                    #:env Σ #:store σ)
   (raises imp-id_current)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  collect-importss : ((imp-id ...) ...) (LI ...) #:env Σ #:store σ -> (Σ σ) or (raises e)
;; put the imported vars' values into the l-toplevel environment (i.e. store - σ)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(collect-importss () () #:env Σ #:store σ) (Σ σ)]
  [(collect-importss ((imp-id_1 ...) (imp-id_2 ...) ...) (LI_1 LI_2 ...) #:env Σ #:store σ)
   (collect-importss ((imp-id_2 ...) ...) (LI_2 ...) #:env Σ_new #:store σ_new)
   (where (Σ_new σ_new) ,(term (collect-imports (imp-id_1 ...) LI_1 #:env Σ #:store σ)))]
  [(collect-importss ((imp-id_1 ...) (imp-id_2 ...) ...) (LI_1 LI_2 ...) #:env Σ #:store σ)
   (raises e)
   (where (raises e) ,(term (collect-imports (imp-id_1 ...) LI_1 #:env Σ #:store σ)))]
  ; error : not enough imported instances
  [(collect-importss ((imp-id_1 ...) (imp-id_2 ...) ...) () #:env Σ #:store σ)
   (raises not-enough-imported-instances)]
  ; error : too many imported instances
  [(collect-importss () (LI ...) #:env Σ #:store σ)
   (raises too-many-imported-instances)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  collect-linklet-defined-names : (l-top ...) (x ...) -> (x ...)
;; Collect the ids defined in the given linklet's forms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(collect-linklet-defined-names () (x ...)) (x ...)] ; return
  ; we already have it
  [(collect-linklet-defined-names ((define-values (x) e) l-top_1 ...) (x_bef ... x x_aft ...))
   (collect-linklet-defined-names (l-top_1 ...) (x_bef ... x x_aft ...))]
  ; put it in
  [(collect-linklet-defined-names ((define-values (x) e) l-top_1 ...) (x_0 ...))
   (collect-linklet-defined-names (l-top_1 ...) (x x_0 ...))]
  ; no define, pass
  [(collect-linklet-defined-names (l-top l-top_1 ...) (x_0 ...))
   (collect-linklet-defined-names (l-top_1 ...) (x_0 ...))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  uninitialize-exports : Ω x (exp-id ...) (x ...) -> Ω ; (with the updated instance)
;; adds variables to target for each exported id that's not defined by the linklet
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; return the new linklet env (with the new instance)
  [(uninitialize-exports Ω x_T () (x_1 ...)) Ω]
  ;; regular export sym (without rename)
  [(uninitialize-exports
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_0 C) ...)) (x_aft any_aft) ...) ; <- Ω
    x_T (x_exp exp-id_1 ...) (x ...))

   (uninitialize-exports
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_exp uninit) (x_0 C) ...)) (x_aft any_aft) ...) ; <- Ω
    x_T (exp-id_1 ...) (x ...))
   (side-condition (not (member (term x_exp) (term (x ...))))) ; not defined
   (side-condition (not (member (term x_exp) (term (x_0 ...)))))]; target doesn't have it
  ;; regular export sym (WITH rename)
  [(uninitialize-exports
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_0 C) ...)) (x_aft any_aft) ...) ; <- Ω
    x_T ((x_int x_ext) exp-id_1 ...) (x ...)) ;; (internal-exported-id external-exported-id)

   (uninitialize-exports
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_ext uninit) (x_0 C) ...)) (x_aft any_aft) ...)
    x_T (exp-id_1 ...) (x ...))
   (side-condition (not (member (term x_2) (term (x ...)))))
   (side-condition (not (member (term x_2) (term (x_0 ...)))))]
  ; else case
  [(uninitialize-exports Ω x_T (exp-id_0 exp-id_1 ...) (x ...))
   (uninitialize-exports Ω x_T (exp-id_1 ...) (x ...))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  copy-exports-to-target : Ω x (exp-id ...) -> Ω
;; (overwrites)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(copy-exports-to-target
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id_0 ...) (x C) ...)) (x_aft any_aft) ...) x_T (exp-id ...))
   ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x C) ...)) (x_aft any_aft) ...)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  put-target-to-env : Σ x_T Ω -> Σ or (raises e)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(put-target-to-env 
    Σ x_T
    ((x_bef any_bef) ... (x_T LI) (x_aft any_aft) ...))
   (extend Σ (current-linklet-instance) (LI))]
  [(put-target-to-env Σ x_T Ω)
   (raises x_T)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  ;instantiate-entry : Ω Σ σ L LI ... (#:target x) -> (v/LI Ω Σ σ)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(instantiate-entry Ω Σ σ (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) LI ...)
   (instantiate-loop (l-top ...) Ω_1 Σ_1 σ_1 #:target x_T #:last-val (void) #:result instance)
   (where (Σ_1 σ_1) ,(term (collect-importss ((imp-id ...) ...) (LI ...) #:env Σ #:store σ)))
   (where x_T ,(variable-not-in (term Ω) 'new-inst))
   (where Ω_1 ,(term (uninitialize-exports ; put the exports of the linklet into-vvvv-the new instance
                                           (extend Ω (x_T) ((linklet-instance (exp-id ...))))
                                           x_T
                                           (exp-id ...)
                                           (collect-linklet-defined-names (l-top ...) ()))))]
  ; eval (targeted instantiation)
  [(instantiate-entry Ω Σ σ (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) LI ... #:target x_T)
   (instantiate-loop (l-top ...) Ω_1 Σ_2 σ_1 #:target x_T #:last-val (void) #:result value)
   (where (Σ_1 σ_1) ,(term (collect-importss ((imp-id ...) ...) (LI ...) #:env Σ #:store σ)))
   (where Σ_2 ,(term (put-target-to-env Σ_1 x_T Ω)))
   (where Ω_1 ,(term (uninitialize-exports ; overwrite target's exports
                                           (copy-exports-to-target Ω x_T (exp-id ...))
                                           x_T
                                           (exp-id ...)
                                           (collect-linklet-defined-names (l-top ...) ()))))]
  ;; import errors (regular instantitation)
  [(instantiate-entry Ω Σ σ (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) LI ...)
   (raises e)
   (where (raises e) ,(term (collect-importss ((imp-id ...) ...) (LI ...) #:env Σ #:store σ)))]
  ;; import errors (targeted)
  ;; no target found error
  [(instantiate-entry Ω Σ σ (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) LI ... #:target x_T)
   (raises e)
   (where (raises e) ,(term (collect-importss ((imp-id ...) ...) (LI ...) #:env Σ #:store σ)))]
  ;; no target found error
  [(instantiate-entry Ω Σ σ (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) LI ... #:target x_T)
   (raises e)
   (where (Σ_1 σ_1) ,(term (collect-importss ((imp-id ...) ...) (LI ...) #:env Σ #:store σ)))
   (where (raises e) ,(term (put-target-to-env Σ_1 x_T Ω)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  target-add-or-overwrite : Σ σ x cell v x Ω  -> (Ω σ)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; target has the var, so overwrite the cell value
  [(target-add-or-overwrite
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_B C_B) ... (x cell) (x_A C_A) ...)) (x_aft any_aft) ...))

   (((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_B C_B) ... (x cell) (x_A C_A) ...)) (x_aft any_aft) ...)
    (extend σ (cell) (v_1)))]

  ; target has the var, but it's uninit
  [(target-add-or-overwrite
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_B C_B) ... (x uninit) (x_A C_A) ...)) (x_aft any_aft) ...))

   (((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_B C_B) ... (x cell_1) (x_A C_A) ...)) (x_aft any_aft) ...)
    σ)]

  ; target doesn't have the var
  ; so add a new one
  [(target-add-or-overwrite
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_old C_old) ...)) (x_aft any_aft) ...))

   (((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x cell_1) (x_old C_old) ...)) (x_aft any_aft) ...)
    σ)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction Linklets
  modify-target : Σ σ x cell v x Ω -> (Ω σ)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; recall : (exp-id ...) in target is really the linklet's exports
  ; name in exports (without rename)
  [(modify-target
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id_bef ... x exp-id_aft ...) (x_old C_old) ...)) (x_aft any_aft) ...))
   (target-add-or-overwrite
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id_bef ... x exp-id_aft ...) (x_old C_old) ...)) (x_aft any_aft) ...))]

  ; name in exports (with a rename)
  [(modify-target
    Σ σ x_int cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id_bef ... (x_int x_ext) exp-id_aft ...) (x_old C_old) ...)) (x_aft any_aft) ...))
   (target-add-or-overwrite
    Σ σ x_ext cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id_bef ... (x_int x_ext) exp-id_aft ...) (x_old C_old) ...)) (x_aft any_aft) ...))]

  ; target does NOT have it (name is not in exports, so don't worry about renames)
  [(modify-target
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_old C_old) ...)) (x_aft any_aft) ...))
   (target-add-or-overwrite
    Σ σ x cell_1 v_1 x_T
    ((x_bef any_bef) ... (x_T (linklet-instance (exp-id ...) (x_old C_old) ...)) (x_aft any_aft) ...))
   (side-condition (not (member (term x) (term (x_old ...)))))]

  ; we're not exporting the name, and
  ; target already has it, so avoid modifying the target
  [(modify-target Σ σ x cell v x_T Ω) (Ω σ)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instantiate-loop
(define-metafunction Linklets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(instantiate-loop () Ω Σ σ
                     #:target x_T #:last-val v #:result instance) ((lookup Ω x_T) Ω Σ σ)]
  [(instantiate-loop () Ω Σ σ
                     #:target x_T #:last-val v #:result value) (v Ω Σ σ)]

  [(instantiate-loop ((define-values (x_0) e) l-top ...) Ω Σ
                     σ #:target x_T #:last-val v #:result v/i)
   ; loop define
   (instantiate-loop (l-top ...) Ω_1
                     (extend Σ_1 (x_0) (cell_1))
                     (extend σ_2 (cell_1) (v_1))
                     #:target x_T
                     #:last-val (void)
                     #:result v/i)
   (where (v_1 Σ_1 σ_1) ,(term (rc-api (e Σ σ))))
   (where cell_1 ,(variable-not-in (term (x_0 l-top ...)) (term ,(gensym))))
   (where (Ω_1 σ_2) ,(term (modify-target Σ σ_1 x_0 cell_1 v_1 x_T Ω)))]

  ; loop expression
  [(instantiate-loop (e l-top ...) Ω Σ σ
                     #:target x_T #:last-val v #:result v/i)
   (instantiate-loop (l-top ...) Ω Σ_1 σ_1
                     #:target x_T
                     #:last-val v_1
                     #:result v/i)
   (where (v_1 Σ_1 σ_1) ,(term (rc-api (e Σ σ))))]

  ; error from rc-api
  [(instantiate-loop (e l-top ...) Ω Σ σ
                     #:target x_T #:last-val v #:result v/i)
   (raises e_1)
   (where ((raises e_1) Σ_1 σ_1) ,(term (rc-api (e Σ σ))))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PRECHECKS & RUNNING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction Linklets
  [(check-top x_1 (x ...))
   ,(if (member (term x_1) (term (x ...))) #t #f)]
  [(check-top (if e_1 e_2 e_3) (x ...))
   ,(and (term (check-top e_1 (x ...)))
         (term (check-top e_2 (x ...)))
         (term (check-top e_3 (x ...))))]
  [(check-top (begin e ...) (x ...))
   ,(andmap (λ (x) x) (term ((check-top e (x ...)) ...)))]
  [(check-top (lambda (x_f ...) e) (x ...))
   (check-top e (x_f ... x ...))]
  [(check-top (p2 e_1 e_2) (x ...))
   ,(and (term (check-top e_1 (x ...)))
         (term (check-top e_2 (x ...))))]
  [(check-top (p1 e_1) (x ...))
   (check-top e_1 (x ...))]
  [(check-top (set! x_s e) (x ...))
   ,(and (term (check-top x_s (x ...)))
         (term (check-top e (x ...))))]
  [(check-top (let-values (((x_l) e) ...) e_b) (x ...))
   (check-top e_b (x_l ... x ...))]
  [(check-top (raises e)) #t]
  [(check-top (e_1 e ...) (x ...))
   ,(andmap (λ (x) x) (term ((check-top e_1 (x ...))
                             (check-top e (x ...)) ...)))]
  [(check-top any (x ...)) #t])

(define-metafunction Linklets
  [(check-free-vars (linklet () ()) (x ...)) #t]
  ; put the imports
  [(check-free-vars (linklet (() (imp-id_r ...) ...) (exp-id ...) l-top ...) (x ...))
   (check-free-vars (linklet ((imp-id_r ...) ...) (exp-id ...) l-top ...) (x ...))]
  [(check-free-vars (linklet ((x_i imp-id ...) (imp-id_r ...) ...) (exp-id ...) l-top ...) (x ...))
   (check-free-vars (linklet ((imp-id ...) (imp-id_r ...) ...) (exp-id ...) l-top ...) (x_i x ...))]
  [(check-free-vars (linklet (((x_ext x_int) imp-id_cur ...) (imp-id_r ...) ...) (exp-id ...) l-top ...) (x ...))
   (check-free-vars (linklet ((imp-id_cur ...) (imp-id_r ...) ...) (exp-id ...) l-top ...) (x_int x ...))]
  [(check-free-vars (linklet () (x_e exp-id ...) l-top ...) (x ...))
   (check-free-vars (linklet () (exp-id ...) l-top ...) (x_e x ...))]
  ; put the exports
  [(check-free-vars (linklet () ((x_int x_ext) exp-id ...) l-top ...) (x ...))
   (check-free-vars (linklet () (exp-id ...) l-top ...) (x_int x ...))]
  ; add the defined vars
  [(check-free-vars (linklet () () (define-values (x_d) e) l-top ...) (x ...))
   ,(and (term (check-top e (x_d x ...)))
         (term (check-free-vars (linklet () () l-top ...) (x_d x ...))))]
  ; check it
  [(check-free-vars (linklet () () l-top_1 l-top ...) (x ...))
   ,(and (term (check-top l-top_1 (x ...)))
         (term (check-free-vars (linklet () () l-top ...) (x ...))))])
   
(define-metafunction Linklets
  [(check-free-varss) #t]
  [(check-free-varss L_1 L ...)
   ,(and (term (check-free-vars L_1 ()))
         (term (check-free-varss L ...)))])

(define-metafunction Linklets
  [(flatten-exports () (x ...)) (x ...)]
  [(flatten-exports (x_e exp-id ...) (x ...))
   (flatten-exports (exp-id ...) (x_e x ...))]
  [(flatten-exports ((x_int x_ext) exp-id ...) (x ...))
   (flatten-exports (exp-id ...) (x_int x ...))])

(define-metafunction Linklets
  [(flatten-imports () (x ...)) (x ...)]
  [(flatten-imports (x_i imp-id ...) (x ...))
   (flatten-imports (imp-id ...) (x_i x ...))]
  [(flatten-imports ((x_ext x_int) imp-id ...) (x ...))
   (flatten-imports (imp-id ...) (x_int x ...))])

(define-metafunction Linklets
  [(flatten-importss () (x ...)) (x ...)]
  [(flatten-importss ((imp-id ...) (imp-id_r ...) ...) (x ...))
   (flatten-importss ((imp-id_r ...) ...)
                     (flatten-imports (imp-id ...) (x ...)))])

(define-metafunction Linklets
  [(no-duplicates () (x_exp ...)) #t]
  [(no-duplicates (x x_r ...) (x_b ... x x_i ... x x_a ...)) #f]
  [(no-duplicates (x x_r ...) (x_exp ...))
   (no-duplicates (x_r ...) (x_exp ...))])

(define-metafunction Linklets
  [(no-exp/imp-duplicates) #t]
  [(no-exp/imp-duplicates (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) L ...)
   ,(and (term (no-duplicates (x_i ... x_e ...) (x_i ... x_e ...)))
         (term (no-exp/imp-duplicates L ...)))
   (where (x_e ...) (flatten-exports (exp-id ...) ()))
   (where (x_i ...) (flatten-importss ((imp-id ...) ...) ()))])


(define-metafunction Linklets
  [(internals-of-renamed-exports () (x ...)) (x ...)]
  [(internals-of-renamed-exports (x_e exp-id ...) (x ...))
   (internals-of-renamed-exports (exp-id ...) (x_e x ...))]
  [(internals-of-renamed-exports ((x_int x_ext) exp-id ...) (x ...))
   (internals-of-renamed-exports (exp-id ...) (x_int x ...))])
  
(define-metafunction Linklets
  [(no-export-rename-duplicate ()) #t]
  [(no-export-rename-duplicate (x exp-id ...))
   (no-export-rename-duplicate (exp-id ...))]
  [(no-export-rename-duplicate ((x_int x_ext) exp-id ...))
   (no-export-rename-duplicate (exp-id ...))
   (side-condition (not (member (term x_ext)
                                (term (internals-of-renamed-exports
                                       (exp-id ...) ; of the rest of the exports
                                       ())))))]
  [(no-export-rename-duplicate ((x_int x_ext) exp-id ...)) #f])

;;> (let ((i (compile-linklet '(linklet () ((a b) (b e) (d f))
;;                                      (void))))) 2)
;; linklet: duplicate export
;;> (let ((i (compile-linklet '(linklet () ( (b e) (a b) (d f))
;;                                      (void))))) 2)
;;2

(define-metafunction Linklets
  [(no-export-rename-duplicates) #t]
  [(no-export-rename-duplicates (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) L ...)
   ,(and (term (no-export-rename-duplicate (exp-id ...)))
         (term (no-export-rename-duplicates L ...)))])

(define-metafunction Linklets
  [(no-top-define-is-imported () (x ...)) #t]
  [(no-top-define-is-imported ((define-values (x_d) e) l-top ...) (x ...))
   (no-top-define-is-imported (l-top ...) (x ...))
   (side-condition (not (member (term x_d) (term (x ...)))))]
  [(no-top-define-is-imported ((define-values (x_d) e) l-top ...) (x ...)) #f]
  [(no-top-define-is-imported (l-top_1 l-top ...) (x ...))
   (no-top-define-is-imported (l-top ...) (x ...))])

(define-metafunction Linklets
  [(no-non-definable-variables) #t]
  [(no-non-definable-variables (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) L ...)
   ,(and (term (no-top-define-is-imported (l-top ...) (flatten-importss ((imp-id ...) ...) ())))
         (term (no-non-definable-variables L ...)))])

(define-metafunction Linklets
  [(get-defined-instance-ids () (x ...)) (x ...)]
  [(get-defined-instance-ids ((let-inst x_i any) p-top ...) (x ...))
   (get-defined-instance-ids (p-top ...) (x_i x ...))]
  [(get-defined-instance-ids (p-top_1 p-top ...) (x ...))
   (get-defined-instance-ids (p-top ...) (x ...))])

(define-metafunction Linklets
  [(linklet-refs-check-out () (x_l ...) (x_i ...)) #t]
  ; regular instantiate
  [(linklet-refs-check-out ((instantiate x_L x_I ...) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (and (not (member (term x_L) (term (x_i ...))))
                        (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...)))))]
  [(linklet-refs-check-out ((instantiate x_L x_I ...) p-top ...) (x_l ...) (x_i ...)) #f]
  ; regular instantiate (with explicit linklet)
  [(linklet-refs-check-out ((instantiate L x_I ...) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...))))]
  [(linklet-refs-check-out ((instantiate L x_I ...) p-top ...) (x_l ...) (x_i ...)) #f]
  ; instantiate with target
  [(linklet-refs-check-out ((instantiate x_L x_I ... #:target x_t) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (and (not (member (term x_L) (term (x_i ...))))
                        (not (member (term x_t) (term (x_l ...))))
                        (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...)))))]
  [(linklet-refs-check-out ((instantiate x_L x_I ... #:target x_t) p-top ...) (x_l ...) (x_i ...)) #f]
  ; instantiate with target (with explicit linklet)
  [(linklet-refs-check-out ((instantiate L x_I ... #:target x_t) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (and (not (member (term x_t) (term (x_l ...))))
                        (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...)))))]
  [(linklet-refs-check-out ((instantiate L x_I ... #:target x_t) p-top ...) (x_l ...) (x_i ...)) #f]
  ; let-inst
  [(linklet-refs-check-out ((let-inst x_def (instantiate x_L x_I ...)) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (and (not (member (term x_L) (term (x_i ...))))
                        (not (member (term x_def) (term (x_l ...))))
                        (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...)))))]
  [(linklet-refs-check-out ((let-inst x_def (instantiate x_L x_I ...)) p-top ...) (x_l ...) (x_i ...)) #f]
  ; let-inst (with explicit linklet)
  [(linklet-refs-check-out ((let-inst x_def (instantiate L x_I ...)) p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))
   (side-condition (and (not (member (term x_def) (term (x_l ...))))
                        (andmap (λ (i) (not (member i (term (x_l ...))))) (term (x_I ...)))))]
  [(linklet-refs-check-out ((let-inst x_def (instantiate x_L x_I ...)) p-top ...) (x_l ...) (x_i ...)) #f]
  ; others
  [(linklet-refs-check-out (p-top_1 p-top ...) (x_l ...) (x_i ...))
   (linklet-refs-check-out (p-top ...) (x_l ...) (x_i ...))])

(define-metafunction Linklets
  [(no-duplicate-binding-names () (x ...)) #t]
  [(no-duplicate-binding-names ((define-values (x_def) e) l-top ...) (x ...))
   (no-duplicate-binding-names (l-top ...) (x_def x ...))
   (side-condition (not (member (term x_def) (term (x ...)))))]
  [(no-duplicate-binding-names ((define-values (x_def) e) l-top ...) (x ...)) #f]
  [(no-duplicate-binding-names (l-top_any l-top ...) (x ...))
   (no-duplicate-binding-names (l-top ...) (x ...))])

(define-metafunction Linklets
  [(no-duplicate-binding-namess) #t]
  [(no-duplicate-binding-namess (linklet ((imp-id ...) ...) (exp-id ...) l-top ...) L ...)
   ,(and (term (no-duplicate-binding-names (l-top ...) ()))
         (term (no-duplicate-binding-namess L ...)))])

(define-metafunction Linklets
  ;eval-prog :Linklets-> v or closure or stuck or void
  [(eval-prog (program (use-linklets (x_L L) ...) p-top ...))
   (run-prog ((program (use-linklets (x_L L) ...) p-top ...) () () ()))
   (side-condition (and (term (check-free-varss L ...))
                        (term (no-exp/imp-duplicates L ...))
                        (term (no-export-rename-duplicates L ...))
                        (term (no-non-definable-variables L ...))
                        (term (no-duplicate-binding-namess L ...))
                        (term (linklet-refs-check-out
                               (p-top ...)
                               (x_L ...)
                               (get-defined-instance-ids (p-top ...) ())))))]
  [(eval-prog p) stuck])

(define-metafunction Linklets
  ;; return
  [(run-prog ((program (use-linklets) V ... n) Ω Σ σ)) n] ;; number
  [(run-prog ((program (use-linklets) V ... b) Ω Σ σ)) b] ;; boolean
  [(run-prog ((program (use-linklets) V ... (void)) Ω Σ σ)) (void)] ;; void
  [(run-prog ((raises e) Ω Σ σ)) stuck] ;; stuck
  
  ;; load the linklets
  [(run-prog ((program (use-linklets (x_1 L_1) (x L) ...) p-top ...) Ω Σ σ))
   (run-prog ((program (use-linklets) p-top ...) (extend Ω (x_1 x ...) (L_1 L ...)) Σ σ))]

  ;; problem in intermediate steps
  [(run-prog ((program (use-linklets (x L) ...) p-top_1 ... stuck p-top_2 ...) Ω Σ σ)) stuck]

  ;; reduce
  [(run-prog any_1)
   (run-prog any_again)
   (where (any_again) ,(apply-reduction-relation -->βp (term any_1)))]
  [(run-prog any_1) stuckk])


#;(define-metafunction Linklets
  ;debugger : (p Ω Σ σ) -> rc-out
  [(debugger ((program (use-linklets) V ... n) Ω Σ σ)) (n Ω Σ σ)] ;; number
  [(debugger ((program (use-linklets) V ... (void)) Ω Σ σ)) ((void) Ω Σ σ)] ;; void
  [(debugger ((raises e) Ω Σ σ)) (stuck Ω Σ σ)] ;; stuck

  [(debugger ((program (use-linklets (x_1 L_1) (x L) ...) p-top ...) Ω Σ σ))
   (debugger ((program (use-linklets) p-top ...) (extend Ω (x_1 x ...) (L_1 L ...)) Σ σ))]

  [(debugger any_1)
   (debugger any_again)
   (where (any_again) ,(apply-reduction-relation -->βp (term any_1)))])

;
