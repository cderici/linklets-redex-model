#lang racket

(require redex
         "racket-core.rkt")

(provide (all-defined-out))

(define-extended-language Linklets RC
  [L ::= (linklet ((imp-id ...) ...) (exp-id ...) l-top ...)]
  [LI ::= (linklet-instance (exp-id ...) (x l-var) ...)] ;; (var-sym cell)

  [L-obj ::= (compiled-linklet ((imp-obj ...) ...)
                               (exp-obj ...)
                               l-top ...)]

  [l-top ::= d e] ; linklet body expressions
  [l-var ::= (variable x v constance)] ; linklet variables
  [d ::= (define-values (x) e)]
  [e ::= .... (var-ref x) (var-ref/no-check x) (var-set! x x) (var-set/check-undef! x v)]

  ; (external-imported-id internal-imported-id)
  [imp-id ::= x (x x)]
  [imp-obj ::= (Import n x x x)] ; group-index id int_id ext_id
  ; (internal-exported-id external-exported-id)
  [exp-id ::= x (x x)]
  [exp-obj ::= (Export x x x)] ; int_id int_gensymed ext_id

  [constance ::= #f constant consistent]

  ;; compile-instantiate expressions
  [CL ::= (compile-linklet L)]
  [I ::= (make-instance (exp-id ...) (x v) ...)
         (instantiate-linklet linkl-ref inst-ref ...)] ; instantiate
  [T ::= (instantiate-linklet linkl-ref inst-ref ... #:target x)] ; evaluate

  [linkl-ref ::= x L (raises e)]
  [inst-ref ::= x LI (raises e)]

  ;; program-stuff
  [p-top :== I T (let-inst x I) (instance-variable-value x x)]
  [p ::= (program (use-linklets (x_!_ L) ...) p-top ... final-expr)]
  [final-expr ::= p-top v]

  [ω   ::= ((x L) ...)] ; linklet env
  [Ω   ::= ((x LI) ...)] ; linklet instance env

  [EP ::= hole
          (program (use-linklets) V ... (let-inst x EL) p-top ... final-expr)
          (program (use-linklets) V ... EL p-top ... final-expr)
          (program (use-linklets) V ... EL)]

  [EL ::= hole
          (instantiate-linklet EL x ...) ;; resolve the linklet
          (instantiate-linklet L LI ... EL inst-ref ...) ;; resolve the imported instances

          (instantiate-linklet EL inst-ref ... #:target inst-ref) ;; resolve the linklet
          (instantiate-linklet L LI ... EL inst-ref ... #:target inst-ref) ;; resolve the imported instances

          (instance-variable-value EL x)])

; A separate pass
(define-metafunction Linklets
  all-toplevels : (l-top ...) (x ...) -> (x ...)
  [(all-toplevels () (x ...)) (x ...)]
  [(all-toplevels ((define-values (x) e) l-top ...) (x_tops ...))
   (all-toplevels (l-top ...) (x_tops ... x))]
  [(all-toplevels (l-top_1 l-top ...) (x ...))
   (all-toplevels (l-top ...) (x ...))])

; A separate (slightly deeper) pass
(define-metafunction Linklets
  get-mutated-vars-expr : l-top (x ...) -> (x ...)
  [(get-mutated-vars-expr (set! x v) (x_muts ...)) (x x_muts ...)]
  [(get-mutated-vars-expr (begin l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ...))]
  [(get-mutated-vars-expr l-top (x ...)) (x ...)])

(define-metafunction Linklets
  get-all-mutated-vars : (l-top ...) (x ...) -> (x ...)
  [(get-all-mutated-vars () (x ...)) (x ...)]
  [(get-all-mutated-vars (l-top_1 l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ... x_new_muts ... ))
   (where (x_new_muts ...) (get-mutated-vars-expr l-top_1 ()))])

; Process Imports
(define-metafunction Linklets
  process-import : n (imp-id ...) (imp-obj ...) -> (imp-obj ...)
  [(process-import n () (imp-obj ...)) (imp-obj ...)]
  [(process-import n (x imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x x) ))
   (where x_gen ,(variable-not-in (term (x imp-id ...)) (term x)))]
  [(process-import n ((x_ext x_int) imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x_int x_ext)))
   (where x_gen ,(variable-not-in (term ((x_ext x_int) imp-id ...)) (term x)))])

(define-metafunction Linklets
  process-importss : n ((imp-id ...) ...) ((imp-obj ...) ...) -> ((imp-obj ...) ...)
  [(process-importss n () ((imp-obj ...) ...)) ((imp-obj ...) ...)]
  [(process-importss n ((imp-id_1 ...) (imp-id ...) ...) ((imp-obj ...) ...))
   (process-importss ,(add1 (term n))
                     ((imp-id ...) ...)
                     ((imp-obj ...) ... (imp-obj_1 ...)))
   (where (imp-obj_1 ...) (process-import n (imp-id_1 ...) ()))])

; Process Exports
(define-metafunction Linklets
  process-exports : (exp-id ...) (exp-obj ...) -> (exp-obj ...)
  [(process-exports () (exp-obj ...)) (exp-obj ...)]
  [(process-exports (x exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x x_gen x)))
   (where x_gen ,(variable-not-in (term (x exp-id ...)) (term x)))]
  [(process-exports ((x_int x_ext) exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x_int x_gen x_ext)))
   (where x_gen ,(variable-not-in (term ((x_int x_ext) exp-id ...)) (term x)))])

;; compile-linklet-body == sexp_to_ast (in Pycket)
(define-metafunction Linklets
  ; compile-linklet-body : exprs lex-env importss exports mutated-ids toplevel-ids out
  compile-linklet-body : (l-top ...) (x ...) ((imp-obj ...) ...) (exp-obj ...) (x ...) (x ...) (l-top ...) -> (l-top ...)
  ; base case
  [(compile-linklet-body () (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) (l-top ...)) (l-top ...)]
  ; values
  [(compile-linklet-body (v l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... v))]
  ; raises
  [(compile-linklet-body ((raises e) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (raises e)))]
  ; symbols
  ; important parts are if the symbol is one of exports or imports
  ; if it's not, then it's either a toplevel defined (within linklet) or a primitive (op)(which is handled in a separate case below)

  ; 1) if it's one of imports
  [(compile-linklet-body (x_current l-top ...) (x_lex ...)
                         ((imp-obj_before ...) ...
                          ((Import n_bef x_gen_bef x_int_bef x_ext_bef) ...
                           (Import n_cur x_gen_cur x_current x_ext_cur)
                           (Import n_aft x_gen_aft x_int_aft x_ext_aft) ...)
                          (imp-obj_after ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj_before ...) ...
                          ((Import n_bef x_gen_bef x_int_bef x_ext_bef) ...
                           (Import n_cur x_gen_cur x_current x_ext_cur)
                           (Import n_aft x_gen_aft x_int_aft x_ext_aft) ...)
                          (imp-obj_after ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (var-ref/no-check x_gen_cur)))]
  ; 2) if it's one of exports
  ; create variable if
  [(compile-linklet-body (x_int_cur l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         ; one of exports
                         ((Export x_int_bef x_gen_bef x_ext_bef) ...
                          (Export x_int_cur x_gen_cur x_ext_cur)
                          (Export x_int_aft x_gen_aft x_ext_aft) ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         ((Export x_int_bef x_gen_bef x_ext_bef) ...
                          (Export x_int_cur x_gen_cur x_ext_cur)
                          (Export x_int_aft x_gen_aft x_ext_aft) ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (var-ref x_gen_cur)))
   ; it is mutated
   (side-condition (member (term x_int_cur) (term (x_mut ...))))]

  [(compile-linklet-body (x_int_cur l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         ; one of exports
                         ((Export x_int_bef x_gen_bef x_ext_bef) ...
                          (Export x_int_cur x_gen_cur x_ext_cur)
                          (Export x_int_aft x_gen_aft x_ext_aft) ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         ((Export x_int_bef x_gen_bef x_ext_bef) ...
                          (Export x_int_cur x_gen_cur x_ext_cur)
                          (Export x_int_aft x_gen_aft x_ext_aft) ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (var-ref x_gen_cur)))
   ; not defined in the toplevel (within the linklet)
   (side-condition (not (member (term x_int_cur) (term (x_top ...)))))]

  ; 3) symbol is neither import nor export, treat normal
  [(compile-linklet-body (x l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... x))]


  ; define-values is the juicy part
  ; if we see a define-values, we look at exported vars.
  ; if the defined id is exported, we add a new linklet variable for that.
  ; export's internal id should be the same with the defined id.
  ; we create the variable with the exports internal gensym.
  [(compile-linklet-body ((define-values (x) e) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj_before ... (Export x x_gen x_int) exp-obj_after ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj_before ... (Export x x_gen x_int) exp-obj_after ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ...
                                         (define-values (x) e_new)
                                         (var-set! x_gen x)))
   (where (e_new)
          (compile-linklet-body (e) (x x_lex ...)
                                ((imp-obj ...) ...)
                                (exp-obj_before ... (Export x x_gen x_int) exp-obj_after ...)
                                (x_mut ...) (x_top ...) ()))]
  ; if the defined id is not exported, then we recurse and continue as normal
  [(compile-linklet-body ((define-values (x) e) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (define-values (x) e_new)))
   (where (e_new) (compile-linklet-body (e) (x x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; begin
  [(compile-linklet-body ((begin e ...) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (begin e_new ...)))
   (where (e_new ...) (compile-linklet-body (e ...) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; op
  [(compile-linklet-body ((o e ...) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (o e_new ...)))
   (where (e_new ...) (compile-linklet-body (e ...) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]

  ; set!
  ; if it's an exported variable, don't emit a regular set!
  ; we're going to variable-set! the exported linklet variable
  [(compile-linklet-body ((set! x_int_cur e) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (name exps ((Export x_int_bef x_gen_bef x_ext_bef) ...
                                     (Export x_int_cur x_gen_cur x_ext_cur)
                                     (Export x_int_aft x_gen_aft x_ext_aft) ...))
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         exps
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (var-set/check-undef! x_gen_cur e_new)))
   (where (e_new) (compile-linklet-body (e) (x_lex ...) ((imp-obj ...) ...) exps (x_mut ...) (x_top ...) ()))]
  ; set! - as usual
  [(compile-linklet-body ((set! x e) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (set! x e_new)))
   (where (e_new) (compile-linklet-body (e) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; if
  [(compile-linklet-body ((if e_tst e_thn e_els) l-top ...)
                         (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ...
                                         (if e_tst_new e_thn_new e_els_new)))
   (where (e_tst_new) (compile-linklet-body (e_tst) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))
   (where (e_thn_new) (compile-linklet-body (e_thn) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))
   (where (e_els_new) (compile-linklet-body (e_els) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; lambda
  [(compile-linklet-body ((lambda (x ...) e_body) l-top ...)
                         (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (lambda (x ...) e_body)))
   (where (e_body_new) (compile-linklet-body (e_body) (x ... x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; let-values
  [(compile-linklet-body ((let-values (((x_rhs) e_rhs) ...) e_body) l-top ...)
                         (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ...
                                         (let-values (((x_rhs) e_rhs_new) ...) e_body_new)))
   (where (e_rhs_new ...) (compile-linklet-body (e_rhs ...) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))
   (where (e_body_new) (compile-linklet-body (e_body) (x_rhs ... x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]
  ; app
  [(compile-linklet-body ((e ...) l-top ...) (x_lex ...)
                         ((imp-obj ...) ...)
                         (exp-obj ...)
                         (x_mut ...) (x_top ...) (l-top_compiled ...))
   (compile-linklet-body (l-top ...) (x_lex ...)
                         ((imp-obj ...) ...) (exp-obj ...)
                         (x_mut ...) (x_top ...)
                         (l-top_compiled ... (e_new ...)))
   (where (e_new ...) (compile-linklet-body (e ...) (x_lex ...) ((imp-obj ...) ...) (exp-obj ...) (x_mut ...) (x_top ...) ()))]

  )


(define-metafunction Linklets
  compile-linklet : L -> L-obj or stuck
  [(compile-linklet (linklet ((imp-id ...) ...) (exp-id ...) l-top ...))
   (compiled-linklet ((imp-obj ...) ...) (exp-obj ...) l-top_compiled ...)
   (where ((imp-obj ...) ...) (process-importss 0 ((imp-id ...) ...) ()))
   (where (exp-obj ...) (process-exports (exp-id ...) ()))
   (where (x_mut ...) (get-all-mutated-vars (l-top ...) ()))
   (where (x_top ...) (all-toplevels (l-top ...) ()))
   (where (l-top_compiled ...)
	  (compile-linklet-body (l-top ...) ()
                                ((imp-obj ...) ...) (exp-obj ...)
                                (x_mut ...) (x_top ...) ()))
   ])
