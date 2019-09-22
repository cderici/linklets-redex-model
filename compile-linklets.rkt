#lang racket

(require redex
         "linklets.rkt")

(provide (all-defined-out))

(define-extended-language LinkletsCompile Linklets
  [exprs ::= (l-top ...)]
  [lex-ids ::= (x ...)]
  [mut-ids ::= (x ...)]
  [top-ids ::= (x ...)])

; A separate pass
(define-metafunction LinkletsCompile
  all-toplevels : (l-top ...) (x ...) -> (x ...)
  [(all-toplevels () (x ...)) (x ...)]
  [(all-toplevels ((define-values (x) e) l-top ...) (x_tops ...))
   (all-toplevels (l-top ...) (x_tops ... x))]
  [(all-toplevels (l-top_1 l-top ...) (x ...))
   (all-toplevels (l-top ...) (x ...))])

; A separate (slightly deeper) pass
(define-metafunction LinkletsCompile
  get-mutated-vars-expr : l-top (x ...) -> (x ...)
  [(get-mutated-vars-expr (set! x v) (x_muts ...)) (x x_muts ...)]
  [(get-mutated-vars-expr (begin l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ...))]
  [(get-mutated-vars-expr l-top (x ...)) (x ...)])

(define-metafunction LinkletsCompile
  get-all-mutated-vars : (l-top ...) (x ...) -> (x ...)
  [(get-all-mutated-vars () (x ...)) (x ...)]
  [(get-all-mutated-vars (l-top_1 l-top ...) (x_muts ...))
   (get-all-mutated-vars (l-top ...) (x_muts ... x_new_muts ... ))
   (where (x_new_muts ...) (get-mutated-vars-expr l-top_1 ()))])

; Process Imports
(define-metafunction LinkletsCompile
  process-import : n (imp-id ...) (imp-obj ...) -> (imp-obj ...)
  [(process-import n () (imp-obj ...)) (imp-obj ...)]
  [(process-import n (x imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x x) ))
   (where x_gen ,(variable-not-in (term (x imp-id ...)) (term x)))]
  [(process-import n ((x_ext x_int) imp-id ...) (imp-obj ...))
   (process-import n (imp-id ...) (imp-obj ... (Import n x_gen x_int x_ext)))
   (where x_gen ,(variable-not-in (term ((x_ext x_int) imp-id ...)) (term x)))])

(define-metafunction LinkletsCompile
  process-importss : n ((imp-id ...) ...) ((imp-obj ...) ...) -> ((imp-obj ...) ...)
  [(process-importss n () ((imp-obj ...) ...)) ((imp-obj ...) ...)]
  [(process-importss n ((imp-id_1 ...) (imp-id ...) ...) ((imp-obj ...) ...))
   (process-importss ,(add1 (term n))
                     ((imp-id ...) ...)
                     ((imp-obj ...) ... (imp-obj_1 ...)))
   (where (imp-obj_1 ...) (process-import n (imp-id_1 ...) ()))])

; Process Exports
(define-metafunction LinkletsCompile
  process-exports : (exp-id ...) (exp-obj ...) -> (exp-obj ...)
  [(process-exports () (exp-obj ...)) (exp-obj ...)]
  [(process-exports (x exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x x_gen x)))
   (where x_gen ,(variable-not-in (term (x exp-id ...)) (term x)))]
  [(process-exports ((x_int x_ext) exp-id ...) (exp-obj ...))
   (process-exports (exp-id ...) (exp-obj ... (Export x_int x_gen x_ext)))
   (where x_gen ,(variable-not-in (term ((x_int x_ext) exp-id ...)) (term x)))])

#|
 ----  Define-values
if we see a define-values, we look at exported vars.
if the defined id is exported, we add a new linklet variable for that.
export's internal id should be the same with the defined id.
we create the variable with the exports internal gensym.
|#
(define-metafunction LinkletsCompile
  c-def-val : x e c-exps  -> exprs
  [(c-def-val x e_body (exp-obj_before ... (Export x x_gen x_int) exp-obj_after ...))
   ((define-values (x) e_body) (var-set! x_gen x))]
  [(c-def-val x e_body c-exps)
   ((define-values (x) e_body))])

#|
----  Symbol
Important parts are if the symbol is one of exports or imports.
If it's not, then it's either a toplevel defined (within linklet)
or a primitive (op)(which is handled in a separate case below)
|#
(define-metafunction LinkletsCompile
  c-symbol : x mut-ids top-ids c-imps c-exps -> l-top

  ; 1) if it's one of imports
  [(c-symbol x_current mut-ids top-ids
             ((imp-obj_before ...) ...
              ((Import n_bef x_gen_bef x_int_bef x_ext_bef) ...
               (Import n_cur x_gen_cur x_current x_ext_cur)
               (Import n_aft x_gen_aft x_int_aft x_ext_aft) ...)
              (imp-obj_after ...) ...) c-exps)
   (var-ref/no-check x_gen_cur)]
  ; 2-a) if it's one of exports, and it is mutated
  [(c-symbol x_current mut-ids top-ids c-imps
             ((Export x_int_bef x_gen_bef x_ext_bef) ...
              (Export x_current x_gen_cur x_ext_cur)
              (Export x_int_aft x_gen_aft x_ext_aft) ...))
   (var-ref x_gen_cur)
   (side-condition (member (term x_current) (term mut-ids)))]
  ; 2-b) if it's one of exports, and not defined in the toplevel
  ; (within the linklet)
  [(c-symbol x_current mut-ids top-ids c-imps
             ((Export x_int_bef x_gen_bef x_ext_bef) ...
              (Export x_current x_gen_cur x_ext_cur)
              (Export x_int_aft x_gen_aft x_ext_aft) ...))
   (var-ref x_gen_cur)
   (side-condition (not (member (term x_current) (term top-ids))))]
  ; 3) symbol is neither import nor export, treat normal
  [(c-symbol x_current mut-ids top-ids c-imps c-exps) x_current])

;; ----  Set!
(define-metafunction LinkletsCompile
  c-set-bang : x c-exps e -> l-top
  [(c-set-bang x ((Export x_int_bef x_gen_bef x_ext_bef) ...
                  (Export x x_gen_cur x_ext_cur)
                  (Export x_int_aft x_gen_aft x_ext_aft) ...)
               e_rhs)
   (var-set/check-undef! x_gen_cur e_rhs)]
  [(c-set-bang x c-exps e_rhs) (set! x e_rhs)])

;; c-body == sexp_to_ast (in Pycket)
(define-metafunction LinkletsCompile
  c-body : exprs lex-ids c-imps c-exps mut-ids top-ids exprs -> exprs
  ; base case
  [(c-body () lex-ids c-imps c-exps mut-ids top-ids exprs) exprs]
  ; define-values
  [(c-body ((define-values (x) e) l-top ...) (x_lex ...) c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) (x_lex ...) c-imps c-exps mut-ids top-ids (l-top_compiled ... l-top_def_val ...))
   (where (e_new) (c-body (e) (x x_lex ...) c-imps c-exps mut-ids top-ids ()))
   (where (l-top_def_val ...) (c-def-val x e_new c-exps))]
  ; symbols
  [(c-body (x_current l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... l-top_sym))
   (where l-top_sym (c-symbol x_current mut-ids top-ids c-imps c-exps))]
  ; set!
  [(c-body ((set! x e) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... l-top_set_bang))
   (where (e_new) (c-body (e) lex-ids c-imps c-exps mut-ids top-ids ()))
   (where l-top_set_bang (c-set-bang x c-exps e_new))]
  ; others
  [(c-body exprs lex-ids c-imps c-exps mut-ids top-ids exprs_compiled)
   (c-expr exprs lex-ids c-imps c-exps mut-ids top-ids exprs_compiled)])

(define-metafunction LinkletsCompile
  c-expr : exprs lex-ids c-imps c-exps mut-ids top-ids exprs -> exprs
  ; values
  [(c-expr (v l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... v))]
  ; begin
  [(c-expr ((begin e ...) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... (begin e_new ...)))
   (where (e_new ...) (c-body (e ...) lex-ids c-imps c-exps mut-ids top-ids ()))]
  ; op
  [(c-expr ((o e ...) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... (o e_new ...)))
   (where (e_new ...) (c-body (e ...) lex-ids c-imps c-exps mut-ids top-ids ()))]
  ; if
  [(c-expr ((if e_tst e_thn e_els) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... (if e_tst_new e_thn_new e_els_new)))
   (where (e_tst_new) (c-body (e_tst) lex-ids c-imps c-exps mut-ids top-ids ()))
   (where (e_thn_new) (c-body (e_thn) lex-ids c-imps c-exps mut-ids top-ids ()))
   (where (e_els_new) (c-body (e_els) lex-ids c-imps c-exps mut-ids top-ids ()))]
  ; lambda
  [(c-expr ((lambda (x ...) e_body) l-top ...) (x_lex ...) c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) (x_lex ...) c-imps c-exps mut-ids top-ids (l-top_compiled ... (lambda (x ...) e_body_new)))
   (where (e_body_new) (c-body (e_body) (x ... x_lex ...) c-imps c-exps mut-ids top-ids ()))]

  ; let-values
  [(c-expr ((let-values (((x_rhs) e_rhs) ...) e_body) l-top ...) (x_lex ...)
           c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) (x_lex ...) c-imps c-exps mut-ids top-ids
           (l-top_compiled ... (let-values (((x_rhs) e_rhs_new) ...) e_body_new)))
   (where (e_rhs_new ...) (c-body (e_rhs ...) (x_lex ...) c-imps c-exps mut-ids top-ids ()))
   (where (e_body_new) (c-body (e_body) (x_rhs ... x_lex ...) c-imps c-exps mut-ids top-ids ()))]
  ; raises
  [(c-expr ((raises e) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... (raises e)))]
  ; app
  [(c-expr ((e ...) l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ...))
   (c-body (l-top ...) lex-ids c-imps c-exps mut-ids top-ids (l-top_compiled ... (e_new ...)))
   (where (e_new ...) (c-body (e ...) lex-ids c-imps c-exps mut-ids top-ids ()))])

(define-metafunction LinkletsCompile
  compile-linklet : L -> L-obj or stuck
  [(compile-linklet (linklet ((imp-id ...) ...) (exp-id ...) l-top ...))
   (compiled-linklet c-imps c-exps l-top_compiled ...)
   ; where
   (where c-imps (process-importss 0 ((imp-id ...) ...) ()))
   (where c-exps (process-exports (exp-id ...) ()))
   (where mut-ids (get-all-mutated-vars (l-top ...) ()))
   (where top-ids (all-toplevels (l-top ...) ()))
   (where (l-top_compiled ...)
          (c-body (l-top ...) () c-imps c-exps mut-ids top-ids ()))])
