#lang racket

(require redex/pict
         pict
         "../linklets.rkt"
         "../compile-linklets.rkt"
         "../main.rkt")

"-----------------------------------------------------------------"
(render-language-nts '(L l-top d imp-id exp-id))
(define source-img (render-language LinkletSource))
(define bm (pict->bitmap source-img))
(send bm save-file "linklet-source.png" 'png)
"--------------------------- SOURCE DONE -------------------------"

"-----------------------------------------------------------------"
(render-language-nts '(LI L-obj imp-obj exp-obj
                         I linkl-ref inst-ref
                         ω Ω EL EI))
(define runtime-img (render-language Linklets))
(define bm2 (pict->bitmap runtime-img))
(send bm2 save-file "linklet-runtime.png" 'png)
"------------------------- RUNTIME DONE --------------------------"

"-----------------------------------------------------------------"
(render-language-nts '(p p-top final-expr V EP))
(define program (render-language Linklets))
(define bm3 (pict->bitmap program))
(send bm3 save-file "linklet-program.png" 'png)
"------------------------- PROGRAM DONE --------------------------"

"-----------------------------------------------------------------"
(render-reduction-relation-rules '("linklet-lookup" "instance-lookup" "instance variable value" "let-inst" "instantiate linklet" "eval linklet"))
(define reduction (render-reduction-relation -->βp #:style 'vertical))
(define bm4 (pict->bitmap reduction))
(send bm4 save-file "program-reduction.png" 'png)
"---------------------- PROG REDUCTION DONE ----------------------"

"-----------------------------------------------------------------"
(render-reduction-relation-rules #f)
(define i-reduction (render-reduction-relation -->βi-render #:style 'horizontal-side-conditions-same-line))
(define bm5 (pict->bitmap i-reduction))
(send bm5 save-file "linklet-body-reduction.png" 'png)
"------------------------- REDUCTION DONE ------------------------"
