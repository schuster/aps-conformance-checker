#lang racket

;; Defines the abstract APS configurations and helper functions

(provide
 aps#
 subst-n/aps#
 aps#-current-transitions
 aps#-eval
 aps-matches-po?)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "csa-abstract.rkt")

(define-extended-language aps#
  csa#
  (z ((S-hat ...) e-hat σ))
  (σ a# null)
  (u .... a#)
  (v-hat a# a-hat))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps# : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps# e-hat) e-hat]
  [(subst-n/aps# e-hat (x v-hat) any_rest ...)
   (subst-n/aps# (subst/aps# e-hat x v-hat) any_rest ...)])

;; TODO: write tests for this substitution

(define-metafunction aps#
  subst/aps# : e-hat x v-hat -> e-hat
  [(subst/aps# (goto s u ...) x v-hat)
   (goto s (subst/aps#/u u x v-hat) ...)]
  [(subst/aps# (with-outputs ([u po] ...) e-hat) x v-hat)
   (with-outputs ([(subst/aps#/u u x v-hat) (subst/aps#/po po x v-hat)] ...) (subst/aps# e-hat x v-hat))]
  ;; TODO: write the other clauses
  )

(define-metafunction aps#
  subst/aps#/u : u x v-hat -> u
  [(subst/aps#/u x x v-hat) v-hat]
  [(subst/aps#/u x_2 x v-hat) x_2]
  [(subst/aps#/u a x v-hat) a])

(define-metafunction aps#
  subst/aps#/po : po x v-hat -> po
  [(subst/aps#/po x x v-hat) v-hat]
  [(subst/aps#/po x_2 x v-hat) x_2]
  [(subst/aps#/po a x v-hat) a]
  [(subst/aps#/po a-hat x v-hat) a-hat]
  [(subst/aps#/po t x v-hat) t]
  [(subst/aps#/po * x v-hat) *]
  [(subst/aps#/po (list po ...) x v-hat) (list (subst/aps#/po po x v-hat) ...)])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

(define (aps#-current-transitions instance)
  (term (aps#-current-transitions/mf ,instance)))

;; TODO: deal with the case where the pattern variables shadow the state variables
(define-metafunction aps#
  aps#-current-transitions/mf : z -> ((ε -> e-hat) ...)
  [(aps#-current-transitions/mf ((_ ... (define-state (s x ...) (ε -> e-hat) ...) _ ...) (goto s v-hat ...) _))
   ((ε -> (subst-n/aps# e-hat (x v-hat) ...)) ...)])

(define (aps#-eval exp)
  (term (aps#-eval/mf ,exp)))

(define-metafunction aps#
  aps#-eval/mf : e-hat -> [(goto s v-hat ...) ([a#ext po] ...)]
  [(aps#-eval/mf (goto s a#ext ...))
   [(goto s a#ext ...) ()]]
  [(aps#-eval/mf (with-outputs ([a#ext_1 po_1] any_rest ...) e-hat))
   [(goto s a#ext) ([a#ext_1 po_1] any_outputs ...)]
   (where [(goto s a#ext) (any_outputs ...)]
          (aps#-eval/mf (with-outputs (any_rest ...) e-hat)))]
  [(aps#-eval/mf (with-outputs () e-hat))
   (aps#-eval/mf e-hat)])

;; TODO: test the eval function

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

(define (aps-matches-po? value pattern)
  (term (aps-matches-po?/mf ,value ,pattern)))

(define-metafunction aps#
  aps-matches-po?/mf : v po -> boolean
  [(aps-matches-po?/mf _ *) #t]
  [(aps-matches-po?/mf _ x) #t]
  ;; TODO: self
  [(aps-matches-po?/mf t t) #t]
  [(aps-matches-po?/mf (list v ..._n) (list po ..._n))
   ;; TODO: find a better way to normalize to boolean rather than not/not
   ,(andmap
     (lambda (v po) (term (aps-matches-po?/mf ,v ,po)))
     (term (v ...))
     (term (po ...)))]
  [(aps-matches-po?/mf _ _) #f])

;; TODO: add tests for the match predicate
