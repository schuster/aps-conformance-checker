#lang racket

;; Defines the abstract APS configurations and helper functions

(provide
 aps#
 aps#-α-z
 subst-n/aps#
 aps#-current-transitions
 aps#-eval
 aps#-matches-po?
 step-spec-with-goto
 aps#-transition-pattern
 aps#-transition-expression
 aps#-commitment-address
 aps#-commitment-pattern
 aps#-goto-state)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "csa-abstract.rkt")

(module+ test
  (require rackunit))

(define-extended-language aps#
  csa#
  (z ((S-hat ...) e-hat σ))
  (σ a# null)
  (u .... a#)
  (v-hat a# a-hat))

;; TODO: change the language and conformance so that I don't have to do this little initial
;; abstraction
(define (aps#-α-z spec-instance)
  ;; Doing a redex-let here just to add a codomain contract
  (redex-let aps# ([z (term (aps#-α-z/mf ,spec-instance))])
             (term z)))

(define-metafunction aps#
  aps#-α-z/mf : any -> any
  [(aps#-α-z/mf (addr natural))
   (init-addr natural)]
  [(aps#-α-z/mf (any ...))
   ((aps#-α-z/mf any) ...)]
  [(aps#-α-z/mf any) any])

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
  [(subst/aps#/u a# x v-hat) a#])

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

(define (aps#-eval exp subst)
  (redex-let aps# ([(any_binding ...) subst])
    (term (aps#-eval/mf (subst-n/aps# ,exp any_binding ...)))))

(define-metafunction aps#
  aps#-eval/mf : e-hat -> [(goto s a#ext ...) ([a#ext po] ...)]
  [(aps#-eval/mf (goto s a#ext ...))
   [(goto s a#ext ...) ()]]
  [(aps#-eval/mf (with-outputs ([a#ext_1 po_1] any_rest ...) e-hat))
   [(goto s a#ext ...) ([a#ext_1 po_1] any_outputs ...)]
   ;; TODO: this is an example of a where clause I expect to always succeed. I should write a macro on
   ;; reduction-relation that enforces that
   (where [(goto s a#ext ...) (any_outputs ...)]
          (aps#-eval/mf (with-outputs (any_rest ...) e-hat)))]
  [(aps#-eval/mf (with-outputs () e-hat))
   (aps#-eval/mf e-hat)])

;; TODO: test the eval function

(define (step-spec-with-goto spec-instance goto-exp)
  (redex-let aps# ([((S-hat ...) _ σ) spec-instance])
             (term ((S-hat ...) ,goto-exp σ))))

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

(define (aps#-matches-po? value pattern)
  (term (aps#-matches-po?/mf ,value ,pattern)))

(define-metafunction aps#
  aps#-matches-po?/mf : v# po -> boolean
  [(aps#-matches-po?/mf _ *) #t]
  [(aps#-matches-po?/mf _ x) #t]
  ;; TODO: self
  [(aps#-matches-po?/mf t t) #t]
  [(aps#-matches-po?/mf (list v ..._n) (list po ..._n))
   ;; TODO: find a better way to normalize to boolean rather than not/not
   ,(andmap
     (lambda (v po) (term (aps#-matches-po?/mf ,v ,po)))
     (term (v ...))
     (term (po ...)))]
  [(aps#-matches-po?/mf _ _) #f])

;; TODO: add tests for the match predicate

;; ---------------------------------------------------------------------------------------------------
;; Selectors

;; TODO: test these

(define (aps#-transition-pattern transition)
  (redex-let aps# ([(ε -> _) transition])
    (term ε)))

(define (aps#-transition-expression transition)
  (redex-let aps# ([(_ -> e-hat) transition])
    (term e-hat)))

(module+ test
  (define transition (term [(tuple a b) -> (with-outputs ([a *]) (goto S))]))

  (check-equal? (aps#-transition-pattern transition) (term (tuple a b)))
  (check-equal? (aps#-transition-expression transition) (term (with-outputs ([a *]) (goto S))))
  (define transition2 (term [unobs -> (with-outputs ([x *]) (goto S2))]))
  (check-equal? (aps#-transition-pattern transition2) (term unobs)))

(define (aps#-goto-state goto-exp)
  (redex-let aps# ([(goto s _ ...) goto-exp])
             (term s)))

(module+ test
  (check-equal? (aps#-goto-state (term (goto A))) (term A))
  (check-equal? (aps#-goto-state (term (goto B (SINGLE-ACTOR-ADDR SINGLE-ACTOR-ADDR)))) (term B)))

(define (aps#-commitment-address commitment)
  (redex-let aps# ([[a#ext _] commitment])
    (term a#ext)))

(define (aps#-commitment-pattern commitment)
  (redex-let aps# ([[_ po] commitment])
    (term po)))

(module+ test
  (define commitment (term [(* (Addr Nat)) (tuple)]))
  (check-equal? (aps#-commitment-address commitment) (term (* (Addr Nat))))
  (check-equal? (aps#-commitment-pattern commitment) (term (tuple))))
