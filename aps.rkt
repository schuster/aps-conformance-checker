#lang racket

;; Defines the Redex language and helpers for the APS specification language

(provide aps
         aps-eval
         subst-n/aps
         subst/aps
         aps-valid-config?
         aps-valid-instance?
         aps-config-observable-addresses
         aps-config-from-instances)

;; ---------------------------------------------------------------------------------------------------
;; APS

(require
 redex/reduction-semantics
 "csa.rkt")

(module+ test
  (require rackunit))

(define-extended-language aps
  csa-eval
  (e-hat (let-spec (x (goto s u ...) S-hat ...) e-hat)
         (goto s u ...)
         (with-outputs ([u po] ...) e-hat))
  (S-hat (define-state (s x ...) (ε -> e-hat) ...))
  (ε unobs
     p)
  (u x) ; arguments
  (p *
     x
     t
     (variant t p ...)
     (record [l p] ...))
  (po *
      x
      self
      t
      (variant t po ...)
      (record [l po] ...)
      (or po po ...)))

(define-extended-language aps-eval
  aps
  (Σ ((z ...) O))
  (O ((a po ...) ...))
  (z ((S-hat ...) e-hat σ))
  (σ a null)
  (u .... a)
  (v-hat a a-hat))

(define-metafunction aps-eval
  subst-n/aps : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps e-hat) e-hat]
  [(subst-n/aps e-hat (x v-hat) any_rest ...)
   (subst-n/aps (subst/aps e-hat x v-hat) any_rest ...)])

;; TODO: write tests for this substitution

(define-metafunction aps-eval
  subst/aps : e-hat x v-hat -> e-hat
  [(subst/aps (goto s u ...) x v-hat)
   (goto s (subst/aps/u u x v-hat) ...)]
  [(subst/aps (with-outputs ([u po] ...) e-hat) x v-hat)
   (with-outputs ([(subst/aps/u u x v-hat) (subst/aps/po po x v-hat)] ...) (subst/aps e-hat x v-hat))]
  ;; TODO: write the other clauses
  )

(define-metafunction aps-eval
  subst/aps/u : u x v-hat -> u
  [(subst/aps/u x x v-hat) v-hat]
  [(subst/aps/u x_2 x v-hat) x_2]
  [(subst/aps/u a x v-hat) a])

(define-metafunction aps-eval
  subst/aps/po : po x v-hat -> po
  [(subst/aps/po x x v-hat) v-hat]
  [(subst/aps/po x_2 x v-hat) x_2]
  [(subst/aps/po a x v-hat) a]
  [(subst/aps/po a-hat x v-hat) a-hat]
  [(subst/aps/po t x v-hat) t]
  [(subst/aps/po * x v-hat) *]
  [(subst/aps/po (variant t po ...) x v-hat) (variant t (subst/aps/po po x v-hat) ...)]
  [(subst/aps/po (record [l po] ...) x v-hat)
   (record [l (subst/aps/po x v-hat)] ...)]
  [(subst/aps/po (or po_1 po_rest ...) x v-hat)
   (or (subst/aps/po po_1 x v-hat) (subst/aps/po po_rest x v-hat) ...)])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (aps-valid-config? c)
  (if (redex-match aps-eval Σ c) #t #f))

(define (aps-valid-instance? i)
  (if (redex-match aps-eval z i) #t #f))

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (aps-config-observable-addresses config)
  (term (config-observable-addresses/mf ,config)))

(define-metafunction aps-eval
  config-observable-addresses/mf : Σ -> (a ...)
  [(config-observable-addresses/mf ((z ...) _))
   (a ... ...)
   (where ((_ (goto s a ...) _) ...) (z ...))])

(module+ test
  (check-equal?
   (aps-config-observable-addresses
    (aps-config-from-instances
     (term ((((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
             (goto Always (addr 3) (addr 4))
             (addr 1))))))
   (term ((addr 3) (addr 4)))))

(define (aps-config-from-instances instances)
  (redex-let* aps-eval ([(z ...) instances]
                        [((_ (goto _ a ...) _) ...) (term (z ...))]
                        ;; TODO: remove duplicates from a...
                        [Σ (term ((z ...) ((a) ... ...)))])
              (term Σ)))
