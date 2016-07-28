#lang racket

;; Defines the Redex language and helpers for the APS specification language

(provide aps
         aps-eval
         subst-n/aps
         subst/aps
         aps-valid-config?
         aps-config-observable-addresses
         aps-config-only-instance-address

         ;; Testing helpers
         make-spec
         make-exclusive-spec)

;; ---------------------------------------------------------------------------------------------------
;; APS

(require
 redex/reduction-semantics
 "csa.rkt")

(module+ test
  (require rackunit))

(define-extended-language aps
  csa-eval
  (e-hat (spawn-spec ((goto s u ...) S-hat ...) e-hat)
         (goto s u ...)
         (with-outputs ([u po] ...) e-hat))
  (S-hat (define-state (s x ...) (ε -> e-hat) ...))
  (ε unobs
     p)
  (u x) ; arguments
  (p *
     x
     (variant t p ...)
     (record [l p] ...))
  (po *
      (spawn-spec (goto s u ...) S-hat ...)
      self
      (variant t po ...)
      (record [l po] ...)))

;; TODO: remove the idea of instances, just need configs of a single instance

(define-extended-language aps-eval
  aps
  (Σ ((z ...) (a ...) O))
  (O ((a po ...) ...))
  (z ((S-hat ...) e-hat σ))
  (σ a UNKNOWN)
  (u .... a)
  (v-hat a))

(define-metafunction aps-eval
  subst-n/aps : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps e-hat) e-hat]
  [(subst-n/aps e-hat (x v-hat) any_rest ...)
   (subst-n/aps (subst/aps e-hat x v-hat) any_rest ...)])

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
  [(subst/aps/po t x v-hat) t]
  [(subst/aps/po * x v-hat) *]
  [(subst/aps/po (variant t po ...) x v-hat) (variant t (subst/aps/po po x v-hat) ...)]
  [(subst/aps/po (record [l po] ...) x v-hat)
   (record [l (subst/aps/po x v-hat)] ...)])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (aps-valid-config? c)
  (if (redex-match aps-eval Σ c) #t #f))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps-config-only-instance-address config)
  (redex-let* aps-eval ([((z) _ _) config]
                        [(_ _ σ) (term z)])
              (term σ)))

(module+ test
  (test-case "config only instance address"
    (define spec (term (([((define-state (A))) (goto A) (addr 2 Nat)]) () ())))
    (check-not-false (redex-match aps-eval Σ spec))
    (check-equal? (aps-config-only-instance-address spec) (term (addr 2 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (aps-config-observable-addresses config)
  (term (config-observable-addresses/mf ,config)))

(define-metafunction aps-eval
  config-observable-addresses/mf : Σ -> (a ...)
  [(config-observable-addresses/mf ((z ...) _ _))
   (a ... ...)
   (where ((_ (goto s a ...) _) ...) (z ...))])

(module+ test
  (check-equal?
   (aps-config-observable-addresses
    (make-exclusive-spec
     (term (((define-state (Always r1 r2)
               [* -> (goto Always r1 r2)]))
            (goto Always (addr 3 Nat) (addr 4 Nat))
            (addr 1 Nat)))))
   (term ((addr 3 Nat) (addr 4 Nat)))))

(define (make-exclusive-spec instance)
  (make-spec instance null))

(define (make-spec instance receptionists)
  (redex-let* aps-eval ([z instance]
                        [(a_rec ...) receptionists]
                        [(_ (goto _ a ...) _) (term z)]
                        ;; TODO: remove duplicates from a...
                        [Σ (term ((z) (a_rec ...) ((a) ...)))])
              (term Σ)))
