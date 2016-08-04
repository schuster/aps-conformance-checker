#lang racket

;; Concrete semantic domains for APS (specification language), and associated functions

(provide
 aps-eval
 aps-valid-config?
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

(define-extended-language aps-eval
  aps
  (Σ ((z ...) (a ...) O))
  (O ((a po ...) ...))
  (z ((S-hat ...) e-hat σ))
  (σ a UNKNOWN)
  (u .... a)
  (v-hat a))

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
;; Testing Helpers

(define (make-exclusive-spec instance)
  (make-spec instance null))

(define (make-spec instance receptionists)
  (redex-let* aps-eval ([z instance]
                        [(a_rec ...) receptionists]
                        [(_ (goto _ a ...) _) (term z)]
                        [Σ (term ((z) (a_rec ...) ((a) ...)))])
              (term Σ)))
