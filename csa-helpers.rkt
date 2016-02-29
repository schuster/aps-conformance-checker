#lang racket

;; TODO: move these functions into other files and get rid of this one

(provide
 actor-address
 actor-current-state
 config-only-actor)

(require
 redex/reduction-semantics
 "csa-abstract.rkt")

(define (actor-address the-actor)
  (redex-let csa# ([(a# _) the-actor])
             (term a#)))

(define (actor-current-state the-actor)
  (redex-let csa# ([(_ (_ (in-hole E# (goto s _ ...)))) the-actor])
             (term s)))

(define (config-only-actor prog-config)
  (term (config-only-actor/mf ,prog-config)))

(define-metafunction csa#
  config-only-actor/mf : K# -> α#n
  [(config-only-actor/mf (α# _ _ _))
   α#n
   (where (α#n) α#)])
