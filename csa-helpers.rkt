#lang racket

;; TODO: move these functions into other files and get rid of this one

(provide
 actor-message-type
 actor-address
 actor-current-state
 config-only-actor)

(require
 redex/reduction-semantics
 "csa-abstract.rkt")

(define (actor-message-type the-actor)
  (term (actor-message-type/mf ,the-actor)))

(define-metafunction csa#
  actor-message-type/mf : α#n -> τ
  [(actor-message-type/mf (_ (τ _ _)))
   τ])

(define (actor-address the-actor)
  (redex-let csa# ([(a# _) the-actor])
             (term a#)))

(define (actor-current-state the-actor)
  (redex-let csa# ([(_ (_ _ (in-hole E# (goto s _ ...)))) the-actor])
             (term s)))

(define (config-only-actor prog-config)
  (term (config-only-actor/mf ,prog-config)))

(define-metafunction csa#
  config-only-actor/mf : K# -> α#n
  [(config-only-actor/mf (α# _ _ _))
   α#n
   (where (α#n) α#)])
