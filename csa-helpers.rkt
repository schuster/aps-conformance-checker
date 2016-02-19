#lang racket

(provide
 actor-message-type
 actor-address
 config-only-actor)

(require
 redex/reduction-semantics
 "csa-abstract.rkt")

(define (actor-message-type the-actor)
  (term (actor-message-type/mf ,the-actor)))

(define-metafunction csa#
  actor-message-type/mf : (SINGLE-ACTOR-ADDR (τ (S ...) e)) -> τ
  [(actor-message-type/mf (SINGLE-ACTOR-ADDR (τ (S ...) e)))
   τ])

(define (actor-address the-actor)
  (redex-let csa# ([(a# _) the-actor])
             (term a#)))

(define (config-only-actor prog-config)
  (redex-let csa# ([(((SINGLE-ACTOR-ADDR any_body))
                     ()
                     (SINGLE-ACTOR-ADDR)
                     ;; TODO: update χ# or just get rid of it
                     ())
                    prog-config])
             (term (SINGLE-ACTOR-ADDR any_body))))
