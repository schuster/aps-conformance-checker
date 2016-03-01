#lang racket

;; Defines the desugaring from the surface syntax to the core syntax

(provide desugar-actor)

(require
 redex/reduction-semantics
 "csa.rkt")

;; TODO: consider using Nanopass for this transformation

;; Translates an actor definition from the surface syntax into the core language syntax
;;
;; TODO: add actor args
(define (desugar-actor actor-def address)
  (term (desugar-actor/mf ,actor-def ,address))
  )

(define-metafunction csa-eval
  ;; TODO: define some sort of Redex language that defines the surface-level programs
  desugar-actor/mf : any a -> αn
  [(desugar-actor/mf (define-actor (_) e S ...) a)
   (a ((S ...) e))])

(module+ test
  (require rackunit)

  (check-equal?
   (desugar-actor
    (term (define-actor (IgnoreAll)
            (goto Always)
            (define-state (Always) (m) (goto Always))))
    (term (addr 0)))
   (term ((addr 0)
          (((define-state (Always) (m) (goto Always)))
           (goto Always))))))
