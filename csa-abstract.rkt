;; Defines the abstract interpretation of CSA programs/configurations

#lang racket

(provide)

(require
 redex/reduction-semantics
 csa/model)


;; Abstract interpretation version of CSA
;; NOTE: this handles only single-actor configurations right now
(define-extended-language csa# csa-eval
  (K# (α# μ# ρ# χ#)) ; TODO: update this
  ;; NOTE: for now, assuming only the one special actor
  (α# ((SINGLE-ACTOR-ADDR ((S# ...) e#)) ...))
  (μ# ()) ; NOTE: for now, assuming no internal sends
  (S# (define-state (s x ...) (x) e#)
      ;; TODO: not dealing with timeouts yet...
      ;; (define-state (s x ...) (x) e# [(timeout Nat) e#])
      )
  ;; TODO: these probably should be sets of values, right?
  (v# t
      a# ; TODO: replace this one with a special pattern
      (tuple v# ...)
      (* τ))
  (v#template
   t
   ADDR-HOLE
   (tuple v#template ...)
   (* τ))
  (e# (spawn e# S ...)
      (goto s e# ...)
      (send e# e#)
      self
      (begin e# ... e#)
      (let ([x e#] ...) e#)
      (match e# [p e#] ...)
      (tuple e# ...)
      t
      a#
      x
      Nat
      *)
  (a# single-actor-addr a#ext)
  (a#ext
   (* (Addr τ))
   (s v#template natural time-flag))
  (time-flag MOST-RECENT PREVIOUS)
  (ρ# (SINGLE-ACTOR-ADDR))
  (χ# (a#ext ...))
  (A# ((any_1 ... hole any_2 ...) () ρ χ)) ; TODO: update this
  (E# hole
      (goto s v# ... E# e# ...)
      (send E# e#)
      (send v# E#)
      (begin E# e# ...)
      (let ([x E#] [x e#] ...) e#)
      (match E# [p e#] ...)
      (tuple v# ... E# e# ...)))

  ;; (define-metafunction csa#
  ;;   abstract : K -> K#
  ;;   ;; TODO: handle messages already in the queue
  ;;   ;;
  ;;   ;; TODO: handle ρ and χ
  ;;   [(abstract (α () ρ χ))
  ;;    (α# () ρ χ)
  ;;    (where  ((a ((S ...) e)) ...) α)
  ;;    (where α# ((a (((abstract/S S) ...) (abstract/e e))) ...))])

  ;; (define-metafunction csa#
  ;;   abstract/e : e -> e#
  ;;   [(abstract/e n) Nat]
  ;;   ;; TODO: do something different for addresses (probably need a dictionary of things to substitute
  ;;   ;; for them?)
  ;;   [(abstract/e a) a]
  ;;   ;; TODO: do something more clever for tuples
  ;;   [(abstract/e (tuple e ...)) (tuple (abstract/e e ...))]
  ;;   [(abstract/e (rcv (x) e) [(timeout Nat)]) (rcv (x) (abstract/e e))]
  ;;   ;; The rest of these from here just do the normal tree-walking thing
  ;;   [(abstract/e (spawn e S ...)) (spawn (abstract/e e) (abstract/S S) ...)]
  ;;   [(abstract/e (goto s e ...)) (goto s (abstract/e e) ...)]
  ;;   [(abstract/e (send e_1 e_2)) (send (abstract/e e_1) (abstract/e e_2))]
  ;;   [(abstract/e self) self]
  ;;   [(abstract/e (begin e ...)) (begin (abstract/e e ...))]
  ;;   ;; TODO: let
  ;;   [(abstract/e (match e_1 [p e_2] ...)) (match (abstract/e e) [p (abstract/e e)] ...)]
  ;;   [(abstract/e t) t]
  ;;   [(abstract/e x) x]
  ;;   [(abstract/e (rcv (x) e)) (rcv (x) (abstract/e e))])

;; ---------------------------------------------------------------------------------------------------
;; Helper functions
(define-metafunction csa#
  generate-abstract-messages : τ natural -> (v# ...)
  [(generate-abstract-messages Nat _) ((* Nat))]
  [(generate-abstract-messages t _) (t)]
  [(generate-abstract-messages (Union τ_1 τ_rest ...) natural_max-depth)
   (v#_1 ... v#_rest ...)
   ;; TODO: should I do allow duplicates to be returned?
   (where (v#_1 ...) (generate-abstract-messages τ_1 natural_max-depth))
   (where (v#_rest ...) (generate-abstract-messages (Union τ_rest ...) natural_max-depth))]
  [(generate-abstract-messages (Union) natural_max-depth) ()]
  [(generate-abstract-messages (minfixpt X τ) natural_max-depth)
   (generate-abstract-messages (type-subst τ X (minfixpt X τ)) natural_max-depth)]
  [(generate-abstract-messages (Tuple τ ...) 0)
   ((* (Tuple τ ...)))]
  [(generate-abstract-messages (Tuple τ_1 τ_rest ...) natural_max-depth)
   ,(for/fold ([tuples-so-far null])
             ([sub-tuple (term (generate-abstract-messages (Tuple τ_rest ...) natural_max-depth))])
     (append
      (for/list ([generated-v (term (generate-abstract-messages τ_1 ,(- (term natural_max-depth) 1)))])
        (redex-let csa# ([(tuple v#_other ...) sub-tuple]
                         [v#_1 generated-v])
          (term (tuple v#_1 v#_other ...))))
      tuples-so-far))]
  [(generate-abstract-messages (Tuple) natural_max-depth)
   ((tuple))])

(module+ test
  (require rackunit)

  (check-equal?
   (term (generate-abstract-messages Nat 0))
   (term ((* Nat))))
  ;; tuples of both depths
  ;; addresses...?
  ;; symbols
  ;; recursive types (list of Nat, up to certain depth
  (check-equal? (term (generate-abstract-messages 'Begin 0)) (term ('Begin)))
  (check-equal?
   (term (generate-abstract-messages (Union 'A 'B) 0))
   (term ('A 'B)))
  ;; TODO: allow reordering
  ;; (check-equal?
  ;;  (term (generate-abstract-messages (Union 'A 'B)))
  ;;  (term ('B 'A)))
  (check-equal? (term (generate-abstract-messages (Union) 0)) (term ()))
  (check-equal?
   (term (generate-abstract-messages (minfixpt Dummy Nat) 0))
   (term ((* Nat))))
  (check-equal?
   (term (generate-abstract-messages (Tuple Nat Nat) 0))
   (term ((* (Tuple Nat Nat)))))
  (check-equal?
   (term (generate-abstract-messages (Tuple Nat Nat) 1))
   (term ((tuple (* Nat) (* Nat)))))
  (check-equal?
   (term (generate-abstract-messages (Tuple (Union 'A 'B) (Union 'C 'D)) 0))
   (term ((* (Tuple (Union 'A 'B) (Union 'C 'D))))))
  (check-equal?
   (term (generate-abstract-messages (Tuple (Union 'A 'B) (Union 'C 'D)) 1))
   (term ((tuple 'A 'C) (tuple 'A 'D) (tuple 'B 'C) (tuple 'B 'D))))
  (define list-of-nat (term (minfixpt NatList (Union 'Null (Tuple 'Cons Nat NatList)))))
  (check-equal?
   (term (generate-abstract-messages ,list-of-nat 0))
   (term ('Null (* ,list-of-nat)))))
