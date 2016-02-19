;; Defines the abstract interpretation of CSA programs/configurations

#lang racket

(provide
 csa#
 generate-abstract-messages
 csa#-match
 csa#-eval-transition
 (struct-out program-transition))

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 csa/model)

;; Abstract interpretation version of CSA
;; NOTE: this handles only single-actor configurations right now
;; TODO: make the language inheritance hierarchy correct
(define-extended-language csa# aps
  (K# (α# μ# ρ# χ#)) ; TODO: update this
  ;; NOTE: for now, assuming only the one special actor
  (α# ((SINGLE-ACTOR-ADDR (τ (S# ...) e#)) ...))
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
  (a# SINGLE-ACTOR-ADDR a#ext)
  (a#ext
   (* (Addr τ))
   (s v#template natural time-flag))
  (time-flag MOST-RECENT PREVIOUS)
  (ρ# (SINGLE-ACTOR-ADDR))
  (χ# (a#ext ...))
  ;; H# = handler config (exp + outputs so far)
  (H# (e# ([a#ext v#] ...)))
  ;; (A# ((any_1 ... hole any_2 ...) () ρ χ)) ; TODO: update this
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

;; TODO: define this
(define (generate-abstract-messages type max-depth)
  (term (generate-abstract-messages/mf ,type ,max-depth)))

(define-metafunction csa#
  generate-abstract-messages/mf : τ natural -> (v# ...)
  [(generate-abstract-messages/mf Nat _) ((* Nat))]
  [(generate-abstract-messages/mf t _) (t)]
  [(generate-abstract-messages/mf (Union τ_1 τ_rest ...) natural_max-depth)
   (v#_1 ... v#_rest ...)
   ;; TODO: should I do allow duplicates to be returned?
   (where (v#_1 ...) (generate-abstract-messages/mf τ_1 natural_max-depth))
   (where (v#_rest ...) (generate-abstract-messages/mf (Union τ_rest ...) natural_max-depth))]
  [(generate-abstract-messages/mf (Union) natural_max-depth) ()]
  [(generate-abstract-messages/mf (minfixpt X τ) natural_max-depth)
   (generate-abstract-messages/mf (type-subst τ X (minfixpt X τ)) natural_max-depth)]
  [(generate-abstract-messages/mf (Tuple τ ...) 0)
   ((* (Tuple τ ...)))]
  [(generate-abstract-messages/mf (Tuple τ_1 τ_rest ...) natural_max-depth)
   ,(for/fold ([tuples-so-far null])
             ([sub-tuple (term (generate-abstract-messages/mf (Tuple τ_rest ...) natural_max-depth))])
     (append
      (for/list ([generated-v (term (generate-abstract-messages/mf τ_1 ,(- (term natural_max-depth) 1)))])
        (redex-let csa# ([(tuple v#_other ...) sub-tuple]
                         [v#_1 generated-v])
          (term (tuple v#_1 v#_other ...))))
      tuples-so-far))]
  [(generate-abstract-messages/mf (Tuple) natural_max-depth)
   ((tuple))])

(module+ test
  (require rackunit)

  (check-equal?
   (term (generate-abstract-messages/mf Nat 0))
   (term ((* Nat))))
  ;; tuples of both depths
  ;; addresses...?
  ;; symbols
  ;; recursive types (list of Nat, up to certain depth
  (check-equal? (term (generate-abstract-messages/mf 'Begin 0)) (term ('Begin)))
  (check-equal?
   (term (generate-abstract-messages/mf (Union 'A 'B) 0))
   (term ('A 'B)))
  ;; TODO: allow reordering
  ;; (check-equal?
  ;;  (term (generate-abstract-messages/mf (Union 'A 'B)))
  ;;  (term ('B 'A)))
  (check-equal? (term (generate-abstract-messages/mf (Union) 0)) (term ()))
  (check-equal?
   (term (generate-abstract-messages/mf (minfixpt Dummy Nat) 0))
   (term ((* Nat))))
  (check-equal?
   (term (generate-abstract-messages/mf (Tuple Nat Nat) 0))
   (term ((* (Tuple Nat Nat)))))
  (check-equal?
   (term (generate-abstract-messages/mf (Tuple Nat Nat) 1))
   (term ((tuple (* Nat) (* Nat)))))
  (check-equal?
   (term (generate-abstract-messages/mf (Tuple (Union 'A 'B) (Union 'C 'D)) 0))
   (term ((* (Tuple (Union 'A 'B) (Union 'C 'D))))))
  (check-equal?
   (term (generate-abstract-messages/mf (Tuple (Union 'A 'B) (Union 'C 'D)) 1))
   (term ((tuple 'A 'C) (tuple 'A 'D) (tuple 'B 'C) (tuple 'B 'D))))
  (define list-of-nat (term (minfixpt NatList (Union 'Null (Tuple 'Cons Nat NatList)))))
  (check-equal?
   (term (generate-abstract-messages/mf ,list-of-nat 0))
   (term ('Null (* ,list-of-nat)))))

(define (csa#-match val pat)
  (judgment-holds (csa#-match/j ,val ,pat ([x a#ext] ...))
                  (term ([x a#ext] ...))))

(define-judgment-form csa#
  #:mode (csa#-match/j I I O)
  #:contract (csa#-match/j v# p ((x a#ext) ...))

  [-------------------
   (csa#-match/j _ * ())]

  [-------------------
   (csa#-match/j x a#ext ([x a#ext]))]

  [----------------
   (csa#-match/j t t ())]

  [(csa#-match/j v# p ([x a#ext] ...)) ...
   --------------
   (csa#-match/j (tuple v# ..._n) (tuple p ..._n) ([x a#ext] ... ...))])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; Outputs is a list of abstract-addr/abstract-message pairs
(struct program-transition (message observed? outputs goto-exp))

;; (csa#-eval-transition prog (actor-address the-actor) message)

(define (csa#-eval-transition prog-config actor-address message)
  (redex-let csa# ([(((SINGLE-ACTOR-ADDR (τ (_ ... (define-state (s x_s ..._n) (x_m) e#) _ ...) (in-hole E# (goto s v# ..._n)))))
                     ()
                     (SINGLE-ACTOR-ADDR)
                     ())
                    prog-config])
             ;; TODO: deal with the case where x_m shadows an x_s
             (define results
               (apply-reduction-relation*
                handler-step#
                (term ((csa#-subst-n e# [x_s v#] ...)
                       ()))))
             (for/list ([result results])
               (redex-let csa# ([((goto s v#_param ...) ([a#ext v#_out] ...)) result])
                          ;; TODO: deal with unobserved messages
                          (program-transition message #t (term ([a#ext v#_out] ...)) (term (goto s v#_param ...)))))))

(define handler-step#
  (reduction-relation csa#
    #:domain H#

    ;; TODO: goto into rcv (with/without timeout)

    ;; let, match, begin, send, goto
    (==> (begin v# e# e#_rest ...)
         (begin e# e#_rest ...)
         Begin1)
    (==> (begin v#)
         v#
         Begin2)

    (--> ((in-hole E (send a# v#)) (any_outputs ...))
         ((in-hole E v#)           (any_outputs ... [a# v#]))
         Send)

    ;; TODO: let
    ;; TODO: match

    with
    [(--> ((in-hole E# old) ([a#ext v#] ...))
          ((in-hole E# new) ([a#ext v#] ...)))
     (==> old new)]))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

;; TODO: see if I can use Paul's binding specs to write this code automatically

(define-metafunction csa#
  csa#-subst-n : e# (x v#) ... -> e#
  [(csa#-subst-n e#) e#]
  [(csa#-subst-n e# (x v#) any_rest ...)
   (csa#-subst-n (csa#-subst e# x v#) any_rest ...)])

(define-metafunction csa#
  csa#-subst : e# x v# -> e#
  [(csa#-subst x x v#) v#]
  [(csa#-subst x x_2 v#) x]
  ;; [(csa#-subst n x v) n]
  [(csa#-subst t x v) t]
  ;; [(csa#-subst a x v) a]
  ;; [(csa#-subst (spawn e S ...) self v) (spawn e S ...)]
  ;; [(csa#-subst (spawn e S ...) x v)
  ;;   (spawn (csa#-subst e x v) (csa#-subst/S S x v) ...)]
  [(csa#-subst (goto s e# ...) x v#) (goto s (csa#-subst e# x v#) ...)]
  [(csa#-subst (send e#_1 e#_2) x v#)
   (send (csa#-subst e#_1 x v#) (csa#-subst e#_2 x v#))]
  [(csa#-subst (begin e# ...) x v#) (begin (csa#-subst e# x v#) ...)]
  ;; [(csa#-subst (let ([x_let e] ...) e_body) x v)
  ;;  (let ([x_let (csa#-subst e x v)] ...) e_body)
  ;;  (where (_ ... x _ ...) (x_let ...))] ; check that x is in the list of bound vars
  ;; [(csa#-subst (let ([x_let e] ...) e_body) x v)
  ;;  (let ([x_let (csa#-subst e x v)] ...) (csa#-subst e_body x v))]
  ;; [(csa#-subst (match e [p e_pat] ...) x v)
  ;;  (match (csa#-subst e x v) (csa#-subst/match-clause [p e_pat] x v) ...)]
  ;; [(csa#-subst (tuple e ...) x v) (tuple (csa#-subst e x v) ...)]
  ;; [(csa#-subst (rcv (x) e) x v) (rcv (x) e)]
  ;; [(csa#-subst (rcv (x_h) e) x v) (rcv (x_h) (csa#-subst e x v))]
  ;; [(csa#-subst (rcv (x) e [(timeout n) e_timeout]) x v) (rcv (x) e [(timeout n) e_timeout])]
  ;; [(csa#-subst (rcv (x_h) e [(timeout n) e_timeout]) x v)
  ;;  (rcv (x_h) (csa#-subst e x v) [(timeout n) (csa#-subst e_timeout x v)])]
  )
