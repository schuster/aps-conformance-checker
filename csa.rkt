#lang racket

;; Models the grammar for APS (Agent Protocol Specifications)

(provide csa
         csa-eval
         inject-message
         make-single-agent-config
         handler-step
         aps
         aps-eval
         subst-n/aps
         subst/aps
         type-subst
         csa-valid-config?
         aps-valid-instance?)

;; ---------------------------------------------------------------------------------------------------

(require redex/reduction-semantics)

(module+ test
  (require rackunit))

;; ---------------------------------------------------------------------------------------------------
;; CSA

(define-language csa
  (e (spawn e S ...)
     (goto s e ...)
     (send e e)
     self
     (begin e ... e)
     (let ([x e] ...) e)
     (match e [p e] ...)
     (tuple e ...)
     (primop e ...)
     t
     x
     n)
  (S (define-state (s x ...) (x) e)
     (define-state (s x ...) (x) e [(timeout n) e]))
  (p *
     x
     t
     (tuple p ...))
  (primop < /)
  ((x s) variable-not-otherwise-mentioned)
  (t (quote variable-not-otherwise-mentioned))
  (n natural)
  (τ Nat
     (minfixpt X τ)
     X
     t
     (Tuple τ ...)
     (Union τ ...)
     (Addr τ)) ;; TODO: integrate types into the language
  (X variable-not-otherwise-mentioned))

(define-extended-language csa-eval
  csa
  (K (α μ ρ χ))
  (α (αn ...))
  (αn (a (τ (S ...) e)))
  (μ (m ...))
  (m (a <= v))
  ((ρ χ) (a ...))
  (e ....
     a
     (rcv (x) e)
     (rcv (x) e [(timeout n) e]))
  (v n t (tuple v ...) a)
  (a (addr natural))
  (A ((any_1 ... hole any_2 ...) μ ρ χ))
  (E hole
     (goto s v ... E e ...)
     (send E e)
     (send v E)
     (begin E e ...)
     (let ([x E] [x e] ...) e)
     (match E [p e] ...)
     (tuple v ... E e ...)
     (primop v ... E e ...)))

(define (make-single-agent-config agent)
  (term (make-single-agent-config/mf ,agent)))

(define-metafunction csa-eval
  make-single-agent-config/mf : αn -> K
  [(make-single-agent-config/mf αn)
   ((αn) () (a) ())
   (where (a _) αn)])

(define handler-step
  (reduction-relation csa-eval
    #:domain K
    (--> (in-hole A (a ((S ...) (in-hole E (goto s v ..._n)))))
         (in-hole A (a ((S ...) (rcv (x_h) (subst-n e (x_s v) ...)))))
         (where (_ ... (define-state (s x_s ..._n) (x_h) e) _ ...) (S ...))
         Goto)

    ;; TODO: goto with timeout

    ;; let, match, begin, send, goto
    (==> (begin v e e_rest ...)
         (begin e e_rest ...)
         Begin1)
    (==> (begin v)
         v
         Begin2)

    ;; TODO: do the ρ/χ updates
    (--> ((any_a1 ... (a ((S ...) (in-hole E (send a_2 v)))) any_a2 ...)
          (any_packets ...)
          ρ χ)
         ((any_a1 ... (a ((S ...) (in-hole E v)))            any_a2 ...)
          (any_packets ... (a_2 <= v))
          ρ χ)
         Send)

    ;; TODO: let
    ;; TODO: match

    with
    [(--> (in-hole A (a ((S ...) (in-hole E old))))
          (in-hole A (a ((S ...) (in-hole E new)))))
     (==> old new)]))

(module+ test
  (define empty-A-context (term ((hole) () () ())))
  (define S1-def (term (define-state (S1 a b) (x) (begin a x (goto S1 b a)))))
  (check-not-false (redex-match csa-eval S S1-def))
  (check-not-false (redex-match csa-eval A empty-A-context))
  (define init-config
    (term (in-hole ,empty-A-context ((addr 1) ((,S1-def) (begin 'foo 'baz (goto S1 'bar 'foo)))))))
  (check-not-false (redex-match csa-eval K init-config))
  ;; begin1
  ;; begin2
  ;; goto
  ;; all the way through a goto, with begins

  (check-equal?
   (apply-reduction-relation* handler-step
                              init-config)
   (list (term (in-hole ,empty-A-context
                        ((addr 1) ((,S1-def) (rcv (x) (begin 'bar x (goto S1 'foo 'bar))))))))))

(define-metafunction csa-eval
  subst-n : e (x v) ... -> e
  [(subst-n e) e]
  [(subst-n e (x v) any_rest ...)
   (subst-n (subst e x v) any_rest ...)])

(define-metafunction csa-eval
  subst : e x v -> e
  [(subst x x v) v]
  [(subst x x_2 v) x]
  [(subst n x v) n]
  [(subst t x v) t]
  [(subst a x v) a]
  [(subst (spawn e S ...) self v) (spawn e S ...)]
  [(subst (spawn e S ...) x v)
    (spawn (subst e x v) (subst/S S x v) ...)]
  [(subst (goto s e ...) x v) (goto s (subst e x v) ...)]
  [(subst (send e_1 e_2) x v)
   (send (subst e_1 x v) (subst e_2 x v))]
  [(subst (begin e ...) x v) (begin (subst e x v) ...)]
  [(subst (let ([x_let e] ...) e_body) x v)
   (let ([x_let (subst e x v)] ...) e_body)
   (where (_ ... x _ ...) (x_let ...))] ; check that x is in the list of bound vars
  [(subst (let ([x_let e] ...) e_body) x v)
   (let ([x_let (subst e x v)] ...) (subst e_body x v))]
  [(subst (match e [p e_pat] ...) x v)
   (match (subst e x v) (subst/match-clause [p e_pat] x v) ...)]
  [(subst (tuple e ...) x v) (tuple (subst e x v) ...)]
  [(subst (rcv (x) e) x v) (rcv (x) e)]
  [(subst (rcv (x_h) e) x v) (rcv (x_h) (subst e x v))]
  [(subst (rcv (x) e [(timeout n) e_timeout]) x v) (rcv (x) e [(timeout n) e_timeout])]
  [(subst (rcv (x_h) e [(timeout n) e_timeout]) x v)
   (rcv (x_h) (subst e x v) [(timeout n) (subst e_timeout x v)])])

(define-metafunction csa-eval
  subst/match-clause : [p e] x v -> [p e]
  [(subst/match-clause [p e] x v)
   [p e]
   (side-condition (term (pattern-binds-var p x)))]
  [(subst/match-clause [p e] x v)
   [p (subst e x v)]])

(define-metafunction csa-eval
  pattern-binds-var : p x -> boolean
  [(pattern-binds-var * x) #f]
  [(pattern-binds-var x x) #t]
  [(pattern-binds-var x_1 x_2) #f]
  [(pattern-binds-var t x) #t]
  [(pattern-binds-var (tuple p ...) x)
   ,(ormap values (term ((pattern-binds-var p x) ...)))])

(module+ test
  (check-equal? (term (subst/match-clause [(tuple x y z) x] x 'foo))
                (term [(tuple x y z) x]))
  (check-equal? (term (subst/match-clause [(tuple a y z) x] x 'foo))
                (term [(tuple a y z) 'foo])))

(define-metafunction csa-eval
  subst/S : S x v -> S
  [(subst/S (define-state (s x_s ...) (x_h) e) x v)
   (define-state (s x_s ...) (x_h) e)
   (where (_ ... x _ ...) (x_s ... x_h))]
  [(subst/S (define-state (s x_s ...) (x_h) e) x v)
   (define-state (s x_s ...) (x_h) (subst e x v))]
  [(subst/S (define-state (s x_s ...) (x_h) e_1 [(timeout n) e_2]) x v)
   (define-state (s x_s ...) (x_h) e_1 [(timeout n) e_2])
   (where (_ ... x _ ...) (x_s ... x_h))]
  [(subst/S (define-state (s x_s ...) (x_h) e_1 [(timeout n) e_2]) x v)
   (define-state (s x_s ...) (x_h) (subst e_1 x v) [(timeout n) (subst e_2 x v)])])

(module+ test
  (check-equal? (term (subst 'foo x 'bar))
                (term 'foo))
  (check-equal? (term (subst a a 'foo))
                (term 'foo))
  (check-equal? (term (subst a b 'foo))
                (term a))
  (check-equal? (term (subst (goto s x y) x 'foo))
                (term (goto s 'foo y)))
  (check-equal? (term (subst (begin x y x) x 'foo))
                (term (begin 'foo y 'foo)))

  (check-equal? (term (subst-n (goto s x y z) (x 'foo) (y 'bar)))
                (term (goto s 'foo 'bar z)))
  ;; TODO: more tests
  )

;; Substitutes an external message into the config. Will throw an error if the address is not in the
;; set of receptionists.
(define-metafunction csa-eval
  inject-message : K a v -> K
  ;; TODO: do the case for rcv with timeout, too
  [(inject-message ((any_1 ... (a ((S ...) (rcv (x) e))) any_2 ...) μ (a_1 ... a a_2 ...) χ) a v)
   ((any_1 ... (a ((S ...) (subst e x v))) any_2 ...) μ (a_1 ... a a_2 ...) χ)]
  [(inject-message (_ _ ρ _) a v)
   (side-condition (not (member (term ρ) (term a))))
   (side-condition (error "Address ~s is not a receptionist address" (term a)))])

;; ---------------------------------------------------------------------------------------------------
;; APS

(define-extended-language aps
  csa-eval
  (e-hat (let-spec (x (goto s u ...) S-hat ...) e-hat)
         (goto s u ...)
         (with-outputs ([u po] ...) e-hat))
  (S-hat (define-state (s x ...) (ε -> e-hat) ...))
  (ε unobs
     p)
  (u x) ; arguments
  (po *
      x
      self
      t
      (tuple po ...)))

(define-extended-language aps-eval
  aps
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
  [(subst/aps/po (tuple po ...) x v-hat) (tuple (subst/aps/po po x v-hat) ...)])

;; ---------------------------------------------------------------------------------------------------
;; Type system helpers

(define-metafunction csa
  type-subst : τ X τ -> τ
  [(type-subst Nat _ _) Nat]
  [(type-subst (μ X τ_1) X τ_2)
   (μ X τ_1)]
  ;; TODO: do the full renaming here
  [(type-subst (μ X_1 τ_1) X_2 τ_2)
   (μ X_1 (type-subst τ_1 X_2 τ_2))]
  [(type-subst X X τ) τ]
  [(type-subst X_1 X_2 τ) X_1]
  [(type-subst t _ _) t]
  [(type-subst (Tuple τ ...) X τ_2)
   (Tuple (type-subst τ X τ_2) ...)]
  [(type-subst (Union τ ...) X τ_2)
   (Union (type-subst τ X τ_2) ...)]
  [(type-subst (Addr τ) X τ_2)
   (Addr (type-subst τ X τ_2))])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (csa-valid-config? c)
  (if (redex-match csa-eval K c) #t #f))

(define (aps-valid-instance? i)
  (if (redex-match aps-eval z i) #t #f))
