#lang racket

;; Models the grammar for APS (Actor Protocol Specifications)

(provide csa
         csa-eval
         inject-message
         make-single-actor-config
         make-empty-queues-config
         single-actor-prog->config
         handler-step
         type-subst
         csa-valid-config?
         csa-valid-receptionist-list?
         csa-config-receptionists
         csa-config-internal-addresses
         same-address-without-type?)

;; ---------------------------------------------------------------------------------------------------

(require redex/reduction-semantics)

(module+ test
  (require rackunit))

;; ---------------------------------------------------------------------------------------------------
;; CSA

(define-language csa
  (e (spawn any_loc τ e S ...)
     (goto s e ...)
     (send e e)
     (begin e ... e)
     ;; TODO: let should probably be syntactic sugar for a special kind of case statement
     (let ([x e] ...) e)
     (case e [(t x ...) e] ...)
     ;; TODO: come up with vocab for tagged unions: is a "variant" the full type, or one branch of the
     ;; type, or what?
     (variant t e ...)
     (record [l e] ...)
     (: e l) ; record lookup
     (! e [l e]) ; record (functional) update
     (primop e ...)
     string
     x
     n
     (list e ...)
     (vector e ...)
     (hash)
     (for/fold ([x e]) ([x e]) e))
  (S (define-state (s [x τ] ...) (x) e)
     (define-state (s [x τ] ...) (x) e [(timeout n) e]))
  (primop
   <
   <=
   >
   >=
   =
   /
   +
   -
   and
   or
   not
   random
   ceiling
   cons
   list-ref
   length
   vector-length
   vector-ref
   vector-take
   vector-copy
   vector-append
   hash-ref
   hash-set
   hash-has-key?
   sort-numbers-descending
   ;; printf and abs-len for debugging only
   printf
   print-len)
  (x self
     variable-not-otherwise-mentioned )
  ((s t l) variable-not-otherwise-mentioned)
  (n natural)
  (τ Nat
     String
     (minfixpt X τ)
     X
     (Union [t τ ...] ...)
     (Record [l τ] ...)
     (Addr τ)
     (Listof τ)
     (Vectorof τ)
     (Hash τ τ))
  (X variable-not-otherwise-mentioned))

(define-extended-language csa-eval
  csa
  (K (α μ ρ χ))
  (α (αn ...))
  (αn (a ((S ...) e)))
  (μ (m ...))
  (m (a <= v))
  ((ρ χ) (a ...))
  (e ....
     a
     (rcv (x) e)
     (rcv (x) e [(timeout n) e]))
  (v n
     (variant t v ...)
     (record [l v] ...)
     a
     string
     (list v ...)
     (vector v ...)
     (hash [v v] ...))
  (a (addr natural τ)) ; only used for the initial receptionist lists for now
  (A ((any_1 ... hole any_2 ...) μ ρ χ))
  (E hole
     (goto s v ... E e ...)
     (send E e)
     (send v E)
     (begin E e ...)
     (let ([x v] ... [x E] [x e] ...) e)
     (case E _ ...)
     (variant t v ... E e ...)
     (record [l v] ... [l E] [l e] ...)
     (: E l)
     (! E [l e])
     (! v [l E])
     (primop v ... E e ...)
     (list v ... E e ...)
     (vector v ... E e ...)
     (for/fold ([x E]) ([x e]) e)
     (for/fold ([x v]) ([x E]) e)))

(define (make-single-actor-config actor)
  (term (make-single-actor-config/mf ,actor)))

(define (single-actor-prog->config prog address)
  (redex-let csa-eval ([(let ([x v] ...) (spawn τ e S ...)) prog])
             (term (,address (((subst-n/S S [self ,address] [x v] ...) ...)
                              (subst-n e [self ,address] [x v] ...))))))

(define-metafunction csa-eval
  make-single-actor-config/mf : αn -> K
  [(make-single-actor-config/mf αn)
   ((αn) () (a) ())
   (where (a _) αn)])

(define (make-empty-queues-config receptionists internal-actors)
  (term (make-empty-queues-config/mf ,receptionists ,internal-actors)))

(define-metafunction csa-eval
  make-empty-queues-config/mf : (αn ...) (αn ...) -> K
  [(make-empty-queues-config/mf (αn_receptionist ...) (αn_internal ...))
   ((αn_receptionist ... αn_internal ...)
    ()
    (a_receptionist ...)
    ())
   (where ((a_receptionist _) ...) (αn_receptionist ...))])

(define handler-step
  (reduction-relation csa-eval
    #:domain K
    (--> (in-hole A (a ((S ...) (in-hole E (goto s v ..._n)))))
         (in-hole A (a ((S ...) (rcv (x_h) (subst-n e (x_s v) ...)))))
         (where (_ ... (define-state (s [x_s τ_s] ..._n) (x_h) e) _ ...) (S ...))
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
    ;; TODO: case
    ;; TODO: record lookup

    with
    [(--> (in-hole A (a ((S ...) (in-hole E old))))
          (in-hole A (a ((S ...) (in-hole E new)))))
     (==> old new)]))

(module+ test
  (define empty-A-context (term ((hole) () () ())))
  (define S1-def (term (define-state (S1 [a Nat] [b Nat]) (x) (begin a x (goto S1 b a)))))
  (check-not-false (redex-match csa-eval S S1-def))
  (check-not-false (redex-match csa-eval A empty-A-context))
  (define init-config
    (term (in-hole ,empty-A-context ((addr 1 Nat) ((,S1-def) (begin 0 2 (goto S1 1 0)))))))
  (check-not-false (redex-match csa-eval K init-config))
  ;; begin1
  ;; begin2
  ;; goto
  ;; all the way through a goto, with begins

  (check-equal?
   (apply-reduction-relation* handler-step
                              init-config)
   (list (term (in-hole ,empty-A-context
                        ((addr 1 Nat) ((,S1-def) (rcv (x) (begin 1 x (goto S1 0 1))))))))))

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
  [(subst a x v) a]
  [(subst string x v) string]
  [(subst (spawn any_loc τ e S ...) self v) (spawn any_loc τ e S ...)]
  [(subst (spawn any_loc τ e S ...) x v)
    (spawn any_loc τ (subst e x v) (subst/S S x v) ...)]
  [(subst (goto s e ...) x v) (goto s (subst e x v) ...)]
  [(subst (send e_1 e_2) x v)
   (send (subst e_1 x v) (subst e_2 x v))]
  [(subst (begin e ...) x v) (begin (subst e x v) ...)]
  [(subst (let ([x_let e] ...) e_body) x v)
   (let ([x_let (subst e x v)] ...) e_body)
   (where (_ ... x _ ...) (x_let ...))] ; check that x is in the list of bound vars
  [(subst (let ([x_let e] ...) e_body) x v)
   (let ([x_let (subst e x v)] ...) (subst e_body x v))]
  [(subst (case e [(t x_clause ...) e_clause] ...) x v)
   (case (subst e x v) (subst/case-clause [(t x_clause ...) e_clause] x v) ...)]
  [(subst (record [l e] ...) x v) (record [l (subst e x v)] ...)]
  [(subst (: e_1 l) x v) (: (subst e_1 x v) l)]
  [(subst (! e_1 [l e_2]) x v) (! (subst e_1 x v) [l (subst e_2 x v)])]
  [(subst (record [l e] ...) x v) (record [l (subst e x v)] ...)]
  [(subst (variant t e ...) x v) (variant t (subst e x v) ...)]
  [(subst (primop e ...) x v) (primop (subst e x v) ...)]
  [(subst (list e ...) x v) (list (subst e x v) ...)]
  [(subst (vector e ...) x v) (vector (subst e x v) ...)]
  [(subst (hash) x v) (hash)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x_1 v)
   (for/fold ([x_1 (subst e_1 x_1 v)]) ([x_2 (subst e_2 x_1 v)]) e_3)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x_2 v)
   (for/fold ([x_1 (subst e_1 x_2 v)]) ([x_2 (subst e_2 x_2 v)]) e_3)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x v)
   (for/fold ([x_1 (subst e_1 x v)]) ([x_2 (subst e_2 x v)]) (subst e_3 x v))]
  [(subst (rcv (x) e) x v) (rcv (x) e)]
  [(subst (rcv (x_h) e) x v) (rcv (x_h) (subst e x v))]
  [(subst (rcv (x) e [(timeout n) e_timeout]) x v) (rcv (x) e [(timeout n) e_timeout])]
  [(subst (rcv (x_h) e [(timeout n) e_timeout]) x v)
   (rcv (x_h) (subst e x v) [(timeout n) (subst e_timeout x v)])])

(define-metafunction csa-eval
  subst/case-clause : [(t x ...) e] x v -> [(t x ...) e]
  [(subst/case-clause [(t x_1 ... x x_2 ...) e] x v)
   [(t x_1 ... x x_2 ...)  e]]
  [(subst/case-clause [(t x_other ...) e] x v)
   [(t x_other ...) (subst e x v)]])

(module+ test
  (check-equal? (term (subst/case-clause [(Cons p) (begin p x)] p 0))
                (term [(Cons p) (begin p x)]))
  (check-equal? (term (subst/case-clause [(Cons p) (begin p x)] x 0))
                (term [(Cons p) (begin p 0)]))

  (check-equal? (term (subst (case q [(A) (+ x y)] [(B x z) (+ x z)]) x 5))
                (term (case q [(A) (+ 5 y)] [(B x z) (+ x z)]))))

(define-metafunction csa-eval
  subst/S : S x v -> S
  [(subst/S (define-state (s [x_s τ_s] ...) (x_h) e) x v)
   (define-state (s [x_s τ_s] ...) (x_h) e)
   (where (_ ... x _ ...) (x_s ... x_h))]
  [(subst/S (define-state (s [x_s τ_s] ...) (x_h) e) x v)
   (define-state (s [x_s τ_s] ...) (x_h) (subst e x v))]
  [(subst/S (define-state (s [x_s τ_s] ...) (x_h) e_1 [(timeout n) e_2]) x v)
   (define-state (s [x_s τ_s] ...) (x_h) e_1 [(timeout n) e_2])
   (where (_ ... x _ ...) (x_s ... x_h))]
  [(subst/S (define-state (s [x_s τ_s] ...) (x_h) e_1 [(timeout n) e_2]) x v)
   (define-state (s [x_s τ_s] ...) (x_h) (subst e_1 x v) [(timeout n) (subst e_2 x v)])])

(define-metafunction csa-eval
  subst-n/S : S [x v] ... -> S
  [(subst-n/S S) S]
  [(subst-n/S S [x v] any_rest ...)
   (subst-n/S (subst/S S x v) any_rest ...)])

(module+ test
  (check-equal? (term (subst 0 x 1))
                (term 0))
  (check-equal? (term (subst a a 0))
                (term 0))
  (check-equal? (term (subst a b 0))
                (term a))
  (check-equal? (term (subst (goto s x y) x 0))
                (term (goto s 0 y)))
  (check-equal? (term (subst (begin x y x) x 0))
                (term (begin 0 y 0)))

  (check-equal? (term (subst-n (goto s x y z) (x 0) (y 1)))
                (term (goto s 0 1 z)))
  (check-equal? (term (subst (+ a b) a 1))
                (term (+ 1 b)))
  (check-equal? (term (subst (record [r1 x] [r2 y]) x 2))
                (term (record [r1 2] [r2 y])))
  (check-equal? (term (subst (: rec field) rec (record [field 1])))
                (term (: (record [field 1])  field)))
  (check-equal? (term (subst (! rec [field 2]) rec (record [field 1])))
                (term (! (record [field 1]) [field 2])))
  (check-equal?
   (term (subst-n/S (define-state (S1 [a Nat]) (m) (+ a b)) [a 1] [b 2] [m 3]))
   (term (define-state (S1 [a Nat]) (m) (+ a 2))))
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
;; Type system helpers

(define-metafunction csa
  type-subst : τ X τ -> τ
  [(type-subst Nat _ _) Nat]
  [(type-subst (minfixpt X τ_1) X τ_2)
   (minfixpt X τ_1)]
  ;; TODO: do the full renaming here
  [(type-subst (μ X_1 τ_1) X_2 τ_2)
   (μ X_1 (type-subst τ_1 X_2 τ_2))]
  [(type-subst X X τ) τ]
  [(type-subst X_1 X_2 τ) X_1]
  [(type-subst (Union [t τ ...] ...) X τ_2)
   (Union [t (type-subst τ X τ_2) ...] ...)]
  ;; TODO: Record
  [(type-subst (Addr τ) X τ_2)
   (Addr (type-subst τ X τ_2))])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (csa-valid-config? c)
  (and (redex-match csa-eval K c)
       (not (check-duplicates (csa-config-internal-addresses c)))))

(define (csa-valid-receptionist-list? l)
  (redex-match csa-eval (a ...) l))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (csa-config-internal-addresses config)
  (redex-let* csa-eval ([(((a _) ...) _ _ _) config])
              (term (a ...))))

(define (csa-config-receptionists config)
  (third config))

;; ---------------------------------------------------------------------------------------------------
;; Address matching

(define-judgment-form csa-eval
  #:mode (same-address-without-type?/j I I)
  #:contract (same-address-without-type?/j a a)
  [------
   (same-address-without-type?/j (addr natural _) (addr natural _))])

(define (same-address-without-type? a1 a2)
  (judgment-holds (same-address-without-type?/j ,a1 ,a2)))

(module+ test
  (test-true "Same address"
             (same-address-without-type? '(addr 1 (Union)) '(addr 1 (Union [A]))))
  (test-true "Same address 2"
             (same-address-without-type? '(addr 1 (Union)) '(addr 1 (Union))))
  (test-false "Not same address"
              (same-address-without-type? '(addr 2 (Union)) '(addr 1 (Union))))
  (test-false "Not same address 2"
              (same-address-without-type? '(addr 2 (Union)) '(addr 1 (Union [A])))))
