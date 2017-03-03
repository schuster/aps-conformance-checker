#lang racket

;; Concrete standard semantic domains for CSA, and associated functions

(provide
 csa-eval
 make-single-actor-config
 make-empty-queues-config
 csa-valid-program?
 csa-valid-type?
 csa-valid-config?
 csa-valid-receptionist-list?
 csa-config-receptionists
 csa-config-internal-addresses
 instantiate-prog
 instantiate-prog+bindings
 csa-address-strip-type
 csa-contains-address?)

;; ---------------------------------------------------------------------------------------------------

(require redex/reduction-semantics)

(module+ test
  (require rackunit))

;; ---------------------------------------------------------------------------------------------------
;; CSA

(define-language csa
  ;; A program P is a set of actors declared as spawn expressions (the spawn should be surround by a
  ;; let), with some declared names for the actors, receptionists, and externals. Instantiating the
  ;; program will assign addresses for each of these names and turn the program into its initial
  ;; configuration.
  (P (program
      (receptionists [x_receptionist τ] ...)
      (externals [x_external τ] ...)
      ;; NOTE: ; let-bound values and state args e should be x or v
      (actors [x (let ([x e] ...) (spawn any_loc τ (goto q e ...) Q ...))] ...)))
  (e (spawn any_loc τ e Q ...)
     (goto q e ...)
     (send e e)
     (begin e ... e)
     ;; REFACTOR: let should probably be syntactic sugar for a special kind of case statement
     (let ([x e] ...) e)
     (case e [(t x ...) e] ...)
     (variant t e ...)
     (record [l e] ...)
     (: e l) ; record lookup
     (! e [l e]) ; record (functional) update
     (fold τ e)
     (unfold τ e)
     (primop e ...)
     string
     x
     n
     (list e ...)
     (vector e ...)
     (hash [e e] ...)
     (for/fold ([x e]) ([x e]) e)
     (coerce e τ)) ; only used internally; needed for eviction when actor closes over other addresses
  (Q (define-state (q [x τ] ...) (x) e)
     (define-state (q [x τ] ...) (x) e [(timeout e) e]))
  (primop
   <
   <=
   >
   >=
   =
   mult
   /
   +
   -
   arithmetic-shift
   and
   or
   not
   random
   ceiling
   cons
   list-as-variant
   list-ref
   remove
   length
   vector-length
   vector-ref
   vector-take
   vector-drop
   vector-copy
   vector-append
   hash-ref
   hash-keys
   hash-values
   hash-remove
   hash-set
   hash-has-key?
   hash-empty?
   sort-numbers-descending
   ;; printf and abs-len for debugging only
   printf
   print-len)
  (x self
     variable-not-otherwise-mentioned )
  ((q t l) variable-not-otherwise-mentioned)
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
  (i (α μ ρ χ))
  (α ((a b) ...))
  (b ((Q ...) e)) ; behavior
  (μ (m ...))
  (m (a <= v))
  ((ρ χ) (τa ...))
  (e ....
     v)
  (v n
     (variant t v ...)
     (record [l v] ...)
     (folded τ v)
     τa
     string
     (list v ...)
     (vector v ...)
     (hash [v v] ...))
  (a (addr natural))
  (τa (τ a)) ; an address a able to carry messages of type τ
  )

;; ---------------------------------------------------------------------------------------------------
;; Instantiation

;; Instantiates the given program as a configuration by allocating fresh addresses and subsituting
;; them throughout the program as needed
(define (instantiate-prog prog)
  (term (instantiate-prog/mf ,prog)))

(define-metafunction csa-eval
  instantiate-prog/mf : P -> i
  [(instantiate-prog/mf P)
   i
   (where (i ([x a] ...)) (instantiate-prog+bindings/mf P))])

;; Instantiates the given program as a configuration by allocating fresh addresses and subsituting
;; them throughout the program as needed. Returns both the configuration and the set of bindings for
;; the allocated addresses.
(define (instantiate-prog+bindings prog)
  (term (instantiate-prog+bindings/mf ,prog)))

(define-metafunction csa-eval
  instantiate-prog+bindings/mf : P -> (i ([x τa] ...))
  [(instantiate-prog+bindings/mf
    (program (receptionists [x_receptionist _] ...)
             (externals     [x_external     τ_external] ...)
             (actors        [x_internal (let ([x_let (coerce e_let τ)] ...) e)] ...)))
   (i
    ([x_internal τa_internal] ... [x_external τa_external] ...))

   ;; 1. Generate addresses for internal and external actors
   (where (τa_internal ...) (generate-fresh-addresses/mf ((spawn-type/mf e) ...) ()))
   (where (τa_external ...) (generate-fresh-addresses/mf (τ_external ...) (τa_internal ...)))

   ;; 2. Do substitutions into spawn to get a behavior
   ;; NOTE: assuming for now we can ignore the type coercion automatically put in place
   (where ((v_let ...) ...) (((subst-n e_let
                                       [x_external τa_external] ...
                                       [x_internal τa_internal] ...) ...) ...))
   (where (b ...)
          ((spawn->behavior e
                            ([x_let v_let] ...
                             [x_internal τa_internal] ...
                             [x_external τa_external] ...)
                            τa_internal) ...))

   ;; 3. Construct the configuration
   (where ((_ a_internal) ...) (τa_internal ...))
   (where i
          [; actors
           ((a_internal b) ...)
           ; message store
           ()
           ; receptionists
           ((subst-n x_receptionist [x_internal τa_internal] ...) ...)
           ; externals
           (τa_external ...)])])

(define-metafunction csa-eval
  spawn->behavior : e ([x v] ...) τa -> b
  [(spawn->behavior e_spawn ([x_binding v_binding] ...) τa_self)
   b
   ;; 1. Substitute all non-self bindings
   (where (spawn _ _ e_goto Q ...) (subst-n e_spawn [x_binding v_binding] ...))
   ;; 2. Substitute the self-binding
   (where b (((subst-n/Q Q [self τa_self]) ...) (subst-n e_goto [self τa_self])))])

(module+ test
  (test-case "Instantiate program"
    (define the-prog
      `(program (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                (actors [a (let () (spawn 1 Nat      (goto S1)))]
                        [b (let () (spawn 2 (Record) (goto S2)))]
                        [c (let () (spawn 3 Nat      (goto S3)))])))
    (check-true (redex-match? csa-eval P the-prog))
    (check-equal?
     (instantiate-prog+bindings the-prog)
     `(
       ;; program config
       (
        ;; actors
        (
         ;; a
         ((addr 0) (() (goto S1)))
         ;; b
         ((addr 1) (() (goto S2)))
         ;; c
         ((addr 2) (() (goto S3)))
         )
        ;; messages
        ()
        ;; receptionists
        ((Nat (addr 0)) ((Record) (addr 1)))
        ;; externals
        ((String (addr 3)) ((Union) (addr 4))))
       ;; bindings
       ([a (Nat (addr 0))]
        [b ((Record) (addr 1))]
        [c (Nat (addr 2))]
        [d (String (addr 3))]
        [e ((Union) (addr 4))])))))

;; Returns a list containing one fresh address of the given type per given type τ, where the given
;; list of addresses indicates the existing set of allocated addresses.
(define-metafunction csa-eval
  generate-fresh-addresses/mf : (τ ...) (τa ...) -> (τa ...)
  [(generate-fresh-addresses/mf (τ ...) ((_ (addr natural)) ...))
   ,(map (lambda (type index) `(,type (addr ,(+ (term natural_next) index))))
         (term (τ ...))
         (build-list (length (term (τ ...))) values))
   (where natural_next ,(add1 (apply max -1 (term (natural ...)))))])

(module+ test
  (test-equal? "Fresh address generation"
    (term (generate-fresh-addresses/mf (Nat (Record) Nat)
                                       ((Nat (addr 1)) (Nat (addr 4)) (Nat (addr 2)))))
    `((Nat (addr 5)) ((Record) (addr 6)) (Nat (addr 7))))
  (test-equal? "Fresh address generation 2"
    (term (generate-fresh-addresses/mf (Nat (Record) Nat) ()))
    `((Nat (addr 0)) ((Record) (addr 1)) (Nat (addr 2)))))

;; ---------------------------------------------------------------------------------------------------
;; Testing helpers

(define (make-single-actor-config actor)
  (term (make-single-actor-config/mf ,actor)))

(define-metafunction csa-eval
  make-single-actor-config/mf : ((τ a) b) -> i
  [(make-single-actor-config/mf ((τ a) b))
   (((a b)) () ((τ a)) ())])

(define (make-empty-queues-config receptionists internal-actors)
  (term (make-empty-queues-config/mf ,receptionists ,internal-actors)))

(define-metafunction csa-eval
  make-empty-queues-config/mf : ((τa b) ...) ((τa b) ...) -> i
  [(make-empty-queues-config/mf (((τ_rec a_rec) b_receptionist) ...)
                                (((τ_int a_int) b_int) ...))
   (((a_rec b_receptionist) ... (a_int b_int) ...)
    ()
    ((τ_rec a_rec) ...)
    ())])

;; ---------------------------------------------------------------------------------------------------
;; Substitution

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
  [(subst τa x v) τa]
  [(subst string x v) string]
  [(subst (spawn any_loc τ e Q ...) self v) (spawn any_loc τ e Q ...)]
  [(subst (spawn any_loc τ e Q ...) x v)
    (spawn any_loc τ (subst e x v) (subst/Q Q x v) ...)]
  [(subst (goto q e ...) x v) (goto q (subst e x v) ...)]
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
  [(subst (fold τ e) x v) (fold τ (subst e x v))]
  [(subst (unfold τ e) x v) (unfold τ (subst e x v))]
  [(subst (record [l e] ...) x v) (record [l (subst e x v)] ...)]
  [(subst (variant t e ...) x v) (variant t (subst e x v) ...)]
  [(subst (primop e ...) x v) (primop (subst e x v) ...)]
  [(subst (list e ...) x v) (list (subst e x v) ...)]
  [(subst (vector e ...) x v) (vector (subst e x v) ...)]
  [(subst (hash [e_key e_val] ...) x v) (hash [(subst e_key x v) (subst e_val x v)] ...)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x_1 v)
   (for/fold ([x_1 (subst e_1 x_1 v)]) ([x_2 (subst e_2 x_1 v)]) e_3)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x_2 v)
   (for/fold ([x_1 (subst e_1 x_2 v)]) ([x_2 (subst e_2 x_2 v)]) e_3)]
  [(subst (for/fold ([x_1 e_1]) ([x_2 e_2]) e_3) x v)
   (for/fold ([x_1 (subst e_1 x v)]) ([x_2 (subst e_2 x v)]) (subst e_3 x v))]
  [(subst (coerce e τ) x v) (coerce (subst e x v) τ)])

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
  subst/Q : Q x v -> Q
  [(subst/Q (define-state (q [x_q τ_q] ...) (x_h) e) x v)
   (define-state (q [x_q τ_q] ...) (x_h) e)
   (where (_ ... x _ ...) (x_q ... x_h))]
  [(subst/Q (define-state (q [x_q τ_q] ...) (x_h) e) x v)
   (define-state (q [x_q τ_q] ...) (x_h) (subst e x v))]
  [(subst/Q (define-state (q [x_q τ_q] ...) (x_h) e_1 [(timeout e_3) e_2]) x v)
   (define-state (q [x_q τ_q] ...) (x_h) e_1 [(timeout e_3) e_2])
   (where (_ ... x _ ...) (x_q ... x_h))]
  [(subst/Q (define-state (q [x_q τ_q] ...) (x_h) e_1 [(timeout e_3) e_2]) x v)
   (define-state (q [x_q τ_q] ...) (x_h) (subst e_1 x v) [(timeout e_3) (subst e_2 x v)])])

(define-metafunction csa-eval
  subst-n/Q : Q [x v] ... -> Q
  [(subst-n/Q Q) Q]
  [(subst-n/Q Q [x v] any_rest ...)
   (subst-n/Q (subst/Q Q x v) any_rest ...)])

(module+ test
  (check-equal? (term (subst 0 x 1))
                (term 0))
  (check-equal? (term (subst a a 0))
                (term 0))
  (check-equal? (term (subst a b 0))
                (term a))
  (check-equal? (term (subst (goto q x y) x 0))
                (term (goto q 0 y)))
  (check-equal? (term (subst (begin x y x) x 0))
                (term (begin 0 y 0)))

  (check-equal? (term (subst-n (goto q x y z) (x 0) (y 1)))
                (term (goto q 0 1 z)))
  (check-equal? (term (subst (+ a b) a 1))
                (term (+ 1 b)))
  (check-equal? (term (subst (record [r1 x] [r2 y]) x 2))
                (term (record [r1 2] [r2 y])))
  (check-equal? (term (subst (: rec field) rec (record [field 1])))
                (term (: (record [field 1])  field)))
  (check-equal? (term (subst (! rec [field 2]) rec (record [field 1])))
                (term (! (record [field 1]) [field 2])))
  (check-equal?
   (term (subst-n/Q (define-state (S1 [a Nat]) (m) (+ a b)) [a 1] [b 2] [m 3]))
   (term (define-state (S1 [a Nat]) (m) (+ a 2))))

  (check-equal? (term (subst (fold Nat x) x 5)) (term (fold Nat 5)))
  (check-equal? (term (subst (fold Nat y) x 5)) (term (fold Nat y)))
  (check-equal? (term (subst (unfold Nat x) x 5)) (term (unfold Nat 5))))

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (csa-valid-program? p) (redex-match csa-eval P p))

(define (csa-valid-type? t) (redex-match? csa-eval τ t))

(define (csa-valid-config? c)
  (and (redex-match csa-eval i c)
       (not (check-duplicates (csa-config-internal-addresses c)))))

(define (csa-valid-receptionist-list? l)
  (redex-match csa-eval (τa ...) l))

;; Returns true if the expression contains any address
(define (csa-contains-address? e)
  (term (csa-contains-address?/mf ,e)))

(define-metafunction csa
  csa-contains-address?/mf : any -> boolean
  [(csa-contains-address?/mf (addr _)) #t]
  [(csa-contains-address?/mf (any ...))
   ,(ormap csa-contains-address? (term (any ...)))]
  [(csa-contains-address?/mf _) #f])

(module+ test
  (test-true "csa-contains-address?"
    (csa-contains-address? (term ((Nat (addr 1)) (Nat (addr 2))))))

  (test-false "csa-contains-address?"
    (csa-contains-address? (term ((abc 1 Nat) (def 2 Nat)))))

  (test-true "csa-contains-address?"
    (csa-contains-address? (term (((abc) (Nat (addr 1))) ())))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (csa-config-internal-addresses config)
  (redex-let* csa-eval ([(((a _) ...) _ _ _) config])
    (term (a ...))))

(module+ test
  (redex-let* csa-eval ([b_1 (term (() (goto A)))]
                        [b_2 (term (() (goto B (Nat (addr 3)) (Nat (addr 4)))))]
                        [α (term ([(addr 0) b_1]
                                  [(addr 1) b_2]))]
                        [i (term (α () () ()))])
    (check-equal? (csa-config-internal-addresses (term i))
                  (term ((addr 0) (addr 1))))))

(define (csa-config-receptionists config)
  (third config))

;; Returns the type given in a spawn expression
(define-metafunction csa-eval
  spawn-type/mf : (spawn any_loc τ e Q ...) -> τ
  [(spawn-type/mf (spawn _ τ _ ...))
   τ])

;; Returns just the address part of a typed address
(define (csa-address-strip-type a)
  (second a))

(module+ test
  (check-equal?
   (redex-let csa-eval ([τa (term (Nat (addr 1)))])
     (csa-address-strip-type (term τa)))
   (term (addr 1))))
