#lang racket

;; Concrete semantic domains for APS (specification language), and associated functions

(provide
 aps-eval
 aps-valid-spec?
 aps-valid-config?
 aps-config-obs-interface

 ;; Testing helpers
 make-spec
 make-exclusive-spec
 instantiate-configs)

;; ---------------------------------------------------------------------------------------------------
;; APS

(require
 redex/reduction-semantics
 "csa.rkt")

(module+ test
  (require rackunit))

(define-extended-language aps
  csa-eval
  (spec
   (specification (receptionists [x_rec τ] ...)
                  (externals [x_ext τ] ...)
                  UNKNOWN
                  ([x τ] ...)
                  (goto φ x ...)
                  Φ ...)
   (specification (receptionists [x_rec τ] ...)
                  (externals [x_ext τ] ...)
                  [x τ]
                  ([x τ] ...)
                  (goto φ x ...)
                  Φ ...))
  (Φ (define-state (φ x ...) (pt -> (f ...) (goto φ x ...)) ...))
  ;; effects
  (f (obligation u po)
     (fork (goto φ u ...) Φ ...))
  ;; trigger patterns
  (pt unobs
     p)
  (u x) ; arguments
  ;; input patterns
  (p *
     x
     (variant t p ...)
     (record [l p] ...))
  ;; output patterns
  (po *
      (or po ...)
      (fork (goto φ u ...) Φ ...)
      self
      (variant t po ...)
      (record [l po] ...))
  ;; state name
  (φ variable-not-otherwise-mentioned))

(define-extended-language aps-eval
  aps
  ;; Specification configuration contains the observed environment interface σ, unobserved environment
  ;; interface (a ...), current state, state definitions, and obligation map
  (s (σ (a ...) (goto φ u ...) (Φ ...) O))
  (σ a UNKNOWN)
  (O ([a po ...] ...))
  ;; arguments in aps-eval can be instantiated (as addresses)
  (u .... a))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps-eval
  subst/aps-eval/u : u x a -> u
  [(subst/aps-eval/u x x a) a]
  [(subst/aps-eval/u x_2 x a) x_2]
  [(subst/aps-eval/u a_2 x a) a_2])

(define-metafunction aps-eval
  subst-n/aps-eval/u : u [x a] ... -> u
  [(subst-n/aps-eval/u u) u]
  [(subst-n/aps-eval/u u [x a] any_rest ...)
   (subst-n/aps-eval/u (subst/aps-eval/u u x a) any_rest ...)])

(define-metafunction aps-eval
  subst/aps-eval/po : po x a -> po
  [(subst/aps-eval/po * x a) *]
  [(subst/aps-eval/po (or po ...) x a) (or (subst/aps-eval/po po x a) ...)]
  [(subst/aps-eval/po (fork any_goto any_s-defs ...) self _)
   (fork any_goto any_s-defs ...)]
  [(subst/aps-eval/po (fork (goto φ u ...) Φ ...) x a)
   (fork (goto φ (subst/aps-eval/u u x a) ...)
               (subst/aps-eval/Φ Φ x a) ...)]
  [(subst/aps-eval/po self self a) a]
  [(subst/aps-eval/po self _ _) self]
  [(subst/aps-eval/po (variant t po ...) x a)
   (variant t (subst/aps-eval/po po x a) ...)]
  [(subst/aps-eval/po (record t [l po] ...) x a)
   (record [l (subst/aps-eval/po po x a)] ...)])

(define-metafunction aps-eval
  subst-n/aps-eval/Φ : Φ (x a) ... -> Φ
  [(subst-n/aps-eval/Φ Φ) Φ]
  [(subst-n/aps-eval/Φ Φ (x a) any_rest ...)
   (subst-n/aps-eval/Φ (subst/aps-eval/Φ Φ x a) any_rest ...)])

(define-metafunction aps-eval
  subst/aps-eval/Φ : Φ x a -> Φ
  [(subst/aps-eval/Φ (define-state (φ any_1 ... x any_2 ...) any_trans ...) x a)
   (define-state (φ any_1 ... x any_2 ...) any_trans ...)]
  [(subst/aps-eval/Φ (define-state (φ x_φ ...) any_trans ...) x a)
   (define-state (φ x_φ ...) (subst/aps-eval/trans any_trans x a) ...)])

(define-metafunction aps-eval
  subst/aps-eval/trans : (pt -> (f ...) (goto φ u ...)) x a -> (pt -> (f ...) (goto φ u ...))
  [(subst/aps-eval/trans (p -> (f ...) (goto φ u ...)) x a)
   (p -> (f ...) (goto φ u ...))
   (judgment-holds (pattern-binds-var p x))]
  [(subst/aps-eval/trans (pt -> (f ...) (goto φ u ...)) x a)
   (pt -> ((subst/aps-eval/f f x a) ...) (goto φ (subst/aps-eval/u u x a) ...))])

(define-metafunction aps-eval
  subst/aps-eval/f : f x a -> f
  [(subst/aps-eval/f (obligation u po) x a)
   (obligation (subst/aps-eval/u u x a) (subst/aps-eval/po po x a))]
  [(subst/aps-eval/f (fork (goto φ u ...) Φ ...) x a)
   (fork (goto φ (subst/aps-eval/u u x a) ...)
         (subst/aps-eval/Φ Φ x a) ...)])

(define-judgment-form aps-eval
  #:mode (pattern-binds-var I I)
  #:contract (pattern-binds-var p x)
  [------------
   (pattern-binds-var x x)]

  [(side-condition ,(ormap (lambda (p) (judgment-holds (pattern-binds-var ,p x)))
                           (term (p ...))))
   ----------
   (pattern-binds-var (variant t p ...) x)]

  [(side-condition ,(ormap (lambda (p) (judgment-holds (pattern-binds-var ,p x)))
                           (term (p ...))))
   ----------
   (pattern-binds-var (reocrd [l p] ...) x)])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

(define (aps-valid-spec? φ) (redex-match? aps spec φ))

(define (aps-valid-config? c)
  (if (redex-match aps-eval s c) #t #f))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

;; Returns the observable interface of the given configuration
(define (aps-config-obs-interface config)
  (redex-let* aps-eval ([(σ _ ...) config])
    (term σ)))

(module+ test
  (test-case "config observable interface"
    (define spec (term ((addr 2 Nat)
                        ()
                        (goto A)
                        ((define-state (A)))
                        ())))
    (check-not-false (redex-match aps-eval s spec))
    (check-equal? (aps-config-obs-interface spec) (term (addr 2 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-exclusive-spec defs-state-and-addr)
  (make-spec defs-state-and-addr null))

(define (make-spec defs-state-and-addr receptionists)
  (redex-let* aps-eval ([((Φ ...) (goto φ a_arg ...) σ) defs-state-and-addr]
                        [(a_rec ...) receptionists]
                        [s (term (σ (a_rec ...) (goto φ a_arg ...) (Φ ...) ([a_arg] ...)))])
              (term s)))

;; Instantiates the given program and specification as configurations, allocating fresh addresses for
;; each actor in the program and substituting them throughout both configurations as needed.
(define (instantiate-configs prog spec)
  (term (instantiate-configs/mf ,prog ,spec)))

(define-metafunction aps-eval
  instantiate-configs/mf : P spec -> (i s)
  [(instantiate-configs/mf P spec)
   (i s)
   ;; NOTE: the receptionists and externals for the spec (including their declared types) should be
   ;; subsets of those for the program
   (where (i ([x a] ...)) ,(instantiate-prog+bindings (term P)))
   (where s (instantiate-spec/mf spec ([x a] ...)))])

(module+ test
  (test-case "Instantiate test"
    (define the-prog
      `(program (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                (actors [a (let () (spawn 1 Nat      (goto S1)))]
                        [b (let () (spawn 2 (Record) (goto S2)))]
                        [c (let () (spawn 3 Nat      (goto S3)))])))
    (define the-spec
      `(specification (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                      UNKNOWN
                      ()
                      (goto S1)))
    (check-true (redex-match? csa-eval P the-prog))
    (check-true (redex-match? aps spec the-spec))
    (check-equal?
     (instantiate-configs the-prog the-spec)
     `(
       ;; program config
       (
        ;; actors
        (
         ;; a
         ((addr 0 Nat) (() (goto S1)))
         ;; b
         ((addr 1 (Record)) (() (goto S2)))
         ;; c
         ((addr 2 Nat) (() (goto S3)))
         )
        ;; messages
        ()
        ;; receptionists
        ((addr 0 Nat) (addr 1 (Record)))
        ;; externals
        ((addr 3 String) (addr 4 (Union))))
       ;; spec config
       (;; obs interface
        UNKNOWN
        ;; unobserved environment interface
        ()
        ;; current state
        (goto S1)
        ;; state defs
        ()
        ;; output commitments
        ())))))

;; Instantiates the given spec as a specification configuration, using the given bindings as allocated
;; addresses.
(define-metafunction aps-eval
  instantiate-spec/mf : spec ([x a] ...) -> s
  [(instantiate-spec/mf (specification (receptionists [x_rec _] ...)
                                       (externals [x_cont _] ...)
                                       any_obs-int
                                       ([x_unobs τ_unobs] ...)
                                       (goto φ x_arg ...)
                                       Φ ...)
                        ([x_binding a_binding] ...))
   (; observed environment interface
    σ
    ;; unobserved environment interface
    ((addr natural_unobs τ_unobs) ...)
    ;; current state
    (goto φ a_state-arg ...)
    ; states
    ((subst-n/aps-eval/Φ Φ [x_binding a_binding] ...) ...)
    ;; output commitment map
    ([a_state-arg] ...))
   (where ((addr natural_unobs _) ...) ((subst-n/aps-eval/u x_unobs [x_binding a_binding] ...) ...))
   (where σ (resolve-spec-obs-int/mf any_obs-int ([x_binding a_binding] ...)))
   (where (a_state-arg ...) ((subst-n/aps-eval/u x_arg [x_binding a_binding] ...) ...))])

(module+ test
  (test-case "instantiate spec"
      (define the-spec
      `(specification (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                      UNKNOWN
                      ()
                      (goto S1 d)))
      (check-true (redex-match? aps spec the-spec))
      (check-equal?
       (term (instantiate-spec/mf ,the-spec
                                  ([a (addr 0 Nat)]
                                   [b (addr 1 (Record))]
                                   [c (addr 2 Nat)]
                                   [d (addr 3 String)]
                                   [e (addr 4 (Union))])))
       `(;; self-address
         UNKNOWN
         ;; unobserved environment interface
         ()
         ;; current state
         (goto S1 (addr 3 String))
         ;; state defs
         ()
         ;; obligation map
         ([(addr 3 String)])))))

;; Resolves the observed environment interface address of a specification (either UNKNOWN or [x τ]) to
;; either UNKNOWN or an address, using the given name/address bindings as necessary
(define-metafunction aps-eval
  resolve-spec-obs-int/mf : any ([x a] ...) -> σ
  [(resolve-spec-obs-int/mf UNKNOWN _) UNKNOWN]
  [(resolve-spec-obs-int/mf [x τ] ([x_binding a_binding] ...))
   (addr natural τ)
   (where (addr natural _) (subst-n/aps-eval/u x [x_binding a_binding] ...))])

(module+ test
  (test-equal? "resolve-spec-obs-int on known address"
    (term (resolve-spec-obs-int/mf (ping-server (Addr (Union (Pong))))
                                   ((ping-server (addr 0 (Addr (Union (Pong))))))))
    (term (addr 0 (Addr (Union (Pong)))))))

