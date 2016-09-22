#lang racket

;; Concrete semantic domains for APS (specification language), and associated functions

(provide
 aps-eval
 aps-valid-spec?
 aps-valid-config?
 aps-config-only-instance-address

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
                  S-hat ...
                  (goto s x ...))
   (specification (receptionists [x_rec τ] ...)
                  (externals [x_ext τ] ...)
                  [x τ]
                  ([x τ] ...)
                  S-hat ...
                  (goto s x ...)))
  (e-hat (spawn-spec ((goto s u ...) S-hat ...) e-hat)
         (goto s u ...)
         (with-outputs ([u po] ...) e-hat))
  (S-hat (define-state (s x ...) (ε -> e-hat) ...))
  (ε unobs
     p)
  (u x) ; arguments
  (p *
     x
     (variant t p ...)
     (record [l p] ...))
  (po *
      (spawn-spec (goto s u ...) S-hat ...)
      self
      (variant t po ...)
      (record [l po] ...)))

(define-extended-language aps-eval
  aps
  (Σ ((z ...) (a ...) O))
  (O ((a po ...) ...))
  (z ((S-hat ...) e-hat σ))
  (σ a UNKNOWN)
  (u .... a))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps-eval
  subst-n/aps-eval : e-hat (x a) ... -> e-hat
  [(subst-n/aps-eval e-hat) e-hat]
  [(subst-n/aps-eval e-hat (x a) any_rest ...)
   (subst-n/aps-eval (subst/aps-eval e-hat x a) any_rest ...)])

(define-metafunction aps-eval
  subst/aps-eval : e-hat x a -> e-hat
  [(subst/aps-eval (goto s u ...) x a)
   (goto s (subst/aps-eval/u u x a) ...)]
  [(subst/aps-eval (with-outputs ([u po] ...) e-hat) x a)
   (with-outputs ([(subst/aps-eval/u u x a) (subst/aps-eval/po po x a)] ...)
     (subst/aps-eval e-hat x a))]
  [(subst/aps-eval (spawn-spec ((goto s u ...) S-hat ...) e-hat) x a)
   (spawn-spec ((subst/aps-eval (goto s u ...) x a)
                (subst/aps-eval/S-hat S-hat x a) ...)
               (subst/aps-eval e-hat x a))])

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
  [(subst/aps-eval/po (spawn-spec any_goto any_s-defs ...) self _)
   (spawn-spec any_goto any_s-defs ...)]
  [(subst/aps-eval/po (spawn-spec (goto s u ...) S-hat ...) x a)
   (spawn-spec (goto s (subst/aps-eval/u u x a) ...)
               (subst/aps-eval/S-hat S-hat x a) ...)]
  [(subst/aps-eval/po self self a) a]
  [(subst/aps-eval/po self _ _) self]
  [(subst/aps-eval/po (variant t po ...) x a)
   (variant t (subst/aps-eval/po po x a) ...)]
  [(subst/aps-eval/po (record t [l po] ...) x a)
   (record [l (subst/aps-eval/po po x a)] ...)])

(define-metafunction aps-eval
  subst-n/aps-eval/S-hat : S-hat (x a) ... -> S-hat
  [(subst-n/aps-eval/S-hat S-hat) S-hat]
  [(subst-n/aps-eval/S-hat S-hat (x a) any_rest ...)
   (subst-n/aps-eval/S-hat (subst/aps-eval/S-hat S-hat x a) any_rest ...)])

(define-metafunction aps-eval
  subst/aps-eval/S-hat : S-hat x a -> S-hat
  [(subst/aps-eval/S-hat (define-state (s any_1 ... x any_2 ...) any_trans ...) x a)
   (define-state (s any_1 ... x any_2 ...) any_trans ...)]
  [(subst/aps-eval/S-hat (define-state (s x_s ...) any_trans ...) x a)
   (define-state (s x_s ...) (subst/aps-eval/trans any_trans x a) ...)])

(define-metafunction aps-eval
  subst/aps-eval/trans : (ε -> e-hat) x a -> (ε -> e-hat)
  [(subst/aps-eval/trans (p -> e-hat) x a)
   (p -> e-hat)
   (judgment-holds (pattern-binds-var p x))]
  [(subst/aps-eval/trans (ε -> e-hat) x a)
   (ε -> (subst/aps-eval e-hat x a))])

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

(define (aps-valid-spec? s) (redex-match? aps spec s))

(define (aps-valid-config? c)
  (if (redex-match aps-eval Σ c) #t #f))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps-config-only-instance-address config)
  (redex-let* aps-eval ([((z) _ _) config]
                        [(_ _ σ) (term z)])
              (term σ)))

(module+ test
  (test-case "config only instance address"
    (define spec (term (([((define-state (A))) (goto A) (addr 2 Nat)]) () ())))
    (check-not-false (redex-match aps-eval Σ spec))
    (check-equal? (aps-config-only-instance-address spec) (term (addr 2 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-exclusive-spec instance)
  (make-spec instance null))

(define (make-spec instance receptionists)
  (redex-let* aps-eval ([z instance]
                        [(a_rec ...) receptionists]
                        [(_ (goto _ a ...) _) (term z)]
                        [Σ (term ((z) (a_rec ...) ((a) ...)))])
              (term Σ)))

;; Instantiates the given program and specification as configurations, allocating fresh addresses for
;; each actor in the program and substituting them throughout both configurations as needed.
(define (instantiate-configs prog spec)
  (term (instantiate-configs/mf ,prog ,spec)))

(define-metafunction aps-eval
  instantiate-configs/mf : P spec -> (K Σ)
  [(instantiate-configs/mf P spec)
   (K Σ)
   ;; NOTE: the receptionists and externals for the spec (including their declared types) should be
   ;; subsets of those for the program
   (where (K ([x a] ...)) ,(instantiate-prog+bindings (term P)))
   (where Σ (instantiate-spec/mf spec ([x a] ...)))])

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
       (;; instances
        (
         ;; instance 1
         (;; state defs
          ()
          ;; exp
          (goto S1)
          ;; self-address
          UNKNOWN
          ))
        ;; unobserved environment interface
        ()
        ;; output commitments
        ())))))

;; Instantiates the given spec as a specification configuration, using the given bindings as allocated
;; addresses.
(define-metafunction aps-eval
  instantiate-spec/mf : spec ([x a] ...) -> Σ
  [(instantiate-spec/mf (specification (receptionists [x_rec _] ...)
                                       (externals [x_cont _] ...)
                                       any_obs-int
                                       ([x_unobs τ_unobs] ...)
                                       S-hat ...
                                       (goto s x_arg ...))
                        ([x_binding a_binding] ...))
   (;; instances
    (;; instance 1
     (; states
      ((subst-n/aps-eval/S-hat S-hat [x_binding a_binding] ...) ...)
      ; exp
      (subst-n/aps-eval (goto s x_arg ...) [x_binding a_binding] ...)
      ; address
      σ))
    ;; unobserved environment interface
    ((addr natural_unobs τ_unobs) ...)
    ;; output commitment map
    ())
   (where ((addr natural_unobs _) ...) ((subst-n/aps-eval/u x_unobs [x_binding a_binding] ...) ...))
   (where σ (resolve-spec-obs-int/mf any_obs-int ([x_binding a_binding] ...)))])

(module+ test
  (test-case "instantiate spec"
      (define the-spec
      `(specification (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                      UNKNOWN
                      ()
                      (goto S1)))
      (check-true (redex-match? aps spec the-spec))
      (check-equal?
       (term (instantiate-spec/mf ,the-spec
                                  ([a (addr 0 Nat)]
                                   [b (addr 1 (Record))]
                                   [c (addr 2 Nat)]
                                   [d (addr 3 String)]
                                   [e (addr 4 (Union))])))
       `(;; instances
         (;; instance 1
          (;; state defs
           ()
           ;; exp
           (goto S1)
           ;; self-address
           UNKNOWN
           ))
          ;; unobserved environment interface
          ()
          ;; output commitments
          ()))))

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

