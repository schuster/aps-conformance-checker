#lang racket

;; Concrete semantic domains for APS (specification language), and associated functions

(provide
 aps-eval
 aps-valid-spec?
 aps-valid-psm?

 ;; Testing helpers
 make-psm
 make-anonymous-psm
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
                  mr
                  (goto φ x ...)
                  Φ ...))
  ;; monitored receptionist clause
  (mr (mon-receptionist x)
      no-mon-receptionist)
  (Φ (define-state (φ x ...) (pt -> f ... (goto φ x ...)) ...))
  ;; effects
  (f (obligation u po)
     (fork (goto φ u ...) Φ ...))
  ;; trigger patterns
  (pt free
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
      (fork-addr (goto φ u ...) Φ ...)
      (delayed-fork-addr (goto φ) Φ ...)
      self
      (variant t po ...)
      (record [l po] ...))
  ;; state name
  (φ variable-not-otherwise-mentioned))

(define-extended-language aps-eval
  aps
  ;; Specification configuration contains the observed receptionists ρ_obs, unobserved receptionists
  ;; ρ_unobs, current state, state definitions, and obligation map
  (s ((mk ...) (mk ...) (goto φ mk ...) (Φ ...) O))
  (O ([mk po] ...))
  ;; arguments in aps-eval can be instantiated (as addresses)
  (u .... mk))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps-eval
  subst/aps-eval/u : u x mk -> u
  [(subst/aps-eval/u x x mk) mk]
  [(subst/aps-eval/u x_2 x mk) x_2]
  [(subst/aps-eval/u mk_2 x mk) mk_2])

(define-metafunction aps-eval
  subst-n/aps-eval/u : u [x mk] ... -> u
  [(subst-n/aps-eval/u u) u]
  [(subst-n/aps-eval/u u [x mk] any_rest ...)
   (subst-n/aps-eval/u (subst/aps-eval/u u x mk) any_rest ...)])

;; Judgment holds if the given pattern binds the given variable
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

(define (aps-valid-psm? some-term)
  (redex-match? aps-eval s some-term))

(module+ test
  (test-false "invalid PSM" (aps-valid-psm? `()))
  (test-true "valid PSM" (aps-valid-psm? `[(1) (2 3) (goto A) ((define-state (A))) ([2 *])])))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-psm defs-state-and-mon-rec)
  (redex-let* aps-eval ([((Φ ...) (goto φ mk_arg ...) mk_mon-rec) defs-state-and-mon-rec]
                        [s (term [(mk_mon-rec)
                                  ,(remove-duplicates (term (mk_arg ...)))
                                  (goto φ mk_arg ...)
                                  (Φ ...)
                                  ()])])
    (term s)))

(module+ test
  (test-case "make-psm"
    (define request-response-state-defs
      `((define-state (Always)
          [response-target -> [obligation response-target *] (goto Always)])))
    (check-equal?
     (make-psm
      (term
       (,request-response-state-defs
        (goto Always)
        1)))
     `[(1) () (goto Always) ,request-response-state-defs ()])))

(define (make-anonymous-psm defs-and-state)
  (redex-let* aps-eval ([((Φ ...) (goto φ mk_arg ...)) defs-and-state]
                        [s (term [()
                                  ,(remove-duplicates (term (mk_arg ...)))
                                  (goto φ mk_arg ...)
                                  (Φ ...)
                                  ()])])
    (term s)))

(module+ test
  (test-case "make-anonymous-psm"
    (define self-reveal-state-defs
      `((define-state (Init r)
          [free -> [obligation r self] (goto Running)])
        (define-state (Running)
          [r -> [obligation r *] (goto Running)])))
    (check-equal?
     (make-anonymous-psm (term [,self-reveal-state-defs (goto Init 1)]))
     `[() (1) (goto Init 1) ,self-reveal-state-defs ()])))

;; Instantiates the given program and specification as configurations, allocating fresh addresses for
;; each actor in the program and substituting the markers on those addresses throughout both
;; configurations as needed.
(define (instantiate-configs prog spec)
  (term (instantiate-configs/mf ,prog ,spec)))

(define-metafunction aps-eval
  instantiate-configs/mf : P spec -> (i s)
  [(instantiate-configs/mf P spec)
   (i s)
   ;; NOTE: the receptionists and externals for the spec should be subsets of those for the program,
   ;; and their declared types should match their program analogs
   (where (i ([x_rec mk_rec] ...) ([x_ext mk_ext] ...))
          ,(instantiate-prog+bindings (term P)))
   (where s (instantiate-spec/mf spec ([x_rec mk_rec] ...) ([x_ext mk_ext] ...)))])

(module+ test
  (test-case "Instantiate test"
    (define the-prog
      `(program (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                (let-actors ([a (let () (spawn 1 Nat      (goto S1)))]
                             [b (let () (spawn 2 (Record) (goto S2)))]
                             [c (let () (spawn 3 Nat      (goto S3)))])
                            a b)))
    (define the-spec
      `(specification (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                      no-mon-receptionist
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
         ((addr 1 0) (() (goto S1)))
         ;; b
         ((addr 2 0) (() (goto S2)))
         ;; c
         ((addr 3 0) (() (goto S3)))
         )
        ;; messages
        ()
        ;; receptionists
        ((Nat (marked (addr 1 0) 0)) ((Record) (marked (addr 2 0) 1))))
       ;; spec config
       (;; monitored receptionists
        ()
        ;; monitored externals
        ()
        ;; current state
        (goto S1)
        ;; state defs
        ()
        ;; obligations
        ())))))

;; Instantiates the given spec as a specification configuration, using the given receptionist and
;; external marker-bindings.
(define-metafunction aps-eval
  instantiate-spec/mf : spec ([x mk] ...) ([x mk] ...) -> s
  [(instantiate-spec/mf (specification (receptionists [x_rec _] ...)
                                       (externals [x_cont _] ...)
                                       mr
                                       (goto φ x_arg ...)
                                       Φ ...)
                        ([x_rec mk_rec] ...)
                        ([x_ext mk_ext] ...))
   (;; monitired receptionist
    (resolve-mon-receptionist mr [x_rec mk_rec] ...)
    ;; monitored externals
    ,(remove-duplicates (term (mk_state-arg ...)))
    ;; current state
    (goto φ mk_state-arg ...)
    ;; states
    (Φ ...)
    ;; obligations
    ())
   (where (mk_state-arg ...) ((subst-n/aps-eval/u x_arg [x_ext mk_ext] ...) ...))])

(module+ test
  (test-case "instantiate spec"
      (define the-spec
      `(specification (receptionists [a Nat] [b (Record)]) (externals [d String] [e (Union)])
                      no-mon-receptionist
                      (goto S1 d)))
      (check-true (redex-match? aps spec the-spec))
      (check-equal?
       (term (instantiate-spec/mf ,the-spec
                                  ([a 1]
                                   [b 2])
                                  ([d 3]
                                   [e 4])))
       `(;; observed receptionists
         ()
         ;; unobserved receptionists
         (3)
         ;; current statep
         (goto S1 3)
         ;; state defs
         ()
         ;; obligation map
         ())))

  (test-equal? "Instantiation does not substitute into state definitions"
    (term (instantiate-spec/mf
           (specification (receptionists) (externals [a Nat])
             no-mon-receptionist
             (goto A)
             (define-state (A)
               [free -> (goto B a)]))
           ()
           ([a 1])))
    (term [() () (goto A) ((define-state (A) [free -> (goto B a)])) ()])))

;; Gets the monitored receptionist marker (if any) by substituting in the given receptionist markers
;; to the mr-clause
(define-metafunction aps-eval
  resolve-mon-receptionist : mr [x mk] ... -> (mk ...)
  [(resolve-mon-receptionist (mon-receptionist x) [x_rec mk_rec] ...)
   ((subst-n/aps-eval/u x [x_rec mk_rec] ...))]
  [(resolve-mon-receptionist no-mon-receptionist _ ...)
   ()])

(module+ test
  (test-equal? "resolve-mon-receptionist 1"
    (term (resolve-mon-receptionist (mon-receptionist a) [a 1] [b 2] [c 3]))
    (term (1)))
  (test-equal? "resolve-mon-receptionist 2"
    (term (resolve-mon-receptionist (mon-receptionist b) [a 1] [b 2] [c 3]))
    (term (2)))
  (test-equal? "resolve-mon-receptionist: no-mon-receptionist"
    (term (resolve-mon-receptionist no-mon-receptionist [a 1] [b 2] [c 3]))
    (term ())))
