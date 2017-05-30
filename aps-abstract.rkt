#lang racket

;; Abstract semantic domains for APS (specification language), and associated functions

(provide
 ;; Required by conformance checker
 aps#-config-obs-receptionists
 aps#-config-unobs-receptionists
 aps#-config-singleton-commitments
 aps#-config-many-of-commitments
 aps#-matching-steps
 aps#-resolve-outputs
 aps#-abstract-config
 split-spec
 aps#-blur-config
 canonicalize-pair
 try-rename-address
 reverse-rename-address
 aps#-config-has-commitment?
 aps#-completed-no-transition-config?
 evict-pair
 ;; needed for widening
 aps#-config<=

 ;; Required only for testing
 aps#

 ;; Required by conformance checker for blurring
 aps#-relevant-external-addrs

 ;; Testing helpers
 make-s#
 aps#-make-no-transition-config

 ;; Debugging helpers
 spec-config-without-state-defs)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "aps.rkt"
 "csa.rkt"
 "csa-abstract.rkt"
 "list-helpers.rkt"
 "sexp-helpers.rkt")

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt"))

(define-union-language aps-eval-with-csa#
  aps-eval csa#)

(define-extended-language aps#
  aps-eval-with-csa#
  (s# (ρ#_obs ρ#_unobs (goto φ u ...) (Φ ...) O#))
  (ρ# (τa# ...))
  (u .... a#ext)
  (O# ((a#ext (m po) ...) ...))
  (match-fork (ρ#_obs (goto φ) (Φ ...))))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

(define (aps#-abstract-config spec-config internal-addresses)
  ;; Doing a redex-let here just to add a codomain contract
  (redex-let* aps# ([any_1 (term (aps#-abstract-config/mf ,spec-config ,internal-addresses))]
                    [s# (abstract-obligations (term any_1))])
             (term s#)))

(define-metafunction aps#
  aps#-abstract-config/mf : any (a ...) -> any
  [(aps#-abstract-config/mf a (a_internal ...))
   ,(csa#-abstract-address (term a) (term (a_internal ...)))]
  [(aps#-abstract-config/mf (any ...) (a ...))
   ((aps#-abstract-config/mf any (a ...)) ...)]
  [(aps#-abstract-config/mf any _) any])

(module+ test
  (check-equal?
   (aps#-abstract-config (term (((Nat (addr 0)))
                                ()
                                (goto A (addr 1))
                                ((define-state (A x) (* -> () (goto A x))))
                                (((addr 2) * * (record)))))
                         (term ((addr 0))))
   (term (((Nat (init-addr 0)))
          ()
          (goto A (obs-ext 1))
          ((define-state (A x) (* -> () (goto A x))))
          (((obs-ext 2) [many *] [single (record)]))))))

(define (abstract-obligations config)
  (match-define (list obs unobs goto states obligation-map) config)
  (define abstracted-obligations
    (for/list ([entry obligation-map])
      (let loop ([patterns (cdr entry)]
                 [abstracted-patterns null])
        (match patterns
          [(list) (cons (first entry) (reverse abstracted-patterns))]
          [(list this-pattern other-patterns ...)
           (if (member this-pattern other-patterns)
               (loop (filter (negate (curry equal? this-pattern)) other-patterns)
                     (cons `(many ,this-pattern) abstracted-patterns))
               (loop other-patterns
                     (cons `(single ,this-pattern) abstracted-patterns)))]))))
  (list obs unobs goto states abstracted-obligations))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps#/u : u (x a#) ... -> u
  [(subst-n/aps#/u u) u]
  [(subst-n/aps#/u u (x a#) any_rest ...)
   (subst-n/aps#/u (subst/aps#/u u x a#) any_rest ...)])

(define-metafunction aps#
  subst/aps#/u : u x a# -> u
  [(subst/aps#/u x x a#) a#]
  [(subst/aps#/u x_2 x a#) x_2]
  [(subst/aps#/u a#_2 x a#) a#_2])

(define-metafunction aps#
  subst/aps#/trans : (pt -> (f ...) (goto φ u ...)) x a# -> (pt -> (f ...) (goto φ u ...))
  [(subst/aps#/trans (p -> (f ...) (goto φ u ...)) x a#)
   (p -> (f ...) (goto φ u ...))
   (judgment-holds (pattern-binds-var p x))]
  [(subst/aps#/trans (pt -> (f ...) (goto φ u ...)) x a#)
   (pt -> ((subst/aps#/f f x a#) ...) (goto φ (subst/aps#/u u x a#) ...))])

(define-metafunction aps#
  subst-n/aps#/f : f (x a#) ... -> f
  [(subst-n/aps#/f f) f]
  [(subst-n/aps#/f f (x a#) any_rest ...)
   (subst-n/aps#/f (subst/aps#/f f x a#) any_rest ...)])

(define-metafunction aps#
  subst/aps#/f : f x a# -> f
  [(subst/aps#/f (obligation u po) x a#)
   (obligation (subst/aps#/u u x a#) (subst/aps#/po po x a#))]
  [(subst/aps#/f (fork (goto φ u ...) Φ ...) x a#)
   (fork (goto φ (subst/aps#/u u x a#) ...) Φ ...)])

(define-metafunction aps#
  subst/aps#/po : po x a# -> po
  [(subst/aps#/po * _ _) *]
  [(subst/aps#/po (or po ...) x a#) (or (subst/aps#/po po x a#) ...)]
  [(subst/aps#/po (fork (goto φ u ...) Φ ...) x a#)
   (fork (goto φ (subst/aps#/u u x a#) ...)
         Φ ...)]
  [(subst/aps#/po (delayed-fork (goto φ) Φ ...) x a#)
   (delayed-fork (goto φ) Φ ...)]
  [(subst/aps#/po self _ _) self]
  [(subst/aps#/po (variant t po ...) x a#) (variant t (subst/aps#/po po x a#) ...)]
  [(subst/aps#/po (record [l po] ...) x a#) (record [l (subst/aps#/po po x a#)] ...)])

(module+ test
  (test-equal? "Simple subst/aps#/f test"
    (term (subst/aps#/f [fork (goto S1 x)
                              (define-state (S1 y x) [* -> () (goto S2 y)])
                              (define-state (S2 y) [* -> ([obligation y *]) (goto S2 y)])]
                        x
                        (obs-ext 1)))
    (term [fork (goto S1 (obs-ext 1))
                (define-state (S1 y x) [* -> () (goto S2 y)])
                (define-state (S2 y) [* -> ([obligation y *]) (goto S2 y)])]))

  (test-equal? "Substitute into goto in an output obligation fork"
    (term (subst/aps#/f [obligation (obs-ext 0) (variant A (fork (goto S x)))] x (obs-ext 1)))
    (term [obligation (obs-ext 0) (variant A (fork (goto S (obs-ext 1))))]))

  (test-equal? "Substitute for fork and delayed-fork"
    (term (subst/aps#/f [obligation x (variant A (fork (goto B y)) (delayed-fork (goto C)))]
                        y
                        (obs-ext 1)))
    (term [obligation x (variant A (fork (goto B (obs-ext 1))) (delayed-fork (goto C)))])))

(define-judgment-form aps#
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
;; Transition selection

;; Returns the syntax for each transition of the FSM in the spec config
(define (config-current-transitions config)
  (term (config-current-transitions/mf ,config)))

;; FIX: deal with the case where the pattern variables shadow the state variables
(define-metafunction aps#
  config-current-transitions/mf : s# -> ((pt -> (f ...) (goto φ u ...)) ...)
  [(config-current-transitions/mf
    (_
     _
     (goto φ a# ...)
     (_ ... (define-state (φ x ...) (pt -> (f ...) (goto φ_trans u_trans ...)) ...) _ ...)
     _))
   ((pt ->
        ((subst-n/aps#/f f (x a#) ...) ...)
        (goto φ_trans (subst-n/aps#/u u_trans (x a#) ...) ...)) ...
    ;; Note that we include the "null"/no-step transition
    (unobs -> () (goto φ a# ...)))])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; s# bool trigger -> ([s# (s#_spawn ...)] ...)
;;
;; Returns all spec configs that can possibly be reached in one step by transitioning from the given
;; trigger, also returning spec configs spawned during that transition
(define (aps#-matching-steps spec-config from-observer? trigger)
  (define results
   (remove-duplicates
    (filter
     values
     (map (lambda (t) (attempt-transition spec-config t from-observer? trigger))
          ;; Remove the free-output transitions: these would cause the checker to make many "bad
          ;; guesses" about what conforms to what, and the outputs they use can always be used for
          ;; other transitions.
          (filter (negate (curryr transition-free-output-info (aps#-config-current-state spec-config)))
                  (config-current-transitions spec-config))))))
  (when (null? results)
    (error 'aps#-matching-steps
           "The trigger ~s (from-observer: ~s) has no way to transition in spec config ~s"
           trigger from-observer? (spec-config-without-state-defs spec-config)))
  results)

(module+ test
  (test-equal? "Null step is possible"
               (aps#-matching-steps
                (make-s# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                #f
                (term (timeout/empty-queue (init-addr 0))))
               (list
                (list (make-s# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                      null)))

  (test-equal? "Multiple copies of output commitments are merged"
               (aps#-matching-steps
                (make-s# (term ((define-state (A r) [* -> ((obligation r *)) (goto A r)])))
                         (term (goto A (obs-ext 0)))
                         null
                         (term (((obs-ext 0) (single *)))))
                #t
                (term (external-receive (init-addr 0) (* Nat))))
               (list
                (list
                 (make-s# (term ((define-state (A r) [* -> ((obligation r *)) (goto A r)])))
                          (term (goto A (obs-ext 0)))
                          null
                          (term (((obs-ext 0) (many *)))))
                 null)))

  (test-exn "No match for a trigger leads to exception"
    (lambda (exn) #t)
    (lambda ()
      (aps#-matching-steps
       (make-s# (term ((define-state (A r))))
                (term (goto A (obs-ext 0)))
                null
                (term (((obs-ext 0)))))
       #t
       (term (external-receive (init-addr 0) (* Nat))))))

  (test-equal? "Spec observes address but neither saves it nor has obligations for it"
    (aps#-matching-steps
     (make-s# `((define-state (A) [r -> () (goto A)]))
              `(goto A)
              null
              null)
     #t
     `(external-receive (init-addr 0) (Nat (obs-ext 1))))
    (list `[,(make-s# `((define-state (A) [r -> () (goto A)]))
                      `(goto A)
                      null
                      `([(obs-ext 1)]))
            ()]))

  (test-equal? "Unobserved address not tracked in obligation map"
    (aps#-matching-steps
     (make-s# `((define-state (A) [r -> () (goto A)]))
              `(goto A)
              null
              null)
     #f
     `(external-receive (init-addr 0) (Nat (obs-ext 1))))
    (list `[,(make-s# `((define-state (A) [r -> () (goto A)]))
                      `(goto A)
                      null
                      null)
            ()]))

  (test-equal? "Address matched by wildcard not tracked in obligation map"
    (aps#-matching-steps
     (make-s# `((define-state (A) [* -> () (goto A)]))
              `(goto A)
              null
              null)
     #t
     `(external-receive (init-addr 0) (Nat (obs-ext 1))))
    (list `[,(make-s# `((define-state (A) [* -> () (goto A)]))
                      `(goto A)
                      null
                      null)
            ()])))

;; s# spec-state-transition bool trigger -> [s# (s# ...)] or #f
;;
;; Returns the config updated by running the given transition, if it can be taken from the given
;; trigger, along with all configs spawned in the transition, or #f if the transition is not possible
;; from this trigger
(define (attempt-transition config transition from-observer? trigger)
  (match (match-trigger from-observer?
                        trigger
                        (aps#-config-obs-receptionists config)
                        (aps#-transition-trigger transition))
    [#f #f]
    [(list bindings ...)
     (match-define (list new-obligations pre-configs)
       (perform (subst-into-effects (aps#-transition-effects transition) bindings)
                (merge-receptionists (aps#-config-obs-receptionists config)
                                     (aps#-config-unobs-receptionists config))))
     (define updated-obligation-map
       (term
        (add-commitments
         ,(observe-addresses-from-subst
           (aps#-config-commitment-map config) bindings)
         ,@new-obligations)))
     (define stepped-current-pre-config
       (term (,(aps#-config-obs-receptionists config)
              ,(aps#-config-unobs-receptionists config)
              ,(subst-into-goto (aps#-transition-goto transition) bindings)
              ,(aps#-config-state-defs config)
              ())))
     (dist stepped-current-pre-config pre-configs updated-obligation-map)]))

(module+ test
  (test-equal? "Transition should put observed no-commitment addresses in commitment map"
    (attempt-transition
     `((((Addr Nat) (init-addr 0)))
       ()
       (goto A)
       ((define-state (A) [r -> () (goto A)]))
       ())
     `[r -> () (goto A)]
     #t
     `(external-receive (init-addr 0) (Nat (obs-ext 1))))
    (list
     `((((Addr Nat) (init-addr 0)))
       ()
       (goto A)
       ((define-state (A) [r -> () (goto A)]))
       ([(obs-ext 1)]))
     `()))

  (test-case "Immediate fork pattern transition"
    (define fork-pattern `(fork (goto Z y) (define-state (Z y) [* -> () (goto Z y)])))
    (check-equal?
     (attempt-transition
      `(([(Addr Nat) (init-addr 1)])
        ([String (init-addr 2)])
        (goto A (obs-ext 1))
        ((define-state (A x) [y -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ;; check for captured and uncaptured addresses, too
        ([(obs-ext 1)]
         [(obs-ext 3) (many *)]))
      `[y -> ([obligation (obs-ext 1) ,fork-pattern]) (goto B)]
      #t
      `(external-receive (init-addr 1) ((Addr Nat) (obs-ext 2))))
     (list
      `(([(Addr Nat) (init-addr 1)])
        ([String (init-addr 2)])
        (goto B)
        ((define-state (A x) [y -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ([(obs-ext 3) (many *)]))
      (list
       `(()
         ([(Addr Nat) (init-addr 1)] [String (init-addr 2)])
         (goto Z (obs-ext 2))
         ((define-state (Z y) [* -> () (goto Z y)]))
         ([(obs-ext 2)]
          [(obs-ext 1) (single self)]))))))

  (test-case "Delayed fork pattern transition"
    (define fork-pattern `(delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)])))
    (check-equal?
     (attempt-transition
      `(([(Addr Nat) (init-addr 1)])
        ([String (init-addr 2)])
        (goto A (obs-ext 1))
        ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ;; check for captured and uncaptured addresses, too
        ([(obs-ext 1)]
         [(obs-ext 2)]
         [(obs-ext 3) (many *)]))
      `[* -> ([obligation (obs-ext 1) ,fork-pattern]) (goto B)]
      #t
      `(external-receive (init-addr 1) ((Addr Nat) (obs-ext 2))))
     (list
      `(([(Addr Nat) (init-addr 1)])
        ([String (init-addr 2)])
        (goto B)
        ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ([(obs-ext 1) (single ,fork-pattern)]
         [(obs-ext 2)]
         [(obs-ext 3) (many *)]))
      null))))

;; (f ...) ([x a#] ...) -> (f ...)
;;
;; Substitutes the given bindings into the given effects
(define (subst-into-effects effects bindings)
  (redex-let aps# ([([x a#] ...) bindings])
    (for/list ([effect effects])
      (term (subst-n/aps#/f ,effect [x a#] ...)))))

;; (goto state x ...) ([x a#] ...) -> (goto state a ...)
;;
;; Substitutes the given bindings into the given specification goto expression
(define (subst-into-goto goto bindings)
  (redex-let aps# ([([x a#] ...) bindings]
                   [(goto φ u ...) goto])
    (term (goto φ (subst-n/aps#/u u [x a#] ...) ...))))

;; (f ...) ρ -> (([a# po] ...) (ς ...))
;;
;; Performs the given effects in the context of the given receptionist interface, returning new
;; obligations and forked pre-configurations
(define (perform effects receptionists)
  (for/fold ([results (list null null)])
            ([effect effects])
    (match-define (list obls-so-far pre-configs-so-far) results)
    (match effect
      [`(obligation ,address ,pattern)
       (match-define (list post-extract-pattern extracted-pre-configs)
         (extract pattern receptionists address))
       (list (cons `[,address ,post-extract-pattern] obls-so-far)
             (append pre-configs-so-far extracted-pre-configs))]
      [`(fork ,goto ,state-defs ...)
       (list obls-so-far
             (cons `(() ,receptionists ,goto ,state-defs ()) pre-configs-so-far))])))

(module+ test
  (test-equal? "perform 1"
    (perform
     (list `[obligation (obs-ext 1)
                        (fork (goto Z (obs-ext 2)) (define-state (Z a) [* -> () (goto Z a)]))])
     `([Nat (init-addr 1)]
       [String (init-addr 2)]))
    `(([(obs-ext 1) self])
      ([()
        ([Nat (init-addr 1)]
         [String (init-addr 2)])
        (goto Z (obs-ext 2))
        ((define-state (Z a) [* -> () (goto Z a)]))
        ((obs-ext 1))])))

  (test-equal? "perform delayed-fork obligation"
    (perform
     (list `[obligation (obs-ext 1)
                        (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))])
     `([Nat (init-addr 1)]
       [String (init-addr 2)]))
    `(([(obs-ext 1) (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))])
      ()))

  (test-equal? "perform fork"
    (perform (list `[fork (goto A (obs-ext 1))])
             '())
    `(() ([() () (goto A (obs-ext 1)) () ()]))))

;; po ρ a# -> (po, (ς ...))
;;
;; Extracts all forks from the given pattern that is an obligation on the given address, replacing
;; those patterns with the "self" pattern and creating pre-configurations for each fork using the
;; given receptionists as the unobs receptionists
(define (extract pattern receptionists addr)
  (define (extract-sub-patterns sub-patterns make-pattern)
    (match-define (list `[,extracted-pats ,pre-configs] ...)
      (map (curryr extract receptionists addr) sub-patterns))
    (list (make-pattern extracted-pats) (append* pre-configs)))
  (match pattern
    [`* (list pattern null)]
    [`(or ,pats ...)
     (extract-sub-patterns pats (lambda (pats) `(or ,@pats)))]
    [`(variant ,tag ,pats ...)
     (extract-sub-patterns pats (lambda (pats) `(variant ,tag ,@pats)))]
    [`(record [,fields ,pats] ...)
     (extract-sub-patterns
      pats
      (lambda (pats) `(record ,@(map (lambda (f p) `[,f ,p]) fields pats))))]
    [`(fork ,goto ,state-defs ...)
     (list 'self `([() ,receptionists ,goto ,state-defs (,addr)]))]
    [`(delayed-fork ,_ ,_ ...) (list pattern null)]
    ['self (list pattern null)]))

(module+ test
  (test-equal? "extract 1"
    (extract `(or (fork (goto A (obs-ext 1))) (fork (goto B (obs-ext 2))))
             `([Nat (init-addr 1)])
             `(obs-ext 3))
    `[(or self self)
      ([() ([Nat (init-addr 1)]) (goto A (obs-ext 1)) () ((obs-ext 3))]
       [() ([Nat (init-addr 1)]) (goto B (obs-ext 2)) () ((obs-ext 3))])])

  (test-equal? "extract fork"
    (extract `(fork (goto A (obs-ext 1)) (define-state (A x)))
             `([Nat (init-addr 1)])
             `(obs-ext 3))
    `[self
      ([()
        ([Nat (init-addr 1)])
        (goto A (obs-ext 1))
        ((define-state (A x)))
        ((obs-ext 3))])])

  (test-equal? "extract delayed-fork"
    (extract `(delayed-fork (goto B) (define-state (B)) (define-state (C)))
             `()
             `(obs-ext 2))
    `[(delayed-fork (goto B) (define-state (B)) (define-state (C)))
      ()]))

;; ς (ς ...) O# -> (s# (s# ...))
;;
;; As described in the dissertation, distributes the obligations in the obligation map to each
;; pre-configuration according to the external addresses "relevant" to each pre-config (determined by
;; the state arguments on that configuration and any extra addresses set in the pre-config). Static
;; constraints on the specification ensure that every observed external address is relevant to at most
;; one spec config.
;;
;; The dist function described in the dissertation assigns obligations non-deterministically if the
;; address is not relevant in any pre-config. Here we use the strategy of assigning them to the
;; "current" config by default.
(define (dist current-pre-config forked-pre-configs obligation-map)
  (define-values (remaining-obligation-map forked-configs)
   (for/fold ([obligation-map obligation-map]
              [forked-configs null])
             ([pre-config forked-pre-configs])
     (match-define (list obs-receptionists unobs-receptionists goto state-defs relevants) pre-config)
     (match-define (list remaining-obligation-map forked-map)
       (fork-commitment-map obligation-map (append (externals-in goto) relevants)))
     ;; The new unobs receptionists are *all* receptionists from the parent config, plus the
     ;; observable receptionists of the other forks
     (values remaining-obligation-map
             (cons (term (,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,forked-map))
                   forked-configs))))
  (match current-pre-config
    [`(,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,_)
     (list `(,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,remaining-obligation-map)
           forked-configs)]))

(module+ test
  (test-equal? "Degenerate dist case"
               (dist (term (() () (goto A) ((define-state (A))) ())) null null)
               (list (term (() () (goto A) ((define-state (A))) ())) null))

  (test-equal? "Basic dist case"
    (dist (term (() () (goto A) ((define-state (A))) ()))
          (list `[() () (goto B (obs-ext 2)) ((define-state (B r))) ()])
          (term ([(obs-ext 1) (single *)] [(obs-ext 2) (single (record))])))
    (list (term (() () (goto A) ((define-state (A))) ([(obs-ext 1) (single *)])))
          (list (term (() () (goto B (obs-ext 2)) ((define-state (B r))) ([(obs-ext 2) (single (record))]))))))

  (test-equal? "Dist with extra relevant address"
    (dist (term (() () (goto A (obs-ext 1)) () ()))
          (list (term (() () (goto B) () ((obs-ext 2)))))
          (term ([(obs-ext 1) (single *)]
                 [(obs-ext 2) (many *)])))
    (list (term (() () (goto A (obs-ext 1)) () ([(obs-ext 1) (single *)])))
          (list (term (() () (goto B) () ([(obs-ext 2) (many *)])))))))

;; O# (a# ...) -> (O#_old O#_new)
;;
;; Moves entries from the given obligation map whose address is in the given list and creates a new
;; obligation map from that list
(define (fork-commitment-map commitment-map addresses)
  (term (fork-commitment-map/mf ,commitment-map () ,addresses)))

;; Takes all entries from the first O# that match an address in the given list and moves it to the
;; second O#
(define-metafunction aps#
  fork-commitment-map/mf : O# O# (a#ext ...) -> (O# O#)
  [(fork-commitment-map/mf O#_current O#_new ())
   (O#_current O#_new)]
  [(fork-commitment-map/mf O#_current (any_fork-entries ...) (a#ext any_rest ...))
   (fork-commitment-map/mf O#_updated (any_fork-entries ... (a#ext any_pulled ...)) (any_rest ...))
   (where (O#_updated (any_pulled ...)) (O#-pull O#_current a#ext))])

(define-metafunction aps#
  O#-pull : O# a#ext -> (O# ([m po] ...))
  [(O#-pull (any_1 ... (a#ext any_com ...) any_2 ...) a#ext)
   ((any_1 ... any_2 ...) (any_com ...))]
  [(O#-pull O# a#ext) (O# ())])

(module+ test
  (check-equal?
   (fork-commitment-map
    (term (((obs-ext 1) (single *))
           ((obs-ext 2))
           ((obs-ext 3))
           ((obs-ext 4) (single (record)))))
    (term ((obs-ext 1) (obs-ext 3) (obs-ext 5))))
   (list
    (term (((obs-ext 2))
           ((obs-ext 4) (single (record)))))
    (term (((obs-ext 1) (single *))
           ((obs-ext 3))
           ((obs-ext 5)))))))

;; Adds all addresses matched in the substitution (i.e. the set of bindings) as keys in the output
;; commitment map
(define (observe-addresses-from-subst commitment-map the-subst)
  (redex-let aps# ([(any_map-entries ...) commitment-map]
                   [([_ a#ext] ...) the-subst])
             (term (any_map-entries ... (a#ext) ...))))

;; NOTE: assumes an entry has been added already (e.g. with observe-addresses-from-subst)
(define-metafunction aps#
  add-commitments : O# [a#ext po] ... -> O#
  [(add-commitments O#) O#]
  [(add-commitments (any_1 ... (a#ext any_2 ... (_ po)    any_3 ...) any_4 ...)
                    [a#ext po] any_rest ...)
   (add-commitments (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)
                    any_rest ...)]
  [(add-commitments (any_1 ... (a#ext any_coms ...)             any_2 ...) [a#ext po] any_rest ...)
   (add-commitments (any_1 ... (a#ext any_coms ... (single po)) any_2 ...) any_rest ...)])

(module+ test
  (test-equal? "add-commitments"
               (term (add-commitments
                      ([(obs-ext 1) [single *] [many (record)]]
                       [(obs-ext 2)])
                      [(obs-ext 1) *]
                      [(obs-ext 2) *]
                      [(obs-ext 1) (variant A)]))
               `([(obs-ext 1) [many *] [many (record)] [single (variant A)]]
                 [(obs-ext 2) [single *]])))

;; ---------------------------------------------------------------------------------------------------
;; Input pattern matching

;; Matches the trigger against the given transition pattern, returning the bindings created from the
;; match if such a match exists, else #f
(define (match-trigger from-observer? trigger obs-receptionists pattern)
  (match
      (judgment-holds
       (match-trigger/j ,from-observer? ,trigger ,obs-receptionists ,pattern any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (match-trigger/j I I I I O)
  #:contract (match-trigger/j boolean trigger# ρ# pt ([x a#] ...))

  [-------------------------------------------------------
   (match-trigger/j _ (timeout/empty-queue _) _ unobs ())]

  [-----------------------------------------------------------
   (match-trigger/j _ (timeout/non-empty-queue _) _ unobs ())]

  [----------------------------------------------------------------------
   (match-trigger/j _ (internal-receive _ _ _) _ unobs ())]

  [-----------------------------------------------------------------------
   (match-trigger/j #f (external-receive _ _) _ unobs ())]

  [(aps#-match/j v# p any_bindings)
   ----------------------------------------------------------------
   (match-trigger/j #t (external-receive a# v#) ((_ a#)) p any_bindings)])

(module+ test
  (check-equal?
   (match-trigger #f '(timeout/empty-queue (init-addr 0)) '((Nat (init-addr 0))) 'unobs)
   null)

  (check-equal?
   (match-trigger #f '(timeout/non-empty-queue (init-addr 0)) '((Nat (init-addr 0))) 'unobs)
   null)

  (check-equal?
   (match-trigger #f '(external-receive (init-addr 0) (* Nat)) '((Nat (init-addr 0))) 'unobs)
   null)

  (check-false
   (match-trigger #t '(external-receive (init-addr 0) (* Nat)) '((Nat (init-addr 0))) 'unobs))

  (check-equal?
   (match-trigger #t '(external-receive (init-addr 0) (Nat (obs-ext 1))) '((Nat (init-addr 0))) 'x)
   (list '(x (obs-ext 1))))

  (check-false
   (match-trigger #f '(internal-receive (init-addr 0) (* Nat) single) '((Nat (init-addr 0))) 'x))

  (check-false
   (match-trigger #t '(external-receive (init-addr 0) (* Nat)) '((Nat (init-addr 0))) 'x))

  (check-equal?
   (match-trigger #f '(internal-receive (init-addr 0) (* Nat) single) '((Nat (init-addr 0))) 'unobs)
   null)

  (check-false
   (match-trigger #t '(external-receive (init-addr 0) (variant A)) '(((Union [A]) (init-addr 0))) 'unobs))

  (check-equal?
   (match-trigger #t '(external-receive (init-addr 0) (variant A)) '(((Union [A]) (init-addr 0))) '*)
   null))

(define-judgment-form aps#
  #:mode (aps#-match/j I I O)
  #:contract (aps#-match/j v# p ((x a#) ...))

  [-------------------
   (aps#-match/j _ * ())]

  [-----------------------------------
   (aps#-match/j (τ a#ext) x ([x a#ext]))]

  [(aps#-match/j v# p ([x a#_binding] ...)) ...
   --------------
   (aps#-match/j (variant t v# ..._n) (variant t p ..._n) ([x a#_binding] ... ...))]

  [(aps#-match/j v# p ([x a#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (record [l v#] ..._n) (record [l p] ..._n) ([x a#_binding] ... ...))]

  [(aps#-match/j (* τ) p ([x a#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (* (Record [l τ] ..._n)) (record [l p] ..._n) ([x a#_binding] ... ...))]

  ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
  ;; therefore would not write patterns for them
  [(aps#-match/j v# p ([x a#_binding] ...))
   -----------------------------------------------------------
   (aps#-match/j (folded _ v#) p ([x a#_binding] ...))])

(module+ test
  (check-true (judgment-holds (aps#-match/j (* Nat) * ())))
  (check-true (judgment-holds (aps#-match/j (Nat (obs-ext 1)) x ([x (obs-ext 1)]))))
  (check-true (judgment-holds (aps#-match/j (variant A (* String)) (variant A *) ())))
  (check-true (judgment-holds (aps#-match/j (variant A (Nat (obs-ext 1)))
                                            (variant A x)
                                            ([x (obs-ext 1)]))))
  (check-false (judgment-holds (aps#-match/j (* (Union [A (Addr Nat)] [B])) (variant A *) ())))
  (check-true (judgment-holds (aps#-match/j (record [a (Nat (obs-ext 1))])
                                            (record [a x])
                                            ([x (obs-ext 1)]))))
  (check-true (judgment-holds (aps#-match/j (* (Record [a (Addr Nat)])) (record [a *]) ())))
  (check-true (judgment-holds (aps#-match/j (* Nat) * any)))
  (check-false (judgment-holds (aps#-match/j (* Nat) x any)))
  (check-true (judgment-holds (aps#-match/j (folded Nat (Nat (obs-ext 1))) x any)))
  ;; matches two ways, but should only return one result:
  (check-equal? (judgment-holds (aps#-match/j (folded Nat (* Nat)) * any_bindings) any_bindings)
                (list '())))

;; ---------------------------------------------------------------------------------------------------
;; Output pattern matching

;; v# ρ# (listof pattern) -> (listof [po ρ#_obs ρ#_unobs (match-fork ...)])
;;
;; Attempts to match the given value and observed receptionist map against all of the given patterns,
;; returning a list of tuples [po ρ#_obs ρ#_unobs (match-fork ...)] for each way to match against one
;; of the given patterns.
(define (find-matching-patterns value obs-receptionists patterns)
  (reverse
   (for/fold ([success-results null])
             ([pattern patterns])
     (define this-pattern-results
       (map (curry cons pattern) (aps#-match-po value obs-receptionists pattern)))
     (append success-results this-pattern-results))))

(module+ test
  (check-equal?
   (list->set (find-matching-patterns `(variant A) null (list '* '(variant A) '(variant B))))
   (set `[* () () ()]
        `[(variant A) () () ()])))

;; v# ρ#_obs po -> (Listof [ρ#_obs ρ#_unobs (match-fork ...)])
;;
;; Attempts to match the given message and observed receptionist set against the given
;; pattern. Returns the outputs from every successful judgment for the match relation.
(define (aps#-match-po value obs-receptionists pattern)
  (judgment-holds (aps#-matches-po?/j ,value
                                      ,obs-receptionists
                                      ,pattern
                                      any_new-obs-receptionists
                                      any_new-unobs-receptionists
                                      any_forks)
                  (any_new-obs-receptionists any_new-unobs-receptionists any_forks)))

(define-judgment-form aps#
  #:mode (aps#-matches-po?/j I I I O O O)
  #:contract (aps#-matches-po?/j v# ρ#_obs po ρ#_obs-new ρ#_unobs (match-fork ...))

  [-----
   (aps#-matches-po?/j v# ρ#_obs * ρ#_obs ,(internals-in (term v#)) ())]

  [(aps#-matches-po?/j v# ρ#_obs po                  any_obs-recs any_unobs-receptionists any_forks)
   -----
   (aps#-matches-po?/j v# ρ#_obs (or _ ... po _ ...) any_obs-recs any_unobs-receptionists any_forks)]

  [----
   (aps#-matches-po?/j (τ a#int)
                       ρ#_obs
                       (delayed-fork (goto φ) Φ ...)
                       ρ#_obs
                       ()
                       ((([τ a#int]) (goto φ) (Φ ...))))]

  [----
   (aps#-matches-po?/j τa# (τa#) self (τa#) () ())]

  [----
   (aps#-matches-po?/j [τ a#int] () self ([τ a#int]) () ())]

  [(aps#-list-matches-po?/j ((v# po) ...) ρ#_obs any_obs-recs any_unobs-receptionists any_forks)
   ------
   (aps#-matches-po?/j (variant t v# ..._n)
                       ρ#_obs
                       (variant t po ..._n)
                       any_obs-recs
                       any_unobs-receptionists
                       any_forks)]

  ;; Records

  [(aps#-list-matches-po?/j ((v# po) ...) ρ#_obs any_obs-recs any_unobs-receptionists any_forks)
   ------
   (aps#-matches-po?/j (record [l v#] ..._n)
                       ρ#_obs
                       (record [l po] ..._n)
                       any_obs-recs
                       any_unobs-receptionists
                       any_forks)]

  [(aps#-list-matches-po?/j (((* τ) po) ...) ρ#_obs any_obs-recs any_unobs-receptionists any_forks)
   -----
   (aps#-matches-po?/j (* (Record [l τ] ..._n))
                       ρ#_obs
                       (record [l po] ..._n)
                       any_obs-recs
                       any_unobs-receptionists
                       any_forks)]

  ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
  ;; therefore would not write patterns for them
  [(aps#-matches-po?/j v# ρ#_obs po any_obs-recs any_unobs-receptionists any_forks)
   -------------------------------------------------------------------------------------
   (aps#-matches-po?/j (folded _ v#) ρ#_obs po any_obs-recs any_unobs-receptionists any_forks)])

(define-judgment-form aps#
  #:mode (aps#-list-matches-po?/j I I O O O)
  #:contract (aps#-list-matches-po?/j ((v# po) ...) ρ#_obs ρ#_obs-new ρ#_unobs (match-fork ...))

  [---------
   (aps#-list-matches-po?/j () any_addr any_addr () ())]

  [(aps#-matches-po?/j v# ρ#_obs po any_obs-rec1 (any_unobs-receptionists1 ...) (any_forks1 ...))
   (aps#-list-matches-po?/j (any_rest ...)
                            any_obs-rec1
                            any_obs-rec2
                            (any_unobs-receptionists2 ...)
                            (any_forks2 ...))
   ---------
   (aps#-list-matches-po?/j ((v# po) any_rest ...)
                            ρ#_obs
                            any_obs-rec2
                            (any_unobs-receptionists1 ... any_unobs-receptionists2 ...)
                            (any_forks1 ... any_forks2 ...))])

(module+ test
  (check-equal?
   (aps#-match-po '(* Nat) '() '*)
   (list (list '() null null)))
  (check-equal?
   (aps#-match-po '(* Nat) '() '(record))
   null)
  (check-equal?
   (aps#-match-po '(Nat (init-addr 0)) '() 'self)
   (list (list '((Nat (init-addr 0))) null null)))
  (check-equal?
   (aps#-match-po '(Nat (init-addr 0)) '() '*)
   (list (list '() (list '(Nat (init-addr 0))) null)))
  (check-equal?
   (aps#-match-po '(Nat (obs-ext 0)) '() 'self)
   null)
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (Nat (init-addr 2))) '() '(variant A * self))
   (list (list '((Nat (init-addr 2))) '() '())))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (Nat (init-addr 2))) '() '(variant A * *))
   (list (list '() '((Nat (init-addr 2))) '())))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (Nat (init-addr 2))) '((Nat (init-addr 2))) '(variant A * self))
   (list (list '((Nat (init-addr 2))) '() '())))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (Nat (init-addr 2)))
                  '((Nat (init-addr 2)))
                  '(or (variant A * self) (variant B)))
   (list (list '((Nat (init-addr 2))) '() '())))
  (check-equal? (aps#-match-po (term (variant A)) '() (term (or (variant A) (variant B))))
                (list (list '() null null)))
  (check-equal? (aps#-match-po (term (variant B)) '() (term (or (variant A) (variant B))))
                (list (list '() null null)))
  (check-equal?
   (aps#-match-po (term (variant C)) '() (term (or (variant A) (variant B))))
   null)
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (Nat (init-addr 2)))
                  '((Nat (init-addr 1)))
                  '(variant A * self))
   null)
  (test-equal? "Spawn match po test"
   (aps#-match-po '(Nat (spawn-addr 'foo NEW))
                  '()
                  '(delayed-fork (goto B) (define-state (B))))
   (list (list '()
               '()
               '([([Nat (spawn-addr 'foo NEW)]) (goto B) ((define-state (B)))]))))
  (test-equal? "Full match po test"
   (aps#-match-po '(variant A (Nat (spawn-addr 'foo NEW)) (Nat (init-addr 2)))
                  '()
                  '(variant A (delayed-fork (goto B) (define-state (B))) self))
   (list (list '((Nat (init-addr 2)))
               '()
               '([([Nat (spawn-addr 'foo NEW)])
                  (goto B)
                  ((define-state (B)))]))))

  (test-equal? "Fold test"
   (aps#-match-po '(folded Nat (variant A)) '() '(variant A))
   (list (list '() '() '())))

  (test-equal? "'Or' pattern can match in multiple ways"
    (list->set (aps#-match-po `[Nat (init-addr 1)] null `(or * self)))
    (set `[([Nat (init-addr 1)]) () ()]
         `[() ([Nat (init-addr 1)]) ()])))

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; (s# ...) ((a#ext v# m) ...) ->  (Listof [(s# ...) ([a po] ...)])
;;
;; Given a list of all active spec configs (the current one plus any new forks), returns a list of
;; tuples of the specification configs after having resolved all of the given outputs (removing output
;; commitments as necessary) and a list of the satisfied commitments. The list represents all possible
;; ways to match the outputs.
(define (aps#-resolve-outputs spec-configs outputs)
  (unless (null?
           (filter (lambda (addr) (ormap (curryr config-observes-address? addr) spec-configs))
                   (externals-in (map csa#-output-message outputs))))
    (error 'aps#-resolve-outputs
           "Cannot check conformance for program that sends observed external addresses to environment. Violating outputs: ~s"
           outputs))

  (match outputs
    [(list) (list `(,spec-configs ()))]
    [(list output remaining-outputs ...)
     (define address (csa#-output-address output))
     (define message (csa#-output-message output))
     (define quantity (csa#-output-multiplicity output))
     ;; TODO: compute the new receptionists with output-matching instead when I switch the addresses
     ;; to not include types
     (define exposed-receptionists (internals-in message))
     (match (find-with-rest (curryr config-observes-address? address) spec-configs)
       [#f
        ;; we can ignore outputs on unobserved addresses, but need to add any escaped internal
        ;; addresses as part of the unobserved receptionists on all configs
        (aps#-resolve-outputs
         (map (curryr config-merge-unobs-addresses exposed-receptionists) spec-configs)
         remaining-outputs)]
       [(list earlier-configs config later-configs)
        (define updated-unobserving-configs
          (map (curryr config-merge-unobs-addresses exposed-receptionists)
               (append earlier-configs later-configs)))
        ;; for every possible way to match this particular output
        (for/fold ([results null])
                  ([resolve-result (resolve-output config address message quantity)])
          (match-define (list resolved-configs fulfilled-pattern) resolve-result)
          ;; for every possible way to match the remaining outputs
          (for/fold ([results results])
                    ([next-result (aps#-resolve-outputs
                                   (append updated-unobserving-configs resolved-configs)
                                   remaining-outputs)])
            ;; add the result to our list of possible results
            (match-define (list final-configs other-fulfillments) next-result)
            (define new-resolve-outputs-result
              `[,final-configs ,(cons `[,address ,fulfilled-pattern] other-fulfillments)])
            (cons new-resolve-outputs-result results)))])]))

(module+ test
  (define (make-dummy-spec commitments)
    (term (() () (goto DummyState) ((define-state (DummyState))) ,commitments)))

  (test-equal? "resolve test: no outputs"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1)))))
     (term ()))
    (list `[,(list (make-dummy-spec `(((obs-ext 1))))) ()]))
  (test-equal? "resolve test 1"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1)))))
     (term (((obs-ext 1) (* Nat) single))))
    null)
  (test-equal? "resolve test 1: many"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1)))))
     (term (((obs-ext 1) (* Nat) many))))
    null)
  (test-equal? "resolve test 2"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1) (single *)))))
     (term (((obs-ext 1) (* Nat) single))))
    (list `[,(list (make-dummy-spec `(((obs-ext 1)))))
            ([(obs-ext 1) *])]))
  (test-equal? "resolve test 3"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1) (single *) (single (record))))))
     (term (((obs-ext 1) (* Nat) single))))
    (list `[,(list (make-dummy-spec `(((obs-ext 1) (single (record))))))
            (((obs-ext 1) *))]))
  (test-equal? "resolve test 4"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1) (many *) (single (record))))))
     (term (((obs-ext 1) (* Nat) single))))
    (list `[,(list (make-dummy-spec `(((obs-ext 1) (many *) (single (record))))))
            (((obs-ext 1) *))]))
  (test-equal? "resolve loop test"
    (aps#-resolve-outputs
     (list (make-dummy-spec `(((obs-ext 1) (many *) (single (record))))))
     (term ([(obs-ext 1) (* Nat) many])))
    null)
  (define free-output-spec
    (term
     (()
      ()
      (goto S1 (obs-ext 1) (obs-ext 2))
      ((define-state (S1 a b)
         [x -> ([obligation x *]) (goto S1)]
         [x -> ([obligation b *]) (goto S1)]
         [unobs -> ([obligation a (variant A)]) (goto S2)]
         [unobs -> ([obligation a (variant B)]) (goto S1 a b)]
         [unobs -> ([obligation a (variant C)]) (goto S1 a b)]
         [unobs -> ([obligation b (variant D)]) (goto S1 a b)]))
      ([(obs-ext 1)] [(obs-ext 2)]))))
  (test-equal? "resolve against free outputs"
    (aps#-resolve-outputs (list free-output-spec) (term ([(obs-ext 1) (variant C) many])))
    (list `[,(list free-output-spec) ([(obs-ext 1) (variant C)])]))

  (test-equal? "resolve with unobs transitions"
    (aps#-resolve-outputs
     (list `[()
             ()
             (goto A (obs-ext 1))
             ((define-state (A x)
                [unobs -> ([obligation x (variant C)]) (goto B)]))
             ([(obs-ext 1)])])
     (term ([(obs-ext 1) (variant C) single])))
    (list `[,(list
              `[()
                ()
                (goto B)
                ((define-state (A x)
                   [unobs -> ([obligation x (variant C)]) (goto B)]))
                ([(obs-ext 1)])])
            ([(obs-ext 1) (variant C)])]))

  (test-equal? "resolve against two different branches of an 'or' pattern"
    (list->set
     (aps#-resolve-outputs
      (list
       (term
        (()
         ()
         (goto S1)
         ((define-state (S1)))
         ([(obs-ext 1) (single (or * (delayed-fork (goto B))))]))))
      (term ([(obs-ext 1) (Nat (init-addr 2)) single]))))
    (set
     ;; result 1 (match against the fork)
     `[,(list
         (term
          (()
           ((Nat (init-addr 2)))
           (goto S1)
           ((define-state (S1)))
           ([(obs-ext 1)])))
         (term
          (((Nat (init-addr 2)))
           ()
           (goto B)
           ()
           ())))
       ,(list (term [(obs-ext 1) (or * (delayed-fork (goto B)))]))]
     ;; result 2 (match against *)
     `[,(list
         (term
          (()
           ((Nat (init-addr 2)))
           (goto S1)
           ((define-state (S1)))
           ([(obs-ext 1)]))))
       ,(list (term [(obs-ext 1) (or * (delayed-fork (goto B)))]))]))

  (test-equal? "Resolve against spawned spec"
    (aps#-resolve-outputs
     (list `(() () (goto S1) ((define-state (S1))) ([(obs-ext 1) [single (variant A *)]]))
           `(() () (goto S2) ((define-state (S2))) ([(obs-ext 2) [single (variant B *)]])))
     (list `[(obs-ext 1) (variant A (Nat (init-addr 1))) single]
           `[(obs-ext 2) (variant B (Nat (init-addr 2))) single]))
    (list `[,(list `(()
                     ((Nat (init-addr 1))
                      (Nat (init-addr 2)))
                     (goto S1)
                     ((define-state (S1)))
                     ([(obs-ext 1)]))
                   `(()
                     ((Nat (init-addr 1))
                      (Nat (init-addr 2)))
                     (goto S2)
                     ((define-state (S2)))
                     ([(obs-ext 2)])))
            ,(list '[(obs-ext 1) (variant A *)]
                   '[(obs-ext 2) (variant B *)])]))

  (test-equal? "Resolve against self pattern, no existing obs receptionist"
    (aps#-resolve-outputs
     (list `(() () (goto S1) ((define-state (S1))) ([(obs-ext 1) [single self]])))
     (list `[(obs-ext 1) [Nat (init-addr 1)] single]))
    (list `[,(list `(([Nat (init-addr 1)])
                     ()
                     (goto S1)
                     ((define-state (S1)))
                     ([(obs-ext 1)])))
            ,(list `[(obs-ext 1) self])]))

  (test-equal? "Resolve against self pattern, existing obs receptionist"
    (aps#-resolve-outputs
     (list `(([Nat (init-addr 1)])
             ()
             (goto S1)
             ((define-state (S1)))
             ([(obs-ext 1) [single self]])))
     (list `[(obs-ext 1) [Nat (init-addr 1)] single]))
    (list `[,(list `(([Nat (init-addr 1)])
                     ()
                     (goto S1)
                     ((define-state (S1)))
                     ([(obs-ext 1)])))
            ,(list `[(obs-ext 1) self])]))

  (test-equal? "Resolve against self pattern, existing other obs receptionist"
    (aps#-resolve-outputs
     (list `(([Nat (init-addr 1)])
             ()
             (goto S1)
             ((define-state (S1)))
             ([(obs-ext 1) [single self]])))
     (list `[(obs-ext 1) [Nat (init-addr 2)] single]))
    null)

  (test-equal? "Addresses in unobserved messages are added to receptionists"
    (aps#-resolve-outputs
     (list `(() () (goto S1) ((define-state (S1))) ())
           `(() () (goto S2) ((define-state (S2))) ()))
     (list `[(obs-ext 1) (variant A (Nat (init-addr 1)) (String (init-addr 2))) single]))
    (list `[,(list `(()
                     ((Nat (init-addr 1))
                      (String (init-addr 2)))
                     (goto S1)
                     ((define-state (S1)))
                     ())
                   `(()
                     ((Nat (init-addr 1))
                      (String (init-addr 2)))
                     (goto S2)
                     ((define-state (S2)))
                     ()))
            ()]))

  (test-equal? "Addresses in messages to wildcard addresses are added to receptionists"
    (aps#-resolve-outputs
     (list `(() () (goto S1) ((define-state (S1))) ()))
     (list `[(* (Addr (Union [A (Addr Nat) (Addr String)])))
             (variant A (Nat (init-addr 1)) (String (init-addr 2)))
             single]))
    (list `[,(list `(()
                     ((Nat (init-addr 1))
                      (String (init-addr 2)))
                     (goto S1)
                     ((define-state (S1)))
                     ()))
            ()]))

  (test-exn "External observed addresses in messages causes resolve-outputs to blow up"
    (lambda (exn) #t)
    (lambda ()
      (aps#-resolve-outputs
       (list (make-dummy-spec (list `[(obs-ext 1)])))
       (list `[(* (Addr (Addr Nat))) (Nat (obs-ext 1)) single]))))

  (test-equal? "External unobserved addresses in messages do not cause blow-up"
    (aps#-resolve-outputs
     (list (make-dummy-spec (list `[(obs-ext 1)])))
     (list `[(* (Addr (Addr Nat))) (Nat (obs-ext 2)) single]))
    (list `[,(list (make-dummy-spec (list `[(obs-ext 1)]))) ()])))

;; s# a# v# m -> ([(s# ...) po] ...)
;;
;; Returns a set of tuples each containing a list of specification configs and a pattern such that the
;; input configuration can take an output step with the given message to the given configurations and
;; using the returned pattern to match the message.
(define (resolve-output config address message quantity)
  (match quantity
    ['single
     (match (resolve-with-obligation config address message)
       [(list)
        ;; if we can't find a match with existing patterns, try the free-output patterns
        (match (resolve-with-free-obl-patterns config address message)
          [(list)
           ;; if free-output patterns also don't match, try the other unobs-transition
           ;; patterns as a last resort
           (resolve-with-unobs-transition config address message)]
          [results results])]
       [results results])]
    ['many
     ;; have to use free-output patterns if output may have been sent more than once (e.g. in
     ;; a loop)
     (resolve-with-free-obl-patterns config address message)]))

(module+ test
  (test-equal? "resolve-output 1"
    (resolve-output
     (make-dummy-spec `([(obs-ext 1) [single *]]))
     `(obs-ext 1)
     `(* Nat)
     `single)
    (list `[(,(make-dummy-spec `([(obs-ext 1)]))) *])))

;; s# a# v# -> ([(s# ...) po] ...)
(define (resolve-with-obligation config address message)
  (define commitment-patterns
    (map commitment-pattern
         (commitments-for-address (aps#-config-commitment-map config) address)))
  (match-define (list obs-recs unobs-recs goto state-defs obligations) config)
  (define success-results
    (filter values (find-matching-patterns message obs-recs commitment-patterns)))
  (for/list ([match-result success-results])
    (define matched-pattern (first match-result))
    (define remaining-obligations
      (aps#-remove-commitment-pattern obligations address matched-pattern))
    (list (incorporate-output-match-results `(,obs-recs ,unobs-recs ,goto ,state-defs ())
                                            remaining-obligations
                                            (rest match-result))
          matched-pattern)))

(module+ test
 (test-equal? "resolve-with-obligation 1"
   (resolve-with-obligation
    (make-dummy-spec `([(obs-ext 1) [single *]]))
    `(obs-ext 1)
    `(* Nat))
   (list `[(,(make-dummy-spec `([(obs-ext 1)]))) *])))

(define (resolve-with-unobs-transition config address message)
  (define transition-patterns (get-unobs-transition-patterns config address))
  (match-define (list obs-recs unobs-recs _ state-defs obligations) config)
  (define success-results
    (filter values (find-matching-patterns message obs-recs (hash-keys transition-patterns))))
  (for/list ([match-result success-results])
    (define matched-pattern (first match-result))
    (define transitioned-pre-config
      `(,(aps#-config-obs-receptionists config)
        ,(aps#-config-unobs-receptionists config)
        ,(hash-ref transition-patterns matched-pattern)
        ,(aps#-config-state-defs config)
        ()))
    (list (incorporate-output-match-results transitioned-pre-config
                                            (aps#-config-commitment-map config)
                                            (rest match-result))
          matched-pattern)))

;; s# a# v# -> ([(s# ...) po] ...)
;;
;; Returns a set of tuples each containing a list of specification configs and a pattern such that the
;; input configuration can take an output step with the given message to the given configurations and
;; using the returned free obligation pattern to match the message.
(define (resolve-with-free-obl-patterns config address message)
  (define free-patterns (hash-ref (build-free-output-map config) address null))
  (match-define `[,obs-recs ,unobs-recs ,goto ,state-defs ,obligations] config)
  (define success-results (filter values (find-matching-patterns message obs-recs free-patterns)))
  (for/list ([success-result success-results])
    (list (incorporate-output-match-results
           `[,obs-recs ,unobs-recs ,goto ,state-defs ()]
           obligations
           (rest success-result))
          (first success-result))))

;; s# O# [ρ#_o ρ#_u (match-fork ...)] -> (s# ...)
(define (incorporate-output-match-results original-pre-config
                                          obligations
                                          match-result)
  (match-define (list matched-obs-receptionists matched-unobs-receptionists match-forks) match-result)
  (match-define (list _ original-unobs-recs goto state-defs _) original-pre-config)
  (define all-fork-obs-receptionists (append* (map first match-forks)))
  (define updated-pre-config
    (list matched-obs-receptionists
          (merge-receptionists
           original-unobs-recs
           (merge-receptionists matched-unobs-receptionists all-fork-obs-receptionists))
          goto
          state-defs
          null))
  (define forked-pre-configs
    (for/list ([match-fork match-forks])
      (match-define (list (list fork-obs-rec) goto state-defs) match-fork)
      (define other-fork-obs-receptionists
        ;; "remove" removes only the first item that matches, so if any other fork had the same
        ;; receptionist address and type, it will be included in the unobs receptionist here
        (remove fork-obs-rec all-fork-obs-receptionists))
      `[(,fork-obs-rec)
        ,(merge-receptionists
          matched-obs-receptionists
          (merge-receptionists matched-unobs-receptionists other-fork-obs-receptionists))
        ,goto
        ,state-defs
        ()]))
  (match-define (list s1 (list s2s ...)) (dist updated-pre-config forked-pre-configs obligations))
  (cons s1 s2s))

(module+ test
  (test-equal? "incorporate-output-match-results 1"
    (incorporate-output-match-results
     `(() () (goto A) ((define-state (A))) ())
     null
     `[([Nat (init-addr 1)]) ([String (init-addr 2)]) ()])
    (list `(([Nat (init-addr 1)]) ([String (init-addr 2)]) (goto A) ((define-state (A))) ())))

  (test-equal? "incorporate-output-match-results with delayed-fork"
    (list->set
     (incorporate-output-match-results
      `(() () (goto A) ((define-state (A))) ())
      `([(obs-ext 1) [single *]])
      `[() () ([([Nat (init-addr 1)]) (goto B) ((define-state (B)))])]))
    (set
     `(() ([Nat (init-addr 1)]) (goto A) ((define-state (A))) ([(obs-ext 1) [single *]]))
     `(([Nat (init-addr 1)]) () (goto B) ((define-state (B))) ()))))

(define (config-observes-address? config addr)
  (match (commitments-for-address (aps#-config-commitment-map config) addr)
    [#f #f]
    [_ #t]))

(define (aps#-remove-commitment-pattern commitment-map address pat)
  (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

(define-metafunction aps#
  remove-commitment-pattern/mf : O# a#ext po -> O#
  [(remove-commitment-pattern/mf (any_1 ... (a#ext any_2 ... (single po) any_3 ...) any_4 ...)
                                 a#ext
                                 po)
   (any_1 ... (a#ext any_2 ... any_3 ...) any_4 ...)]
  [(remove-commitment-pattern/mf (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)
                                 a#ext
                                 po)
   (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)]
  ;; we might call this metafunction with a free output pattern not in the obligation list, so if the
  ;; pattern doesn't exist just return the existing map
  [(remove-commitment-pattern/mf any_obligations _ _) any_obligations])

(module+ test
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) (single *)))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) (single *)))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) (many *)))) (term (obs-ext 1)) (term *))
    (term (((obs-ext 1) (many *)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) (single *) (single (record))))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1) (single (record))))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) (single *) (single (record)) (many (record [a *]))) ((obs-ext 2) (single *))))
    (term (obs-ext 1))
    (term *))
   (term (((obs-ext 1) (single (record)) (many (record [a *]))) ((obs-ext 2) (single *))))))

(define (config-merge-unobs-addresses config new-addrs)
  `(,(aps#-config-obs-receptionists config)
    ,(merge-receptionists (aps#-config-unobs-receptionists config) new-addrs)
    ,(aps#-config-current-state config)
    ,(aps#-config-state-defs config)
    ,(aps#-config-commitment-map config)))

(define (aps#-config-has-commitment? config address pattern)
  (judgment-holds (aps#-commitment-map-has-commitment?/j ,(aps#-config-commitment-map config)
                                                         ,address
                                                         ,pattern)))

(define-judgment-form aps#
  #:mode (aps#-commitment-map-has-commitment?/j I I I)
  #:contract (aps#-commitment-map-has-commitment?/j O# a# po)
  [-----
   (aps#-commitment-map-has-commitment?/j (_ ... [a# _ ... (_ po) _ ...] _ ...) a# po)])

(module+ test
  (define has-commitment-test-config
    (term (() () (goto S1) () (((obs-ext 1) (single *))
                               ((obs-ext 2) (single *) (single (record)))))))
  (test-false "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 3)) (term *)))
  (test-false "aps#-config-has-commitment? 2"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 1)) (term (record))))
  (test-true "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 2)) (term (record)))))

;; If the specification's current state has an unobserved transition to the same state whose only
;; effect is a single obligation on an observed address, we call that obligation "free" because we may
;; take that transition an unbounded number of times to match an unbounded number of outputs that
;; match that pattern.
;;
;; This function returns a hashtable from addresses to patterns indicating all free patterns in the
;; current configuration.
(define (build-free-output-map config)
  (define current-state (aps#-config-current-state config))
  (for/fold ([free-pattern-map (hash)])
            ([trans (config-current-transitions config)])
    (match (transition-free-output-info trans current-state)
      [(list addr pattern)
       (hash-set free-pattern-map
                 addr
                 (match (hash-ref free-pattern-map addr #f)
                   [#f (list pattern)]
                   [other-patterns (cons pattern other-patterns)]))]
      [_ free-pattern-map])))

(define (transition-free-output-info trans current-state)
  (match trans
    [`(unobs -> ([obligation ,addr ,pattern]) ,(== current-state))
     (list addr pattern)]
    [_ #f]))

(module+ test
  (check-equal?
   (build-free-output-map
    free-output-spec)
   (hash '(obs-ext 1) (list '(variant C) '(variant B))
         '(obs-ext 2) (list '(variant D)))))

;; s# a# -> (Hash po (goto φ u ...))
(define (get-unobs-transition-patterns config target-addr)
  (define current-state (aps#-config-current-state config))
  (for/fold ([unobs-transition-patterns (hash)])
            ([trans (config-current-transitions config)])
    (match trans
      [`(unobs -> ([obligation ,obligation-addr ,pattern]) ,new-state)
       (if (and (equal? obligation-addr target-addr)
                (not (equal? new-state current-state)))
           (hash-set unobs-transition-patterns pattern new-state)
           unobs-transition-patterns)]
      [_ unobs-transition-patterns])))

(module+ test
  (define unobs-transition-spec
    (term
     (()
      ()
      (goto S1 (obs-ext 1) (obs-ext 2))
      ((define-state (S1 a b)
         [x -> ([obligation x *]) (goto S1)]
         [x -> ([obligation b *]) (goto S1)]
         [unobs -> ([obligation a (variant A)]) (goto S2 a b)]
         [unobs -> ([obligation a (variant B)]) (goto S2 a a)]
         [unobs -> ([obligation a (variant C)]) (goto S1 a b)]
         [unobs -> ([obligation b (variant D)]) (goto S1 a b)]
         [unobs -> ([obligation b (variant E)]) (goto S2 a b)]))
      ([(obs-ext 1)] [(obs-ext 2)]))))
  (check-equal?
   (get-unobs-transition-patterns unobs-transition-spec `(obs-ext 1))
   (hash `(variant A) `(goto S2 (obs-ext 1) (obs-ext 2))
         `(variant B) `(goto S2 (obs-ext 1) (obs-ext 1))))
  (check-equal?
   (get-unobs-transition-patterns unobs-transition-spec `(obs-ext 2))
   (hash `(variant E) `(goto S2 (obs-ext 1) (obs-ext 2)))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-config-obs-receptionists config)
  (redex-let aps# ([(ρ# _ ...) config])
    (term ρ#)))

(define (aps#-config-unobs-receptionists config)
  (term (config-unobs-receptionists/mf ,config)))

(define-metafunction aps#
  config-unobs-receptionists/mf : s# -> ((τ a#int) ...)
  [(config-unobs-receptionists/mf (_ (any_rec ...) _ ...)) (any_rec ...)])

(module+ test
  (redex-let aps# ([s# `(((Nat (init-addr 2)))
                         ((Nat (init-addr 0))
                          (Nat (init-addr 1)))
                         (goto A)
                         ()
                         ())])
    (check-equal? (aps#-config-unobs-receptionists (term s#))
                  `((Nat (init-addr 0))
                    (Nat (init-addr 1))))))

(define (aps#-config-state-defs config)
  (redex-let aps# ([(_ _ _ any_state-defs _) config])
             (term any_state-defs)))

(define (aps#-config-current-state config)
  (redex-let aps# ([(_ _ any_goto _ ...) config])
    (term any_goto)))

(define (aps#-config-current-state-args config)
  (redex-let aps# ([(_ _ (goto _ a# ...) _ ...) config])
    (term (a# ...))))

(define (aps#-config-commitment-map config)
  (term (config-commitment-map/mf ,config)))

(define-metafunction aps#
  config-commitment-map/mf : s# -> O#
  [(config-commitment-map/mf (_ _ _ _ O#)) O#])

(module+ test
  (test-equal? "Config commitment map"
    (aps#-config-commitment-map `(((Nat (init-addr 1))) () (goto A1) () ()))
    '()))

;; Returns all singleton commitments in the config as a list of address/pattern pairs
(define (aps#-config-singleton-commitments config)
  (term (config-commitments-by-multiplicity/mf ,config single)))

;; Returns all many-of commitments in the config as a list of address/pattern pairs
(define (aps#-config-many-of-commitments config)
  (term (config-commitments-by-multiplicity/mf ,config many)))

(define-metafunction aps#
  config-commitments-by-multiplicity/mf : s# m -> ([a#ext po] ...)
  [(config-commitments-by-multiplicity/mf s# m_target)
   ,(append*
     (for/list ([address (term (a#ext ...))]
                [pattern-list (term ((po_result ...) ...))])
       (for/list ([pattern pattern-list]) (list address pattern))))
   (where ((a#ext (m_any po) ...) ...) ,(aps#-config-commitment-map (term s#)))
   (where (((_ po_result) ...) ...)
          ,(map (lambda (com-list)
                  (filter (lambda (com) (equal? (first com) (term m_target))) com-list))
                (term (((m_any po) ...) ...))))])

(module+ test
  (test-equal? "config-singleton-commitments"
    (aps#-config-singleton-commitments
     `(()
       ()
       (goto S1)
       ()
       ([(obs-ext 1) (single *) (many (record))]
        [(obs-ext 2)]
        [(obs-ext 3) (single *) (single (variant A)) (single (record [a *]))])))
    (list `[(obs-ext 1) *]
          `[(obs-ext 3) *]
          `[(obs-ext 3) (variant A)]
          `[(obs-ext 3) (record [a *])]))

  (test-equal? "config-many-of-commitments"
    (aps#-config-many-of-commitments
     `(()
       ()
       (goto S1)
       ()
       ([(obs-ext 1) (single *) (many (record))]
        [(obs-ext 2)]
        [(obs-ext 3) (single *) (single (variant A)) (single (record [a *]))]
        [(obs-ext 4) (many *) (many (variant A)) (single (record [a *]))])))
    (list `[(obs-ext 1) (record)]
          `[(obs-ext 4) *]
          `[(obs-ext 4) (variant A)])))

(define (aps#-transition-trigger transition)
  (redex-let aps# ([(pt -> _ _) transition])
    (term pt)))

(define (aps#-transition-effects transition)
  (third transition))

(define (aps#-transition-goto transition)
  (fourth transition))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (aps#-commitment-entry-patterns entry)
  (redex-let aps# ([(_ (_ po) ...)  entry])
    (term (po ...))))

(module+ test
  (test-case "aps#-commitment-entry-patterns"
    (redex-let* aps# ([any_entry (term [(obs-ext 1) [single *] [many (record)]])]
                      [O# (term (any_entry))])
      (check-equal? (aps#-commitment-entry-patterns (term any_entry))
                    (list '* '(record))))))

(define (commitments-for-address commitment-map address)
  (term (commitments-for-address/mf ,commitment-map ,address)))

(define-metafunction aps#
  commitments-for-address/mf : O# a#ext -> ((m po) ...) or #f
  [(commitments-for-address/mf (_ ... (a#ext (m po) ...) _ ...)
                               a#ext)
   ((m po) ...)]
  [(commitments-for-address/mf _ _) #f])

(module+ test
  (define test-O#
    (term (((obs-ext 1) (single *) (many (record)))
           ((obs-ext 2) (single (variant True)) (single (variant False))))))
  (check-equal?
   (commitments-for-address
    test-O#
    (term (obs-ext 1)))
   (term ((single *) (many (record)))))
  (check-equal?
   (commitments-for-address
    test-O#
    (term (obs-ext 2)))
   (term ((single (variant True)) (single (variant False)))))
  (check-false
   (commitments-for-address
    test-O#
    (term (obs-ext 3)))))

(define (commitment-pattern commitment)
  (redex-let aps# ([(m po) commitment]) (term po)))

;; "Relevant" external addresses are those in either the current state arguments or obligations of a
;; spec config
(define (aps#-relevant-external-addrs s#)
  (term (relevant-external-addrs/mf ,s#)))

(define-metafunction aps#
  relevant-external-addrs/mf : s# -> (a#ext ...)
  [(relevant-external-addrs/mf s#)
   (any_commitment-addr ...)
   (where ((any_commitment-addr _ ...) ...) (config-commitment-map/mf s#))])

(module+ test
  (check-equal?
   (aps#-relevant-external-addrs
    (redex-let* aps#
                ([O# (term (((obs-ext 1)) ((obs-ext 2)) ((obs-ext 3)) ((obs-ext 4))))]
                 [s# (term (()
                            ()
                            (goto Always (obs-ext 1) (obs-ext 2) (obs-ext 3))
                            ((define-state (Always r1 r2) (* -> () (goto Always r1 r2))))
                            O#))])
                (term s#)))
   (term ((obs-ext 1) (obs-ext 2) (obs-ext 3) (obs-ext 4)))))

;; ---------------------------------------------------------------------------------------------------
;; Spec Split

;; s# -> (Listof s#)
;;
;; Splits the given specifcation configuration into multiple configs, to ensure the space of explored
;; spec configs is finite. For each external address in the commitment map that is not a state
;; argument and does not have a "self" pattern in one of its patterns (and therefore will never have
;; more commitments addeded nor be needed to resolve the current self address), it creates a new
;; config consisting only of the commitments on that address (along with commitments for any addresses
;; mentioned in fork patterns for that address) and a dummy FSM with no transitions. After removing
;; those commitment map entries, the remaining config is also returned. The unobserved environment's
;; interface does not change in any of the new configs.
(define (split-spec config)
  (define entries (aps#-config-commitment-map config))
  ;; A commitment map entry is "relevant" if its address is used as a state argument or one of its
  ;; patterns contains the "self" pattern. For each irrelevant entry, we split off a new spec config.
  (define-values (relevant-entries irrelevant-entries)
    (partition
     (lambda (entry)
       (or (member (aps#-commitment-entry-address entry) (aps#-config-current-state-args config))
           (ormap pattern-contains-self? (aps#-commitment-entry-patterns entry))))
     (aps#-config-commitment-map config)))
  (define commitment-only-configs
    (for/list ([entry irrelevant-entries])
      (aps#-config-from-commitment-entry
       entry
       (aps#-config-obs-receptionists config)
       (aps#-config-unobs-receptionists config))))
  (cons (term (,(aps#-config-obs-receptionists config)
               ,(aps#-config-unobs-receptionists config)
               ,(aps#-config-current-state config)
               ,(aps#-config-state-defs config)
               ,relevant-entries))
        commitment-only-configs))

(module+ test
  (define (make-simple-spec-for-split-test commitments)
    (term
     (((Nat (init-addr 0)))
      ()
      (goto A (obs-ext 0))
      ((define-state (A x) [* -> () (goto A x)]))
      ,commitments)))

  (test-equal? "split spec with one FSM gets same spec"
    (split-spec (make-simple-spec-for-split-test '()))
    (list (make-simple-spec-for-split-test '())))

  (test-equal? "split with one related commit"
   (split-spec (make-simple-spec-for-split-test `(((obs-ext 0) (single *)))))
   (list (make-simple-spec-for-split-test `(((obs-ext 0) (single *))))))

  (test-same-items? "split with unrelated commit"
   (split-spec (make-simple-spec-for-split-test `(((obs-ext 1) (single *)))))
   (list (make-simple-spec-for-split-test `())
         (aps#-make-no-transition-config `((Nat (init-addr 0))) `(((obs-ext 1) (single *))))))

  (test-equal? "split a dummy state"
    (split-spec (aps#-make-no-transition-config null `(((obs-ext 1) (single *)))))
    (list (aps#-make-no-transition-config null `(((obs-ext 1) (single *))))))

  (test-equal? "split a spec with a 'self' commitment"
    (split-spec (term (()
                       ()
                       (goto A)
                       ()
                       (((obs-ext 1) (single self))))))
    (list (term (()
                 ()
                 (goto A)
                 ()
                 (((obs-ext 1) (single self)))))))

  (test-equal? "split spec with fork mentioning self pattern"
    (split-spec (term (()
                       ()
                       (goto A (obs-ext 2))
                       ()
                       (((obs-ext 1) [single (fork (goto B)
                                                   (define-state (B)
                                                     [x -> ([obligation x self]) (goto B)]))])
                        ((obs-ext 2))))))
    (list
     (term (()
            ()
            (goto A (obs-ext 2))
            ()
            (((obs-ext 2)))))
     (aps#-make-no-transition-config
      null
      (list `((obs-ext 1) [single (fork (goto B)
                                        (define-state (B)
                                          [x -> ([obligation x self]) (goto B)]))]))))))

(define (pattern-contains-self? pat)
  (match pat
    ['self #t]
    [(? symbol?) #f]
    [`(fork ,_ ...) #f]
    [`(delayed-fork ,_ ...) #f]
    [`(or ,pats ...) (ormap pattern-contains-self? pats)]
    [`(variant ,_ ,pats ...) (ormap pattern-contains-self? pats)]
    [`(record [,_ ,pats] ...) (ormap pattern-contains-self? pats)]))

(module+ test
  (test-false "pattern-contains-self?: self only in fork's state def"
    (pattern-contains-self?
     `(fork (goto A) (define-state (A x) [unobs -> ([obligation x self]) (goto A x)]))))
  (test-true "pattern-contains-self?: true"
    (pattern-contains-self? `(record [a *] [b self])))
    (test-true "pattern-contains-self?: true 2"
      (pattern-contains-self? `(variant A * self)))
  (test-true "pattern-contains-self?: true 3"
    (pattern-contains-self? `(or (variant B) (variant A * self))))
  (test-false "pattern-contains-self?: false"
    (pattern-contains-self? `(record [a *] [b (variant B)])))
  (test-false "pattern-contains-self?: false 2"
    (pattern-contains-self? `(record [a (fork (goto A))] )))
  (test-false "pattern-contains-self?: false 3"
    (pattern-contains-self? `(record [a (delayed-fork (goto A))] ))))

;; Makes a specification config with no observed receptionist and an FSM with no transitions. Used for
;; specifications where only the commitments are important.
(define (aps#-make-no-transition-config unobs-receptionists commitments)
  ;; TODO: expecting the first entry to be the relevant entry is a hack and should be removed once I
  ;; switch over to delayed forks
  (term (()
         ,unobs-receptionists
         (goto DummySpecFsmState ,(aps#-commitment-entry-address (first commitments)))
         ((define-state (DummySpecFsmState x)))
         ,commitments)))

(module+ test
  (test-equal? "aps#-make-no-transition-config"
    (aps#-make-no-transition-config (list `[Nat (init-addr 0)])
                                    (list `[(obs-ext 0) [* single]]
                                          `[(obs-ext 1)]))
    `(()
      ([Nat (init-addr 0)])
      (goto DummySpecFsmState (obs-ext 0))
      ((define-state (DummySpecFsmState x)))
      ([(obs-ext 0) [* single]]
       [(obs-ext 1)]))))

;; Creates a spec config with a transition-less FSM and a commitment map with just the given
;; entry. The receptionists for the unobserved environment will be the given list plus the given FSM
;; address if it is not UNKONWN.
(define (aps#-config-from-commitment-entry entry obs-receptionists unobs-receptionists)
  (aps#-make-no-transition-config (merge-receptionists unobs-receptionists obs-receptionists)
                                  (list entry)))

(module+ test
  (check-equal?
   (aps#-config-from-commitment-entry
    (term ((obs-ext 0) (single *) (single (record [a *] [b *]))))
    '()
    null)
   (aps#-make-no-transition-config '() '(((obs-ext 0) (single *) (single (record [a *] [b *]))))))

  (test-equal? "Commitment entry spec should also include old FSM address as unobs receptionist"
    (aps#-config-from-commitment-entry
     (term ((obs-ext 0) (single *) (single (record [a *] [b *]))))
     '((Nat (init-addr 0)))
     null)
    (aps#-make-no-transition-config
     '((Nat (init-addr 0)))
     '(((obs-ext 0) (single *) (single (record [a *] [b *]))))))

  (test-equal? "Merge obs address into unobs addrs"
    (aps#-config-from-commitment-entry (term ((obs-ext 0)))
                                         `(((Union [A]) (init-addr 0)))
                                         `(((Union [B]) (init-addr 0))))
    (aps#-make-no-transition-config
     `(((Union [A] [B]) (init-addr 0)))
     '(((obs-ext 0))))))

(define (aps#-completed-no-transition-config? s)
  ;; A configuration is a completed, no-transition configuration if its only current transition is the
  ;; implicit do-nothing transition, it has no remaining obligations, and no observable receptionist.
  (and (null? (aps#-config-obs-receptionists s))
       (= 1 (length (config-current-transitions s)))
       (match (aps#-config-commitment-map s)
         [(list `(,_) ...) #t]
         [_ #f])))

(module+ test
  ;; empty config set, non-empty configs, other kind of spec config with empty coms
  (test-case "completed-no-transition-config?: no commitments"
    (redex-let aps# ([s# (aps#-make-no-transition-config null (list `((obs-ext 1))))])
      (check-true (aps#-completed-no-transition-config? (term s#)))))
  (test-case "completed-no-transition-config?: some commitments"
    (redex-let aps# ([s# (aps#-make-no-transition-config null (list `((obs-ext 1) (single *))))])
      (check-false (aps#-completed-no-transition-config? (term s#)))))
  (test-case "completed-no-transition-config?: spec with transitions, no commitments"
    (redex-let aps# ([s#
                      `(()
                        ()
                        (goto A)
                        ((define-state (A) [unobs -> () (goto A)]))
                        ())])
      (check-false (aps#-completed-no-transition-config? (term s#)))))
  (test-case "completed-no-transition-config?: observed interface"
    (redex-let aps# ([s#
                      `(((Nat (init-addr 1)))
                        ()
                        (goto A)
                        ((define-state (A)))
                        ())])
      (check-false (aps#-completed-no-transition-config? (term s#))))))

;; ---------------------------------------------------------------------------------------------------
;; Blurring

;; Blurs the given specification configuration by removing all receptionists in the unobserved
;; environment interface with the wrong spawn flag
(define (aps#-blur-config config internals-to-blur)
  (redex-let aps# ([[any_obs-receptionists
                     any_unobs-receptionists
                     any_exp
                     any_state-defs
                     any_out-coms]
                    config])
    (define blurred-unobs-env
      (csa#-blur-addresses (term any_unobs-receptionists) internals-to-blur null))
    (term [any_obs-receptionists
           ,(merge-receptionists null blurred-unobs-env)
           any_exp
           any_state-defs
           any_out-coms])))

(module+ test
  (test-equal? "aps#-blur-config"
    (aps#-blur-config (aps#-make-no-transition-config
                       `((Nat (init-addr 0))
                         (Nat (spawn-addr 1 OLD))
                         (Nat (spawn-addr 1 NEW))
                         (Nat (spawn-addr 2 NEW))
                         (Nat (blurred-spawn-addr 1))
                         (Nat (spawn-addr 2 OLD)))
                       `([(obs-ext 0)]))
                      (list (term (spawn-addr 1 NEW))))
    (aps#-make-no-transition-config
     `((Nat (init-addr 0))
       (Nat (spawn-addr 1 OLD))
       (Nat (blurred-spawn-addr 1))
       (Nat (spawn-addr 2 NEW))
       (Nat (spawn-addr 2 OLD)))
     `([(obs-ext 0)])))

  (test-equal? "aps#-blur-config merges addresses after blur"
    (aps#-blur-config `(()
                        ([(Union [A]) (blurred-spawn-addr 1)]
                         [(Union [B]) (spawn-addr 1 OLD)])
                        (goto S)
                        ()
                        ())
                      (list `(spawn-addr 1 OLD)))
     `(()
       ([(Union [A] [B]) (blurred-spawn-addr 1)])
       (goto S)
       ()
       ())))

;; (define-metafunction aps#
;;   blur-receptionists : (a#int ...) spawn-flag -> (a#int ...)
;;   [(blur-receptionists () _) ()]
;;   [(blur-receptionists ((spawn-addr any_loc spawn-flag τ) any_rest ...) spawn-flag)
;;    (blur-receptionists (any_rest ...) spawn-flag)]
;;   [(blur-receptionists (any_1 any_rest ...) spawn-flag)
;;    (any_1 any_result ...)
;;    (where (any_result ...) (blur-receptionists (any_rest ...) spawn-flag))])

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization (i.e. renaming)

;; Given an impl config/spec config pair, transforms it into an equivalent (for the purpose of
;; conformance), canonical form. Also returns the address rename map. Specifically:
;;
;; 1. Changes all spawn address new/old flags to OLD (assumes that these configs have already been
;; blurred so that either an OLD or a NEW version of an address exists, but not both)
;;
;; 2. Renames all atomic external addresses such that the first one in the spec config's state
;; argument list is address 0, then address 1, then address 2, and so on. The remaining atomic
;; external addresses are sorted and then given the next available address identifiers in order (so if
;; addresses 52, 81, and 35 remain and 6 is the next available identifier, 35 would map to 6, 52 to 7,
;; and 81 to 8).
;;
;; 3. Also sorts the escaped addresses in the impl config and the receptionists in the spec config
;; (not strictly necessary to ensure a bounded state space, but provides a form of symmetry
;; reduction).
(define (canonicalize-pair impl-config spec-config)
  (match-define (list aged-impl-config aged-spec-config)
    (age-addresses (list impl-config spec-config)))
  (define state-args (aps#-config-current-state-args aged-spec-config))
  (define state-arg-substitutions
    (for/list ([state-arg state-args]
               [new-number (build-list (length state-args) values)])
      (redex-let aps# ([(obs-ext natural) state-arg])
        (list (term natural) new-number))))
  (define remaining-observed-addrs
    (filter (lambda (addr) (not (member addr state-args)))
            (map aps#-commitment-entry-address (aps#-config-commitment-map aged-spec-config))))
  (define remaining-substitutions
    (for/list ([addr (sort remaining-observed-addrs sexp<?)]
               [new-number (build-list (length remaining-observed-addrs)
                                       (curry + (length state-args)))])
      (redex-let aps# ([(obs-ext natural) addr])
        (list (term natural) new-number))))
  (define substitutions (append state-arg-substitutions remaining-substitutions))
  (match-define (list renamed-impl-config renamed-spec-config)
    (rename-external-addresses (list aged-impl-config aged-spec-config) substitutions))
  (list (csa#-sort-config-components renamed-impl-config)
        (aps#-sort-obligation-entries (aps#-sort-receptionists renamed-spec-config))
        substitutions))

(module+ test
  (test-equal? "canonicalize 1"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((init-addr 0)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (Nat (obs-ext 25)) (Nat (obs-ext 42)) (Nat (obs-ext 10)))))))
     (term
      (((Nat (init-addr 0)))
       ()
       (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
       ((define-state (A a b c) [* -> () (goto A)]))
       (((obs-ext 25)) ((obs-ext 42)) ((obs-ext 10))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (Nat (obs-ext 0)) (Nat (obs-ext 1)) (Nat (obs-ext 2)))))))
      (((Nat (init-addr 0)))
       ()
       (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
       ((define-state (A a b c) [* -> () (goto A)]))
       (((obs-ext 0)) ((obs-ext 1)) ((obs-ext 2))))
      ([25 0] [42 1] [10 2]))))

  (test-equal? "canonicalize 2"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((spawn-addr 0 OLD)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (Nat (obs-ext 10)) (Nat (obs-ext 42)) (Nat (obs-ext 25)))))))
     (term
      (((Nat (spawn-addr 0 OLD)))
       ()
       (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
       ((define-state (A c b a) [* -> () (goto A)]))
       (((obs-ext 25)) ((obs-ext 42)) ((obs-ext 10))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((spawn-addr 0 OLD)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (Nat (obs-ext 2)) (Nat (obs-ext 1)) (Nat (obs-ext 0)))))))
      (((Nat (spawn-addr 0 OLD)))
       ()
       (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
       ((define-state (A c b a) [* -> () (goto A)]))
       (((obs-ext 0)) ((obs-ext 1)) ((obs-ext 2))))
      ([25 0] [42 1] [10 2]))))

  (test-equal? "canonicalize spec config with self patterns"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((init-addr 1)
             (() (goto A)))))
     `[()
       ()
       (goto B (obs-ext 99))
       ()
       ([(obs-ext 57) [single self]]
        [(obs-ext 99)]
        [(obs-ext 42) [single self]])])
    `[,(make-single-actor-abstract-config
        (term ((init-addr 1)
               (() (goto A)))))
      [()
       ()
       (goto B (obs-ext 0))
       ()
       ([(obs-ext 0)]
        [(obs-ext 1) [single self]]
        [(obs-ext 2) [single self]])]
      [[99 0]
       [42 1]
       [57 2]]]))

;; Given a term, changes all spawn addresses of the form (spawn-addr _ NEW _) to (spawn-addr _ OLD _),
;; to ensure that spawned addresses in the next handler are fresh.
(define (age-addresses some-term)
  (match some-term
    [(and addr `(spawn-addr ,loc ,flag))
     (if (equal? flag 'NEW)
         (term (spawn-addr ,loc OLD))
         addr)]
    [(list terms ...) (map age-addresses terms)]
    [_ some-term]))

(module+ test
  (test-equal? "Age addresses test"
    (redex-let aps# ([e# `(list (Nat (spawn-addr 1 NEW))
                                (Nat (spawn-addr 2 OLD))
                                (Nat (init-addr 3))
                                (Nat (obs-ext 4)))])
        (age-addresses (term e#)))
    `(list (Nat (spawn-addr 1 OLD))
           (Nat (spawn-addr 2 OLD))
           (Nat (init-addr 3))
           (Nat (obs-ext 4)))))

;; Any (Listof (List Natural Natural)) -> Any
;;
;; Renames precise external addresses in the given term by replacing its number with
;; the corresponding number in the alist mapping
(define (rename-external-addresses term number-mapping)
  (match term
    [`(obs-ext ,old-num)
     (match (findf (lambda (entry) (eq? (first entry) old-num)) number-mapping)
       [#f `(obs-ext ,old-num)]
       [(list _ new-num) `(obs-ext ,new-num)])]
    [(list subterms ...)
     (map (curryr rename-external-addresses number-mapping) subterms)]
    [_ term]))

(module+ test
  (check-equal?
   (rename-external-addresses
    `(some-term (obs-ext 2) (another-term (obs-ext 5)) (obs-ext 13) (obs-ext 0))
    `([2 1] [13 2] [5 3]))
   (term (some-term (obs-ext 1) (another-term (obs-ext 3)) (obs-ext 2) (obs-ext 0)))))

;; Returns a spec config identical to the given one except that the the receptionist list is sorted
(define (aps#-sort-receptionists config)
  (redex-let aps# ([(any_obs-receptionists any_unobs-receptionists any_rest ...) config])
    (term (any_obs-receptionists ,(sort (term any_unobs-receptionists) sexp<?) any_rest ...))))

(define (aps#-sort-obligation-entries config)
  (match-define `[,obs-recs ,unobs-recs ,goto ,state-defs ,obligation-map] config)
  (define (entry< entry1 entry2)
    (sexp<? (aps#-commitment-entry-address entry1)
            (aps#-commitment-entry-address entry2)))
  `[,obs-recs
    ,unobs-recs
    ,goto
    ,state-defs
    ,(sort obligation-map entry<)])

(define (try-rename-address rename-map addr)
  (redex-let aps# ([(obs-ext natural) addr])
    (match (findf (lambda (entry) (equal? (first entry) (term natural))) rename-map)
      [#f #f]
      [(list _ new) (term (obs-ext ,new))])))

(module+ test
  (test-equal? "try-rename-address success"
    (try-rename-address (term ([1 3] [2 4])) (term (obs-ext 2)))
    (term (obs-ext 4)))
  (test-false "try-rename-address failure"
    (try-rename-address (term ([1 3] [2 4])) (term (obs-ext 5)))))

;; Performs the reverse of the mapping indicated by the given address rename map on the given address
(define (reverse-rename-address rename-map addr)
    (redex-let aps# ([(obs-ext natural) addr])
    (match (findf (lambda (entry) (equal? (second entry) (term natural))) rename-map)
      [#f (error 'reverse-rename-address "Unable to find entry for ~s in ~s" addr rename-map)]
      [(list prev _) (term (obs-ext ,prev))])))

(module+ test
  (test-equal? "try-rename-address success"
    (reverse-rename-address (term ([1 3] [2 4])) (term (obs-ext 4)))
    (term (obs-ext 2))))

;; ---------------------------------------------------------------------------------------------------
;; Eviction

(define (evict-pair i s)
  ;; TODO: add the rename map stuff (although technically it's not needed, since the only changed
  ;; addresses are no longer in the resulting configuration
  (for/fold ([pair (list i s)])
            ;; need to check for obs externals, obs internal
            ([addr (csa#-addrs-to-evict i)])
    (match (aps#-config-obs-receptionists s)
      [(list `(,_ (? (curry equal? addr)))) pair]
      [_
       (match-define (list new-impl-config new-unobs-receptionists)
         (csa#-evict i addr))
       (define all-unobs-receptionists
         (merge-receptionists
          (remove-receptionist (aps#-config-unobs-receptionists s) addr)
          new-unobs-receptionists))
       (define new-spec-config
         `(,(aps#-config-obs-receptionists s)
           ,all-unobs-receptionists
           ,(aps#-config-current-state s)
           ,(aps#-config-state-defs s)
           ,(aps#-config-commitment-map s)))
       (list new-impl-config new-spec-config)])))

(module+ test
  (test-equal? "evict-pair"
    (evict-pair
     `[([(init-addr 1)
         [((define-state (A) (m)
             (begin (Nat (spawn-addr (EVICT Nat ()) OLD))
                    (goto A))))
          (goto A)]]
        [(spawn-addr (EVICT Nat ()) OLD)
         [((define-state (B [x (Addr String)]) (m) (goto B x)))
          (goto B (String (init-addr 2)))]])
       ()
       ()]
     `[()
       ((Nat (init-addr 1)) (Nat (spawn-addr (EVICT Nat ()) OLD)))
       (goto A)
       ()
       ()])
    (list
     `[([(init-addr 1)
         [((define-state (A) (m)
             (begin (* (Addr Nat))
                    (goto A))))
          (goto A)]])
       ()
       ()]
     `[()
       ((Nat (init-addr 1))
        (String (init-addr 2)))
       (goto A)
       ()
       ()])))

(define (remove-receptionist receptionists addr-to-remove)
  (filter (lambda (rec) (not (equal? (second rec) addr-to-remove)))
          receptionists))

;; ---------------------------------------------------------------------------------------------------
;; Widening helpers

;; s# s# -> Boolean
;;
;; A spec config s1 is <= s2 if they are identical except for their unobserved interface, which must
;; have (at most) strictly grown in s2 compared to s1
(define (aps#-config<= s1 s2)
  (match-let ([(list `(,obs1 ,unobs1 ,goto1 ,states1 ,obligations1)
                     `(,obs2 ,unobs2 ,goto2 ,states2 ,obligations2))
               (list s1 s2)])
    (and (equal? (list obs1 goto1 states1 obligations1)
                 (list obs2 goto2 states2 obligations2))
         (receptionists<= unobs1 unobs2))))

(module+ test
  (test-true "config<= for identical configs"
    (aps#-config<=
     `(([Nat (init-addr 1)])
       ()
       (goto A)
       ()
       ())
     `(([Nat (init-addr 1)])
       ()
       (goto A)
       ()
       ())))
  (test-true "config<= for configs with <= unobs interfaces"
    (aps#-config<=
     `(([Nat (init-addr 1)])
       ([(Union [A]) (init-addr 2)])
       (goto S)
       ()
       ())
     `(([Nat (init-addr 1)])
       ([(Union [A] [B]) (init-addr 2)])
       (goto S)
       ()
       ())))
  (test-false "config<= for configs with incomparable unobs interfaces"
    (aps#-config<=
     `(([Nat (init-addr 1)])
       ([(Union [A]) (init-addr 2)])
       (goto S)
       ()
       ())
     `(([Nat (init-addr 1)])
       ([Nat (init-addr 1)])
       (goto S)
       ()
       ()))))

;; (τa ...) (τa ...) -> Boolean
;;
;; An interface i1 is <= i2 if i2 contains all addresses from i1 and has a >= type for each address
(define (receptionists<= i1 i2)
  (for/and ([typed-addr1 i1])
    (match (findf (lambda (typed-addr2) (equal? (second typed-addr1) (second typed-addr2))) i2)
      [#f #f]
      [(list type2 _) (type<= (first typed-addr1) type2)])))

(module+ test
  (test-true "receptionists<= for equal interfaces"
    (receptionists<= `([Nat (init-addr 1)]) `([Nat (init-addr 1)])))
  (test-false "receptionists<= for interfaces with different addresses"
    (receptionists<= `([Nat (init-addr 1)]) `([Nat (init-addr 2)])))
  (test-true "receptionists<= where one interface has a new address"
    (receptionists<= `([Nat (init-addr 1)])
                     `([Nat (init-addr 1)] [Nat (init-addr 2)])))
  (test-true "receptionists<= where one interface expands the type"
    (receptionists<= `([(Union [A])     (init-addr 1)])
                     `([(Union [A] [B]) (init-addr 1)])))
  (test-false "receptionists<= where one interface shrinks the type"
    (receptionists<= `([(Union [A] [B]) (init-addr 1)])
                     `([(Union [A])     (init-addr 1)]))))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-s# defs goto unobs-receptionists out-coms)
  (term (((Nat (init-addr 0))) ,unobs-receptionists ,goto ,defs ,out-coms)))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define (spec-config-without-state-defs config)
  (redex-let aps# ([(any_obs-rec any_unobs-rec any_goto _ any_out) config])
    (term (any_obs-rec any_unobs-rec any_goto any_out))))
