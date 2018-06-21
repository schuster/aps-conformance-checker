#lang racket

;; Abstract semantic domains for APS (specification language), and associated functions

;; (provide
;;  ;; Required by conformance checker
;;  aps#-config-obs-receptionists
;;  aps#-config-unobs-receptionists
;;  aps#-config-commitments
;;  aps#-matching-steps
;;  aps#-resolve-outputs
;;  aps#-abstract-config
;;  split-psm
;;  aps#-blur-config
;;  canonicalize-pair
;;  try-rename-address
;;  reverse-rename-address
;;  aps#-config-has-commitment?
;;  aps#-completed-no-transition-psm?
;;  evict-pair
;;  ;; needed for widening
;;  aps#-config<=

;;  ;; Required only for testing
;;  aps#

;;  ;; Required by conformance checker for blurring
;;  aps#-relevant-external-addrs

;;  ;; Testing helpers
;;  make-s#
;;  aps#-make-no-transition-psm

;;  ;; Debugging helpers
;;  spec-config-without-state-defs)

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
  (s# s) ; NOTE: leaving s# in just so I don't have to convert all the code below
  ;; (match-fork (ρ#_obs (goto φ) (Φ ...))) ; TODO: do I still need this?
  )

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps#/u : u (x mk) ... -> u
  [(subst-n/aps#/u u) u]
  [(subst-n/aps#/u u (x mk) any_rest ...)
   (subst-n/aps#/u (subst/aps#/u u x mk) any_rest ...)])

(define-metafunction aps#
  subst/aps#/u : u x mk -> u
  [(subst/aps#/u x x mk) mk]
  [(subst/aps#/u x_2 x mk) x_2]
  [(subst/aps#/u mk_2 x mk) mk_2])

(define-metafunction aps#
  subst/aps#/trans : (pt -> (f ...) (goto φ u ...)) x mk -> (pt -> (f ...) (goto φ u ...))
  [(subst/aps#/trans (p -> (f ...) (goto φ u ...)) x mk)
   (p -> (f ...) (goto φ u ...))
   (judgment-holds (pattern-binds-var p x))]
  [(subst/aps#/trans (pt -> (f ...) (goto φ u ...)) x mk)
   (pt -> ((subst/aps#/f f x mk) ...) (goto φ (subst/aps#/u u x mk) ...))])

(define-metafunction aps#
  subst-n/aps#/f : f (x mk) ... -> f
  [(subst-n/aps#/f f) f]
  [(subst-n/aps#/f f (x mk) any_rest ...)
   (subst-n/aps#/f (subst/aps#/f f x mk) any_rest ...)])

(define-metafunction aps#
  subst/aps#/f : f x mk -> f
  [(subst/aps#/f (obligation u po) x mk)
   (obligation (subst/aps#/u u x mk) (subst/aps#/po po x mk))]
  [(subst/aps#/f (fork (goto φ u ...) Φ ...) x mk)
   (fork (goto φ (subst/aps#/u u x mk) ...) Φ ...)])

(define-metafunction aps#
  subst/aps#/po : po x mk -> po
  [(subst/aps#/po * _ _) *]
  [(subst/aps#/po (or po ...) x mk) (or (subst/aps#/po po x mk) ...)]
  [(subst/aps#/po (fork (goto φ u ...) Φ ...) x mk)
   (fork (goto φ (subst/aps#/u u x mk) ...)
         Φ ...)]
  [(subst/aps#/po (delayed-fork (goto φ) Φ ...) x mk)
   (delayed-fork (goto φ) Φ ...)]
  [(subst/aps#/po self _ _) self]
  [(subst/aps#/po (variant t po ...) x mk) (variant t (subst/aps#/po po x mk) ...)]
  [(subst/aps#/po (record [l po] ...) x mk) (record [l (subst/aps#/po po x mk)] ...)])

(module+ test
  (test-equal? "Simple subst/aps#/f test"
    (term (subst/aps#/f [fork (goto S1 x)
                              (define-state (S1 y x) [* -> () (goto S2 y)])
                              (define-state (S2 y) [* -> ([obligation y *]) (goto S2 y)])]
                        x
                        1))
    (term [fork (goto S1 1)
                (define-state (S1 y x) [* -> () (goto S2 y)])
                (define-state (S2 y) [* -> ([obligation y *]) (goto S2 y)])]))

  (test-equal? "Substitution should not go into state defs"
    (term (subst/aps#/f [fork (goto A x) (define-state (A) [* -> () (goto B x)])] x 1))
    (term [fork (goto A 1) (define-state (A) [* -> () (goto B x)])]))

  (test-equal? "Substitute into goto in an output obligation fork"
    (term (subst/aps#/f [obligation 0 (variant A (fork (goto S x)))] x 1))
    (term [obligation 0 (variant A (fork (goto S 1)))]))

  (test-equal? "Substitute for fork and delayed-fork"
    (term (subst/aps#/f [obligation x (variant A (fork (goto B y)) (delayed-fork (goto C)))]
                        y
                        1))
    (term [obligation x (variant A (fork (goto B 1)) (delayed-fork (goto C)))])))

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
     (goto φ mk ...)
     (_ ... (define-state (φ x ...) (pt -> (f ...) (goto φ_trans u_trans ...)) ...) _ ...)
     _))
   ((pt ->
        ((subst-n/aps#/f f (x mk) ...) ...)
        (goto φ_trans (subst-n/aps#/u u_trans (x mk) ...) ...)) ...
    ;; Note that we include the "null"/no-step transition
    ;; TODO: move this out of here and into aps#-matching-spec-steps
    (free -> () (goto φ mk ...)))])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; s# trigger -> ([s# ...] ...)
;;
;; Returns all spec configs (sets of PSMs) that can possibly be reached in one step by transitioning
;; from the given PSM with the given trigger. Each config includes PSMs, also returning spec configs
;; spawned during that transition
(define (aps#-matching-steps spec-config trigger)
  (define available-transitions
    ;; Remove the free-output transitions: these would cause the checker to make many "bad
    ;; guesses" about what conforms to what, and the outputs they use can always be used for
    ;; other transitions.
    (filter (negate (curryr free-stable-transition? (aps#-psm-current-state spec-config)))
            (config-current-transitions spec-config)))

  (define matching-transitions
    (filter (curry transition-matches? (aps#-psm-mon-receptionists spec-config) trigger)
            available-transitions))
  (when (null? matching-transitions)
      (error 'aps#-matching-steps
             "The trigger ~s has no way to transition in spec config ~s"
             trigger (spec-config-without-state-defs spec-config)))

  (define transition-results
    (map (lambda (t) (take-transition spec-config t trigger)) matching-transitions))
  (remove-duplicates
   (filter (lambda (transitioned-configs)
             (and
              ;; can run into infinite loop if we allow multiple observed markers to have an
              ;; obligation with "self" in the pattern, so we eliminate those transitions
              (<= (length (markers-with-self-obligations (first transitioned-configs))) 1)
              ;; can also run into infinite loop if we allow multiple obligations, so we only use
              ;; transitions that don't duplicate them
              (andmap all-obligations-unique? transitioned-configs)))
           transition-results)))

(module+ test
  (test-equal? "Null step is possible"
               (aps#-matching-steps
                (make-s# (term ((define-state (A))))
                         (term (goto A))
                         (term ()))
                (term (timeout (addr 0 0))))
               (list
                (list (make-s# (term ((define-state (A))))
                               (term (goto A))
                               (term ())))))

  (test-equal? "Monitored receive"
    (aps#-matching-steps
     (make-s# (term ((define-state (A)
                       [*     -> () (goto B)]
                       [free -> () (goto C)])))
              (term (goto A))
              (term ()))
     (term (external-receive (marked (addr 0 0) 0) abs-nat)))
    (list
     (list
      (make-s# (term ((define-state (A)
                        [*     -> () (goto B)]
                        [free -> () (goto C)])))
               (term (goto B))
               (term ())))))

  (test-equal? "Unmonitored receive"
    (list->set
     (aps#-matching-steps
      (make-s# (term ((define-state (A)
                        [*     -> () (goto B)]
                        [free -> () (goto C)])))
               (term (goto A))
               (term ()))
      (term (external-receive (marked (addr 0 0) 1) abs-nat))))
    (set
     ;; "null" transition
     (list
      (make-s# (term ((define-state (A)
                        [*     -> () (goto B)]
                        [free -> () (goto C)])))
               (term (goto A))
               (term ())))
     ;; free transition
     (list
      (make-s# (term ((define-state (A)
                        [*     -> () (goto B)]
                        [free -> () (goto C)])))
               (term (goto C))
               (term ())))))

  (test-equal? "Don't allow multiple copies of obligations"
    (aps#-matching-steps
     (valid-s# `[(0)
                 (1)
                 (goto A 1)
                 ((define-state (A r) [* -> ((obligation r *)) (goto A r)]))
                 ([1 *])])
     (term (external-receive (marked (addr 0 0) 0) abs-nat)))
    null)

  (test-exn "No match for a trigger leads to exception"
    (lambda (exn) #t)
    (lambda ()
      (aps#-matching-steps
       (make-s# (term ((define-state (A))))
                (term (goto A))
                `())
       (term (external-receive (marked (addr 0 0) 0) abs-nat)))))

  (test-equal? "Spec observes address but neither saves it nor has obligations for it"
    (aps#-matching-steps
     (make-s# `((define-state (A) [r -> () (goto A)]))
              `(goto A)
              null)
     `(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 1)))
    (list `[,(valid-s# `[(0)
                         (1)
                         (goto A)
                         ((define-state (A) [r -> () (goto A)]))
                         ()])]))

  (test-equal? "Address received on unmonitored rec not added as monitored external"
    (aps#-matching-steps
     (make-s# `((define-state (A) [r -> () (goto A)]))
              `(goto A)
              null)
     `(external-receive (marked (addr 0 0) 1) (marked (addr (env Nat) 1) 2)))
    (list `[,(make-s# `((define-state (A) [r -> () (goto A)]))
                      `(goto A)
                      null)]))

  (test-equal? "Address matched by wildcard not added as monitored external"
    (aps#-matching-steps
     (make-s# `((define-state (A) [* -> () (goto A)]))
              `(goto A)
              null)
     `(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 2)))
    (list `[,(make-s# `((define-state (A) [* -> () (goto A)]))
                      `(goto A)
                      null)]))

  (test-equal? "Don't return transitions that would have addrs with multiple self obls"
    (aps#-matching-steps
     (valid-s# `[(0)
                 (2)
                 (goto A)
                 ((define-state (A) [r -> ([obligation r self]) (goto A)]))
                 ([2 self])])
     `(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 3)))
    null))

;; Returns the set of markers for which the given PSM has an obligation whose pattern contains a
;; "self" pattern
(define (markers-with-self-obligations psm)
  (define self-obls
    (filter
     (lambda (obligation) (pattern-contains-self? (aps#-obligation-pattern obligation)))
     (aps#-psm-obligations psm)))
  (remove-duplicates (map aps#-obligation-dest self-obls)))

(module+ test
  (test-equal? "Addresses with self obligation"
    (markers-with-self-obligations
     `[()
       ()
       (goto A)
       ()
       ([1 self]
        [2 *]
        [3 (record [a *] [b self])])])
    (list 1 3)))

(define (all-obligations-unique? psm)
  (not (check-duplicates (aps#-psm-obligations psm))))

(module+ test
  (test-true "Does not have duplicate obligations"
    (all-obligations-unique? `[() () (goto A) () ([1 *] [1 (variant A)])]))
  (test-false "Has duplicate obligations"
    (all-obligations-unique? `[() () (goto A) () ([1 (variant A)] [1 *] [1 (variant A)])])))

;; state-transition trigger
(define (transition-matches? mon-recs trigger transition)
  (match (match-trigger mon-recs trigger (aps#-transition-trigger transition))
    [#f #f]
    [_ #t]))

(module+ test
  (test-true "received message matches transition pattern"
    (transition-matches? (list 1)
                         `(external-receive (marked (addr 0 0) 1) (variant A))
                         `[(variant A) -> () (goto B)]))

  (test-false "received message does not match transition pattern"
    (transition-matches? (list 1)
                         `(external-receive (marked (addr 0 0) 1) (variant B))
                         `[(variant A) -> () (goto B)]))

  (test-false "received message on unobs marker does not match transition pattern"
    (transition-matches? (list 1)
                         `(external-receive (marked (addr 0 0) 2) (variant A))
                         `[(variant A) -> () (goto B)]))

  (test-false "received message on monitored marker cannot match free transition"
    (transition-matches? (list 1)
                         `(external-receive (marked (addr 0 0) 1) (variant A))
                         `[free -> () (goto B)]))

  (test-true "received message on unmonitored marker matches free transition"
    (transition-matches? (list 1)
                         `(external-receive (marked (addr 0 0) 2) (variant A))
                         `[free -> () (goto B)])))

;; s# spec-state-transition trigger -> (s# ...)
;;
;; Returns the config updated by running the given transition, along with all configs spawned in the
;; transition.
(define (take-transition psm transition trigger)
  (match-define (list bindings ...)
    (match-trigger (aps#-psm-mon-receptionists psm)
                   trigger
                   (aps#-transition-trigger transition)))
  (match-define (list new-obligations forked-psms self-markers)
    (perform (subst-into-effects (aps#-transition-effects transition) bindings)))
  (define fork-mon-externals (append* (map aps#-psm-mon-externals forked-psms)))
  (define new-goto (subst-into-goto (aps#-transition-goto transition) bindings))
  (define new-mon-externals
    (append
     (aps#-goto-args new-goto)
     self-markers
     (filter (lambda (m) (not (member m fork-mon-externals))) (map second bindings))))
  (define stepped-current-psm
    (term [,(aps#-psm-mon-receptionists psm)
           ,(remove-duplicates (append (aps#-psm-mon-externals psm) new-mon-externals))
           ,new-goto
           ,(aps#-psm-state-defs psm)
           ,(aps#-psm-obligations psm)]))
  (dist stepped-current-psm forked-psms new-obligations))

(module+ test
  (test-equal? "Transition should put observed no-commitment marker in monitored-externals"
    (take-transition
     `[(0)
       ()
       (goto A)
       ((define-state (A) [r -> () (goto A)]))
       ()]
     `[r -> () (goto A)]
     `(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 1)))
    (list
     `[(0)
       (1)
       (goto A)
       ((define-state (A) [r -> () (goto A)]))
       ()]))

  (test-equal? "Pattern-matched marker added to monitored externals"
    (take-transition
     `[(1)
       ()
       (goto A)
       ()
       ()]
     `[x -> () (goto A)]
     `(external-receive (marked (addr 0 0) 1) (marked (addr (env Nat) 1) 2)))
    (list `[(1) (2) (goto A) () ()]))

  (test-equal? "Pattern-matched marker not added to monitored externals if fork keeps it"
    (take-transition
     `[(1)
       ()
       (goto A)
       ()
       ()]
     `[x -> ([fork (goto B x)]) (goto A)]
     `(external-receive (marked (addr 0 0) 1) (marked (addr (env Nat) 1) 2)))
    (list `[(1) () (goto A) () ()]
          `[() (2) (goto B 2) () ()]))

  (test-equal? "Markers with commitments and added to state arg should be added exactly once to obligations"
    (take-transition
     `[(0)
       ()
       (goto A)
       ((define-state (A) [r -> ([obligation r *]) (goto B r)]))
       ()]
     `[r -> ([obligation r *]) (goto B r)]
     `(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 1)))
    (list
     `[(0)
       (1)
       (goto B 1)
       ((define-state (A) [r -> ([obligation r *]) (goto B r)]))
       ([1 *])]))

  (test-case "Immediate fork pattern transition"
    (define fork-pattern `(fork (goto Z y) (define-state (Z y) [* -> () (goto Z y)])))
    (check-equal?
     (take-transition
      `[(1)
        (3 4)
        (goto A 3)
        ((define-state (A x) [(variant A y z) -> ([obligation z ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ;; check for captured and uncaptured addresses, too
        ([4 *])]
      `[(variant A y z) -> ([obligation z ,fork-pattern]) (goto B)]
      `(external-receive (marked (addr 1 0) 1)
                         (variant A
                                  (marked (addr (env (Addr Nat)) 5) 5)
                                  (marked (addr (env (Addr Nat)) 6) 6))))
     (list
      `((1)
        (3 4)
        (goto B)
        ((define-state (A x) [(variant A y z) -> ([obligation z ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ([4 *]))
      `(()
        (6 5)
        (goto Z 5)
        ((define-state (Z y) [* -> () (goto Z y)]))
        ([6 self])))))

  (test-case "Delayed fork pattern transition"
    (define fork-pattern `(delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)])))
    (check-equal?
     (take-transition
      `((0)
        (1 2 3)
        (goto A 1)
        ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ;; check for captured and uncaptured addresses, too
        ([3 *]))
      `[* -> ([obligation 1 ,fork-pattern]) (goto B)]
      `(external-receive (marked (addr 1 0) 0) (marked (addr (env (Addr Nat)) 2) 4)))
     (list
      `((0)
        (1 2 3)
        (goto B)
        ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
         (define-state (B) [* -> () (goto B)]))
        ([3 *]
         [1 ,fork-pattern]))))))

;; (f ...) ([x mk] ...) -> (f ...)
;;
;; Substitutes the given bindings into the given effects
(define (subst-into-effects effects bindings)
  (redex-let aps# ([([x mk] ...) bindings])
    (for/list ([effect effects])
      (term (subst-n/aps#/f ,effect [x mk] ...)))))

;; (goto state x ...) ([x mk] ...) -> (goto state mk ...)
;;
;; Substitutes the given bindings into the given specification goto expression
(define (subst-into-goto goto bindings)
  (redex-let aps# ([([x mk] ...) bindings]
                   [(goto φ u ...) goto])
    (term (goto φ (subst-n/aps#/u u [x mk] ...) ...))))

;; (f ...) ρ -> [([mk po] ...) (s ...) (mk ...)]
;;
;; Performs the given effects, returning new obligations, forked PSMs, and markers that have a "self"
;; pattern for this PSM
(define (perform effects)
  (for/fold ([results (list null null null)])
            ([effect effects])
    (match-define (list obls-so-far forks-so-far self-markers-so-far) results)
    (match effect
      [`(obligation ,dest ,pattern)
       (match-define (list post-extract-pattern extracted-psms markers-for-self)
         (extract pattern dest))
       (list (cons `[,dest ,post-extract-pattern] obls-so-far)
             (append forks-so-far extracted-psms)
             (remove-duplicates (append self-markers-so-far markers-for-self)))]
      [`(fork ,goto ,state-defs ...)
       (list obls-so-far
             (cons `[()
                     ,(remove-duplicates (aps#-goto-args goto))
                     ,goto
                     ,state-defs
                     ()]
                   forks-so-far)
             self-markers-so-far)])))

(module+ test
  (test-equal? "perform 1"
    (perform
     (list `[obligation 1
                        (fork (goto Z 2) (define-state (Z a) [* -> () (goto Z a)]))]))
    `[([1 self])
      ([()
        (1 2)
        (goto Z 2)
        ((define-state (Z a) [* -> () (goto Z a)]))
        ()])
      ()])

  (test-equal? "perform delayed-fork obligation"
    (perform
     (list `[obligation 1
                        (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))]))
    `(([1 (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))])
      ()
      ()))

  (test-equal? "perform fork"
    (perform (list `[fork (goto A 1)]))
    `(()
      ([() (1) (goto A 1) () ()])
      ()))

  (test-equal? "perform obligation with 'self'"
    (perform (list `[obligation 1 (variant A self)]))
    `[([1 (variant A self)])
      ()
      (1)])

  (test-equal? "perform multiple effects"
    (perform (list
              `[obligation 1 (fork (goto Z 2) (define-state (Z a) [* -> () (goto Z a)]))]
              `[obligation 3 (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))]
              `[fork (goto A 4)]
              `[obligation 5 (variant A self)]))
    `[([5 (variant A self)]
       [3 (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))]
       [1 self])
      ([() (4) (goto A 4) () ()]
       [() (1 2) (goto Z 2) ((define-state (Z a) [* -> () (goto Z a)])) ()])
      (5)]))

;; po mk -> (po, (s ...), (mk ...))
;;
;; Extracts all forks from the given pattern that is an obligation on the given address, replacing
;; those patterns with the "self" pattern and creating PSMs for each fork. Also returns the markers
;; for obligations that have a "self" pattern referring to the current PSM
(define (extract pattern dest)
  (define (extract-sub-patterns sub-patterns make-pattern)
    (match-define (list `[,extracted-pats ,forks ,markers-for-self] ...)
      (map (curryr extract dest) sub-patterns))
    (list (make-pattern extracted-pats)
          (append* forks)
          (append* markers-for-self)))
  (match pattern
    [`* (list pattern null null)]
    [`(or ,pats ...)
     (extract-sub-patterns pats (lambda (pats) `(or ,@pats)))]
    [`(variant ,tag ,pats ...)
     (extract-sub-patterns pats (lambda (pats) `(variant ,tag ,@pats)))]
    [`(record [,fields ,pats] ...)
     (extract-sub-patterns
      pats
      (lambda (pats) `(record ,@(map (lambda (f p) `[,f ,p]) fields pats))))]
    [`(fork ,goto ,state-defs ...)
     (list 'self
           (list `[()
                   ,(remove-duplicates (cons dest (aps#-goto-args goto)))
                   ,goto
                   ,state-defs
                   ()])
           null)]
    [`(delayed-fork ,_ ,_ ...) (list pattern null null)]
    ['self (list pattern null (list dest))]))

(module+ test
  (test-equal? "extract 1"
    (extract `(or (fork (goto A 1))
                  (fork (goto B 2)))
             3)
    `[(or self self)
      ([() (3 1) (goto A 1) () ()]
       [() (3 2) (goto B 2) () ()])
      ()])

  (test-equal? "extract fork"
    (extract `(fork (goto A 1) (define-state (A x)))
             2)
    `[self
      ([()
        (2 1)
        (goto A 1)
        ((define-state (A x)))
        ()])
      ()])

  (test-equal? "extract delayed-fork"
    (extract `(delayed-fork (goto B) (define-state (B)) (define-state (C)))
             2)
    `[(delayed-fork (goto B) (define-state (B)) (define-state (C)))
      ()
      ()])

  (test-equal? "extract self"
    (extract `(variant A self) 1)
    `[(variant A self)
      ()
      (1)]))

;; s (s ...) O -> (s ...)
;;
;; As described in the dissertation, distributes the given obligations to each PSM according to the
;; monitored externals on each PSM. Also checks that no two PSMs monitor the same external
;; marker. Returns the list of updated PSMs, with the "current" one as the first item in the list.
;;
;; Assumes that every obligation has *some* PSM in the given ones that monitors the obligation's
;; destination marker.
(define (dist current-psm forked-psms new-obligations)
  (define duplicate-marker
    (check-duplicates (append* (map aps#-psm-mon-externals (cons current-psm forked-psms)))))
  (when duplicate-marker
    (error 'dist "Multiple PSMs monitor the marker ~s" duplicate-marker))
  (for/list ([psm (cons current-psm forked-psms)])
    (add-obligations psm (filter (curryr obligation-relevant-to? psm) new-obligations))))

(module+ test
  (test-equal? "Degenerate dist case"
    (dist `[() () (goto A) ((define-state (A))) ()] null null)
    (list `[() () (goto A) ((define-state (A))) ()]))

  (test-equal? "Basic dist case"
    (dist `[() (1) (goto A) ((define-state (A))) ()]
          (list `[() (2) (goto B 2) ((define-state (B r))) ()])
          (list `[1 *]
                `[2 (record)]))
    (list `[() (1) (goto A) ((define-state (A))) ([1 *])]
          `[() (2) (goto B 2) ((define-state (B r))) ([2 (record)])]))

  (test-equal? "Dist with extra relevant address"
    (dist `[() (1) (goto A 1) () ()]
          (list `[() (2) (goto B) () ()])
          (list `[1 *]
                `[2 *]))
    (list `[() (1) (goto A 1) () ([1 *])]
          `[() (2) (goto B) () ([2 *])]))

  (test-equal? "Dist an obligation with self pattern and that destination marker in the forked PSM's args"
    (dist `[() () (goto A) () ()]
          (list (term (() (1) (goto B 1) () ())))
          (list `[1 (variant X self)]))
    (list `[() () (goto A) () ()]
          `[() (1) (goto B 1) () ([1 (variant X self)])]))

  (test-exn "Cannot distribute obligations over PSMs that monitor same marker"
    (lambda (exn) #t)
    (lambda ()
      (dist `[() (1) (goto A 1) () ()]
            (list `[() (1) (goto B 1) () ()])
            (list `[1 *])))))

;; True iff the given oblgiation's destination marker is monitored by the PSM.
(define (obligation-relevant-to? obl psm)
  (member (aps#-obligation-dest obl) (aps#-psm-mon-externals psm)))

;; Adds all of the given obligations to the given PSM
(define (add-obligations psm new-obls)
  (match-define `[,mon-recs ,mon-exts ,goto ,state-defs ,old-obls] psm)
  `[,mon-recs ,mon-exts ,goto ,state-defs ,(append old-obls new-obls)])

;; ---------------------------------------------------------------------------------------------------
;; Input pattern matching

;; Matches the trigger against the given transition pattern in a context where the given markers are
;; the monitored receptionist markers, returning the bindings created from the match if such a match
;; exists, else #f
(define (match-trigger mon-recs trigger pattern)
  (match
      (judgment-holds
       (match-trigger/j ,mon-recs ,trigger ,pattern any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (match-trigger/j I I I O)
  #:contract (match-trigger/j (mk ...) trigger# pt ([x mk] ...))

  [-------------------------------------------------------
   (match-trigger/j _ (timeout _) free ())]

  [----------------------------------------------------------------------
   (match-trigger/j _ (internal-receive _ _ _) free ())]

  [(side-condition ,(not (member (term mk) (term (mk_mon-recs ...)))))
   -----------------------------------------------------------------------
   (match-trigger/j (mk_mon-recs ...) (external-receive (marked _ mk) _) free ())]

  [(aps#-match/j v# p any_bindings)
   --------------------------------------------------------------------------------------
   (match-trigger/j (_ ... mk _ ...) (external-receive (marked a# mk) v#) p any_bindings)])

(module+ test
  (test-equal? "Timeout matches free transition"
   (match-trigger null '(timeout (addr 0 0)) 'free)
   null)

  (test-equal? "External-receive on unmonitored marker matches free transition"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 2) abs-nat) 'free)
   null)

  (test-false "External receive on monitored receptionist does not match free transition"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 1) abs-nat) 'free))

  (test-equal? "External receive on monitored receptionist matches var-pattern transition"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 1) (marked (addr (env Nat) 1) 2)) 'x)
   (list '[x 2]))

  (test-false "Internal receive does not match pattern transition"
   (match-trigger (list 1) '(internal-receive (addr 0 0) abs-nat single) 'x))

  (test-false "External receive of natural does not match var-pattern transition"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 1) abs-nat)  'x))

  (test-equal? "Internal receive matches free transition"
   (match-trigger (list 1) '(internal-receive (addr 0 0) abs-nat single) 'free)
   null)

  (test-false "External receive on monitored receptionist does not match free transition (2)"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 1) (variant A)) 'free))

  (test-equal? "External receive of variant matches * pattern"
   (match-trigger (list 1) '(external-receive (marked (addr 0 0) 1) (variant A)) '*)
   null))

(define-judgment-form aps#
  #:mode (aps#-match/j I I O)
  #:contract (aps#-match/j v# p ((x mk) ...))

  [-------------------
   (aps#-match/j _ * ())]

  [-----------------------------------
   ;; The model checker should enforce by this point that all received addresses have exactly one
   ;; marker
   (aps#-match/j (marked a# mk) x ([x mk]))]

  [(aps#-match/j v# p ([x mk_binding] ...)) ...
   --------------
   (aps#-match/j (variant t v# ..._n) (variant t p ..._n) ([x mk_binding] ... ...))]

  [(aps#-match/j v# p ([x mk_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (record [l v#] ..._n) (record [l p] ..._n) ([x mk_binding] ... ...))]

  ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
  ;; therefore would not write patterns for them
  [(aps#-match/j v# p ([x mk_binding] ...))
   -----------------------------------------------------------
   (aps#-match/j (folded _ v#) p ([x mk_binding] ...))])

(module+ test
  (check-true (judgment-holds (aps#-match/j abs-nat * ())))
  (check-true (judgment-holds (aps#-match/j (marked (addr (env Nat) 1) 2) x ([x 2]))))
  (check-true (judgment-holds (aps#-match/j (variant A abs-string) (variant A *) ())))
  (check-true (judgment-holds (aps#-match/j (variant A (marked (addr (env Nat) 1) 2))
                                            (variant A x)
                                            ([x 2]))))
  (check-true (judgment-holds (aps#-match/j (record [a (marked (addr (env Nat) 1) 2)])
                                            (record [a x])
                                            ([x 2]))))
  (check-true (judgment-holds (aps#-match/j abs-nat * any)))
  (check-false (judgment-holds (aps#-match/j abs-nat x any)))
  (check-true (judgment-holds (aps#-match/j (folded Nat (marked (addr (env Nat) 1) 2)) x any)))
  ;; matches two ways, but should only return one result:
  (check-equal? (judgment-holds (aps#-match/j (folded Nat abs-nat) * any_bindings) any_bindings)
                (list '())))

;; ---------------------------------------------------------------------------------------------------
;; Output pattern matching

;; v# (listof pattern) -> (listof [po (mk ...) (s ...)])
;;
;; Attempts to match the given value against all of the given patterns, returning a list of tuples [po
;; (match-fork ...)] for each way to match against one of the given patterns.
(define (find-matching-patterns value patterns)
  (reverse
   (for/fold ([success-results null])
             ([pattern patterns])
     (define this-pattern-results
       (map (curry cons pattern) (aps#-match-po value pattern)))
     (append success-results this-pattern-results))))

(module+ test
  (check-equal?
   (list->set (find-matching-patterns `(variant A) (list '* '(variant A) '(variant B))))
   (set `[* () ()]
        `[(variant A) () ()])))

;; v# po -> (Listof [(mk ...) (s ...))
;;
;; Attempts to match the given message against the given pattern. Returns the outputs from every
;; successful judgment for the match relation.
(define (aps#-match-po value pattern)
  (judgment-holds (aps#-matches-po?/j ,value ,pattern any_markers any_forks)
                  [any_markers any_forks]))

(define-judgment-form aps#
  #:mode (aps#-matches-po?/j I I O O)
  #:contract (aps#-matches-po?/j v# po (mk ...) (s ...))

  [-----
   (aps#-matches-po?/j v# * () ())]

  [(aps#-matches-po?/j v# po                  any_self-markers any_forks)
   -----
   (aps#-matches-po?/j v# (or _ ... po _ ...) any_self-markers any_forks)]

  [(side-condition ,(csa#-internal-address? (term a#)))
   ----
   ;; every sent-to-env address should have exactly *one* marker on it, because of the various
   ;; transformations
   (aps#-matches-po?/j (marked a# mk)
                       (delayed-fork (goto φ) Φ ...)
                       ()
                       ([(mk) () (goto φ) (Φ ...) ()]))]

  [(side-condition ,(csa#-internal-address? (term a#)))
   ----
   (aps#-matches-po?/j (marked a# mk) self (mk) ())]

  [(aps#-list-matches-po?/j ((v# po) ...) any_self-markers any_forks)
   ------
   (aps#-matches-po?/j (variant t v# ..._n)
                       (variant t po ..._n)
                       any_self-markers
                       any_forks)]

  ;; Records

  [(aps#-list-matches-po?/j ((v# po) ...) any_self-markers any_forks)
   ------
   (aps#-matches-po?/j (record [l v#] ..._n)
                       (record [l po] ..._n)
                       any_self-markers
                       any_forks)]

  ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
  ;; therefore would not write patterns for them
  [(aps#-matches-po?/j v# po any_self-markers any_forks)
   -------------------------------------------------------------------------------------
   (aps#-matches-po?/j (folded _ v#) po any_self-markers any_forks)])

(define-judgment-form aps#
  #:mode (aps#-list-matches-po?/j I O O)
  #:contract (aps#-list-matches-po?/j ((v# po) ...) (mk ...) (s ...))

  [---------
   (aps#-list-matches-po?/j () () ())]

  [(aps#-matches-po?/j v# po (any_self-markers1 ...) (any_forks1 ...))
   (aps#-list-matches-po?/j (any_rest ...)
                            (any_self-markers2 ...)
                            (any_forks2 ...))
   ---------
   (aps#-list-matches-po?/j ((v# po) any_rest ...)
                            (any_self-markers1 ... any_self-markers2 ...)
                            (any_forks1 ... any_forks2 ...))])

;; TODO: ensure somewhere that at most one self-addr is used

(module+ test
  (test-equal? "Output match with *"
    (aps#-match-po 'abs-nat '*)
    (list `[() ()]))
  (test-equal? "Output-match abs-nat against record"
    (aps#-match-po 'abs-nat '(record))
    null)
  (test-equal? "Output-match address with self"
    (aps#-match-po '(marked (addr 0 0) 1) 'self)
    (list `[(1) ()]))
  (test-equal? "Output-match address with *"
    (aps#-match-po '(marked (addr 0 0) 1) '*)
    (list `[() ()]))
  (test-equal? "Output-match external address with self"
    (aps#-match-po '(marked (addr (env Nat) 0) 1) 'self)
    null)
  (test-equal? "Output-match contained address with self"
    (aps#-match-po '(variant A abs-nat (marked (addr 2 0) 1)) '(variant A * self))
    (list `[(1) ()]))
  (test-equal? "Output-match contained address with *"
    (aps#-match-po '(variant A abs-nat (marked (addr 2 0) 1)) '(variant A * *))
    (list `[() ()]))
  (test-equal? "Variant match with address/or pattern"
    (aps#-match-po '(variant A abs-nat (marked (addr 2 0) 1))
                   '(or (variant A * self) (variant B)))
    (list `[(1) ()]))
  (test-equal? "Variant match with or pattern 2"
    (aps#-match-po (term (variant A)) (term (or (variant A) (variant B))))
    (list `[() ()]))
  (test-equal? "Variant match with or pattern 3"
    (aps#-match-po (term (variant B)) (term (or (variant A) (variant B))))
    (list `[() ()]))
  (test-equal? "Variant match with or pattern 4"
    (aps#-match-po (term (variant C)) (term (or (variant A) (variant B))))
   null)
  (test-equal? "Spawn match po test"
    (aps#-match-po '(marked (addr 'foo 1) 2)
                   '(delayed-fork (goto B) (define-state (B))))
    (list `[() ([(2) () (goto B) ((define-state (B))) ()])]))
  (test-equal? "Full match po test"
    (aps#-match-po '(variant A (marked (addr 'foo 1) 1) (marked (addr 2 0) 2))
                   '(variant A (delayed-fork (goto B) (define-state (B))) self))
    (list `[(2) ([(1) () (goto B) ((define-state (B))) ()])]))
  (test-equal? "Fold test"
    (aps#-match-po `(folded (minfixpt X (Addr (Union [Done] [More X]))) (marked (addr 0 0) 1))
                   '(delayed-fork (goto B) (define-state (B))))
    (list `[() ([(1) () (goto B) ((define-state (B))) ()])]))
  (test-equal? "'Or' pattern can match in multiple ways"
    (list->set (aps#-match-po `(marked (addr 1 0) 2) `(or * self)))
    (set `[() ()]
         `[(2) ()])))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Commitment Satisfaction

;; ;; TODO: need to ensure that the PSM ends up with at most one specified receptionist marker (I think
;; ;; this was originally done in the pattern matching)

;; ;; (s# ...) ((a#ext v# m) ...) -> (Listof (List (s# ...) ([a# po] ...)]))
;; ;;
;; ;; Given a list of all active spec configs (the current one plus any new forks), returns a list of
;; ;; ways to step the given configurations to match the given outputs. Each "way" is a list of stepped
;; ;; configurations and a list of obligations fulfilled as part of those steps (where the obligation may
;; ;; be fulfilled in any one step).
;; (define (aps#-resolve-outputs spec-configs outputs)
;;   (unless (null?
;;            (filter (lambda (addr) (ormap (curryr config-observes-address? addr) spec-configs))
;;                    (externals-in (map csa#-output-message outputs))))
;;     (error 'aps#-resolve-outputs
;;            "Cannot check conformance for program that sends observed external addresses to environment. Violating outputs: ~s"
;;            outputs))
;;   (aps#-resolve-outputs/internal spec-configs outputs))

;; ;; (Listof s# ...) ((a#ext v# m) ...) -> (Listof (List (s# ...) ([a# po] ...)])
;; (define (aps#-resolve-outputs/internal spec-configs outputs)
;;   (match outputs
;;     [(list) (list `(,spec-configs ()))]
;;     [(list output remaining-outputs ...)
;;      (append*
;;       (for/list ([resolved-configs-and-fulfillments (resolve-output/many-configs spec-configs output)])
;;         (match-define (list resolved-configs fulfillments) resolved-configs-and-fulfillments)
;;         ;; returns a list of resolve-results
;;         (for/list ([new-resolved-configs-and-fulfillments (aps#-resolve-outputs/internal resolved-configs remaining-outputs)])
;;           (match-define (list new-configs new-fulfillments) new-resolved-configs-and-fulfillments)
;;           (list new-configs (append fulfillments new-fulfillments)))))]))

;; (module+ test
;;   (define (make-dummy-spec commitments)
;;     (term (() () (goto DummyState) ((define-state (DummyState))) ,commitments)))

;;   (test-equal? "resolve test: no outputs"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec `(((addr (env Nat) 1)))))
;;      (term ()))
;;     (list `[,(list (make-dummy-spec `(((addr (env Nat) 1))))) ()]))
;;   (test-equal? "resolve test 1"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec `(((addr (env Nat) 1)))))
;;      (term (((addr (env Nat) 1) abs-nat single))))
;;     null)
;;   (test-equal? "resolve test 1: many"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec `(((addr (env Nat) 1)))))
;;      (term (((addr (env Nat) 1) abs-nat many))))
;;     null)
;;   (test-equal? "resolve test 2"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec `(((addr (env Nat) 1) *))))
;;      (term (((addr (env Nat) 1) abs-nat single))))
;;     (list `[,(list (make-dummy-spec `(((addr (env Nat) 1)))))
;;             ([(addr (env Nat) 1) *])]))
;;   (test-equal? "resolve test 3"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec `(((addr (env Nat) 1) * (record)))))
;;      (term (((addr (env Nat) 1) abs-nat single))))
;;     (list `[,(list (make-dummy-spec `(((addr (env Nat) 1) (record)))))
;;             (((addr (env Nat) 1) *))]))
;;   (define free-output-spec
;;     (term
;;      (()
;;       ()
;;       (goto S1 (addr (env (Union [A] [B] [C] [D])) 1) (addr (env (Union [A] [B] [C] [D])) 2))
;;       ((define-state (S1 a b)
;;          [x -> ([obligation x *]) (goto S1)]
;;          [x -> ([obligation b *]) (goto S1)]
;;          [free -> ([obligation a (variant A)]) (goto S2)]
;;          [free -> ([obligation a (variant B)]) (goto S1 a b)]
;;          [free -> ([obligation a (variant C)]) (goto S1 a b)]
;;          [free -> ([obligation b (variant D)]) (goto S1 a b)]))
;;       ([(addr (env (Union [A] [B] [C] [D])) 1)] [(addr (env (Union [A] [B] [C] [D])) 2)]))))
;;   (test-equal? "resolve against free outputs"
;;     (aps#-resolve-outputs (list free-output-spec) (term ([(addr (env (Union [A] [B] [C] [D])) 1) (variant C) many])))
;;     (list `[,(list free-output-spec) ()]))

;;   (test-equal? "resolve with unobs transitions"
;;     (aps#-resolve-outputs
;;      (list `[()
;;              ()
;;              (goto A (addr (env (Union [A] [B] [C] [D])) 1))
;;              ((define-state (A x)
;;                 [free -> ([obligation x (variant C)]) (goto B)]))
;;              ([(addr (env (Union [A] [B] [C] [D])) 1)])])
;;      (term ([(addr (env (Union [A] [B] [C] [D])) 1) (variant C) single])))
;;     (list `[,(list
;;               `[()
;;                 ()
;;                 (goto B)
;;                 ((define-state (A x)
;;                    [free -> ([obligation x (variant C)]) (goto B)]))
;;                 ([(addr (env (Union [A] [B] [C] [D])) 1)])])
;;             ([(addr (env (Union [A] [B] [C] [D])) 1) (variant C)])]))

;;   (test-equal? "resolve against two different branches of an 'or' pattern"
;;     (list->set
;;      (aps#-resolve-outputs
;;       (list
;;        (term
;;         (()
;;          ()
;;          (goto S1)
;;          ((define-state (S1)))
;;          ([(addr (env (Addr Nat)) 1) (or * (delayed-fork (goto B)))]))))
;;       (term ([(addr (env (Addr Nat)) 1) (addr 2 0) single]))))
;;     (set
;;      ;; result 1 (match against the fork)
;;      `[,(list
;;          (term
;;           (()
;;            ((Nat (addr 2 0)))
;;            (goto S1)
;;            ((define-state (S1)))
;;            ([(addr (env (Addr Nat)) 1)])))
;;          (term
;;           (((Nat (addr 2 0)))
;;            ()
;;            (goto B)
;;            ()
;;            ())))
;;        ,(list (term [(addr (env (Addr Nat)) 1) (or * (delayed-fork (goto B)))]))]
;;      ;; result 2 (match against *)
;;      `[,(list
;;          (term
;;           (()
;;            ((Nat (addr 2 0)))
;;            (goto S1)
;;            ((define-state (S1)))
;;            ([(addr (env (Addr Nat)) 1)]))))
;;        ,(list (term [(addr (env (Addr Nat)) 1) (or * (delayed-fork (goto B)))]))]))

;;   (test-equal? "Resolve against spawned spec"
;;     (aps#-resolve-outputs
;;      (list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 1) (variant A *)]))
;;            `(() () (goto S2) ((define-state (S2))) ([(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 2) (variant B *)])))
;;      (list `[(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 1) (variant A (addr 1 0)) single]
;;            `[(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 2) (variant B (addr 2 0)) single]))
;;     (list `[,(list `(()
;;                      ((Nat (addr 1 0))
;;                       (Nat (addr 2 0)))
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ([(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 1)]))
;;                    `(()
;;                      ((Nat (addr 1 0))
;;                       (Nat (addr 2 0)))
;;                      (goto S2)
;;                      ((define-state (S2)))
;;                      ([(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 2)])))
;;             ,(list '[(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 1) (variant A *)]
;;                    '[(addr (env (Union [A (Addr Nat)] [B (Addr Nat)])) 2) (variant B *)])]))

;;   (test-equal? "Resolve against self pattern, no existing obs receptionist"
;;     (aps#-resolve-outputs
;;      (list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Addr Nat)) 1) self])))
;;      (list `[(addr (env (Addr Nat)) 1) (addr 1 0) single]))
;;     (list `[,(list `(([Nat (addr 1 0)])
;;                      ()
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ([(addr (env (Addr Nat)) 1)])))
;;             ,(list `[(addr (env (Addr Nat)) 1) self])]))

;;   (test-equal? "Resolve against self pattern, existing obs receptionist"
;;     (aps#-resolve-outputs
;;      (list `(([Nat (addr 1 0)])
;;              ()
;;              (goto S1)
;;              ((define-state (S1)))
;;              ([(addr (env (Addr Nat)) 1) self])))
;;      (list `[(addr (env (Addr Nat)) 1) (addr 1 0) single]))
;;     (list `[,(list `(([Nat (addr 1 0)])
;;                      ()
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ([(addr (env (Addr Nat)) 1)])))
;;             ,(list `[(addr (env (Addr Nat)) 1) self])]))

;;   (test-equal? "Resolve against self pattern, existing other obs receptionist"
;;     (aps#-resolve-outputs
;;      (list `(([Nat (addr 1 0)])
;;              ()
;;              (goto S1)
;;              ((define-state (S1)))
;;              ([(addr (env (Addr Nat)) 1) self])))
;;      (list `[(addr (env (Addr Nat)) 1) (addr 2 0) single]))
;;     null)

;;   (test-equal? "Addresses in unobserved messages are added to receptionists"
;;     (aps#-resolve-outputs
;;      (list `(() () (goto S1) ((define-state (S1))) ())
;;            `(() () (goto S2) ((define-state (S2))) ()))
;;      (list `[(addr (env (Union [A (Addr Nat) (Addr String)])) 1)
;;              (variant A (addr 1 0) (addr 2 0))
;;              single]))
;;     (list `[,(list `(()
;;                      ((Nat (addr 1 0))
;;                       (String (addr 2 0)))
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ())
;;                    `(()
;;                      ((Nat (addr 1 0))
;;                       (String (addr 2 0)))
;;                      (goto S2)
;;                      ((define-state (S2)))
;;                      ()))
;;             ()]))

;;   (test-equal? "Addresses in messages to collective addresses are added to receptionists"
;;     (aps#-resolve-outputs
;;      (list `(() () (goto S1) ((define-state (S1))) ()))
;;      (list `[(collective-addr (env (Union [A (Addr Nat) (Addr String)])))
;;              (variant A (addr 1 0) (addr 2 0))
;;              single]))
;;     (list `[,(list `(()
;;                      ((Nat (addr 1 0))
;;                       (String (addr 2 0)))
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ()))
;;             ()]))

;;   (test-exn "External observed addresses in messages causes resolve-outputs to blow up"
;;     (lambda (exn) #t)
;;     (lambda ()
;;       (aps#-resolve-outputs
;;        (list (make-dummy-spec (list `[(addr (env Nat) 1)])))
;;        (list `[(collective-addr (env (Addr Nat))) (addr (env Nat) 1) single]))))

;;   (test-equal? "External unobserved addresses in messages do not cause blow-up"
;;     (aps#-resolve-outputs
;;      (list (make-dummy-spec (list `[(addr (env Nat) 1)])))
;;      (list `[(collective-addr (env (Addr Nat))) (addr (env Nat) 2) single]))
;;     (list `[,(list (make-dummy-spec (list `[(addr (env Nat) 1)]))) ()]))

;;   (test-equal?
;;       "Resolve against two configs that both observe (e.g. for when transition is both obs and unobs)"
;;     (aps#-resolve-outputs
;;      (list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]))
;;            `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])))
;;      (list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b (variant B)]) single]))
;;     (list `[,(list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)]))
;;                    `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)])))
;;             ,(list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]
;;                    `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])]))

;;   (test-equal?
;;       "Resolve against two configs that both observe, one has multiple possible patterns"
;;     (list->set
;;      (aps#-resolve-outputs
;;       (list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]))
;;             `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])
;;                                                       (record [a *]           [b *])])))
;;       (list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b (variant B)]) single])))
;;     (set `[,(list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)]))
;;                    `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *] [b *])])))
;;             ,(list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]
;;                    `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])]
;;           `[,(list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)]))
;;                    `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])))
;;             ,(list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *] [b (variant B)])]
;;                    `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *] [b *])])])))

;; (define (resolve-output/many-configs configs output)
;;   ;; (printf "resolve-output/many-configs ~s ~s\n" configs output)
;;   (match configs
;;     [(list) (list `[() ()])]
;;     [(list config remaining-configs ...)
;;      (define address (csa#-output-address output))
;;      (define type (csa#-output-type output))
;;      (define message (csa#-output-message output))
;;      (define quantity (csa#-output-multiplicity output))
;;      (append*
;;       (for/list ([resolved-configs-and-fulfillments (resolve-output config address type message quantity)])
;;         (match-define (list resolved-configs fulfillments) resolved-configs-and-fulfillments)
;;         ;; returns a list of resolve-results
;;         (for/list ([remaining-resolve-result (resolve-output/many-configs remaining-configs output)])
;;           (match-define (list remaining-resolved-configs new-fulfillments) remaining-resolve-result)
;;           (list (append resolved-configs remaining-resolved-configs)
;;                 (append fulfillments new-fulfillments)))))]))

;; (module+ test
;;   (test-equal?
;;       "resolve-output/many-configs: Addresses in unobserved messages are added to receptionists"
;;     (resolve-output/many-configs
;;      (list `(() () (goto S1) ((define-state (S1))) ())
;;            `(() () (goto S2) ((define-state (S2))) ()))
;;      `[(addr (env (Union [A (Addr Nat) (Addr String)])) 1) (variant A (addr 1 0) (addr 2 0)) single])
;;     (list `[,(list `(()
;;                      ((Nat (addr 1 0))
;;                       (String (addr 2 0)))
;;                      (goto S1)
;;                      ((define-state (S1)))
;;                      ())
;;                    `(()
;;                      ((Nat (addr 1 0))
;;                       (String (addr 2 0)))
;;                      (goto S2)
;;                      ((define-state (S2)))
;;                      ()))
;;             ()]))

;;   (test-equal? "resolve-output/many-configs: Resolve against two configs that both observe (e.g. for when transition is both obs and unobs)"
;;     (resolve-output/many-configs
;;      (list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]))
;;            `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])))
;;      `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b (variant B)]) single])
;;     (list `[,(list `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)]))
;;                    `(() () (goto S1) ((define-state (S1))) ([(addr (env (Record [a (Union [A])] [b (Union [B])])) 1)])))
;;             ,(list `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a *]           [b (variant B)])]
;;                    `[(addr (env (Record [a (Union [A])] [b (Union [B])])) 1) (record [a (variant A)] [b *])])])))

;; ;; s# a# v# m -> ([(s# ...) ([a po] ...)] ...)
;; ;;
;; ;; Returns a set of tuples each containing a list of specification configs and a set of obligations
;; ;; such that the input configuration can take an output step with the given message to the given
;; ;; configurations and fulfill the resturned obligations to match the message.
;; (define (resolve-output config address type message quantity)
;;   (cond
;;     [(config-observes-address? config address)
;;      (match quantity
;;        ['single
;;         (define config-list-pattern-pairs
;;           (match (resolve-with-obligation config address type message)
;;             [(list)
;;              ;; if we can't find a match with existing patterns, try the free-output patterns
;;              (match (resolve-with-free-obl-patterns config address type message)
;;                [(list)
;;                 ;; if free-output patterns also don't match, try the other free-transition
;;                 ;; patterns as a last resort
;;                 (resolve-with-free-transition config address type message)]
;;                [results results])]
;;             [results results]))
;;         (for/list ([clpp config-list-pattern-pairs])
;;           (match-define (list configs pattern) clpp)
;;           (list configs `([,address ,pattern])))]
;;        ['many
;;         ;; have to use free-output patterns if output may have been sent more than once (e.g. in
;;         ;; a loop)
;;         (map
;;          (lambda (resolve-result)
;;            (match-define `[,configs ,_] resolve-result)
;;            ;; many-of outputs don't fulfill an obligation, because they *might* not
;;            ;; happen. Macro-steps only records the minimal set of fulfillments
;;            (list configs null))
;;          (resolve-with-free-obl-patterns config address type message))])]
;;     [else
;;      ;; TODO: should I save the result of internal-addr-types for performance?
;;      (define exposed-receptionists (internal-addr-types message type))
;;      (list `[,(list (config-merge-unobs-addresses config exposed-receptionists))
;;              ()])]))

;; (module+ test
;;   (test-equal? "resolve-output 1"
;;     (resolve-output
;;      (make-dummy-spec `([(addr (env Nat) 1) *]))
;;      `(addr (env Nat) 1)
;;      `Nat
;;      `abs-nat
;;      `single)
;;     (list `[(,(make-dummy-spec `([(addr (env Nat) 1)]))) ([(addr (env Nat) 1) *])]))
;;   (test-equal? "resolve-output unobserved address"
;;     (resolve-output
;;      `(() () (goto A) ((define-state (A))) ())
;;      `(addr (env (Addr Nat)) 1)
;;      `(Addr Nat)
;;      `(addr 1 0)
;;      `single)
;;     (list `[,(list `(() ([Nat (addr 1 0)]) (goto A) ((define-state (A))) ()))
;;             ()])))

;; ;; s# a# v# -> ([(s# ...) po] ...)
;; (define (resolve-with-obligation config address type message)
;;   (define commitment-patterns
;;     (commitments-for-address (aps#-config-commitment-map config) address))
;;   (match-define (list obs-recs unobs-recs goto state-defs obligations) config)
;;   (define success-results
;;     (filter values (find-matching-patterns message type obs-recs commitment-patterns)))
;;   (for/list ([match-result success-results])
;;     (define matched-pattern (first match-result))
;;     (define remaining-obligations
;;       (aps#-remove-commitment-pattern obligations address matched-pattern))
;;     (list (incorporate-output-match-results `(,obs-recs ,unobs-recs ,goto ,state-defs ())
;;                                             remaining-obligations
;;                                             (rest match-result))
;;           matched-pattern)))

;; (module+ test
;;  (test-equal? "resolve-with-obligation 1"
;;    (resolve-with-obligation
;;     (make-dummy-spec `([(addr (env  Nat) 1) *]))
;;     `(addr (env Nat) 1)
;;     `Nat
;;     `abs-nat)
;;    (list `[,(list (make-dummy-spec `([(addr (env Nat) 1)]))) *])))

;; ;; s# a# v# -> ([(s# ...) po] ...)
;; (define (resolve-with-free-transition config address type message)
;;   (define non-free-stable-transitions
;;     (filter
;;      (negate (curry transition-to-same-state? config))
;;      (get-free-transitions-for-resolution config address)))
;;   (resolve-with-transitions config address type message non-free-stable-transitions))

;; (module+ test
;;   (test-equal? "resolve-with-free-transition with fork"
;;    (resolve-with-free-transition
;;     `[()
;;       ()
;;       (goto A (addr (env (Addr Nat)) 1))
;;       ((define-state (A x)
;;          [free -> ([obligation x [fork (goto C) (define-state (C))]]) (goto B)]))
;;       ([(addr (env (Addr Nat)) 1)])]
;;     `(addr (env (Addr Nat)) 1)
;;     `(Addr Nat)
;;     `(addr 1 0))
;;    `([([([Nat (addr 1 0)])
;;         ()
;;         (goto C)
;;         ((define-state (C)))
;;         ([(addr (env (Addr Nat)) 1)])]
;;        [()
;;         ([Nat (addr 1 0)])
;;         (goto B)
;;         ((define-state (A x)
;;            [free -> ([obligation x [fork (goto C) (define-state (C))]]) (goto B)]))
;;         ()])
;;       self])))

;; ;; s# a# v# (transition# ...) -> ([(s# ...) po] ...)
;; ;;
;; ;; Attempts to resolve the given output step from the given spec config using any one of the given
;; ;; transitions (only one transition per attempt).
;; (define (resolve-with-transitions config address type message possible-transitions)
;;   (for/fold ([results null])
;;             ([trans possible-transitions])
;;     ;; REFACTOR: I'm using a fake trigger here, but attempt-transition probably shouldn't require a
;;     ;; trigger at all
;;     (define all-configs (attempt-transition config trans #f `(timeout (addr 1 0))))
;;     (match-define (list earlier-configs observing-config later-configs)
;;       (find-with-rest (curryr config-observes-address? address) all-configs))
;;     (define exposed-receptionists (internal-addr-types message type))
;;     (define updated-unobserving-configs
;;           (map (curryr config-merge-unobs-addresses exposed-receptionists)
;;                (append earlier-configs later-configs)))
;;     (append
;;      results
;;      (for/list ([result (resolve-with-obligation observing-config address type message)])
;;        (match-define `[,resolved-configs ,pattern] result)
;;        `[,(append resolved-configs updated-unobserving-configs) ,pattern]))))

;; ;; s# a# v# -> ([(s# ...) po] ...)
;; ;;
;; ;; Returns a set of tuples each containing a list of specification configs and a pattern such that the
;; ;; input configuration can take an output step with the given message to the given configurations and
;; ;; using the returned free obligation pattern to match the message.
;; (define (resolve-with-free-obl-patterns config address type message)
;;   (define free-stable-transitions
;;     (filter
;;      (curry transition-to-same-state? config)
;;      (get-free-transitions-for-resolution config address)))
;;   (resolve-with-transitions config address type message free-stable-transitions))

;; s [(mk ...) (s ...)] -> (s ...)
(define (incorporate-output-match-results original-psm match-result)
  (match-define (list matched-self-markers matched-forks) match-result)
  (match-define (list original-mon-inputs original-mon-exts goto state-defs obligations) original-psm)
  (define updated-mon-inputs (remove-duplicates (append matched-self-markers original-mon-inputs)))
  (when (> (length updated-mon-inputs) 1)
    (error 'incorporate-output-match-results "Cannot have more than one monitored input marker"))
  (define updated-original-psm
    `[,updated-mon-inputs
      ,original-mon-exts
      ,goto
      ,state-defs
      ,obligations])
  (cons updated-original-psm matched-forks))

(module+ test
  (test-equal? "incorporate-output-match-results 1"
    (incorporate-output-match-results
     `(() () (goto A) ((define-state (A))) ())
     `[(1) ()])
    (list `[(1) () (goto A) ((define-state (A))) ()]))

  (test-equal? "incorporate-output-match-results with delayed-fork"
    (list->set
     (incorporate-output-match-results
      `(() () (goto A) ((define-state (A))) ([1 *]))
      `[() ([(2) () (goto B) ((define-state (B))) ()])]))
    (set
     `(() () (goto A) ((define-state (A))) ([1 *]))
     `((2) () (goto B) ((define-state (B))) ()))))

(define (aps#-config-has-commitment? config marker pattern)
  (member `[,marker ,pattern] (aps#-psm-obligations config)))

(module+ test
  (define has-commitment-test-config
    (term (()
           ()
           (goto S1)
           ()
           ([1 *] [2 *] [2 (record)]))))
  (test-false "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term 3) (term *)))
  (test-false "aps#-config-has-commitment? 2"
    (aps#-config-has-commitment? has-commitment-test-config (term 1) (term (record))))
  (test-not-false "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term 2) (term (record)))))

;; Returns #t if this transition goes to the given state and has exactly one effect (an obligation)
(define (free-stable-transition? transition full-state)
  (match transition
    [`(free -> ([obligation ,_ ,_]) ,(== full-state)) #t]
    [_ #f]))

;; s# a# -> ([pt -> (f ...) (goto φ u ...)])
;;
;; Returns the transitions (after subsitution with the current state arguments) of the PSM that have an unobs
;; trigger and a single obligation effect
(define (get-free-transitions-for-resolution psm target-marker)
  (filter
   (lambda (trans)
     (match trans
       [`(free -> ([obligation ,obligation-marker ,_]) ,_)
        (equal? obligation-marker target-marker)]
       [_ #f]))
   (config-current-transitions psm)))

(module+ test
  (define free-transition-spec
    (term
     (()
      ()
      (goto S1 1 2)
      ((define-state (S1 a b)
         [x -> ([obligation x *]) (goto S1)]
         [x -> ([obligation b *]) (goto S1)]
         [free -> ([obligation a (variant A)]) (goto S2 a b)]
         [free -> ([obligation a (variant B)]) (goto S2 a a)]
         [free -> ([obligation a (variant C)]) (goto S1 a b)]
         [free -> ([obligation b (variant D)]) (goto S1 a b)]
         [free -> ([obligation b (variant E)]) (goto S2 a b)]))
      ())))
  (check-equal?
   (get-free-transitions-for-resolution free-transition-spec 1)
   `([free -> ([obligation 1 (variant A)]) (goto S2 1 2)]
     [free -> ([obligation 1 (variant B)]) (goto S2 1 1)]
     [free -> ([obligation 1 (variant C)]) (goto S1 1 2)]))
  (check-equal?
   (get-free-transitions-for-resolution free-transition-spec 2)
   `([free -> ([obligation 2 (variant D)]) (goto S1 1 2)]
     [free -> ([obligation 2 (variant E)]) (goto S2 1 2)])))

(define (transition-to-same-state? config transition)
  (equal? (aps#-transition-goto transition) (aps#-psm-current-state config)))

(module+ test
  (let ([transition-test-config `[() () (goto A 1) () ()]])
    (test-true "transition-to-same-state? true"
      (transition-to-same-state? transition-test-config `[free -> () (goto A 1)]))
    (test-false "transition-to-same-state? wrong state"
      (transition-to-same-state? transition-test-config `[free -> () (goto B 1)]))
    (test-false "transition-to-same-state? wrong address"
      (transition-to-same-state? transition-test-config `[free -> () (goto A 2)]))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-psm-mon-receptionists psm)
  (redex-let aps# ([((mk ...) _ ...) psm])
    (term (mk ...))))

(define (aps#-psm-mon-externals psm)
  (redex-let aps# ([(_ (mk ...) _ ...) psm])
    (term (mk ...))))

(module+ test
  (define mon-markers-test-psm `[(2) (0 1) (goto A) () ()])
  (test-true "valid psm: mon-markers-test-psm" (redex-match? aps# s# mon-markers-test-psm))
  (test-equal? "mon-receptionists "(aps#-psm-mon-receptionists mon-markers-test-psm) `(2))
  (test-equal? "mon-externals" (aps#-psm-mon-externals     mon-markers-test-psm) `(0 1)))

(define (aps#-psm-state-defs psm)
  (redex-let aps# ([(_ _ _ any_state-defs _) psm])
             (term any_state-defs)))

(define (aps#-psm-current-state psm)
  (redex-let aps# ([(_ _ any_goto _ ...) psm])
    (term any_goto)))

(define (aps#-psm-current-state-args psm)
  (aps#-goto-args (aps#-psm-current-state psm)))

(define (aps#-psm-obligations psm)
  (term (psm-obligations/mf ,psm)))

(define-metafunction aps#
  psm-obligations/mf : s# -> O
  [(psm-obligations/mf (_ _ _ _ O)) O])

(module+ test
  (test-equal? "aps#-psm-obligations"
    (aps#-psm-obligations
     `(()
       (1 2 3)
       (goto S1)
       ()
       ([1 *]
        [1 (record)]
        [3 *]
        [3 (variant A)]
        [3 (record [a *])])))
    (term ([1 *]
           [1 (record)]
           [3 *]
           [3 (variant A)]
           [3 (record [a *])]))))

(define (aps#-transition-trigger transition)
  (redex-let aps# ([(pt -> _ _) transition])
    (term pt)))

(define (aps#-transition-effects transition)
  (third transition))

(define (aps#-transition-goto transition)
  (fourth transition))

(define (aps#-goto-args goto-exp)
  (rest (rest goto-exp)))

(define (aps#-obligation-dest o)
  (first o))

(define (aps#-obligation-pattern o)
  (second o))

(define (obligations-for-marker obligations marker)
  (map aps#-obligation-pattern
       (filter (lambda (obl) (equal? (aps#-obligation-dest obl) marker))
               obligations)))

(module+ test
  (define test-O
    (term ((1 *)
           (1 (record))
           (2 (variant True))
           (2 (variant False)))))
  (check-equal?
   (obligations-for-marker test-O (term 1))
   (term (* (record))))
  (check-equal?
   (obligations-for-marker test-O (term 2))
   (term ((variant True) (variant False))))
  (check-equal?
   (obligations-for-marker test-O (term 3))
   null))

;; ---------------------------------------------------------------------------------------------------
;; Spec Split

;; s# -> (Listof s#)
;;
;; Splits the given PSM into multiple PSMs, to ensure the space of explored PSMs is finite. For each
;; monitored external marker in the commitment map that is not a state argument and does not have a
;; "self" pattern in one of its patterns (and therefore will never have more obligations addeded nor
;; be needed to resolve the current self address), it creates a new PSM consisting only of the
;; obligations on that marker and a dummy FSM with no transitions. After removing those obligations,
;; the remaining PSM is also returned.
(define (split-psm psm)
  ;; A marker is "relevant" if it is a state argument or one of its obligation patterns contains the
  ;; "self" pattern. For each irrelevant marker, we split off a new PSM.
  (define-values (relevant-markers irrelevant-markers)
    (partition
     (lambda (marker)
       (or (member marker (aps#-psm-current-state-args psm))
           (ormap pattern-contains-self? (obligations-for-marker (aps#-psm-obligations psm) marker))))
     (aps#-psm-mon-externals psm)))
  (define obligation-only-psms
    (for/list ([marker irrelevant-markers])
      (aps#-psm-from-marker-and-obligations
       marker
       (obligations-for-marker (aps#-psm-obligations psm) marker))))
  (cons (term (,(aps#-psm-mon-receptionists psm)
               ,relevant-markers
               ,(aps#-psm-current-state psm)
               ,(aps#-psm-state-defs psm)
               ,(filter
                 (lambda (obl) (member (aps#-obligation-dest obl) relevant-markers))
                 (aps#-psm-obligations psm))))
        obligation-only-psms))

(module+ test
  (define (make-simple-psm-for-split-test mon-exts obligations)
    (redex-let aps# ([s# (term
                          (()
                           ,mon-exts
                           (goto A 0)
                           ((define-state (A x) [* -> () (goto A x)]))
                           ,obligations))])
      (term s#)))

  (test-equal? "split spec with one FSM gets same spec"
    (split-psm (make-simple-psm-for-split-test '() '()))
    (list (make-simple-psm-for-split-test '() '())))

  (test-equal? "split with one related commit"
    (split-psm (make-simple-psm-for-split-test `(0) `([0 *])))
    (list (make-simple-psm-for-split-test  `(0) `([0 *]))))

  (test-same-items? "split with unrelated commit"
    (split-psm (make-simple-psm-for-split-test `(1) `([1 *])))
    (list (make-simple-psm-for-split-test `() `())
         (aps#-psm-from-marker-and-obligations 1 (list `*))))

  (test-equal? "split a dummy state"
    (split-psm (aps#-psm-from-marker-and-obligations 1 (list `*)))
    (list (aps#-psm-from-marker-and-obligations 1 (list `*))))

  (test-equal? "split a spec with a 'self' commitment"
    (split-psm (term (()
                      (1)
                      (goto A)
                      ()
                      ((1 self)))))
    (list (term (()
                 (1)
                 (goto A)
                 ()
                 ((1 self)))))))

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
     `(fork (goto A) (define-state (A x) [free -> ([obligation x self]) (goto A x)]))))
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

;; Makes a PSM with no observed receptionist, a single observed external, and an FSM with no transitions. Used for
;; specifications where only the commitments are important.
(define (aps#-psm-from-marker-and-obligations mon-external obl-patterns)
  (term (()
         (,mon-external)
         (goto DummySpecFsmState ,mon-external)
         ((define-state (DummySpecFsmState x)))
         ,(map (lambda (p) `[,mon-external ,p]) obl-patterns))))

(module+ test
  (test-equal? "aps#-psm-from-marker-and-obligations"
    (aps#-psm-from-marker-and-obligations 0 (list `*))
    `(()
      (0)
      (goto DummySpecFsmState 0)
      ((define-state (DummySpecFsmState x)))
      ([0 *])))

  (test-equal? "aps#-psm-from-marker-and-obligations 2"
    (aps#-psm-from-marker-and-obligations 0 `(* (record [a *] [b *])))
    `(()
      (0)
      (goto DummySpecFsmState 0)
      ((define-state (DummySpecFsmState x)))
      ([0 *] [0 (record [a *] [b *])]))))

(define (aps#-completed-no-transition-psm? s)
  ;; A configuration is a completed, no-transition configuration if its only current transition is the
  ;; implicit do-nothing transition, it has no remaining obligations, and no observable receptionist.
  (and (null? (aps#-psm-mon-receptionists s))
       (= 1 (length (config-current-transitions s)))
       (null? (aps#-psm-obligations s))))

(module+ test
  ;; empty config set, non-empty configs, other kind of spec config with empty coms
  (test-case "completed-no-transition-psm?: no commitments"
    (redex-let aps# ([s# (aps#-psm-from-marker-and-obligations 1 null)])
      (check-true (aps#-completed-no-transition-psm? (term s#)))))
  (test-case "completed-no-transition-psm?: some commitments"
    (redex-let aps# ([s# (aps#-psm-from-marker-and-obligations 1 (list `*))])
      (check-false (aps#-completed-no-transition-psm? (term s#)))))
  (test-case "completed-no-transition-psm?: spec with transitions, no commitments"
    (redex-let aps# ([s#
                      `(()
                        ()
                        (goto A)
                        ((define-state (A) [free -> () (goto A)]))
                        ())])
      (check-false (aps#-completed-no-transition-psm? (term s#)))))
  (test-case "completed-no-transition-psm?: observed receptionist"
    (redex-let aps# ([s#
                      `((1)
                        ()
                        (goto A)
                        ((define-state (A)))
                        ())])
      (check-false (aps#-completed-no-transition-psm? (term s#))))))

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization (i.e. renaming)

;; Given an impl config/PSM pair, transforms it into an equivalent (for the purpose of conformance),
;; canonical form. Also returns the address and marker rename maps. Specifically:
;;
;; 1. Changes all spawn address ages (0/1) to 0 (assumes that these configs have already been
;; blurred so that either a 0 or a 1 version of an address exists, but not both)
;;
;; 2. Renames all markers such that the specified receptionist (if any) gets 0, then the state
;; arguments of the PSM, then the (at most one) monitored external that is not a state argument.
;;
;; 3. Also sorts the components of the config and PSM (not strictly necessary to ensure a bounded
;; state space, but provides a form of symmetry reduction).
(define (canonicalize-pair impl-config psm)
  (match-define `(,aged-impl-config ,addr-substitutions) (csa#-age-addresses impl-config))
  (define markers-to-rename
    (remove-duplicates
     (append
      (aps#-psm-mon-receptionists psm)
      (aps#-psm-current-state-args psm)
      (map aps#-obligation-dest (aps#-psm-obligations psm)))))

  (define marker-substitutions
    (for/list ([old-marker markers-to-rename]
               [new-marker (build-list (length markers-to-rename) values)])
      `[,old-marker ,new-marker]))
  (define renamed-impl-config (csa#-rename-markers aged-impl-config marker-substitutions))
  (define renamed-spec-config (aps#-rename-markers psm marker-substitutions))
  (list (csa#-sort-config-components renamed-impl-config)
        (aps#-sort-psm-components renamed-spec-config)
        addr-substitutions
        marker-substitutions))

(module+ test
  (test-equal? "canonicalize 1"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((addr 0 0)
             (((define-state (A) (m) (goto A)))
              (goto A
                    (marked (addr (env Nat) 0) 3)
                    (marked (addr (env Nat) 0) 2)
                    (marked (addr (env Nat) 0) 4)))))
      (term ([Nat (marked (addr 0 0) 7)])))
     (term
      ((7)
       (2 3 4)
       (goto A 4 3 2)
       ((define-state (A a b c) [* -> () (goto A)]))
       ([2 *] [3 (record)]))))
    (list
     (make-single-actor-abstract-config
      (term ((addr 0 0)
             (((define-state (A) (m) (goto A)))
              (goto A
                    (marked (addr (env Nat) 0) 2)
                    (marked (addr (env Nat) 0) 3)
                    (marked (addr (env Nat) 0) 1)))))
      (term ([Nat (marked (addr 0 0) 0)])))
     (term
      ((0)
       (1 2 3)
       (goto A 1 2 3)
       ((define-state (A a b c) [* -> () (goto A)]))
       ([2 (record)] [3 *])))
     `([(addr 0 0) (addr 0 0)])
     `([7 0]
       [4 1]
       [3 2]
       [2 3])))

  (test-equal? "canonicalize spec config with self patterns"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((addr 1 0) (() (goto A (marked (addr (env Nat) 0) 57)))))
      '())
     `[()
       ()
       (goto B)
       ()
       ([57 self])])
    `[,(make-single-actor-abstract-config
        (term ((addr 1 0) (() (goto A (marked (addr (env Nat) 0) 0)))))
        '())
      [()
       ()
       (goto B)
       ()
       ([0 self])]
      ([(addr 1 0) (addr 1 0)])
      ([57 0])]))

(define (aps#-rename-markers psm subst)
  (define (rename-marker m)
    (second (assoc m subst)))
  (match-define `[,mon-recs ,mon-exts (goto ,state ,args ...) ,state-defs ,obls] psm)
  `[,(map rename-marker mon-recs)
    ,(map rename-marker mon-exts)
    (goto ,state ,@(map rename-marker args))
    ,state-defs
    ,(map (lambda (obl)
            `[,(rename-marker (aps#-obligation-dest obl))
              ,(aps#-obligation-pattern obl)])
          obls)])

(module+ test
  (test-equal? "aps#-rename-markers"
    (aps#-rename-markers
     (term
      ((7)
       (2 3 4)
       (goto A 4 3 2)
       ((define-state (A a b c) [* -> () (goto A)]))
       ([2 *] [3 (record)])))
     `([7 0]
       [4 1]
       [3 2]
       [2 3]))
    (term
     ((0)
      (3 2 1)
      (goto A 1 2 3)
      ((define-state (A a b c) [* -> () (goto A)]))
      ([3 *] [2 (record)])))))

;; Returns a spec config identical to the given one, except that the the obs-recs, obs-exts, and obls
;; are sorted
(define (aps#-sort-psm-components psm)
  (match-define `[,mon-recs ,mon-exts ,state ,state-defs ,obls] psm)
  `[,(sort mon-recs sexp<?)
    ,(sort mon-exts sexp<?)
    ,state
    ,state-defs
    ,(sort obls sexp<?)])

;; (define (try-rename-address rename-map addr)
;;   (match-define `(addr ,loc ,old-id) addr)
;;   (match (findf (lambda (entry) (eq? (first entry) old-id)) rename-map)
;;     [#f #f]
;;     [(list _ new-id) `(addr ,loc ,new-id)]))

;; (module+ test
;;   (test-equal? "try-rename-address success"
;;     (try-rename-address (term ([1 3] [2 4])) (term (addr (env Nat) 2)))
;;     (term (addr (env Nat) 4)))
;;   (test-false "try-rename-address failure"
;;     (try-rename-address (term ([1 3] [2 4])) (term (addr (env Nat) 5)))))

;; ;; Performs the reverse of the mapping indicated by the given address rename map on the given address
;; (define (reverse-rename-address rename-map addr)
;;   (match-define `(addr ,loc ,id) addr)
;;   (match (findf (lambda (entry) (equal? (second entry) id)) rename-map)
;;     [#f (error 'reverse-rename-address "Unable to find entry for ~s in ~s" addr rename-map)]
;;     [(list prev _) (term (addr ,loc ,prev))]))

;; (module+ test
;;   (test-equal? "try-rename-address success"
;;     (reverse-rename-address (term ([1 3] [2 4])) (term (addr (env Nat) 4)))
;;     (term (addr (env Nat) 2))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Eviction

;; (define (evict-pair i s)
;;   ;; TODO: add the rename map stuff (although technically it's not needed, since the only changed
;;   ;; addresses are no longer in the resulting configuration
;;   (for/fold ([pair (list i s)])
;;             ;; need to check for obs externals, obs internal
;;             ([addr (csa#-addrs-to-evict i)])
;;     (match (aps#-config-obs-receptionists s)
;;       [(list `(,_ (? (curry equal? addr)))) pair]
;;       [_
;;        (match-define (list new-impl-config new-unobs-receptionists)
;;          (csa#-evict i addr))
;;        (define all-unobs-receptionists
;;          (merge-receptionists
;;           (remove-receptionist (aps#-config-unobs-receptionists s) addr)
;;           new-unobs-receptionists))
;;        (define new-spec-config
;;          `(,(aps#-config-obs-receptionists s)
;;            ,all-unobs-receptionists
;;            ,(aps#-config-current-state s)
;;            ,(aps#-config-state-defs s)
;;            ,(aps#-config-commitment-map s)))
;;        (list new-impl-config new-spec-config)])))

;; (module+ test
;;   (test-equal? "evict-pair"
;;     (evict-pair
;;      `[([(addr 1 0)
;;          [((define-state (A) (m)
;;              (begin (addr (EVICT Nat ()) 0)
;;                     (goto A))))
;;           (goto A)]]
;;         [(addr (EVICT Nat ()) 0)
;;          [((define-state (B [x (Addr String)]) (m) (goto B x)))
;;           (goto B (addr 2 0))]])
;;        ()
;;        ()]
;;      `[()
;;        ((Nat (addr 1 0)) (Nat (addr (EVICT Nat ()) 0)))
;;        (goto A)
;;        ()
;;        ()])
;;     (list
;;      `[([(addr 1 0)
;;          [((define-state (A) (m)
;;              (begin (collective-addr (env Nat))
;;                     (goto A))))
;;           (goto A)]])
;;        ()
;;        ()]
;;      `[()
;;        ((Nat (addr 1 0))
;;         (String (addr 2 0)))
;;        (goto A)
;;        ()
;;        ()])))

;; (define (remove-receptionist receptionists addr-to-remove)
;;   (filter (lambda (rec) (not (equal? (second rec) addr-to-remove)))
;;           receptionists))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Widening helpers

;; ;; s# s# -> Boolean
;; ;;
;; ;; A spec config s1 is <= s2 if they are identical except for their unobserved interface, which must
;; ;; have (at most) strictly grown in s2 compared to s1
;; (define (aps#-config<= s1 s2)
;;   (match-let ([(list `(,obs1 ,unobs1 ,goto1 ,states1 ,obligations1)
;;                      `(,obs2 ,unobs2 ,goto2 ,states2 ,obligations2))
;;                (list s1 s2)])
;;     (and (equal? (list obs1 goto1 states1 obligations1)
;;                  (list obs2 goto2 states2 obligations2))
;;          (receptionists<= unobs1 unobs2))))

;; (module+ test
;;   (test-true "config<= for identical configs"
;;     (aps#-config<=
;;      `(([Nat (addr 1 0)])
;;        ()
;;        (goto A)
;;        ()
;;        ())
;;      `(([Nat (addr 1 0)])
;;        ()
;;        (goto A)
;;        ()
;;        ())))
;;   (test-true "config<= for configs with <= unobs interfaces"
;;     (aps#-config<=
;;      `(([Nat (addr 1 0)])
;;        ([(Union [A]) (addr 2 0)])
;;        (goto S)
;;        ()
;;        ())
;;      `(([Nat (addr 1 0)])
;;        ([(Union [A] [B]) (addr 2 0)])
;;        (goto S)
;;        ()
;;        ())))
;;   (test-false "config<= for configs with incomparable unobs interfaces"
;;     (aps#-config<=
;;      `(([Nat (addr 1 0)])
;;        ([(Union [A]) (addr 2 0)])
;;        (goto S)
;;        ()
;;        ())
;;      `(([Nat (addr 1 0)])
;;        ([Nat (addr 1 0)])
;;        (goto S)
;;        ()
;;        ()))))

;; ;; (τa ...) (τa ...) -> Boolean
;; ;;
;; ;; An interface i1 is <= i2 if i2 contains all addresses from i1 and has a >= type for each address
;; (define (receptionists<= i1 i2)
;;   (for/and ([typed-addr1 i1])
;;     (match (findf (lambda (typed-addr2) (equal? (second typed-addr1) (second typed-addr2))) i2)
;;       [#f #f]
;;       [(list type2 _) (type<= (first typed-addr1) type2)])))

;; (module+ test
;;   (test-true "receptionists<= for equal interfaces"
;;     (receptionists<= `([Nat (addr 1 0)]) `([Nat (addr 1 0)])))
;;   (test-false "receptionists<= for interfaces with different addresses"
;;     (receptionists<= `([Nat (addr 1 0)]) `([Nat (addr 2 0)])))
;;   (test-true "receptionists<= where one interface has a new address"
;;     (receptionists<= `([Nat (addr 1 0)])
;;                      `([Nat (addr 1 0)] [Nat (addr 2 0)])))
;;   (test-true "receptionists<= where one interface expands the type"
;;     (receptionists<= `([(Union [A])     (addr 1 0)])
;;                      `([(Union [A] [B]) (addr 1 0)])))
;;   (test-false "receptionists<= where one interface shrinks the type"
;;     (receptionists<= `([(Union [A] [B]) (addr 1 0)])
;;                      `([(Union [A])     (addr 1 0)]))))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-s# defs goto out-coms)
  (term ((0) () ,goto ,defs ,out-coms)))

(define (valid-s# psm)
  (redex-let aps# ([s# psm])
    (term s#)))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Debugging

(define (spec-config-without-state-defs config)
  (match-define `[,mon-recs ,mon-exts ,goto ,_ ,obls] config)
  `[,mon-recs ,mon-exts ,goto ,obls])
