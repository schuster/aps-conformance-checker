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
;;  split-spec
;;  aps#-blur-config
;;  canonicalize-pair
;;  try-rename-address
;;  reverse-rename-address
;;  aps#-config-has-commitment?
;;  aps#-completed-no-transition-config?
;;  evict-pair
;;  ;; needed for widening
;;  aps#-config<=

;;  ;; Required only for testing
;;  aps#

;;  ;; Required by conformance checker for blurring
;;  aps#-relevant-external-addrs

;;  ;; Testing helpers
;;  make-s#
;;  aps#-make-no-transition-config

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

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Transition selection

;; ;; Returns the syntax for each transition of the FSM in the spec config
;; (define (config-current-transitions config)
;;   (term (config-current-transitions/mf ,config)))

;; ;; FIX: deal with the case where the pattern variables shadow the state variables
;; (define-metafunction aps#
;;   config-current-transitions/mf : s# -> ((pt -> (f ...) (goto φ u ...)) ...)
;;   [(config-current-transitions/mf
;;     (_
;;      _
;;      (goto φ a# ...)
;;      (_ ... (define-state (φ x ...) (pt -> (f ...) (goto φ_trans u_trans ...)) ...) _ ...)
;;      _))
;;    ((pt ->
;;         ((subst-n/aps#/f f (x a#) ...) ...)
;;         (goto φ_trans (subst-n/aps#/u u_trans (x a#) ...) ...)) ...
;;     ;; Note that we include the "null"/no-step transition
;;     (free -> () (goto φ a# ...)))])

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Evaluation

;; ;; s# bool trigger -> ([s# ...] ...)
;; ;;
;; ;; Returns all spec configs that can possibly be reached in one step by transitioning from the given
;; ;; trigger, also returning spec configs spawned during that transition
;; (define (aps#-matching-steps spec-config observed? unobserved? trigger)
;;   ;; The semantics for specs says it has to take an obs step if the trigger is observed, and
;;   ;; unobserved step if the trigger is unobserved, and both if it can be both observed and
;;   ;; unobserved. So here we compute all ways to do an obs transition, all ways to do an unobs
;;   ;; transition, then find all possible combinations of those different transitions.
;;   (define available-transitions
;;     ;; Remove the free-output transitions: these would cause the checker to make many "bad
;;     ;; guesses" about what conforms to what, and the outputs they use can always be used for
;;     ;; other transitions.
;;     (filter (negate (curryr free-stable-transition? (aps#-config-current-state spec-config)))
;;             (config-current-transitions spec-config)))
;;   (define (possible-transitions-for from-observer?)
;;     (define raw-results
;;       (filter values
;;        (map (lambda (t) (attempt-transition spec-config t from-observer? trigger))
;;             available-transitions)))
;;     (when (null? raw-results)
;;       (error 'aps#-matching-steps
;;              "The trigger ~s (from-observer: ~s) has no way to transition in spec config ~s"
;;              trigger from-observer? (spec-config-without-state-defs spec-config)))
;;     (filter (lambda (transitioned-configs)
;;               (and
;;                ;; can run into infinite loop if we allow multiple observed addresses to have an
;;                ;; obligation with "self" in the pattern, so we eliminate those transitions
;;                (<= (length (addrs-with-self-obligations (first transitioned-configs))) 1)
;;                ;; can also run into infinite loop if we allow multiple obligations, so we only use
;;                ;; transitions that don't duplicate them
;;                (andmap all-obligations-unique? transitioned-configs)))
;;             raw-results))
;;   (define obs-steps
;;     (cond
;;       [observed? (possible-transitions-for #t)]
;;       [else
;;        ;; if not observed, return a list containing a single "empty" transition so we can combine the
;;        ;; unobs moves with something
;;        (list null)]))
;;   (define unobs-steps
;;     (cond
;;       [unobserved? (possible-transitions-for #f)]
;;       [else
;;        ;; if not unobserved, return a list containing a single "empty" transition so we can combine
;;        ;; the obs moves with something
;;        (list null)]))

;;   (remove-duplicates
;;    (for/fold ([all-steps null])
;;              ([obs-step obs-steps])
;;      (define this-step-with-unobs-steps
;;        (for/list ([unobs-step unobs-steps])
;;          (remove-duplicates (append obs-step unobs-step))))
;;      (append all-steps this-step-with-unobs-steps))))

;; (module+ test
;;   (test-equal? "Null step is possible"
;;                (aps#-matching-steps
;;                 (make-s# (term ((define-state (A))))
;;                          (term (goto A))
;;                          (term ())
;;                          (term ()))
;;                 #f #t
;;                 (term (timeout (addr 0 0))))
;;                (list
;;                 (list (make-s# (term ((define-state (A))))
;;                          (term (goto A))
;;                          (term ())
;;                          (term ())))))

;;   (test-case "Can do obs and unobs at same time"
;;     (define (make-test-config current-state)
;;       (make-s# (term ((define-state (A)
;;                         [*     -> () (goto B)]
;;                         [free -> () (goto C)])))
;;                (term (goto ,current-state))
;;                (term ())
;;                (term ())))
;;     (check-equal?
;;      (list->set
;;       (aps#-matching-steps (make-test-config 'A)
;;                            #t #t
;;                            (term (external-receive (addr 0 0) abs-nat))))
;;      (set
;;       ;; Option 1: A and B
;;       (list (make-test-config 'B) (make-test-config 'A))
;;       ;; Option 2: A and C
;;       (list (make-test-config 'B) (make-test-config 'C)))))

;;   (test-equal? "Don't allow multiple copies of obligations"
;;     (aps#-matching-steps
;;      (make-s# (term ((define-state (A r) [* -> ((obligation r *)) (goto A r)])))
;;               (term (goto A (addr (env Nat) 0)))
;;               null
;;               (term (((addr (env Nat) 0) *))))
;;      #t #f
;;      (term (external-receive (addr 0 0) abs-nat)))
;;     null)

;;   (test-exn "No match for a trigger leads to exception"
;;     (lambda (exn) #t)
;;     (lambda ()
;;       (aps#-matching-steps
;;        (make-s# (term ((define-state (A r))))
;;                 (term (goto A (addr (env Nat) 0)))
;;                 null
;;                 (term (((addr (env Nat) 0)))))
;;        #t #f
;;        (term (external-receive (addr 0 0) abs-nat)))))

;;   (test-equal? "Spec observes address but neither saves it nor has obligations for it"
;;     (aps#-matching-steps
;;      (make-s# `((define-state (A) [r -> () (goto A)]))
;;               `(goto A)
;;               null
;;               null)
;;      #t #f
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     (list `[,(make-s# `((define-state (A) [r -> () (goto A)]))
;;                       `(goto A)
;;                       null
;;                       `([(addr (env Nat) 1)]))]))

;;   (test-equal? "Unobserved address not tracked in obligation map"
;;     (aps#-matching-steps
;;      (make-s# `((define-state (A) [r -> () (goto A)]))
;;               `(goto A)
;;               null
;;               null)
;;      #f #t
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     (list `[,(make-s# `((define-state (A) [r -> () (goto A)]))
;;                       `(goto A)
;;                       null
;;                       null)]))

;;   (test-equal? "Address matched by wildcard not tracked in obligation map"
;;     (aps#-matching-steps
;;      (make-s# `((define-state (A) [* -> () (goto A)]))
;;               `(goto A)
;;               null
;;               null)
;;      #t #f
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     (list `[,(make-s# `((define-state (A) [* -> () (goto A)]))
;;                       `(goto A)
;;                       null
;;                       null)]))

;;   (test-equal? "Don't return transitions that would have addrs with multiple self obls"
;;     (aps#-matching-steps
;;      (make-s# `((define-state (A) [r -> ([obligation r self]) (goto A)]))
;;               `(goto A)
;;               null
;;               `([(addr (env Nat) 2) self]))
;;      #t #f
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     null))

;; (define (addrs-with-self-obligations config)
;;   (map aps#-commitment-entry-address
;;        (filter
;;         (lambda (obl-map-entry)
;;           (ormap pattern-contains-self?
;;                  (aps#-commitment-entry-patterns obl-map-entry)))
;;         (aps#-config-commitment-map config))))

;; (module+ test
;;   (test-equal? "Addresses with self obligation"
;;     (addrs-with-self-obligations
;;      `(() () (goto A) () ([(addr 0 0) self]
;;                           [(addr 0 1) *]
;;                           [(addr 0 2) (record [a *] [b self])])))
;;     (list `(addr 0 0) `(addr 0 2))))

;; (define (all-obligations-unique? config)
;;   (andmap
;;    (lambda (entry)
;;      (if (check-duplicates (aps#-commitment-entry-patterns entry))
;;          #f
;;          #t))
;;    (aps#-config-commitment-map config)))

;; (module+ test
;;   (test-true "Does not have duplicate obligations"
;;     (all-obligations-unique? `(() () (goto A) () ([(addr 0 0) * (variant A)]))))
;;   (test-false "Has duplicate obligations"
;;     (all-obligations-unique? `(() () (goto A) () ([(addr 0 0) (variant A) * (variant A) ])))))

;; ;; s# spec-state-transition bool trigger -> [s# ...] or #f
;; ;;
;; ;; Returns the config updated by running the given transition, if it can be taken from the given
;; ;; trigger, along with all configs spawned in the transition, or #f if the transition is not possible
;; ;; from this trigger
;; (define (attempt-transition config transition from-observer? trigger)
;;   (match (match-trigger from-observer?
;;                         trigger
;;                         (aps#-config-obs-receptionists config)
;;                         (aps#-transition-trigger transition))
;;     [#f #f]
;;     [(list bindings ...)
;;      (match-define (list new-obligations pre-configs)
;;        (perform (subst-into-effects (aps#-transition-effects transition) bindings)
;;                 (merge-receptionists (aps#-config-obs-receptionists config)
;;                                      (aps#-config-unobs-receptionists config))))
;;      (define updated-obligation-map
;;        (term
;;         (add-commitments
;;          ,(observe-addresses-from-subst
;;            (aps#-config-commitment-map config) bindings)
;;          ,@new-obligations)))
;;      (define stepped-current-pre-config
;;        (term (,(aps#-config-obs-receptionists config)
;;               ,(aps#-config-unobs-receptionists config)
;;               ,(subst-into-goto (aps#-transition-goto transition) bindings)
;;               ,(aps#-config-state-defs config)
;;               ())))
;;      (dist stepped-current-pre-config pre-configs updated-obligation-map)]))

;; (module+ test
;;   (test-equal? "Transition should put observed no-commitment addresses in commitment map"
;;     (attempt-transition
;;      `((((Addr Nat) (addr 0 0)))
;;        ()
;;        (goto A)
;;        ((define-state (A) [r -> () (goto A)]))
;;        ())
;;      `[r -> () (goto A)]
;;      #t
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     (list
;;      `((((Addr Nat) (addr 0 0)))
;;        ()
;;        (goto A)
;;        ((define-state (A) [r -> () (goto A)]))
;;        ([(addr (env Nat) 1)]))))

;;   (test-equal? "Address with commitments and added to state arg should be added exactly once to obligations"
;;     (attempt-transition
;;      `((((Addr Nat) (addr 0 0)))
;;        ()
;;        (goto A)
;;        ((define-state (A) [r -> ([obligation r *]) (goto B r)]))
;;        ())
;;      `[r -> ([obligation r *]) (goto B r)]
;;      #t
;;      `(external-receive (addr 0 0) (addr (env Nat) 1)))
;;     (list
;;      `((((Addr Nat) (addr 0 0)))
;;        ()
;;        (goto B (addr (env Nat) 1))
;;        ((define-state (A) [r -> ([obligation r *]) (goto B r)]))
;;        ([(addr (env Nat) 1) *]))))

;;   (test-case "Immediate fork pattern transition"
;;     (define fork-pattern `(fork (goto Z y) (define-state (Z y) [* -> () (goto Z y)])))
;;     (check-equal?
;;      (attempt-transition
;;       `(([(Addr Nat) (addr 1 0)])
;;         ([String (addr 2 0)])
;;         (goto A (addr (env Nat) 1))
;;         ((define-state (A x) [y -> ([obligation x ,fork-pattern]) (goto B)])
;;          (define-state (B) [* -> () (goto B)]))
;;         ;; check for captured and uncaptured addresses, too
;;         ([(addr (env Nat) 1)]
;;          [(addr (env Nat) 3) *]))
;;       `[y -> ([obligation (addr (env Nat) 1) ,fork-pattern]) (goto B)]
;;       #t
;;       `(external-receive (addr 1 0) (addr (env (Addr Nat)) 2)))
;;      (list
;;       `(([(Addr Nat) (addr 1 0)])
;;         ([String (addr 2 0)])
;;         (goto B)
;;         ((define-state (A x) [y -> ([obligation x ,fork-pattern]) (goto B)])
;;          (define-state (B) [* -> () (goto B)]))
;;         ([(addr (env Nat) 3) *]))
;;       `(()
;;         ([(Addr Nat) (addr 1 0)] [String (addr 2 0)])
;;         (goto Z (addr (env (Addr Nat)) 2))
;;         ((define-state (Z y) [* -> () (goto Z y)]))
;;         ([(addr (env (Addr Nat)) 2)]
;;          [(addr (env Nat) 1) self])))))

;;   (test-case "Delayed fork pattern transition"
;;     (define fork-pattern `(delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)])))
;;     (check-equal?
;;      (attempt-transition
;;       `(([(Addr Nat) (addr 1 0)])
;;         ([String (addr 2 0)])
;;         (goto A (addr (env Nat) 1))
;;         ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
;;          (define-state (B) [* -> () (goto B)]))
;;         ;; check for captured and uncaptured addresses, too
;;         ([(addr (env Nat) 1)]
;;          [(addr (env Nat) 2)]
;;          [(addr (env Nat) 3) *]))
;;       `[* -> ([obligation (addr (env Nat) 1) ,fork-pattern]) (goto B)]
;;       #t
;;       `(external-receive (addr 1 0) (addr (env (Addr Nat)) 2)))
;;      (list
;;       `(([(Addr Nat) (addr 1 0)])
;;         ([String (addr 2 0)])
;;         (goto B)
;;         ((define-state (A x) [* -> ([obligation x ,fork-pattern]) (goto B)])
;;          (define-state (B) [* -> () (goto B)]))
;;         ([(addr (env Nat) 1) ,fork-pattern]
;;          [(addr (env Nat) 2)]
;;          [(addr (env Nat) 3) *]))))))

;; ;; (f ...) ([x a#] ...) -> (f ...)
;; ;;
;; ;; Substitutes the given bindings into the given effects
;; (define (subst-into-effects effects bindings)
;;   (redex-let aps# ([([x a#] ...) bindings])
;;     (for/list ([effect effects])
;;       (term (subst-n/aps#/f ,effect [x a#] ...)))))

;; ;; (goto state x ...) ([x a#] ...) -> (goto state a ...)
;; ;;
;; ;; Substitutes the given bindings into the given specification goto expression
;; (define (subst-into-goto goto bindings)
;;   (redex-let aps# ([([x a#] ...) bindings]
;;                    [(goto φ u ...) goto])
;;     (term (goto φ (subst-n/aps#/u u [x a#] ...) ...))))

;; ;; (f ...) ρ -> (([a# po] ...) (ς ...))
;; ;;
;; ;; Performs the given effects in the context of the given receptionist interface, returning new
;; ;; obligations and forked pre-configurations
;; (define (perform effects receptionists)
;;   (for/fold ([results (list null null)])
;;             ([effect effects])
;;     (match-define (list obls-so-far pre-configs-so-far) results)
;;     (match effect
;;       [`(obligation ,address ,pattern)
;;        (match-define (list post-extract-pattern extracted-pre-configs)
;;          (extract pattern receptionists address))
;;        (list (cons `[,address ,post-extract-pattern] obls-so-far)
;;              (append pre-configs-so-far extracted-pre-configs))]
;;       [`(fork ,goto ,state-defs ...)
;;        (list obls-so-far
;;              (cons `(() ,receptionists ,goto ,state-defs ()) pre-configs-so-far))])))

;; (module+ test
;;   (test-equal? "perform 1"
;;     (perform
;;      (list `[obligation (addr (env Nat) 1)
;;                         (fork (goto Z (addr (env Nat) 2)) (define-state (Z a) [* -> () (goto Z a)]))])
;;      `([Nat (addr 1 0)]
;;        [String (addr 2 0)]))
;;     `(([(addr (env Nat) 1) self])
;;       ([()
;;         ([Nat (addr 1 0)]
;;          [String (addr 2 0)])
;;         (goto Z (addr (env Nat) 2))
;;         ((define-state (Z a) [* -> () (goto Z a)]))
;;         ((addr (env Nat) 1))])))

;;   (test-equal? "perform delayed-fork obligation"
;;     (perform
;;      (list `[obligation (addr (env Nat) 1)
;;                         (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))])
;;      `([Nat (addr 1 0)]
;;        [String (addr 2 0)]))
;;     `(([(addr (env Nat) 1) (delayed-fork (goto Z) (define-state (Z) [* -> () (goto Z)]))])
;;       ()))

;;   (test-equal? "perform fork"
;;     (perform (list `[fork (goto A (addr (env Nat) 1))])
;;              '())
;;     `(() ([() () (goto A (addr (env Nat) 1)) () ()]))))

;; ;; po ρ a# -> (po, (ς ...))
;; ;;
;; ;; Extracts all forks from the given pattern that is an obligation on the given address, replacing
;; ;; those patterns with the "self" pattern and creating pre-configurations for each fork using the
;; ;; given receptionists as the unobs receptionists
;; (define (extract pattern receptionists addr)
;;   (define (extract-sub-patterns sub-patterns make-pattern)
;;     (match-define (list `[,extracted-pats ,pre-configs] ...)
;;       (map (curryr extract receptionists addr) sub-patterns))
;;     (list (make-pattern extracted-pats) (append* pre-configs)))
;;   (match pattern
;;     [`* (list pattern null)]
;;     [`(or ,pats ...)
;;      (extract-sub-patterns pats (lambda (pats) `(or ,@pats)))]
;;     [`(variant ,tag ,pats ...)
;;      (extract-sub-patterns pats (lambda (pats) `(variant ,tag ,@pats)))]
;;     [`(record [,fields ,pats] ...)
;;      (extract-sub-patterns
;;       pats
;;       (lambda (pats) `(record ,@(map (lambda (f p) `[,f ,p]) fields pats))))]
;;     [`(fork ,goto ,state-defs ...)
;;      (list 'self `([() ,receptionists ,goto ,state-defs (,addr)]))]
;;     [`(delayed-fork ,_ ,_ ...) (list pattern null)]
;;     ['self (list pattern null)]))

;; (module+ test
;;   (test-equal? "extract 1"
;;     (extract `(or (fork (goto A (addr (env Nat) 1))) (fork (goto B (addr (env Nat) 2))))
;;              `([Nat (addr 1 0)])
;;              `(addr (env Nat) 3))
;;     `[(or self self)
;;       ([() ([Nat (addr 1 0)]) (goto A (addr (env Nat) 1)) () ((addr (env Nat) 3))]
;;        [() ([Nat (addr 1 0)]) (goto B (addr (env Nat) 2)) () ((addr (env Nat) 3))])])

;;   (test-equal? "extract fork"
;;     (extract `(fork (goto A (addr (env Nat) 1)) (define-state (A x)))
;;              `([Nat (addr 1 0)])
;;              `(addr (env Nat) 3))
;;     `[self
;;       ([()
;;         ([Nat (addr 1 0)])
;;         (goto A (addr (env Nat) 1))
;;         ((define-state (A x)))
;;         ((addr (env Nat) 3))])])

;;   (test-equal? "extract delayed-fork"
;;     (extract `(delayed-fork (goto B) (define-state (B)) (define-state (C)))
;;              `()
;;              `(addr (env Nat) 2))
;;     `[(delayed-fork (goto B) (define-state (B)) (define-state (C)))
;;       ()]))

;; ;; ς (ς ...) O# -> (s# ...)
;; ;;
;; ;; As described in the dissertation, distributes the obligations in the obligation map to each
;; ;; pre-configuration according to the external addresses "relevant" to each pre-config (determined by
;; ;; the state arguments on that configuration and any extra addresses set in the pre-config). Static
;; ;; constraints on the specification ensure that every observed external address is relevant to at most
;; ;; one spec config.
;; ;;
;; ;; The dist function described in the dissertation assigns obligations non-deterministically if the
;; ;; address is not relevant in any pre-config. Here we use the strategy of assigning them to the
;; ;; "current" config by default.
;; (define (dist current-pre-config forked-pre-configs obligation-map)
;;   (define-values (remaining-obligation-map forked-configs)
;;    (for/fold ([obligation-map obligation-map]
;;               [forked-configs null])
;;              ([pre-config forked-pre-configs])
;;      (match-define (list obs-receptionists unobs-receptionists goto state-defs relevants) pre-config)
;;      (match-define (list remaining-obligation-map forked-map)
;;        (fork-commitment-map obligation-map (append (externals-in goto) relevants)))
;;      ;; The new unobs receptionists are *all* receptionists from the parent config, plus the
;;      ;; observable receptionists of the other forks
;;      (values remaining-obligation-map
;;              (cons (term (,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,forked-map))
;;                    forked-configs))))
;;   (match current-pre-config
;;     [`(,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,_)
;;      (cons `(,obs-receptionists ,unobs-receptionists ,goto ,state-defs ,remaining-obligation-map)
;;            forked-configs)]))

;; (module+ test
;;   (test-equal? "Degenerate dist case"
;;                (dist (term (() () (goto A) ((define-state (A))) ())) null null)
;;                (list (term (() () (goto A) ((define-state (A))) ()))))

;;   (test-equal? "Basic dist case"
;;     (dist (term (() () (goto A) ((define-state (A))) ()))
;;           (list `[() () (goto B (addr (env Nat) 2)) ((define-state (B r))) ()])
;;           (term ([(addr (env Nat) 1) *] [(addr (env Nat) 2) (record)])))
;;     (list (term (() () (goto A) ((define-state (A))) ([(addr (env Nat) 1) *])))
;;           (term (() () (goto B (addr (env Nat) 2)) ((define-state (B r))) ([(addr (env Nat) 2) (record)])))))

;;   (test-equal? "Dist with extra relevant address"
;;     (dist (term (() () (goto A (addr (env Nat) 1)) () ()))
;;           (list (term (() () (goto B) () ((addr (env Nat) 2)))))
;;           (term ([(addr (env Nat) 1) *]
;;                  [(addr (env Nat) 2) *])))
;;     (list (term (() () (goto A (addr (env Nat) 1)) () ([(addr (env Nat) 1) *])))
;;           (term (() () (goto B) () ([(addr (env Nat) 2) *])))))

;;   (test-equal? "Dist an obligation with self pattern and that address in the fork's args"
;;     (dist (term (() () (goto A) () ()))
;;           (list (term (() () (goto B (addr (env Nat) 1)) () ((addr (env Nat) 1)))))
;;           (term ([(addr (env Nat) 1) (variant X self)])))
;;     (list (term (() () (goto A) () ()) )
;;           (term (() () (goto B (addr (env Nat) 1)) () ([(addr (env Nat) 1) (variant X self)]))))))

;; ;; O# (a# ...) -> (O#_old O#_new)
;; ;;
;; ;; Moves entries from the given obligation map whose address is in the given list and creates a new
;; ;; obligation map from that list. The list of addresses may contain duplicates.
;; (define (fork-commitment-map commitment-map addresses)
;;   (term (fork-commitment-map/mf ,commitment-map () ,(remove-duplicates addresses))))

;; ;; Takes all entries from the first O# that match an address in the given list and moves it to the
;; ;; second O#. The list of addresses must *not* contain duplicates.
;; (define-metafunction aps#
;;   fork-commitment-map/mf : O# O# (a# ...) -> (O# O#)
;;   [(fork-commitment-map/mf O#_current O#_new ())
;;    (O#_current O#_new)]
;;   [(fork-commitment-map/mf O#_current (any_fork-entries ...) (a# any_rest ...))
;;    (fork-commitment-map/mf O#_updated (any_fork-entries ... (a# any_pulled ...)) (any_rest ...))
;;    (where (O#_updated (any_pulled ...)) (O#-pull O#_current a#))])

;; (define-metafunction aps#
;;   O#-pull : O# a# -> (O# (po ...))
;;   [(O#-pull (any_1 ... (a# any_com ...) any_2 ...) a#)
;;    ((any_1 ... any_2 ...) (any_com ...))]
;;   [(O#-pull O# a#) (O# ())])

;; (module+ test
;;   (check-equal?
;;    (fork-commitment-map
;;     (term (((addr (env Nat) 1) *)
;;            ((addr (env Nat) 2))
;;            ((addr (env Nat) 3))
;;            ((addr (env Nat) 4) (record))))
;;     (term ((addr (env Nat) 1) (addr (env Nat) 3) (addr (env Nat) 5))))
;;    (list
;;     (term (((addr (env Nat) 2))
;;            ((addr (env Nat) 4) (record))))
;;     (term (((addr (env Nat) 1) *)
;;            ((addr (env Nat) 3))
;;            ((addr (env Nat) 5))))))

;;   (test-equal? "fork-commitment-map: No duplicate entries when address list has duplicates"
;;     (fork-commitment-map `([(addr (env Nat) 1) *]) (list `(addr (env Nat) 1) `(addr (env Nat) 1)))
;;     `[()
;;       ([(addr (env Nat) 1) *])]))

;; ;; Adds all addresses matched in the substitution (i.e. the set of bindings) as keys in the output
;; ;; commitment map
;; (define (observe-addresses-from-subst commitment-map the-subst)
;;   (redex-let aps# ([(any_map-entries ...) commitment-map]
;;                    [([_ a#_ext] ...) the-subst])
;;              (term (any_map-entries ... (a#_ext) ...))))

;; ;; NOTE: assumes an entry has been added already (e.g. with observe-addresses-from-subst)
;; (define-metafunction aps#
;;   add-commitments : O# [a# po] ... -> O#
;;   [(add-commitments O#) O#]
;;   [(add-commitments (any_1 ... (a# any_coms ...)             any_2 ...) [a# po] any_rest ...)
;;    (add-commitments (any_1 ... (a# any_coms ... po) any_2 ...) any_rest ...)])

;; (module+ test
;;   (test-equal? "add-commitments"
;;                (term (add-commitments
;;                       ([(addr (env Nat) 1) * (record)]
;;                        [(addr (env Nat) 2)])
;;                       [(addr (env Nat) 1) *]
;;                       [(addr (env Nat) 2) *]
;;                       [(addr (env Nat) 1) (variant A)]))
;;                `([(addr (env Nat) 1) * (record) * (variant A)]
;;                  [(addr (env Nat) 2) *])))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Input pattern matching

;; ;; Matches the trigger against the given transition pattern, returning the bindings created from the
;; ;; match if such a match exists, else #f
;; (define (match-trigger from-observer? trigger obs-receptionists pattern)
;;   (match
;;       (judgment-holds
;;        (match-trigger/j ,from-observer? ,trigger ,obs-receptionists ,pattern any_bindings)
;;        any_bindings)
;;     [(list) #f]
;;     [(list binding-list) binding-list]
;;     [(list _ _ _ ...)
;;      (error 'match-trigger
;;             "Match resulted in multiple possible substitutions")]))

;; (define-judgment-form aps#
;;   #:mode (match-trigger/j I I I I O)
;;   #:contract (match-trigger/j boolean trigger# ρ# pt ([x a#] ...))

;;   [-------------------------------------------------------
;;    (match-trigger/j _ (timeout _) _ free ())]

;;   [----------------------------------------------------------------------
;;    (match-trigger/j _ (internal-receive _ _ _) _ free ())]

;;   [-----------------------------------------------------------------------
;;    (match-trigger/j #f (external-receive _ _) _ free ())]

;;   [(aps#-match/j v# p any_bindings)
;;    ----------------------------------------------------------------
;;    (match-trigger/j #t (external-receive a# v#) ((_ a#)) p any_bindings)])

;; (module+ test
;;   (check-equal?
;;    (match-trigger #f '(timeout (addr 0 0)) '((Nat (addr 0 0))) 'free)
;;    null)

;;   (check-equal?
;;    (match-trigger #f '(external-receive (addr 0 0) abs-nat) '((Nat (addr 0 0))) 'free)
;;    null)

;;   (check-false
;;    (match-trigger #t '(external-receive (addr 0 0) abs-nat) '((Nat (addr 0 0))) 'free))

;;   (check-equal?
;;    (match-trigger #t '(external-receive (addr 0 0) (addr (env Nat) 1)) '((Nat (addr 0 0))) 'x)
;;    (list '(x (addr (env Nat) 1))))

;;   (check-false
;;    (match-trigger #f '(internal-receive (addr 0 0) abs-nat single) '((Nat (addr 0 0))) 'x))

;;   (check-false
;;    (match-trigger #t '(external-receive (addr 0 0) abs-nat) '((Nat (addr 0 0))) 'x))

;;   (check-equal?
;;    (match-trigger #f '(internal-receive (addr 0 0) abs-nat single) '((Nat (addr 0 0))) 'free)
;;    null)

;;   (check-false
;;    (match-trigger #t '(external-receive (addr 0 0) (variant A)) '(((Union [A]) (addr 0 0))) 'free))

;;   (check-equal?
;;    (match-trigger #t '(external-receive (addr 0 0) (variant A)) '(((Union [A]) (addr 0 0))) '*)
;;    null))

;; (define-judgment-form aps#
;;   #:mode (aps#-match/j I I O)
;;   #:contract (aps#-match/j v# p ((x a#) ...))

;;   [-------------------
;;    (aps#-match/j _ * ())]

;;   [(side-condition ,(not (csa#-internal-address? (term a#))))
;;    -----------------------------------
;;    (aps#-match/j a# x ([x a#]))]

;;   [(aps#-match/j v# p ([x a#_binding] ...)) ...
;;    --------------
;;    (aps#-match/j (variant t v# ..._n) (variant t p ..._n) ([x a#_binding] ... ...))]

;;   [(aps#-match/j v# p ([x a#_binding] ...)) ...
;;    ---------------------------------------------
;;    (aps#-match/j (record [l v#] ..._n) (record [l p] ..._n) ([x a#_binding] ... ...))]

;;   ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
;;   ;; therefore would not write patterns for them
;;   [(aps#-match/j v# p ([x a#_binding] ...))
;;    -----------------------------------------------------------
;;    (aps#-match/j (folded _ v#) p ([x a#_binding] ...))])

;; (module+ test
;;   (check-true (judgment-holds (aps#-match/j abs-nat * ())))
;;   (check-true (judgment-holds (aps#-match/j (addr (env Nat) 1) x ([x (addr (env Nat) 1)]))))
;;   (check-false (judgment-holds (aps#-match/j (addr 0 1) x ([x (addr 0 1)]))))
;;   (check-true (judgment-holds (aps#-match/j (variant A abs-string) (variant A *) ())))
;;   (check-true (judgment-holds (aps#-match/j (variant A (addr (env Nat) 1))
;;                                             (variant A x)
;;                                             ([x (addr (env Nat) 1)]))))
;;   (check-true (judgment-holds (aps#-match/j (record [a (addr (env Nat) 1)])
;;                                             (record [a x])
;;                                             ([x (addr (env Nat) 1)]))))
;;   (check-true (judgment-holds (aps#-match/j abs-nat * any)))
;;   (check-false (judgment-holds (aps#-match/j abs-nat x any)))
;;   (check-true (judgment-holds (aps#-match/j (folded Nat (addr (env Nat) 1)) x any)))
;;   ;; matches two ways, but should only return one result:
;;   (check-equal? (judgment-holds (aps#-match/j (folded Nat abs-nat) * any_bindings) any_bindings)
;;                 (list '())))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Output pattern matching

;; ;; v# ρ# (listof pattern) -> (listof [po ρ#_obs ρ#_unobs (match-fork ...)])
;; ;;
;; ;; Attempts to match the given value and observed receptionist map against all of the given patterns,
;; ;; returning a list of tuples [po ρ#_obs ρ#_unobs (match-fork ...)] for each way to match against one
;; ;; of the given patterns.
;; (define (find-matching-patterns value type obs-receptionists patterns)
;;   (reverse
;;    (for/fold ([success-results null])
;;              ([pattern patterns])
;;      (define this-pattern-results
;;        (map (curry cons pattern) (aps#-match-po value type obs-receptionists pattern)))
;;      (append success-results this-pattern-results))))

;; (module+ test
;;   (check-equal?
;;    (list->set (find-matching-patterns `(variant A) `(Union [A]) null (list '* '(variant A) '(variant B))))
;;    (set `[* () () ()]
;;         `[(variant A) () () ()])))

;; ;; v# ρ#_obs po -> (Listof [ρ#_obs ρ#_unobs (match-fork ...)])
;; ;;
;; ;; Attempts to match the given message and observed receptionist set against the given
;; ;; pattern. Returns the outputs from every successful judgment for the match relation.
;; (define (aps#-match-po value type obs-receptionists pattern)
;;   (judgment-holds (aps#-matches-po?/j ,value
;;                                       ,type
;;                                       ,obs-receptionists
;;                                       ,pattern
;;                                       any_new-obs-receptionists
;;                                       any_new-unobs-receptionists
;;                                       any_forks)
;;                   (any_new-obs-receptionists any_new-unobs-receptionists any_forks)))

;; (define-judgment-form aps#
;;   #:mode (aps#-matches-po?/j I I I I O O O)
;;   #:contract (aps#-matches-po?/j v# τ ρ#_obs po ρ#_obs-new ρ#_unobs (match-fork ...))

;;   [-----
;;    (aps#-matches-po?/j v# τ ρ#_obs * ρ#_obs ,(internal-addr-types (term v#) (term τ)) ())]

;;   [(aps#-matches-po?/j v# τ ρ#_obs po                  any_obs-recs any_unobs-receptionists any_forks)
;;    -----
;;    (aps#-matches-po?/j v# τ ρ#_obs (or _ ... po _ ...) any_obs-recs any_unobs-receptionists any_forks)]

;;   [(side-condition ,(csa#-internal-address? (term a#)))
;;    ----
;;    (aps#-matches-po?/j a#
;;                        (Addr τ)
;;                        ρ#_obs
;;                        (delayed-fork (goto φ) Φ ...)
;;                        ρ#_obs
;;                        ()
;;                        ((([τ a#]) (goto φ) (Φ ...))))]

;;   [(side-condition ,(csa#-internal-address? (term a#)))
;;    ----
;;    (aps#-matches-po?/j a# (Addr τ) ([τ a#]) self ([τ a#]) () ())]

;;   [(side-condition ,(csa#-internal-address? (term a#)))
;;    ----
;;    (aps#-matches-po?/j a# (Addr τ) () self ([τ a#]) () ())]

;;   [(aps#-list-matches-po?/j ((v# τ po) ...) ρ#_obs any_obs-recs any_unobs-receptionists any_forks)
;;    ------
;;    (aps#-matches-po?/j (variant t v# ..._n)
;;                        (Union _ ... (t τ ..._n) _ ...)
;;                        ρ#_obs
;;                        (variant t po ..._n)
;;                        any_obs-recs
;;                        any_unobs-receptionists
;;                        any_forks)]

;;   ;; Records

;;   [(aps#-list-matches-po?/j ((v# τ po) ...) ρ#_obs any_obs-recs any_unobs-receptionists any_forks)
;;    ------
;;    (aps#-matches-po?/j (record [l v#] ..._n)
;;                        (Record [l τ] ..._n)
;;                        ρ#_obs
;;                        (record [l po] ..._n)
;;                        any_obs-recs
;;                        any_unobs-receptionists
;;                        any_forks)]

;;   ;; Just ignore folds in the values: in a real language, the programmer wouldn't see them and
;;   ;; therefore would not write patterns for them
;;   [(aps#-matches-po?/j v# (type-subst τ X (minfixpt X τ)) ρ#_obs po any_obs-recs any_unobs-receptionists any_forks)
;;    -------------------------------------------------------------------------------------
;;    (aps#-matches-po?/j (folded (minfixpt X τ) v#) (minfixpt X τ) ρ#_obs po any_obs-recs any_unobs-receptionists any_forks)])

;; (define-judgment-form aps#
;;   #:mode (aps#-list-matches-po?/j I I O O O)
;;   #:contract (aps#-list-matches-po?/j ((v# τ po) ...) ρ#_obs ρ#_obs-new ρ#_unobs (match-fork ...))

;;   [---------
;;    (aps#-list-matches-po?/j () any_addr any_addr () ())]

;;   [(aps#-matches-po?/j v# τ ρ#_obs po any_obs-rec1 (any_unobs-receptionists1 ...) (any_forks1 ...))
;;    (aps#-list-matches-po?/j (any_rest ...)
;;                             any_obs-rec1
;;                             any_obs-rec2
;;                             (any_unobs-receptionists2 ...)
;;                             (any_forks2 ...))
;;    ---------
;;    (aps#-list-matches-po?/j ((v# τ po) any_rest ...)
;;                             ρ#_obs
;;                             any_obs-rec2
;;                             (any_unobs-receptionists1 ... any_unobs-receptionists2 ...)
;;                             (any_forks1 ... any_forks2 ...))])

;; (module+ test
;;   (check-equal?
;;    (aps#-match-po 'abs-nat `Nat '() '*)
;;    (list (list '() null null)))
;;   (check-equal?
;;    (aps#-match-po 'abs-nat 'Nat '() '(record))
;;    null)
;;   (check-equal?
;;    (aps#-match-po '(addr 0 0) `(Addr Nat) '() 'self)
;;    (list (list '((Nat (addr 0 0))) null null)))
;;   (check-equal?
;;    (aps#-match-po '(addr 0 0) `(Addr Nat) '() '*)
;;    (list (list '() (list '(Nat (addr 0 0))) null)))
;;   (check-equal?
;;    (aps#-match-po '(addr (env Nat) 0) `(Addr Nat) '() 'self)
;;    null)
;;   (check-equal?
;;    (aps#-match-po '(variant A abs-nat (addr 2 0)) `(Union [A Nat (Addr Nat)]) '() '(variant A * self))
;;    (list (list '((Nat (addr 2 0))) '() '())))
;;   (check-equal?
;;    (aps#-match-po '(variant A abs-nat (addr 2 0)) `(Union [A Nat (Addr Nat)]) '() '(variant A * *))
;;    (list (list '() '((Nat (addr 2 0))) '())))
;;   (check-equal?
;;    (aps#-match-po '(variant A abs-nat (addr 2 0)) `(Union [A Nat (Addr Nat)]) '((Nat (addr 2 0))) '(variant A * self))
;;    (list (list '((Nat (addr 2 0))) '() '())))
;;   (test-equal? "Variant match with address/or pattern"
;;    (aps#-match-po '(variant A abs-nat (addr 2 0))
;;                   `(Union [A Nat (Addr Nat)])
;;                   '((Nat (addr 2 0)))
;;                   '(or (variant A * self) (variant B)))
;;    (list (list '((Nat (addr 2 0))) '() '())))
;;   (test-equal? "Variant match with or pattern 2"
;;     (aps#-match-po (term (variant A)) '(Union [A] [B] [C]) '() (term (or (variant A) (variant B))))
;;     (list (list '() null null)))
;;   (test-equal? "Variant match with or pattern 3"
;;     (aps#-match-po (term (variant B)) '(Union [A] [B] [C]) '() (term (or (variant A) (variant B))))
;;     (list (list '() null null)))
;;   (test-equal? "Variant match with or pattern 4"
;;    (aps#-match-po (term (variant C)) '(Union [A] [B] [C])'() (term (or (variant A) (variant B))))
;;    null)
;;   (test-equal? "Variant match with self"
;;     (aps#-match-po '(variant A abs-nat (addr 2 0))
;;                    '(Union [A Nat (Addr Nat)])
;;                    '((Nat (addr 1 0)))
;;                    '(variant A * self))
;;     null)
;;   (test-equal? "Spawn match po test"
;;     (aps#-match-po '(addr 'foo 1)
;;                    '(Addr Nat)
;;                    '()
;;                    '(delayed-fork (goto B) (define-state (B))))
;;     (list (list '()
;;                 '()
;;                 '([([Nat (addr 'foo 1)]) (goto B) ((define-state (B)))]))))
;;   (test-equal? "Full match po test"
;;     (aps#-match-po '(variant A (addr 'foo 1) (addr 2 0))
;;                    '(Union [A (Addr Nat) (Addr Nat)])
;;                    '()
;;                    '(variant A (delayed-fork (goto B) (define-state (B))) self))
;;    (list (list '((Nat (addr 2 0)))
;;                '()
;;                '([([Nat (addr 'foo 1)])
;;                   (goto B)
;;                   ((define-state (B)))]))))

;;   (test-case "Fold test"
;;     (define rec-type '(minfixpt X (Addr (Union [Done] [More X]))))
;;     (check-equal?
;;      (aps#-match-po `(folded ,rec-type (addr 0 0))
;;                     rec-type
;;                     '()
;;                     '(delayed-fork (goto B) (define-state (B))))
;;      (list (list '()
;;                  `()
;;                  (list `[([(Union [Done] [More ,rec-type]) (addr 0 0)])
;;                          (goto B)
;;                          ((define-state (B)))])))))

;;   (test-equal? "'Or' pattern can match in multiple ways"
;;     (list->set (aps#-match-po `(addr 1 0) '(Addr Nat) null `(or * self)))
;;     (set `[([Nat (addr 1 0)]) () ()]
;;          `[() ([Nat (addr 1 0)]) ()])))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Commitment Satisfaction

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

;; ;; s# O# [ρ#_o ρ#_u (match-fork ...)] -> (s# ...)
;; (define (incorporate-output-match-results original-pre-config
;;                                           obligations
;;                                           match-result)
;;   (match-define (list matched-obs-receptionists matched-unobs-receptionists match-forks) match-result)
;;   (match-define (list _ original-unobs-recs goto state-defs _) original-pre-config)
;;   (define all-fork-obs-receptionists (append* (map first match-forks)))
;;   (define updated-pre-config
;;     (list matched-obs-receptionists
;;           (merge-receptionists
;;            original-unobs-recs
;;            (merge-receptionists matched-unobs-receptionists all-fork-obs-receptionists))
;;           goto
;;           state-defs
;;           null))
;;   (define forked-pre-configs
;;     (for/list ([match-fork match-forks])
;;       (match-define (list (list fork-obs-rec) goto state-defs) match-fork)
;;       (define other-fork-obs-receptionists
;;         ;; "remove" removes only the first item that matches, so if any other fork had the same
;;         ;; receptionist address and type, it will be included in the unobs receptionist here
;;         (remove fork-obs-rec all-fork-obs-receptionists))
;;       `[(,fork-obs-rec)
;;         ,(merge-receptionists
;;           matched-obs-receptionists
;;           (merge-receptionists matched-unobs-receptionists other-fork-obs-receptionists))
;;         ,goto
;;         ,state-defs
;;         ()]))
;;   (dist updated-pre-config forked-pre-configs obligations))

;; (module+ test
;;   (test-equal? "incorporate-output-match-results 1"
;;     (incorporate-output-match-results
;;      `(() () (goto A) ((define-state (A))) ())
;;      null
;;      `[([Nat (addr 1 0)]) ([String (addr 2 0)]) ()])
;;     (list `(([Nat (addr 1 0)]) ([String (addr 2 0)]) (goto A) ((define-state (A))) ())))

;;   (test-equal? "incorporate-output-match-results with delayed-fork"
;;     (list->set
;;      (incorporate-output-match-results
;;       `(() () (goto A) ((define-state (A))) ())
;;       `([(addr (env Nat) 1) *])
;;       `[() () ([([Nat (addr 1 0)]) (goto B) ((define-state (B)))])]))
;;     (set
;;      `(() ([Nat (addr 1 0)]) (goto A) ((define-state (A))) ([(addr (env Nat) 1) *]))
;;      `(([Nat (addr 1 0)]) () (goto B) ((define-state (B))) ()))))

;; (define (config-observes-address? config addr)
;;   (match (commitments-for-address (aps#-config-commitment-map config) addr)
;;     [#f #f]
;;     [_ #t]))

;; (define (aps#-remove-commitment-pattern commitment-map address pat)
;;   (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

;; (define-metafunction aps#
;;   remove-commitment-pattern/mf : O# a# po -> O#
;;   [(remove-commitment-pattern/mf (any_1 ... (a# any_2 ... po any_3 ...) any_4 ...)
;;                                  a#
;;                                  po)
;;    (any_1 ... (a# any_2 ... any_3 ...) any_4 ...)]
;;   ;; we might call this metafunction with a free output pattern not in the obligation list, so if the
;;   ;; pattern doesn't exist just return the existing map
;;   ;;
;;   ;; NOTE: I think now that I've set the macro-step obligations to record only the *minimal* set of
;;   ;; fulfilled obligations, this case wouldn't happen, but I'm leaving it in for now
;;   [(remove-commitment-pattern/mf any_obligations _ _) any_obligations])

;; (module+ test
;;   (check-equal?
;;    (aps#-remove-commitment-pattern
;;     (term (((addr (env Nat) 1) *))) (term (addr (env Nat) 1)) (term *))
;;    (term (((addr (env Nat) 1)))))
;;   (check-equal?
;;    (aps#-remove-commitment-pattern
;;     (term (((addr (env Nat) 1) *))) (term (addr (env Nat) 1)) (term *))
;;    (term (((addr (env Nat) 1)))))
;;   (check-equal?
;;    (aps#-remove-commitment-pattern
;;     (term (((addr (env Nat) 1) * (record)))) (term (addr (env Nat) 1)) (term *))
;;    (term (((addr (env Nat) 1) (record)))))
;;   (check-equal?
;;    (aps#-remove-commitment-pattern
;;     (term (((addr (env Nat) 1) * (record) (record [a *])) ((addr (env Nat) 2) *)))
;;     (term (addr (env Nat) 1))
;;     (term *))
;;    (term (((addr (env Nat) 1) (record) (record [a *])) ((addr (env Nat) 2) *)))))

;; (define (config-merge-unobs-addresses config new-addrs)
;;   `(,(aps#-config-obs-receptionists config)
;;     ,(merge-receptionists (aps#-config-unobs-receptionists config) new-addrs)
;;     ,(aps#-config-current-state config)
;;     ,(aps#-config-state-defs config)
;;     ,(aps#-config-commitment-map config)))

;; (define (aps#-config-has-commitment? config address pattern)
;;   (judgment-holds (aps#-commitment-map-has-commitment?/j ,(aps#-config-commitment-map config)
;;                                                          ,address
;;                                                          ,pattern)))

;; (define-judgment-form aps#
;;   #:mode (aps#-commitment-map-has-commitment?/j I I I)
;;   #:contract (aps#-commitment-map-has-commitment?/j O# a# po)
;;   [-----
;;    (aps#-commitment-map-has-commitment?/j (_ ... [a# _ ... po _ ...] _ ...) a# po)])

;; (module+ test
;;   (define has-commitment-test-config
;;     (term (() () (goto S1) () (((addr (env Nat) 1) *)
;;                                ((addr (env Nat) 2) * (record))))))
;;   (test-false "aps#-config-has-commitment? 1"
;;     (aps#-config-has-commitment? has-commitment-test-config (term (addr (env Nat) 3)) (term *)))
;;   (test-false "aps#-config-has-commitment? 2"
;;     (aps#-config-has-commitment? has-commitment-test-config (term (addr (env Nat) 1)) (term (record))))
;;   (test-true "aps#-config-has-commitment? 1"
;;     (aps#-config-has-commitment? has-commitment-test-config (term (addr (env Nat) 2)) (term (record)))))

;; ;; Returns #t if this transition goes to the given state and has exactly one effect (an obligation)
;; (define (free-stable-transition? transition full-state)
;;   (match transition
;;     [`(free -> ([obligation ,_ ,_]) ,(== full-state)) #t]
;;     [_ #f]))

;; ;; s# a# -> ([pt -> (f ...) (goto φ u ...)])
;; ;;
;; ;; Returns the transitions (after subsitution with the current state arguments) with an unobs trigger
;; ;; and a single effect: an obligation
;; (define (get-free-transitions-for-resolution config target-addr)
;;   (filter
;;    (lambda (trans)
;;      (match trans
;;        [`(free -> ([obligation ,obligation-addr ,_]) ,_)
;;         (equal? obligation-addr target-addr)]
;;        [_ #f]))
;;    (config-current-transitions config)))

;; (module+ test
;;   (define free-transition-spec
;;     (term
;;      (()
;;       ()
;;       (goto S1 (addr (env Nat) 1) (addr (env Nat) 2))
;;       ((define-state (S1 a b)
;;          [x -> ([obligation x *]) (goto S1)]
;;          [x -> ([obligation b *]) (goto S1)]
;;          [free -> ([obligation a (variant A)]) (goto S2 a b)]
;;          [free -> ([obligation a (variant B)]) (goto S2 a a)]
;;          [free -> ([obligation a (variant C)]) (goto S1 a b)]
;;          [free -> ([obligation b (variant D)]) (goto S1 a b)]
;;          [free -> ([obligation b (variant E)]) (goto S2 a b)]))
;;       ([(addr (env Nat) 1)] [(addr (env Nat) 2)]))))
;;   (check-equal?
;;    (get-free-transitions-for-resolution free-transition-spec `(addr (env Nat) 1))
;;    `([free -> ([obligation (addr (env Nat) 1) (variant A)]) (goto S2 (addr (env Nat) 1) (addr (env Nat) 2))]
;;      [free -> ([obligation (addr (env Nat) 1) (variant B)]) (goto S2 (addr (env Nat) 1) (addr (env Nat) 1))]
;;      [free -> ([obligation (addr (env Nat) 1) (variant C)]) (goto S1 (addr (env Nat) 1) (addr (env Nat) 2))]))
;;   (check-equal?
;;    (get-free-transitions-for-resolution free-transition-spec `(addr (env Nat) 2))
;;    `([free -> ([obligation (addr (env Nat) 2) (variant D)]) (goto S1 (addr (env Nat) 1) (addr (env Nat) 2))]
;;      [free -> ([obligation (addr (env Nat) 2) (variant E)]) (goto S2 (addr (env Nat) 1) (addr (env Nat) 2))])))

;; (define (transition-to-same-state? config transition)
;;   (equal? (aps#-transition-goto transition) (aps#-config-current-state config)))

;; (module+ test
;;   (let ([transition-test-config `[() () (goto A (addr (env Nat) 1)) () ()]])
;;     (test-true "transition-to-same-state? true"
;;       (transition-to-same-state? transition-test-config `[free -> () (goto A (addr (env Nat) 1))]))
;;     (test-false "transition-to-same-state? wrong state"
;;       (transition-to-same-state? transition-test-config `[free -> () (goto B (addr (env Nat) 1))]))
;;     (test-false "transition-to-same-state? wrong address"
;;       (transition-to-same-state? transition-test-config `[free -> () (goto A (addr (env Nat) 2))]))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Selectors

;; (define (aps#-config-obs-receptionists config)
;;   (redex-let aps# ([(ρ# _ ...) config])
;;     (term ρ#)))

;; (define (aps#-config-unobs-receptionists config)
;;   (term (config-unobs-receptionists/mf ,config)))

;; (define-metafunction aps#
;;   config-unobs-receptionists/mf : s# -> ((τ a#) ...)
;;   [(config-unobs-receptionists/mf (_ (any_rec ...) _ ...)) (any_rec ...)])

;; (module+ test
;;   (redex-let aps# ([s# `(((Nat (addr 2 0)))
;;                          ((Nat (addr 0 0))
;;                           (Nat (addr 1 0)))
;;                          (goto A)
;;                          ()
;;                          ())])
;;     (check-equal? (aps#-config-unobs-receptionists (term s#))
;;                   `((Nat (addr 0 0))
;;                     (Nat (addr 1 0))))))

;; (define (aps#-config-state-defs config)
;;   (redex-let aps# ([(_ _ _ any_state-defs _) config])
;;              (term any_state-defs)))

;; (define (aps#-config-current-state config)
;;   (redex-let aps# ([(_ _ any_goto _ ...) config])
;;     (term any_goto)))

;; (define (aps#-config-current-state-args config)
;;   (redex-let aps# ([(_ _ (goto _ a# ...) _ ...) config])
;;     (term (a# ...))))

;; (define (aps#-config-commitment-map config)
;;   (term (config-commitment-map/mf ,config)))

;; (define-metafunction aps#
;;   config-commitment-map/mf : s# -> O#
;;   [(config-commitment-map/mf (_ _ _ _ O#)) O#])

;; (module+ test
;;   (test-equal? "Config commitment map"
;;     (aps#-config-commitment-map `(((Nat (addr 1 0))) () (goto A1) () ()))
;;     '()))

;; ;; Returns all singleton commitments in the config as a list of address/pattern pairs
;; (define (aps#-config-commitments config)
;;   (append*
;;    (map (lambda (entry)
;;           (define addr (aps#-commitment-entry-address entry))
;;           (map (lambda (pat) `[,addr ,pat])  (aps#-commitment-entry-patterns entry)))
;;         (aps#-config-commitment-map config))))

;; (module+ test
;;   (test-equal? "config-commitments"
;;     (aps#-config-commitments
;;      `(()
;;        ()
;;        (goto S1)
;;        ()
;;        ([(addr (env Nat) 1) * (record)]
;;         [(addr (env Nat) 2)]
;;         [(addr (env Nat) 3) * (variant A) (record [a *])])))
;;     (list `[(addr (env Nat) 1) *]
;;           `[(addr (env Nat) 1) (record)]
;;           `[(addr (env Nat) 3) *]
;;           `[(addr (env Nat) 3) (variant A)]
;;           `[(addr (env Nat) 3) (record [a *])])))

;; (define (aps#-transition-trigger transition)
;;   (redex-let aps# ([(pt -> _ _) transition])
;;     (term pt)))

;; (define (aps#-transition-effects transition)
;;   (third transition))

;; (define (aps#-transition-goto transition)
;;   (fourth transition))

;; (define (aps#-commitment-entry-address entry)
;;   (redex-let aps# ([(a# _ ...)  entry])
;;              (term a#)))

;; (define (aps#-commitment-entry-patterns entry)
;;   (redex-let aps# ([(_ po ...)  entry])
;;     (term (po ...))))

;; (module+ test
;;   (test-case "aps#-commitment-entry-patterns"
;;     (redex-let* aps# ([any_entry (term [(addr (env Nat) 1) * (record)])]
;;                       [O# (term (any_entry))])
;;       (check-equal? (aps#-commitment-entry-patterns (term any_entry))
;;                     (list '* '(record))))))

;; (define (commitments-for-address commitment-map address)
;;   (term (commitments-for-address/mf ,commitment-map ,address)))

;; (define-metafunction aps#
;;   commitments-for-address/mf : O# a# -> (po ...) or #f
;;   [(commitments-for-address/mf (_ ... (a# po ...) _ ...)
;;                                a#)
;;    (po ...)]
;;   [(commitments-for-address/mf _ _) #f])

;; (module+ test
;;   (define test-O#
;;     (term (((addr (env Nat) 1) * (record))
;;            ((addr (env Nat) 2) (variant True) (variant False)))))
;;   (check-equal?
;;    (commitments-for-address
;;     test-O#
;;     (term (addr (env Nat) 1)))
;;    (term (* (record))))
;;   (check-equal?
;;    (commitments-for-address
;;     test-O#
;;     (term (addr (env Nat) 2)))
;;    (term ((variant True) (variant False))))
;;   (check-false
;;    (commitments-for-address
;;     test-O#
;;     (term (addr (env Nat) 3)))))

;; ;; "Relevant" external addresses are those in either the current state arguments or obligations of a
;; ;; spec config
;; (define (aps#-relevant-external-addrs s#)
;;   (term (relevant-external-addrs/mf ,s#)))

;; (define-metafunction aps#
;;   relevant-external-addrs/mf : s# -> (a# ...)
;;   [(relevant-external-addrs/mf s#)
;;    (any_commitment-addr ...)
;;    (where ((any_commitment-addr _ ...) ...) (config-commitment-map/mf s#))])

;; (module+ test
;;   (check-equal?
;;    (aps#-relevant-external-addrs
;;     (redex-let* aps#
;;                 ([O# (term (((addr (env Nat) 1)) ((addr (env Nat) 2)) ((addr (env Nat) 3)) ((addr (env Nat) 4))))]
;;                  [s# (term (()
;;                             ()
;;                             (goto Always (addr (env Nat) 1) (addr (env Nat) 2) (addr (env Nat) 3))
;;                             ((define-state (Always r1 r2) (* -> () (goto Always r1 r2))))
;;                             O#))])
;;                 (term s#)))
;;    (term ((addr (env Nat) 1) (addr (env Nat) 2) (addr (env Nat) 3) (addr (env Nat) 4)))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Spec Split

;; ;; s# -> (Listof s#)
;; ;;
;; ;; Splits the given specifcation configuration into multiple configs, to ensure the space of explored
;; ;; spec configs is finite. For each external address in the commitment map that is not a state
;; ;; argument and does not have a "self" pattern in one of its patterns (and therefore will never have
;; ;; more commitments addeded nor be needed to resolve the current self address), it creates a new
;; ;; config consisting only of the commitments on that address (along with commitments for any addresses
;; ;; mentioned in fork patterns for that address) and a dummy FSM with no transitions. After removing
;; ;; those commitment map entries, the remaining config is also returned. The unobserved environment's
;; ;; interface does not change in any of the new configs.
;; (define (split-spec config)
;;   (define entries (aps#-config-commitment-map config))
;;   ;; A commitment map entry is "relevant" if its address is used as a state argument or one of its
;;   ;; patterns contains the "self" pattern. For each irrelevant entry, we split off a new spec config.
;;   (define-values (relevant-entries irrelevant-entries)
;;     (partition
;;      (lambda (entry)
;;        (or (member (aps#-commitment-entry-address entry) (aps#-config-current-state-args config))
;;            (ormap pattern-contains-self? (aps#-commitment-entry-patterns entry))))
;;      (aps#-config-commitment-map config)))
;;   (define commitment-only-configs
;;     (for/list ([entry irrelevant-entries])
;;       (aps#-config-from-commitment-entry
;;        entry
;;        (aps#-config-obs-receptionists config)
;;        (aps#-config-unobs-receptionists config))))
;;   (cons (term (,(aps#-config-obs-receptionists config)
;;                ,(aps#-config-unobs-receptionists config)
;;                ,(aps#-config-current-state config)
;;                ,(aps#-config-state-defs config)
;;                ,relevant-entries))
;;         commitment-only-configs))

;; (module+ test
;;   (define (make-simple-spec-for-split-test commitments)
;;     (term
;;      (((Nat (addr 0 0)))
;;       ()
;;       (goto A (addr (env Nat) 0))
;;       ((define-state (A x) [* -> () (goto A x)]))
;;       ,commitments)))

;;   (test-equal? "split spec with one FSM gets same spec"
;;     (split-spec (make-simple-spec-for-split-test '()))
;;     (list (make-simple-spec-for-split-test '())))

;;   (test-equal? "split with one related commit"
;;    (split-spec (make-simple-spec-for-split-test `(((addr (env Nat) 0) *))))
;;    (list (make-simple-spec-for-split-test `(((addr (env Nat) 0) *)))))

;;   (test-same-items? "split with unrelated commit"
;;    (split-spec (make-simple-spec-for-split-test `(((addr (env Nat) 1) *))))
;;    (list (make-simple-spec-for-split-test `())
;;          (aps#-make-no-transition-config `((Nat (addr 0 0))) `(((addr (env Nat) 1) *)))))

;;   (test-equal? "split a dummy state"
;;     (split-spec (aps#-make-no-transition-config null `(((addr (env Nat) 1) *))))
;;     (list (aps#-make-no-transition-config null `(((addr (env Nat) 1) *)))))

;;   (test-equal? "split a spec with a 'self' commitment"
;;     (split-spec (term (()
;;                        ()
;;                        (goto A)
;;                        ()
;;                        (((addr (env Nat) 1) self)))))
;;     (list (term (()
;;                  ()
;;                  (goto A)
;;                  ()
;;                  (((addr (env Nat) 1) self))))))

;;   (test-equal? "split spec with fork mentioning self pattern"
;;     (split-spec (term (()
;;                        ()
;;                        (goto A (addr (env Nat) 2))
;;                        ()
;;                        (((addr (env Nat) 1) (fork (goto B)
;;                                                   (define-state (B)
;;                                                     [x -> ([obligation x self]) (goto B)])))
;;                         ((addr (env Nat) 2))))))
;;     (list
;;      (term (()
;;             ()
;;             (goto A (addr (env Nat) 2))
;;             ()
;;             (((addr (env Nat) 2)))))
;;      (aps#-make-no-transition-config
;;       null
;;       (list `((addr (env Nat) 1) (fork (goto B)
;;                                        (define-state (B)
;;                                          [x -> ([obligation x self]) (goto B)]))))))))

;; (define (pattern-contains-self? pat)
;;   (match pat
;;     ['self #t]
;;     [(? symbol?) #f]
;;     [`(fork ,_ ...) #f]
;;     [`(delayed-fork ,_ ...) #f]
;;     [`(or ,pats ...) (ormap pattern-contains-self? pats)]
;;     [`(variant ,_ ,pats ...) (ormap pattern-contains-self? pats)]
;;     [`(record [,_ ,pats] ...) (ormap pattern-contains-self? pats)]))

;; (module+ test
;;   (test-false "pattern-contains-self?: self only in fork's state def"
;;     (pattern-contains-self?
;;      `(fork (goto A) (define-state (A x) [free -> ([obligation x self]) (goto A x)]))))
;;   (test-true "pattern-contains-self?: true"
;;     (pattern-contains-self? `(record [a *] [b self])))
;;     (test-true "pattern-contains-self?: true 2"
;;       (pattern-contains-self? `(variant A * self)))
;;   (test-true "pattern-contains-self?: true 3"
;;     (pattern-contains-self? `(or (variant B) (variant A * self))))
;;   (test-false "pattern-contains-self?: false"
;;     (pattern-contains-self? `(record [a *] [b (variant B)])))
;;   (test-false "pattern-contains-self?: false 2"
;;     (pattern-contains-self? `(record [a (fork (goto A))] )))
;;   (test-false "pattern-contains-self?: false 3"
;;     (pattern-contains-self? `(record [a (delayed-fork (goto A))] ))))

;; ;; Makes a specification config with no observed receptionist and an FSM with no transitions. Used for
;; ;; specifications where only the commitments are important.
;; (define (aps#-make-no-transition-config unobs-receptionists commitments)
;;   ;; TODO: expecting the first entry to be the relevant entry is a hack and should be removed once I
;;   ;; switch over to delayed forks
;;   (term (()
;;          ,unobs-receptionists
;;          (goto DummySpecFsmState ,(aps#-commitment-entry-address (first commitments)))
;;          ((define-state (DummySpecFsmState x)))
;;          ,commitments)))

;; (module+ test
;;   (test-equal? "aps#-make-no-transition-config"
;;     (aps#-make-no-transition-config (list `[Nat (addr 0 0)])
;;                                     (list `[(addr (env Nat) 0) *]
;;                                           `[(addr (env Nat) 1)]))
;;     `(()
;;       ([Nat (addr 0 0)])
;;       (goto DummySpecFsmState (addr (env Nat) 0))
;;       ((define-state (DummySpecFsmState x)))
;;       ([(addr (env Nat) 0) *]
;;        [(addr (env Nat) 1)]))))

;; ;; Creates a spec config with a transition-less FSM and a commitment map with just the given
;; ;; entry. The receptionists for the unobserved environment will be the given list plus the given FSM
;; ;; address if it is not UNKONWN.
;; (define (aps#-config-from-commitment-entry entry obs-receptionists unobs-receptionists)
;;   (aps#-make-no-transition-config (merge-receptionists unobs-receptionists obs-receptionists)
;;                                   (list entry)))

;; (module+ test
;;   (check-equal?
;;    (aps#-config-from-commitment-entry
;;     (term ((addr (env Nat) 0) * (record [a *] [b *])))
;;     '()
;;     null)
;;    (aps#-make-no-transition-config '() '(((addr (env Nat) 0) * (record [a *] [b *])))))

;;   (test-equal? "Commitment entry spec should also include old FSM address as unobs receptionist"
;;     (aps#-config-from-commitment-entry
;;      (term ((addr (env Nat) 0) * (record [a *] [b *])))
;;      '((Nat (addr 0 0)))
;;      null)
;;     (aps#-make-no-transition-config
;;      '((Nat (addr 0 0)))
;;      '(((addr (env Nat) 0) * (record [a *] [b *])))))

;;   (test-equal? "Merge obs address into unobs addrs"
;;     (aps#-config-from-commitment-entry (term ((addr (env Nat) 0)))
;;                                          `(((Union [A]) (addr 0 0)))
;;                                          `(((Union [B]) (addr 0 0))))
;;     (aps#-make-no-transition-config
;;      `(((Union [A] [B]) (addr 0 0)))
;;      '(((addr (env Nat) 0))))))

;; (define (aps#-completed-no-transition-config? s)
;;   ;; A configuration is a completed, no-transition configuration if its only current transition is the
;;   ;; implicit do-nothing transition, it has no remaining obligations, and no observable receptionist.
;;   (and (null? (aps#-config-obs-receptionists s))
;;        (= 1 (length (config-current-transitions s)))
;;        (match (aps#-config-commitment-map s)
;;          [(list `(,_) ...) #t]
;;          [_ #f])))

;; (module+ test
;;   ;; empty config set, non-empty configs, other kind of spec config with empty coms
;;   (test-case "completed-no-transition-config?: no commitments"
;;     (redex-let aps# ([s# (aps#-make-no-transition-config null (list `((addr (env Nat) 1))))])
;;       (check-true (aps#-completed-no-transition-config? (term s#)))))
;;   (test-case "completed-no-transition-config?: some commitments"
;;     (redex-let aps# ([s# (aps#-make-no-transition-config null (list `((addr (env Nat) 1) *)))])
;;       (check-false (aps#-completed-no-transition-config? (term s#)))))
;;   (test-case "completed-no-transition-config?: spec with transitions, no commitments"
;;     (redex-let aps# ([s#
;;                       `(()
;;                         ()
;;                         (goto A)
;;                         ((define-state (A) [free -> () (goto A)]))
;;                         ())])
;;       (check-false (aps#-completed-no-transition-config? (term s#)))))
;;   (test-case "completed-no-transition-config?: observed interface"
;;     (redex-let aps# ([s#
;;                       `(((Nat (addr 1 0)))
;;                         ()
;;                         (goto A)
;;                         ((define-state (A)))
;;                         ())])
;;       (check-false (aps#-completed-no-transition-config? (term s#))))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Blurring

;; ;; Blurs the given specification configuration by removing all receptionists in the unobserved
;; ;; environment interface with the wrong spawn flag
;; (define (aps#-blur-config config internals-to-blur)
;;   (redex-let aps# ([[any_obs-receptionists
;;                      any_unobs-receptionists
;;                      any_exp
;;                      any_state-defs
;;                      any_out-coms]
;;                     config])
;;     (define blurred-unobs-env
;;       (csa#-blur-addresses (term any_unobs-receptionists) internals-to-blur null))
;;     (term [any_obs-receptionists
;;            ,(merge-receptionists null blurred-unobs-env)
;;            any_exp
;;            any_state-defs
;;            any_out-coms])))

;; (module+ test
;;   (test-equal? "aps#-blur-config"
;;     (aps#-blur-config (aps#-make-no-transition-config
;;                        `((Nat (addr 0 0))
;;                          (Nat (addr 1 0))
;;                          (Nat (addr 1 1))
;;                          (Nat (addr 2 1))
;;                          (Nat (collective-addr 1))
;;                          (Nat (addr 2 0)))
;;                        `([(addr (env Nat) 0)]))
;;                       (list (term (addr 1 1))))
;;     (aps#-make-no-transition-config
;;      `((Nat (addr 0 0))
;;        (Nat (addr 1 0))
;;        (Nat (collective-addr 1))
;;        (Nat (addr 2 1))
;;        (Nat (addr 2 0)))
;;      `([(addr (env Nat) 0)])))

;;   (test-equal? "aps#-blur-config merges addresses after blur"
;;     (aps#-blur-config `(()
;;                         ([(Union [A]) (collective-addr 1)]
;;                          [(Union [B]) (addr 1 0)])
;;                         (goto S)
;;                         ()
;;                         ())
;;                       (list `(addr 1 0)))
;;      `(()
;;        ([(Union [A] [B]) (collective-addr 1)])
;;        (goto S)
;;        ()
;;        ())))

;; ;; (define-metafunction aps#
;; ;;   blur-receptionists : (a#int ...) spawn-flag -> (a#int ...)
;; ;;   [(blur-receptionists () _) ()]
;; ;;   [(blur-receptionists ((spawn-addr any_loc spawn-flag τ) any_rest ...) spawn-flag)
;; ;;    (blur-receptionists (any_rest ...) spawn-flag)]
;; ;;   [(blur-receptionists (any_1 any_rest ...) spawn-flag)
;; ;;    (any_1 any_result ...)
;; ;;    (where (any_result ...) (blur-receptionists (any_rest ...) spawn-flag))])

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Canonicalization (i.e. renaming)

;; ;; NOTE: OLD/NEW are now 0/1; comments have not been updated yet

;; ;; Given an impl config/spec config pair, transforms it into an equivalent (for the purpose of
;; ;; conformance), canonical form. Also returns the address rename map. Specifically:
;; ;;
;; ;; 1. Changes all spawn address new/old flags to OLD (assumes that these configs have already been
;; ;; blurred so that either an OLD or a NEW version of an address exists, but not both)
;; ;;
;; ;; 2. Renames all atomic external addresses such that the first one in the spec config's state
;; ;; argument list is address 0, then address 1, then address 2, and so on. The remaining atomic
;; ;; external addresses are sorted and then given the next available address identifiers in order (so if
;; ;; addresses 52, 81, and 35 remain and 6 is the next available identifier, 35 would map to 6, 52 to 7,
;; ;; and 81 to 8).
;; ;;
;; ;; 3. Also sorts the escaped addresses in the impl config and the receptionists in the spec config
;; ;; (not strictly necessary to ensure a bounded state space, but provides a form of symmetry
;; ;; reduction).
;; (define (canonicalize-pair impl-config spec-config)
;;   (match-define (list aged-impl-config aged-spec-config)
;;     (age-addresses (list impl-config spec-config)))
;;   (define state-args (aps#-config-current-state-args aged-spec-config))
;;   (define state-arg-substitutions
;;     (for/list ([state-arg state-args]
;;                [new-number (build-list (length state-args) values)])
;;       (redex-let aps# ([(addr _ natural) state-arg])
;;         (list (term natural) new-number))))
;;   (define remaining-observed-addrs
;;     (filter (lambda (addr) (not (member addr state-args)))
;;             (map aps#-commitment-entry-address (aps#-config-commitment-map aged-spec-config))))
;;   (define remaining-substitutions
;;     (for/list ([addr (sort remaining-observed-addrs sexp<?)]
;;                [new-number (build-list (length remaining-observed-addrs)
;;                                        (curry + (length state-args)))])
;;       (redex-let aps# ([(addr _ natural) addr])
;;         (list (term natural) new-number))))
;;   (define substitutions (append state-arg-substitutions remaining-substitutions))
;;   (match-define (list renamed-impl-config renamed-spec-config)
;;     (rename-external-addresses (list aged-impl-config aged-spec-config) substitutions))
;;   (list (csa#-sort-config-components renamed-impl-config)
;;         (aps#-sort-obligation-entries (aps#-sort-receptionists renamed-spec-config))
;;         substitutions))

;; (module+ test
;;   (test-equal? "canonicalize 1"
;;     (canonicalize-pair
;;      (make-single-actor-abstract-config
;;       (term ((addr 0 0)
;;              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
;;               (goto A (addr (env Nat) 25) (addr (env Nat) 42) (addr (env Nat) 10))))))
;;      (term
;;       (((Nat (addr 0 0)))
;;        ()
;;        (goto A (addr (env Nat) 25) (addr (env Nat) 42) (addr (env Nat) 10))
;;        ((define-state (A a b c) [* -> () (goto A)]))
;;        (((addr (env Nat) 25)) ((addr (env Nat) 42)) ((addr (env Nat) 10))))))
;;     (term
;;      (,(make-single-actor-abstract-config
;;         (term ((addr 0 0)
;;                (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
;;                 (goto A (addr (env Nat) 0) (addr (env Nat) 1) (addr (env Nat) 2))))))
;;       (((Nat (addr 0 0)))
;;        ()
;;        (goto A (addr (env Nat) 0) (addr (env Nat) 1) (addr (env Nat) 2))
;;        ((define-state (A a b c) [* -> () (goto A)]))
;;        (((addr (env Nat) 0)) ((addr (env Nat) 1)) ((addr (env Nat) 2))))
;;       ([25 0] [42 1] [10 2]))))

;;   (test-equal? "canonicalize 2"
;;     (canonicalize-pair
;;      (make-single-actor-abstract-config
;;       (term ((addr 0 0)
;;              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
;;               (goto A (addr (env Nat) 10) (addr (env Nat) 42) (addr (env Nat) 25))))))
;;      (term
;;       (((Nat (addr 0 0)))
;;        ()
;;        (goto A (addr (env Nat) 25) (addr (env Nat) 42) (addr (env Nat) 10))
;;        ((define-state (A c b a) [* -> () (goto A)]))
;;        (((addr (env Nat) 25)) ((addr (env Nat) 42)) ((addr (env Nat) 10))))))
;;     (term
;;      (,(make-single-actor-abstract-config
;;         (term ((addr 0 0)
;;                (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
;;                 (goto A (addr (env Nat) 2) (addr (env Nat) 1) (addr (env Nat) 0))))))
;;       (((Nat (addr 0 0)))
;;        ()
;;        (goto A (addr (env Nat) 0) (addr (env Nat) 1) (addr (env Nat) 2))
;;        ((define-state (A c b a) [* -> () (goto A)]))
;;        (((addr (env Nat) 0)) ((addr (env Nat) 1)) ((addr (env Nat) 2))))
;;       ([25 0] [42 1] [10 2]))))

;;   (test-equal? "canonicalize spec config with self patterns"
;;     (canonicalize-pair
;;      (make-single-actor-abstract-config
;;       (term ((addr 1 0)
;;              (() (goto A)))))
;;      `[()
;;        ()
;;        (goto B (addr (env Nat) 99))
;;        ()
;;        ([(addr (env Nat) 57) self]
;;         [(addr (env Nat) 99)]
;;         [(addr (env Nat) 42) self])])
;;     `[,(make-single-actor-abstract-config
;;         (term ((addr 1 0)
;;                (() (goto A)))))
;;       [()
;;        ()
;;        (goto B (addr (env Nat) 0))
;;        ()
;;        ([(addr (env Nat) 0)]
;;         [(addr (env Nat) 1) self]
;;         [(addr (env Nat) 2) self])]
;;       [[99 0]
;;        [42 1]
;;        [57 2]]]))

;; ;; Given a term, changes all spawn addresses of the form (spawn-addr _ NEW _) to (spawn-addr _ OLD _),
;; ;; to ensure that spawned addresses in the next handler are fresh.
;; (define (age-addresses some-term)
;;   (match some-term
;;     [(and `(addr ,loc ,id) (? csa#-internal-address?))
;;      (if (equal? id 1)
;;          (term (addr ,loc 0))
;;          some-term)]
;;     [(list terms ...) (map age-addresses terms)]
;;     [_ some-term]))

;; (module+ test
;;   (test-equal? "Age addresses test"
;;     (redex-let aps# ([e# `(list (addr 1 1)
;;                                 (addr 2 0)
;;                                 (addr 3 0)
;;                                 (addr (env Nat) 4))])
;;         (age-addresses (term e#)))
;;     `(list (addr 1 0)
;;            (addr 2 0)
;;            (addr 3 0)
;;            (addr (env Nat) 4))))

;; ;; Any (Listof (List Natural Natural)) -> Any
;; ;;
;; ;; Renames precise external addresses in the given term by replacing its number with
;; ;; the corresponding number in the alist mapping
;; (define (rename-external-addresses term number-mapping)
;;   (match term
;;     [(and `(addr ,loc ,old-id) (? (negate csa#-internal-address?)))
;;      (match (findf (lambda (entry) (eq? (first entry) old-id)) number-mapping)
;;        [#f `(addr ,loc ,old-id)]
;;        [(list _ new-id) `(addr ,loc ,new-id)])]
;;     [(list subterms ...)
;;      (map (curryr rename-external-addresses number-mapping) subterms)]
;;     [_ term]))

;; (module+ test
;;   (check-equal?
;;    (rename-external-addresses
;;     `(some-term (addr (env Nat) 2) (another-term (addr (env Nat) 5)) (addr (env Nat) 13) (addr (env Nat) 0))
;;     `([2 1] [13 2] [5 3]))
;;    (term (some-term (addr (env Nat) 1) (another-term (addr (env Nat) 3)) (addr (env Nat) 2) (addr (env Nat) 0)))))

;; ;; Returns a spec config identical to the given one except that the the receptionist list is sorted
;; (define (aps#-sort-receptionists config)
;;   (redex-let aps# ([(any_obs-receptionists any_unobs-receptionists any_rest ...) config])
;;     (term (any_obs-receptionists ,(sort (term any_unobs-receptionists) sexp<?) any_rest ...))))

;; (define (aps#-sort-obligation-entries config)
;;   (match-define `[,obs-recs ,unobs-recs ,goto ,state-defs ,obligation-map] config)
;;   (define (entry< entry1 entry2)
;;     (sexp<? (aps#-commitment-entry-address entry1)
;;             (aps#-commitment-entry-address entry2)))
;;   `[,obs-recs
;;     ,unobs-recs
;;     ,goto
;;     ,state-defs
;;     ,(sort obligation-map entry<)])

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

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Testing Helpers

;; (define (make-s# defs goto unobs-receptionists out-coms)
;;   (term (((Nat (addr 0 0))) ,unobs-receptionists ,goto ,defs ,out-coms)))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Debugging

;; (define (spec-config-without-state-defs config)
;;   (redex-let aps# ([(any_obs-rec any_unobs-rec any_goto _ any_out) config])
;;     (term (any_obs-rec any_unobs-rec any_goto any_out))))
