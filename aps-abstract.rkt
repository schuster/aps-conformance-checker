#lang racket

;; Abstract semantic domains for APS (specification language), and associated functions

(provide
 ;; Required by conformance checker
 ;; TODO: consider having this one return the address or #f
 aps#-config-obs-interface
 aps#-unknown-address?
 aps#-config-receptionists
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
 "sexp-helpers.rkt")

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt"))

(define-union-language aps-eval-with-csa#
  aps-eval csa#)

(define-extended-language aps#
  aps-eval-with-csa#
  (s# (σ# (a#int_unobs-receptionists ...) (goto φ u ...) (Φ ...) O#))
  (σ# a# UNKNOWN) ; observed environment interface
  (u .... a#ext)
  (O# ((a#ext (m po) ...) ...)))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

(define (aps#-abstract-config spec-config internal-addresses)
  ;; Doing a redex-let here just to add a codomain contract
  (redex-let aps# ([s# (term (aps#-abstract-config/mf ,spec-config ,internal-addresses))])
             (term s#)))

;; TODO: rewrite this and put a better contract on here once we put #'s on all the APS# non-terminals
(define-metafunction aps#
  aps#-abstract-config/mf : any (a ...) -> any
  [(aps#-abstract-config/mf a (a_internal ...))
   ,(csa#-abstract-address (term a) (term (a_internal ...)))]
  [(aps#-abstract-config/mf (any ...) (a ...))
   ((aps#-abstract-config/mf any (a ...)) ...)]
  [(aps#-abstract-config/mf any _) any])

(module+ test
  (check-equal?
   (aps#-abstract-config (term ((addr 0 Nat)
                                ()
                                (goto A (addr 1 Nat))
                                ((define-state (A x) (* -> () (goto A x))))
                                ()))
                         (term ((addr 0 Nat))))
   (term ((init-addr 0 Nat)
          ()
          (goto A (obs-ext 1 Nat))
          ((define-state (A x) (* -> () (goto A x))))
          ())))

  (test-equal? "Abstraction check for addresses whose types don't match"
    (aps#-abstract-config (term ((addr 0 (Union [B]))
                                 ()
                                 (goto A)
                                 ((define-state (A)))
                                 ()))
                          (term ((addr 0 (Union [C])))))
    (term ((init-addr 0 (Union [B]))
           ()
           (goto A)
           ((define-state (A)))
           ()))))

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
  subst/aps#/po : po x a# -> po
  [(subst/aps#/po * x a#) *]
  [(subst/aps#/po (or po ...) x a#) (or (subst/aps#/po po x a#) ...)]
  [(subst/aps#/po (fork any_goto any_s-defs ...) self _)
   (fork any_goto any_s-defs ...)]
  [(subst/aps#/po (fork (goto φ u ...) Φ ...) x a#)
   (fork (goto φ (subst/aps#/u u x a#) ...)
               (subst/aps#/Φ Φ x a#) ...)]
  [(subst/aps#/po self self a#int) a#int]
  [(subst/aps#/po self _ _) self]
  [(subst/aps#/po (variant t po ...) x a#)
   (variant t (subst/aps#/po po x a#) ...)]
  [(subst/aps#/po (record t [l po] ...) x a#)
   (record [l (subst/aps#/po po x a#)] ...)])

(define-metafunction aps#
  subst/aps#/Φ : Φ x a# -> Φ
  [(subst/aps#/Φ (define-state (φ any_1 ... x any_2 ...) any_trans ...) x a#)
   (define-state (φ any_1 ... x any_2 ...) any_trans ...)]
  [(subst/aps#/Φ (define-state (φ x_φ ...) any_trans ...) x a#)
   (define-state (φ x_φ ...) (subst/aps#/trans any_trans x a#) ...)])

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
   (fork (goto φ (subst/aps#/u u x a#) ...)
         (subst/aps#/Φ Φ x a#) ...)])

(module+ test
  (test-equal? "Simple subst/aps#/f test"
    (term (subst/aps#/f [fork (goto S1 x)
                              (define-state (S1 y x) [* -> () (goto S2 y)])
                              (define-state (S2 y) [* -> ([obligation x *]) (goto S2 y)])]
                        x
                        (obs-ext 1 Nat)))
    (term [fork (goto S1 (obs-ext 1 Nat))
                (define-state (S1 y x) [* -> () (goto S2 y)])
                (define-state (S2 y) [* -> ([obligation (obs-ext 1 Nat) *]) (goto S2 y)])])))

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

;; TODO: deal with the case where the pattern variables shadow the state variables
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
  (remove-duplicates
   (filter
    values
    (map (lambda (t) (attempt-transition spec-config t from-observer? trigger))
         (config-current-transitions spec-config)))))

(module+ test
  (test-equal? "Null step is possible"
               (aps#-matching-steps
                (make-s# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                #f
                (term (timeout/empty-queue (init-addr 0 Nat))))
               (list
                (list (make-s# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                      null)))

  (test-equal? "Multiple copies of output commitments are merged"
               (aps#-matching-steps
                (make-s# (term ((define-state (A r) [* -> ((obligation r *)) (goto A r)])))
                         (term (goto A (obs-ext 0 Nat)))
                         null
                         (term (((obs-ext 0 Nat) (single *)))))
                #t
                (term (external-receive (init-addr 0 Nat) (* Nat))))
               (list
                (list
                 (make-s# (term ((define-state (A r) [* -> ((obligation r *)) (goto A r)])))
                          (term (goto A (obs-ext 0 Nat)))
                          null
                          (term (((obs-ext 0 Nat) (many *)))))
                 null))))

;; Returns the config updated by running the given transition, if it can be taken from the given
;; trigger, along with all configs spawned in the transition, or #f if the transition is not possible
;; from this trigger
(define (attempt-transition config transition from-observer? trigger)
  (match (match-trigger from-observer?
                        trigger
                        (aps#-config-obs-interface config)
                        (aps#-transition-trigger transition))
    [#f #f]
    [(list bindings ...)
     (match-define (list new-goto commitments spawn-infos) (aps#-eval transition bindings))
     (define updated-commitment-map
       (term
        (add-commitments
         ,(observe-addresses-from-subst
           (aps#-config-commitment-map config) bindings)
         ,@commitments)))
     (define stepped-current-config
       (term (,(aps#-config-obs-interface config)
              ,(aps#-config-receptionists config)
              ,new-goto
              ,(aps#-config-state-defs config)
              ,updated-commitment-map)))
     (fork-configs stepped-current-config spawn-infos)]))

;; transition ([x a#] ...) -> goto-exp ([a# po] ...) (<σ#, goto-exp, (Φ ...)> ...)
;;
;; Evaluates the given spec transition with the given variable bindings and returns the results (a
;; goto, the new output commitments, and spawn-info for any spawned specs
(define (aps#-eval transition bindings)
  (term (aps#-eval/mf ,transition ,bindings)))

(define-metafunction aps#
  aps#-eval/mf : (pt -> (f ...) (goto φ u ...)) ([x a#] ...)
  -> [(goto φ a#ext ...) ([a#ext po] ...) ((σ# (goto φ a#ext ...) (Φ ...)) ...)]
  [(aps#-eval/mf (_ -> (f ...) (goto φ u ...)) ([x a#] ...))
   ((goto φ (subst-n/aps#/u u [x a#] ...) ...)
    ([a#_ob po] ...)
    ([UNKNOWN any_fork-state (any_state-defs ...)] ...))
   (where (((obligation a#_ob po) ...)
           ((fork any_fork-state any_state-defs ...) ...))
          ,(collect-effects (term ((subst-n/aps#/f f [x a#] ...) ...))))])

;; (f ...) -> (([a# po] ...) ((<Φ ..., goto-exp, σ#> ...) ...))
(define (collect-effects fs)
  (define-values (obligations forks) (partition (lambda (f) (equal? (car f) 'obligation)) fs))
  (list obligations forks))

;; s# ((σ# goto-exp (Φ ...)) ...) -> s# (s# ...)
;;
;; Given the current configuration and the info needed to spawn new configs, splits information from
;; the current configuration off to form the new configurations
(define (fork-configs current-config spawn-infos)
  (redex-let aps# ([(σ# any_receptionists any_goto any_states O#) current-config])
    (define-values (commitment-map spawned-configs)
      (for/fold ([current-commitment-map (term O#)]
                 [spawned-configs null])
                ([spawn-info spawn-infos])
        (match-define (list address goto state-defs) spawn-info)
        (match-define (list remaining-map spawned-map)
          (fork-commitment-map current-commitment-map (externals-in (list state-defs goto))))
        ;; TODO: figure out what to do with this old receptionist code
        ;; (define new-receptionists
        ;;   (remove-duplicates (append (term any_receptionists)
        ;;                              (if (equal? (aps#-config-only-instance-address current-config) 'UNKNOWN)
        ;;                                  '()
        ;;                                  (list (aps#-config-only-instance-address current-config))))))
        (values remaining-map
                ;; TODO: add parent to this receptionist list
                (cons (term (,address any_receptionists ,goto ,state-defs ,spawned-map))
                      spawned-configs))))
    ;; TODO: add all forked addresses to this receptionist list
    (list (term (σ# any_receptionists any_goto any_states ,commitment-map)) spawned-configs)))

(module+ test
  (test-equal? "Degenerate fork config case"
               (fork-configs (term (UNKNOWN () (goto A) ((define-state (A))) ())) null)
               (list (term (UNKNOWN () (goto A) ((define-state (A))) ())) null))

  (test-equal? "Basic fork config case"
    (fork-configs (term (UNKNOWN () (goto A) ((define-state (A))) ([(obs-ext 1 Nat) (single *)] [(obs-ext 2 Nat) (single (record))])))
                  (term ([UNKNOWN (goto B (obs-ext 2 Nat)) ((define-state (B r)))])))
    (list (term (UNKNOWN () (goto A) ((define-state (A))) ([(obs-ext 1 Nat) (single *)])))
          (list (term (UNKNOWN () (goto B (obs-ext 2 Nat)) ((define-state (B r))) ([(obs-ext 2 Nat) (single (record))])))))))

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
    (term (((obs-ext 1 Nat) (single *))
           ((obs-ext 2 Nat))
           ((obs-ext 3 Nat))
           ((obs-ext 4 Nat) (single (record)))))
    (term ((obs-ext 1 Nat) (obs-ext 3 Nat) (obs-ext 5 Nat))))
   (list
    (term (((obs-ext 2 Nat))
           ((obs-ext 4 Nat) (single (record)))))
    (term (((obs-ext 1 Nat) (single *))
           ((obs-ext 3 Nat))
           ((obs-ext 5 Nat)))))))

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
  [(add-commitments (any_1 ... (a#ext_1 any_2 ... (_ po)    any_3 ...) any_4 ...)
                    [a#ext_2 po] any_rest ...)
   (add-commitments (any_1 ... (a#ext_1 any_2 ... (many po) any_3 ...) any_4 ...)
                    any_rest ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))]
  [(add-commitments (any_1 ... (a#ext_1 any_coms ...)             any_2 ...) [a#ext_2 po] any_rest ...)
   (add-commitments (any_1 ... (a#ext_1 any_coms ... (single po)) any_2 ...) any_rest ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))])

(module+ test
  (test-equal? "add-commitments"
               (term (add-commitments
                      ([(obs-ext 1 Nat) [single *] [many (record)]]
                       [(obs-ext 2 (Union))])
                      [(obs-ext 1 Nat) *]
                      [(obs-ext 2 (Union [A])) *]
                      [(obs-ext 1 Nat) (variant A)]))
               `([(obs-ext 1 Nat) [many *] [many (record)] [single (variant A)]]
                 [(obs-ext 2 (Union)) [single *]])))

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

;; Matches the trigger against the given transition pattern, returning the bindings created from the
;; match if such a match exists, else #f
(define (match-trigger from-observer? trigger address pattern)
  (match
      (judgment-holds
       (match-trigger/j ,from-observer? ,trigger ,address ,pattern any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (match-trigger/j I I I I O)
  #:contract (match-trigger/j boolean trigger# σ# pt ([x v#] ...))

  [-------------------------------------------------------
   (match-trigger/j _ (timeout/empty-queue _) _ unobs ())]

  [-----------------------------------------------------------
   (match-trigger/j _ (timeout/non-empty-queue _) _ unobs ())]

  [----------------------------------------------------------------------
   (match-trigger/j _ (internal-receive _ _) _ unobs ())]

  [-----------------------------------------------------------------------
   (match-trigger/j #f (external-receive _ _) _ unobs ())]

  [(same-internal-address-without-type? a#_1 a#_2)
   (aps#-match/j v# p any_bindings)
   --------------------------------------------------------------------------------
   (match-trigger/j #t (external-receive a#_1 v#) a#_2 p any_bindings)])

(module+ test
  (check-equal?
   (match-trigger #f '(timeout/empty-queue (init-addr 0 Nat)) '(init-addr 0 Nat) 'unobs)
   null)

  (check-equal?
   (match-trigger #f '(timeout/non-empty-queue (init-addr 0 Nat)) '(init-addr 0 Nat) 'unobs)
   null)

  (check-equal?
   (match-trigger #f '(external-receive (init-addr 0 Nat) (* Nat)) '(init-addr 0 Nat) 'unobs)
   null)

  (check-false
   (match-trigger #t '(external-receive (init-addr 0 Nat) (* Nat)) '(init-addr 0 Nat) 'unobs))

  (check-equal?
   (match-trigger #t '(external-receive (init-addr 0 Nat) (obs-ext 1 Nat)) '(init-addr 0 Nat) 'x)
   (list '(x (obs-ext 1 Nat))))

  (check-false
   (match-trigger #f '(internal-receive (init-addr 0 Nat) (* Nat)) '(init-addr 0 Nat) 'x))

  (check-false
   (match-trigger #t '(external-receive (init-addr 0 Nat) (* Nat)) '(init-addr 0 Nat) 'x))

  (check-equal?
   (match-trigger #f '(internal-receive (init-addr 0 Nat) (* Nat)) '(init-addr 0 Nat) 'unobs)
   null)

  (check-false
   (match-trigger #t '(external-receive (init-addr 0 (Union [A] [B])) (variant A)) '(init-addr 0 (Union [A])) 'unobs))

  (check-equal?
   (match-trigger #t '(external-receive (init-addr 0 (Union [A] [B])) (variant A)) '(init-addr 0 (Union [A])) '*)
   null))

(define-judgment-form aps#
  #:mode (aps#-match/j I I O)
  #:contract (aps#-match/j v# p ((x v#) ...))

  [-------------------
   (aps#-match/j _ * ())]

  [-----------------------------------
   (aps#-match/j a#ext x ([x a#ext]))]

  [(aps#-match/j v# p ([x v#_binding] ...)) ...
   --------------
   (aps#-match/j (variant t v# ..._n) (variant t p ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j (* τ) p ([x v#_binding] ...)) ...
   --------------
   (aps#-match/j (* (Union _ ... [t τ ..._n] _ ...)) (variant t p ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j v# p ([x v#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (record [l v#] ..._n) (record [l p] ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j (* τ) p ([x v#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (* (Record [l τ] ..._n)) (record [l p] ..._n) ([x v#_binding] ... ...))])

(module+ test
;; TODO: rewrite these tests
  ;; (check-equal? (aps#-match (term (* Nat)) (term *))
  ;;               (list (term ())))
  ;; (check-equal? (aps#-match (term (received-addr Always ADDR-HOLE 0 MOST-RECENT)) (term x))
  ;;               (list (term ([x (received-addr Always ADDR-HOLE 0 MOST-RECENT)]))))
  ;; (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a 'b)))
  ;;               (list (term ())))
  ;; ;; (displayln (redex-match csa# t (term 'a)))
  ;; ;; (displayln (redex-match csa# v# (term 'a)))
  ;; ;; (displayln (redex-match csa# x (term item)))
  ;; ;; (displayln (build-derivations (aps#-match/j 'a item ())))
  ;; (check-equal? (aps#-match (term 'a) (term item))
  ;;               (list (term ([item 'a]))))
  ;; (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a item)))
  ;;               (list (term ([item 'b]))))
  ;; (check-equal? (aps#-match (term (* (Tuple 'a 'b))) (term (tuple x 'b)))
  ;;               (list (term ([x (* 'a)]))))
  (check-true (judgment-holds (aps#-match/j (* Nat) * any)))
  (check-false (judgment-holds (aps#-match/j (* Nat) x any))))

;;  aps#-match-po (csa#-output-message output) self-address) patterns)

(define (aps#-match-po value self-address pattern)
  (match (judgment-holds (aps#-matches-po?/j ,value
                                             ,self-address
                                             ,pattern
                                             any_new-self
                                             any_spawn-infos
                                             any_recs)
                         (any_new-self any_spawn-infos any_recs))
    [(list) #f]
    [(list result) result]
    [_ (error "Got multiple possible matches from match-po; shouldn't happen")]))

(define-judgment-form aps#
  #:mode (aps#-matches-po?/j I I I O O O)
  #:contract (aps#-matches-po?/j v# σ# po σ# ((σ# (goto φ a# ...) (Φ ...))  ...) (a#int ...))

  [-----
   (aps#-matches-po?/j v# σ# * σ# () ,(internals-in (term v#)))]

  [(aps#-matches-po?/j v# σ# po                  any_self-addr any_spawns any_receptionists)
   -----
   (aps#-matches-po?/j v# σ# (or _ ... po _ ...) any_self-addr any_spawns any_receptionists)]

  [----
   (aps#-matches-po?/j a#int
                       σ#
                       (fork (goto φ a# ...) Φ ...)
                       σ#
                       ((a#int (goto φ a# ...) (Φ ...)))
                       ())]

  [----
   (aps#-matches-po?/j a#int a#int self a#int () ())]

  [----
   (aps#-matches-po?/j a#int UNKNOWN self a#int () ())]

  [(aps#-list-matches-po?/j ((v# po) ...) σ# any_self-addr any_spawns any_receptionists)
   ------
   (aps#-matches-po?/j (variant t v# ..._n)
                       σ#
                       (variant t po ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  [(aps#-list-matches-po?/j (((* τ) po) ...) σ# any_self-addr any_spawns any_receptionists)
   -----
   (aps#-matches-po?/j (* (Union _ ... [t τ ..._n] _ ...))
                       σ#
                       (variant t po ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  ;; Records

  [(aps#-list-matches-po?/j ((v# po) ...) σ# any_self-addr any_spawns any_receptionists)
   ------
   (aps#-matches-po?/j (record [l v#] ..._n)
                       σ#
                       (record [l po] ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  [(aps#-list-matches-po?/j (((* τ) po) ...) σ# any_self-addr any_spawns any_receptionists)
   -----
   (aps#-matches-po?/j (* (Record [l τ] ..._n))
                       σ#
                       (record [l po] ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)])

(define-judgment-form aps#
  #:mode (aps#-list-matches-po?/j I I O O O)
  #:contract (aps#-list-matches-po?/j ((v# po) ...)
                                      σ#
                                      σ#
                                      ((σ# (goto φ a# ...) (Φ ...)) ...)
                                      (a#int ...))
  [---------
   (aps#-list-matches-po?/j () any_addr any_addr () ())]

  [(aps#-matches-po?/j v# σ# po any_addr1 (any_spawn-infos1 ...) (any_receptionists1 ...))
   (aps#-list-matches-po?/j (any_rest ...)
                            any_addr1
                            any_addr2
                            (any_spawn-infos2 ...)
                            (any_receptionists2 ...))
   ---------
   (aps#-list-matches-po?/j ((v# po) any_rest ...)
                            σ#
                            any_addr2
                            (any_spawn-infos1 ... any_spawn-infos2 ...)
                            (any_receptionists1 ... any_receptionists2 ...))])

(module+ test
  (check-equal?
   (aps#-match-po '(* Nat) 'UNKNOWN '*)
   (list 'UNKNOWN null null))
  (check-false
   (aps#-match-po '(* Nat) 'UNKNOWN '(record)))
  (check-equal?
   (aps#-match-po '(init-addr 0 Nat) 'UNKNOWN 'self)
   (list '(init-addr 0 Nat) null null))
  (check-equal?
   (aps#-match-po '(init-addr 0 Nat) 'UNKNOWN '*)
   (list 'UNKNOWN null (list '(init-addr 0 Nat))))
  (check-false
   (aps#-match-po '(obs-ext 0 Nat) 'UNKNOWN 'self))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (init-addr 2 Nat)) 'UNKNOWN '(variant A * self))
   (list '(init-addr 2 Nat) '() '()))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (init-addr 2 Nat)) '(init-addr 2 Nat) '(variant A * self))
   (list '(init-addr 2 Nat) '() '()))
  (check-equal?
   (aps#-match-po '(variant A (* Nat) (init-addr 2 Nat))
                  '(init-addr 2 Nat)
                  '(or (variant A * self) (variant B)))
   (list '(init-addr 2 Nat) '() '()))
  (check-equal? (aps#-match-po (term (variant A)) 'UNKNOWN (term (or (variant A) (variant B))))
                (list 'UNKNOWN null null))
  (check-equal? (aps#-match-po (term (variant B)) 'UNKNOWN (term (or (variant A) (variant B))))
                (list 'UNKNOWN null null))
  (check-false (aps#-match-po (term (variant C)) 'UNKNOWN (term (or (variant A) (variant B)))))
  (check-false
   (aps#-match-po '(variant A (* Nat) (init-addr 2 Nat)) '(init-addr 1 Nat) '(variant A * self)))
  (test-equal? "Spawn match po test"
   (aps#-match-po '(spawn-addr 'foo NEW Nat)
                  'UNKNOWN
                  '(fork (goto B) (define-state (B))))
   (list 'UNKNOWN
         '([(spawn-addr 'foo NEW Nat) (goto B) ((define-state (B)))])
         '()))
  (test-equal? "Full match po test"
   (aps#-match-po '(variant A (spawn-addr 'foo NEW Nat) (init-addr 2 Nat))
                  'UNKNOWN
                  '(variant A (fork (goto B) (define-state (B))) self))
   (list '(init-addr 2 Nat)
         '([(spawn-addr 'foo NEW Nat)
            (goto B)
            ((define-state (B)))])
         '()))

    ;; TODO: rewrite these tests
  ;; (check-true (judgment-holds (aps#-matches-po?/j 'a 'a)))
  ;; (check-true (aps#-matches-po? (term 'a) (term 'a)))
  ;; (check-true (aps#-matches-po? (term (* 'a)) (term 'a)))
  ;; (check-false (aps#-matches-po? (term (* 'a)) (term 'b)))

  ;; (check-true (aps#-matches-po? (term (* (Tuple 'a 'b))) (term (tuple 'a 'b))))
  ;; (check-false (aps#-matches-po? (term (* (Tuple 'a 'b))) (term (tuple 'a 'c))))
  ;; (check-true (aps#-matches-po? (term (tuple (* 'a))) (term (tuple 'a))))
  ;; (check-true (aps#-matches-po? (term (tuple (quote b) (* Nat)))
  ;;                               (term (tuple (quote b) *))))
)

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; s# ((a#ext v#) ...) ->  s# (s# ...) ([a po] ...)
;;
;; Returns a tuple of the specification config after having resolved all of the given outputs
;; (removing output commitments as necessary), a list of the satisfied commitments, and the spawned
;; configs; or #f if a resolution of these outputs is not possible
;;
;; NOTE: assuming there is at most one way to satisfy the given config's commitments with these
;; outputs, which may not necessarily be true (but usually should be)
(define (aps#-resolve-outputs spec-config outputs)
  ;; TODO: deal with loop output
  (let loop ([commitment-map (aps#-config-commitment-map spec-config)]
             [self-address (aps#-config-obs-interface spec-config)]
             [spawn-infos null]
             [added-unobs-receptionists null]
             [satisfied-commitments null]
             [remaining-outputs outputs])
    (match remaining-outputs
      [(list)
       (define updated-config
         (term (,self-address
                ,(merge-receptionists (aps#-config-receptionists spec-config)
                                      added-unobs-receptionists)
                ,(aps#-config-current-state spec-config)
                ,(aps#-config-state-defs spec-config)
                ,commitment-map)))
       (match-define (list remaining-config spawned-configs)
         (fork-configs updated-config spawn-infos))
       (list remaining-config spawned-configs satisfied-commitments)]
      [(list output remaining-outputs ...)
       (define address (csa#-output-address output))
       (match (commitments-for-address commitment-map address)
         ;; we can ignore outputs on unobserved addresses
         [#f (loop commitment-map
                   self-address
                   spawn-infos
                   added-unobs-receptionists
                   satisfied-commitments
                   remaining-outputs)]
         [commitments
          (define patterns (map commitment-pattern commitments))
          ;; NOTE: This assumes there is at most one pattern that matches the message (this should
          ;; usually be true)
          (match (find-matching-pattern patterns (csa#-output-message output) self-address)
            [#f #f]
            [(list pat self-address new-spawn-infos new-receptionists)
             (loop (aps#-remove-commitment-pattern commitment-map address pat)
                   self-address
                   (append spawn-infos new-spawn-infos)
                   (append added-unobs-receptionists new-receptionists)
                   (append satisfied-commitments (list (term (,address ,pat))))
                   remaining-outputs)])])])))

(define (find-matching-pattern patterns message self-address)
  (let loop ([patterns patterns])
    (match patterns
      [(list) #f]
      [(list pattern patterns ...)
       (match (aps#-match-po message self-address pattern)
         [#f (loop patterns)]
         [(list self-addr spawn-infos new-receptionists)
          (list pattern self-addr spawn-infos new-receptionists)])])))

(module+ test
  (define (make-dummy-spec commitments)
    (term (UNKNOWN () (goto DummyState) ((define-state (DummyState))) ,commitments)))
  (test-false "resolve test 1"
    (aps#-resolve-outputs
     (make-dummy-spec `(((obs-ext 1 Nat))))
     (term (((obs-ext 1 Nat) (* Nat))))))
  (test-equal? "resolve test 2"
    (aps#-resolve-outputs
     (make-dummy-spec `(((obs-ext 1 Nat) (single *))))
     (term (((obs-ext 1 Nat) (* Nat)))))
    (list (make-dummy-spec `(((obs-ext 1 Nat))))
          `()
          `(((obs-ext 1 Nat) *))))
  (test-equal? "resolve test 3"
    (aps#-resolve-outputs
     (make-dummy-spec `(((obs-ext 1 Nat) (single *) (single (record)))))
     (term (((obs-ext 1 Nat) (* Nat)))))
    (list (make-dummy-spec `(((obs-ext 1 Nat) (single (record)))))
          `()
          `(((obs-ext 1 Nat) *))))
  (test-equal? "resolve test 4"
    (aps#-resolve-outputs
     (make-dummy-spec `(((obs-ext 1 Nat) (many *) (single (record)))))
     (term (((obs-ext 1 Nat) (* Nat)))))
    (list (make-dummy-spec `(((obs-ext 1 Nat) (many *) (single (record)))))
          `()
          `(((obs-ext 1 Nat) *))))

  ;; TODO: test aps#-resolve-outputs for (along with normal cases):
  ;; * spec that observes an address but neither saves it nor has output commtiments for it
  ;; * POV unobservables
  ;; * wildcard unobservables
  )

(define (aps#-remove-commitment-pattern commitment-map address pat)
  (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

(define-metafunction aps#
  remove-commitment-pattern/mf : O# a#ext po -> O#
  [(remove-commitment-pattern/mf (any_1 ... (a#ext_1 any_2 ... (single po) any_3 ...) any_4 ...)
                                 a#ext_2
                                 po)
   (any_1 ... (a#ext_1 any_2 ... any_3 ...) any_4 ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))]
  [(remove-commitment-pattern/mf (any_1 ... (a#ext_1 any_2 ... (many po) any_3 ...) any_4 ...)
                                 a#ext_2
                                 po)
   (any_1 ... (a#ext_1 any_2 ... (many po) any_3 ...) any_4 ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))])

(module+ test
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1 Nat) (single *)))) (term (obs-ext 1 Nat)) (term *))
   (term (((obs-ext 1 Nat)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1 (Union)) (single *)))) (term (obs-ext 1 (Union (A)))) (term *))
   (term (((obs-ext 1 (Union))))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1 Nat) (many *)))) (term (obs-ext 1 Nat)) (term *))
    (term (((obs-ext 1 Nat) (many *)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1 Nat) (single *) (single (record))))) (term (obs-ext 1 Nat)) (term *))
   (term (((obs-ext 1 Nat) (single (record))))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1 Nat) (single *) (single (record)) (many (record [a *]))) ((obs-ext 2 Nat) (single *))))
    (term (obs-ext 1 Nat))
    (term *))
   (term (((obs-ext 1 Nat) (single (record)) (many (record [a *]))) ((obs-ext 2 Nat) (single *))))))

;; Merges the list of new receptionists into the old one, taking the join of types for duplicate
;; entries and adding new entries otherwise
(define (merge-receptionists old-recs new-recs)
  (term (merge-receptionists/mf ,old-recs ,new-recs)))

(define-metafunction aps#
  merge-receptionists/mf : (a#int ...) (a#int ...) -> (a#int ...)
  [(merge-receptionists/mf any_1 ()) any_1]
  [(merge-receptionists/mf (any_1 ... (init-addr natural τ_1) any_2 ...)
                           ((init-addr natural τ_2) any_rest ...))
   (merge-receptionists/mf (any_1 ...
                           (init-addr natural (type-join τ_1 τ_2))
                           any_2 ...)
                           (any_rest ...))]
  [(merge-receptionists/mf (any_1 ... (spawn-addr any_loc any_flag τ_1) any_2 ...)
                           ((spawn-addr any_loc any_flag τ_2) any_rest ...))
   (merge-receptionists/mf (any_1 ...
                           (spawn-addr any_loc any_flag (type-join τ_1 τ_2))
                           any_2 ...)
                           (any_rest ...))]
  [(merge-receptionists/mf (any_1 ...) (any_curr any_rest ...))
   (merge-receptionists/mf (any_1 ... any_curr) (any_rest ...))])

(module+ test
  (test-equal? "merge receptionists"
    (term
     (merge-receptionists/mf
      ((init-addr 1 Nat)
       (spawn-addr 2 NEW (Union [B]))
       (init-addr 2 (Union [C])))
      ((spawn-addr 2 NEW (Union [A]))
       (init-addr 1 Nat)
       (init-addr 2 (Union [D]))
       (spawn-addr 3 OLD Nat))))
    (term
     ((init-addr 1 Nat)
      (spawn-addr 2 NEW (Union [B] [A]))
      (init-addr 2 (Union [C] [D]))
      (spawn-addr 3 OLD Nat)))))

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
    (term (UNKNOWN () (goto S1) () (((obs-ext 1 Nat) (single *))
                                    ((obs-ext 2 Nat) (single *) (single (record)))))))
  (test-false "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 3 Nat)) (term *)))
  (test-false "aps#-config-has-commitment? 2"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 1 Nat)) (term (record))))
  (test-true "aps#-config-has-commitment? 1"
    (aps#-config-has-commitment? has-commitment-test-config (term (obs-ext 2 Nat)) (term (record)))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-config-obs-interface config)
  (redex-let aps# ([(σ# _ ...) config])
    (term σ#)))

(define (aps#-config-receptionists config)
  (term (config-receptionists/mf ,config)))

(define-metafunction aps#
  config-receptionists/mf : s# -> (a#int ...)
  [(config-receptionists/mf (_ (a#int ...) _ ...)) (a#int ...)])

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
  (test-equal? "foobar"
    (aps#-config-commitment-map `((init-addr 1 Nat) () (goto A1) () ()))
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
     `(UNKNOWN
       ()
       (goto S1)
       ()
       ([(obs-ext 1 Nat) (single *) (many (record))]
        [(obs-ext 2 Nat)]
        [(obs-ext 3 Nat) (single *) (single (variant A)) (single (record [a *]))])))
    (list `[(obs-ext 1 Nat) *]
          `[(obs-ext 3 Nat) *]
          `[(obs-ext 3 Nat) (variant A)]
          `[(obs-ext 3 Nat) (record [a *])]))

  (test-equal? "config-many-of-commitments"
    (aps#-config-many-of-commitments
     `(UNKNOWN
       ()
       (goto S1)
       ()
       ([(obs-ext 1 Nat) (single *) (many (record))]
        [(obs-ext 2 Nat)]
        [(obs-ext 3 Nat) (single *) (single (variant A)) (single (record [a *]))]
        [(obs-ext 4 Nat) (many *) (many (variant A)) (single (record [a *]))])))
    (list `[(obs-ext 1 Nat) (record)]
          `[(obs-ext 4 Nat) *]
          `[(obs-ext 4 Nat) (variant A)])))

(define (aps#-transition-trigger transition)
  (redex-let aps# ([(pt -> _ _) transition])
    (term pt)))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (commitments-for-address commitment-map address)
  (term (commitments-for-address/mf ,commitment-map ,address)))

(define-metafunction aps#
  commitments-for-address/mf : O# a#ext -> ((m po) ...) or #f
  [(commitments-for-address/mf (_ ... (a#ext_1 (m po) ...) _ ...)
                               a#ext_2)
   ((m po) ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))]
  [(commitments-for-address/mf _ _) #f])

(module+ test
  (define test-O#
    (term (((obs-ext 1 Nat) (single *) (many (record)))
           ((obs-ext 2 Nat) (single (variant True)) (single (variant False))))))
  (check-equal?
   (commitments-for-address
    test-O#
    (term (obs-ext 1 Nat)))
   (term ((single *) (many (record)))))
  (check-equal?
   (commitments-for-address
    test-O#
    (term (obs-ext 2 Nat)))
   (term ((single (variant True)) (single (variant False)))))
  (check-false
   (commitments-for-address
    test-O#
    (term (obs-ext 3 Nat)))))

(define (commitment-pattern commitment)
  (redex-let aps# ([(m po) commitment]) (term po)))

;; "Relevant" external addresses are those in either the current state arguments or obligations of a
;; spec config
(define (aps#-relevant-external-addrs s#)
  (term (relevant-external-addrs/mf ,s#)))

(define-metafunction aps#
  relevant-external-addrs/mf : s# -> (a#ext ...)
  [(relevant-external-addrs/mf s#)
   ,(remove-duplicates (term (any_args ... any_commitment-addr ...)))
   (where (any_args ...) ,(aps#-config-current-state-args (term s#)))
   (where ((any_commitment-addr _ ...) ...) (config-commitment-map/mf s#))])

(module+ test
  (check-equal?
   (aps#-relevant-external-addrs
    (redex-let* aps#
                ([O# (term (((obs-ext 1 Nat)) ((obs-ext 3 Nat)) ((obs-ext 4 Nat))))]
                 [s# (term (UNKNOWN
                            ()
                            (goto Always (obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat))
                            ((define-state (Always r1 r2) (* -> () (goto Always r1 r2))))
                            O#))])
                (term s#)))
   (term ((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Spec Split

;; Splits the given specifcation configuration into multiple configs, to ensure the space of explored
;; spec configs is finite. For each external address in the commitment map that is not a state
;; argument (and therefore will never have more commitments addeded), it creates a new config
;; consisting only of the commitments on that address and a dummy FSM with no transitions. After
;; removing those commitment map entries, the remaining config is also returned. The unobserved
;; environment's interface does not change in any of the new configs.
(define (split-spec config)
  (define receptionists (aps#-config-receptionists config))
  ;; A commitment map entry is "relevant" if it is used as a state argument
  (define-values (relevant-entries irrelevant-entries)
    (partition (lambda (entry)
                 (member (aps#-commitment-entry-address entry)
                         (aps#-config-current-state-args config)))
               (aps#-config-commitment-map config)))
  (define commitment-only-configs
    (map (curryr aps#-config-from-commitment-entry
                 (aps#-config-obs-interface config)
                 receptionists)
         irrelevant-entries))
  (cons (term (,(aps#-config-obs-interface config)
               ,receptionists
               ,(aps#-config-current-state config)
               ,(aps#-config-state-defs config)
               ,relevant-entries))
        commitment-only-configs))

(module+ test
  (define (make-simple-spec-for-split-test commitments)
    (term
     ((init-addr 0 Nat)
      ()
      (goto A (obs-ext 0 Nat))
      ((define-state (A x) [* -> () (goto A x)]))
      ,commitments)))

  (test-equal? "split spec with one FSM gets same spec"
    (split-spec (make-simple-spec-for-split-test '()))
    (list (make-simple-spec-for-split-test '())))

  (test-equal? "split with one related commit"
   (split-spec (make-simple-spec-for-split-test `(((obs-ext 0 Nat) (single *)))))
   (list (make-simple-spec-for-split-test `(((obs-ext 0 Nat) (single *))))))

  (test-same-items? "split with unrelated commit"
   (split-spec (make-simple-spec-for-split-test `(((obs-ext 1 Nat) (single *)))))
   (list (make-simple-spec-for-split-test `())
         (aps#-make-no-transition-config `((init-addr 0 Nat)) `(((obs-ext 1 Nat) (single *)))))))

;; Makes a specification config with an UNKNOWN address and an FSM with no transitions. Used for
;; specifications where only the commitments are important.
(define (aps#-make-no-transition-config receptionists commitments)
  (term (UNKNOWN
         ,receptionists
         (goto DummySpecFsmState)
         ((define-state (DummySpecFsmState)))
         ,commitments)))

;; Creates a spec config with a transition-less FSM and a commitment map with just the given
;; entry. The receptionists for the unobserved environment will be the given list plus the given FSM
;; address if it is not UNKONWN.
(define (aps#-config-from-commitment-entry entry fsm-addr receptionists)
  (define all-receptionists
    (remove-duplicates
     (append receptionists
             (if (equal? fsm-addr 'UNKNOWN) '() (list fsm-addr)))))
  (aps#-make-no-transition-config all-receptionists (list entry)))

(module+ test
  (check-equal?
   (aps#-config-from-commitment-entry (term ((obs-ext 0 Nat) (single *) (single (record [a *] [b *])))) 'UNKNOWN null)
   (aps#-make-no-transition-config '() '(((obs-ext 0 Nat) (single *) (single (record [a *] [b *]))))))

  (test-equal? "Commitment entry spec should also include old FSM address as unobs receptionist"
    (aps#-config-from-commitment-entry (term ((obs-ext 0 Nat) (single *) (single (record [a *] [b *]))))
                                     '(init-addr 0 Nat)
                                     null)
    (aps#-make-no-transition-config
     '((init-addr 0 Nat))
     '(((obs-ext 0 Nat) (single *) (single (record [a *] [b *])))))))

;; ---------------------------------------------------------------------------------------------------
;; Blurring

;; Blurs the given specification configuration by removing all receptionists in the unobserved
;; environment interface with the wrong spawn flag
(define (aps#-blur-config config internals-to-blur)
  (redex-let aps# ([[any_addr any_receptionists any_exp any_state-defs any_out-coms] config])
    (term [any_addr
           ,(remove-duplicates
             (csa#-blur-internal-addresses (term any_receptionists) internals-to-blur))
           any_exp
           any_state-defs
           any_out-coms])))

(module+ test
  (test-equal? "aps#-blur-config"
    (aps#-blur-config (aps#-make-no-transition-config
                       `((init-addr  0 Nat)
                         (spawn-addr 1 OLD Nat)
                         (spawn-addr 1 NEW Nat)
                         (spawn-addr 2 NEW Nat)
                         (blurred-spawn-addr 1 Nat)
                         (spawn-addr 2 OLD Nat))
                       `())
                      (list (term (spawn-addr 1 NEW Nat))))
    (aps#-make-no-transition-config
     `((init-addr  0 Nat)
       (spawn-addr 1 OLD Nat)
       (blurred-spawn-addr 1 Nat)
       (spawn-addr 2 NEW Nat)
       (spawn-addr 2 OLD Nat))
     `())))

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
;; 2. Renames all precise external addresses such that the first one is address 0, then address 1,
;; then address 2, and so on.
;;
;; 3. Also sorts the escaped addresses in the impl config and the receptionists in the spec config
;; (not strictly necessary to ensure a bounded state space, but provides a form of symmetry
;; reduction).
(define (canonicalize-pair impl-config spec-config)
  (match-define (list aged-impl-config aged-spec-config)
    (age-addresses (list impl-config spec-config)))
  (define commitment-map (aps#-config-commitment-map spec-config))
  (define substitutions
    (for/list ([entry commitment-map]
               [new-number (build-list (length commitment-map) values)])
      (redex-let aps# ([((obs-ext natural _) _ ...) entry])
        (list (term natural) new-number))))
  (match-define (list renamed-impl-config renamed-spec-config)
    (term (rename-external-addresses ,(list aged-impl-config aged-spec-config) ,@substitutions)))
  (list renamed-impl-config
        (aps#-sort-receptionists renamed-spec-config)
        substitutions))

(module+ test
  (test-equal? "canonicalize 1"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((init-addr 0 Nat)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))))))
     (term
      ((init-addr 0 Nat)
       ()
       (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))
       ((define-state (A a b c) [* -> () (goto A)]))
       (((obs-ext 25 Nat)) ((obs-ext 42 Nat)) ((obs-ext 10 Nat))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0 Nat)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))))))
      ((init-addr 0 Nat)
       ()
       (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))
       ((define-state (A a b c) [* -> () (goto A)]))
       (((obs-ext 0 Nat)) ((obs-ext 1 Nat)) ((obs-ext 2 Nat))))
      ([25 0] [42 1] [10 2]))))

  (test-equal? "canonicalize 2"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((spawn-addr 0 OLD Nat)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (obs-ext 10 Nat) (obs-ext 42 Nat) (obs-ext 25 Nat))))))
     (term
      ((spawn-addr 0 OLD Nat)
       ()
       (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))
       ((define-state (A c b a) [* -> () (goto A)]))
       (((obs-ext 25 Nat)) ((obs-ext 42 Nat)) ((obs-ext 10 Nat))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((spawn-addr 0 OLD Nat)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 2 Nat) (obs-ext 1 Nat) (obs-ext 0 Nat))))))
      ((spawn-addr 0 OLD Nat)
       ()
       (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))
       ((define-state (A c b a) [* -> () (goto A)]))
       (((obs-ext 0 Nat)) ((obs-ext 1 Nat)) ((obs-ext 2 Nat))))
      ([25 0] [42 1] [10 2])))))

;; Given a term, changes all spawn addresses of the form (spawn-addr _ NEW _) to (spawn-addr _ OLD _),
;; to ensure that spawned addresses in the next handler are fresh.
(define (age-addresses some-term)
  (match some-term
    [(and addr `(spawn-addr ,loc ,flag ,type))
     (if (equal? flag 'NEW)
         (term (spawn-addr ,loc OLD ,type))
         addr)]
    [(list terms ...) (map age-addresses terms)]
    [_ some-term]))

;; Renames precise external addresses in the given term by replacing its number natural_old with
;; natural_new, according to the given substitution
(define-metafunction aps#
  rename-external-addresses : any [natural_old natural_new] ... -> any
  [(rename-external-addresses (obs-ext natural_old any_type) _ ... [natural_old natural_new] _ ...)
   (obs-ext natural_new any_type)]
  [(rename-external-addresses (obs-ext natural_old any_type) _ ...)
   (obs-ext natural_old any_type)]
  [(rename-external-addresses (any ...) any_substs ...)
   ((rename-external-addresses any any_substs ...) ...)]
  [(rename-external-addresses any _ ...) any])

(module+ test
  (check-equal?
   (term (rename-external-addresses
          (some-term (obs-ext 2 Nat) (another-term (obs-ext 5 Nat)) (obs-ext 13 Nat))
          [2 1] [13 2] [5 3]))
   (term (some-term (obs-ext 1 Nat) (another-term (obs-ext 3 Nat)) (obs-ext 2 Nat)))))

;; Returns a spec config identical to the given one except that the the receptionist list is sorted
(define (aps#-sort-receptionists config)
  (redex-let aps# ([(any_addr any_receptionists any_rest ...) config])
    (term (any_addr ,(sort (term any_receptionists) sexp<?) any_rest ...))))

(define (try-rename-address rename-map addr)
  (redex-let aps# ([(obs-ext natural any_type) addr])
    (match (findf (lambda (entry) (equal? (first entry) (term natural))) rename-map)
      [#f #f]
      [(list _ new) (term (obs-ext ,new any_type))])))

(module+ test
  (test-equal? "try-rename-address success"
    (try-rename-address (term ([1 3] [2 4])) (term (obs-ext 2 Nat)))
    (term (obs-ext 4 Nat)))
  (test-false "try-rename-address failure"
    (try-rename-address (term ([1 3] [2 4])) (term (obs-ext 5 Nat)))))

;; Performs the reverse of the mapping indicated by the given address rename map on the given address
(define (reverse-rename-address rename-map addr)
    (redex-let aps# ([(obs-ext natural any_type) addr])
    (match (findf (lambda (entry) (equal? (second entry) (term natural))) rename-map)
      [#f (error 'reverse-rename-address "Unable to find entry for ~s in ~s" addr rename-map)]
      [(list prev _) (term (obs-ext ,prev any_type))])))

(module+ test
  (test-equal? "try-rename-address success"
    (reverse-rename-address (term ([1 3] [2 4])) (term (obs-ext 4 Nat)))
    (term (obs-ext 2 Nat))))

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (aps#-unknown-address? a)
  (equal? a 'UNKNOWN))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-s# defs goto receptionists out-coms)
  (term ((init-addr 0 Nat) ,receptionists ,goto ,defs ,out-coms)))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define (spec-config-without-state-defs config)
  (redex-let aps# ([(any_addr any_rec any_goto _ any_out) config])
    (term (any_addr any_rec any_goto any_out))))
