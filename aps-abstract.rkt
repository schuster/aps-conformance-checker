#lang racket

;; Abstract semantic domains for APS (specification language), and associated functions

(provide
 ;; Required by conformance checker
 ;; TODO: consider having this one return the address or #f
 aps#-config-only-instance-address
 aps#-unknown-address?
 aps#-config-receptionists
 aps#-matching-steps
 aps#-resolve-outputs
 aps#-abstract-config
 split-spec
 aps#-blur-config
 canonicalize-pair

 ;; Required by conformance checker for blurring
 aps#-relevant-external-addrs

 ;; Testing helpers
 make-Σ#
 aps#-no-transition-instance

 ;; Debugging helpers
 spec-config-without-state-defs)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "aps.rkt"
 "csa.rkt"
 "csa-abstract.rkt")

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt"))

(define-union-language aps-eval-with-csa#
  aps-eval csa#)

;; TODO: remove the idea of a full config; just have individual instances

;; TODO: add sharps to all of these forms to distinguish from concrete forms
(define-extended-language aps#
  aps-eval-with-csa#
  (Σ ((z ...) (a#int_unobs-receptionists ...) O))
  (z ((S-hat ...) e-hat σ))
  (σ a# UNKNOWN)
  (u .... a#ext)
  (v-hat a#)
  ;; (O ((a#ext (po boolean) ...) ...))
  (O ((a#ext (m po) ...) ...))
  (m single many) ; m for "multiplicity"
  )

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

(define (aps#-abstract-config spec-config internal-addresses)
  ;; Doing a redex-let here just to add a codomain contract
  (redex-let aps# ([Σ (term (aps#-abstract-config/mf ,spec-config ,internal-addresses))])
             (term Σ)))

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
   (aps#-abstract-config (term (((((define-state (A x) (* -> (goto A x))))
                      (goto A (addr 1 Nat))
                      (addr 0 Nat)))
                    ()
                    ()))
             (term ((addr 0 Nat))))
   (term (((((define-state (A x) (* -> (goto A x))))
            (goto A (obs-ext 1 Nat))
            (init-addr 0 Nat)))
          ()
          ())))

  (test-equal? "Abstraction check for addresses whose types don't match"
   (aps#-abstract-config (term (((((define-state (A)))
                      (goto A)
                      (addr 0 (Union [B]))))
                    ()
                    ()))
             (term ((addr 0 (Union [C])))))
   (term (((((define-state (A)))
                      (goto A)
                      (init-addr 0 (Union [B]))))
          ()
          ()))))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps# : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps# e-hat) e-hat]
  [(subst-n/aps# e-hat (x v-hat) any_rest ...)
   (subst-n/aps# (subst/aps# e-hat x v-hat) any_rest ...)])

(define-metafunction aps#
  subst/aps# : e-hat x v-hat -> e-hat
  [(subst/aps# (goto s u ...) x v-hat)
   (goto s (subst/aps#/u u x v-hat) ...)]
  [(subst/aps# (with-outputs ([u po] ...) e-hat) x v-hat)
   (with-outputs ([(subst/aps#/u u x v-hat) (subst/aps#/po po x v-hat)] ...)
     (subst/aps# e-hat x v-hat))]
  [(subst/aps# (spawn-spec ((goto s u ...) S-hat ...) e-hat) x v-hat)
   (spawn-spec ((subst/aps# (goto s u ...) x v-hat)
                (subst/aps#/S-hat S-hat x v-hat) ...)
               (subst/aps# e-hat x v-hat))])

(define-metafunction aps#
  subst/aps#/u : u x v-hat -> u
  [(subst/aps#/u x x v-hat) v-hat]
  [(subst/aps#/u x_2 x v-hat) x_2]
  [(subst/aps#/u a# x v-hat) a#])

(define-metafunction aps#
  subst/aps#/po : po x v-hat -> po
  [(subst/aps#/po * x v-hat) *]
  [(subst/aps#/po (spawn-spec any_goto any_s-defs ...) self _)
   (spawn-spec any_goto any_s-defs ...)]
  [(subst/aps#/po (spawn-spec (goto s u ...) S-hat ...) x v-hat)
   (spawn-spec (goto s (subst/aps#/u u x v-hat) ...)
               (subst/aps#/S-hat S-hat x v-hat) ...)]
  [(subst/aps#/po self self a#int) a#int]
  [(subst/aps#/po self _ _) self]
  [(subst/aps#/po (variant t po ...) x v-hat)
   (variant t (subst/aps#/po po x v-hat) ...)]
  [(subst/aps#/po (record t [l po] ...) x v-hat)
   (record [l (subst/aps#/po po x v-hat)] ...)])

(define-metafunction aps#
  subst/aps#/S-hat : S-hat x v-hat -> S-hat
  [(subst/aps#/S-hat (define-state (s any_1 ... x any_2 ...) any_trans ...) x v-hat)
   (define-state (s any_1 ... x any_2 ...) any_trans ...)]
  [(subst/aps#/S-hat (define-state (s x_s ...) any_trans ...) x v-hat)
   (define-state (s x_s ...) (subst/aps#/trans any_trans x v-hat) ...)])

(define-metafunction aps#
  subst/aps#/trans : (ε -> e-hat) x v-hat -> (ε -> e-hat)
  [(subst/aps#/trans (p -> e-hat) x v-hat)
   (p -> e-hat)
   (judgment-holds (pattern-binds-var p x))]
  [(subst/aps#/trans (ε -> e-hat) x v-hat)
   (ε -> (subst/aps# e-hat x v-hat))])

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

;; Returns the syntax for each transition of the FSM in the spec config (assumes there is at most one
;; FSM)
(define (aps#-instance-transitions instance)
  (term (aps#-instance-transitions/mf ,instance)))

;; TODO: deal with the case where the pattern variables shadow the state variables
(define-metafunction aps#
  aps#-instance-transitions/mf : z -> ((ε -> e-hat) ...)
  [(aps#-instance-transitions/mf
    ((_ ... (define-state (s x ...) (ε -> e-hat) ...) _ ...) (goto s v-hat ...) _))
   ((ε -> (subst-n/aps# e-hat (x v-hat) ...)) ...
    ;; Note that we include the "null"/no-step transition
    (unobs -> (goto s v-hat ...)))])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; (define (aps#-transition-observed? trans)
;;   (term (aps#-transition-observed?/mf ,trans)))

;; (define-metafunction aps#
;;   aps#-transition-observed?/mf : (ε -> e-hat) -> boolean
;;   [(aps#-transition-observed?/mf (p _ _)) #t]
;;   [(aps#-transition-observed?/mf _) #f])

;; (module+ test
;;   (check-false (aps#-transition-observed? (term [unobs -> (goto S x y)])))
;;   (check-true (aps#-transition-observed? (term [(variant Cons y) -> (goto S x y)])))
;;   (check-true (aps#-transition-observed? (term [* -> (goto S x y)]))))

;; Σ bool trigger -> ([Σ (Σ_spawn ...)] ...)
;;
;; Returns all spec configs that can possibly be reached in one step by transitioning from the given
;; trigger, also returning spec configs spawned during that transition
(define (aps#-matching-steps spec-config from-observer? trigger)
  (match (aps#-config-instances spec-config)
    [(list instance)
     (remove-duplicates
      (filter
       values
       (map (lambda (t) (attempt-transition spec-config t from-observer? trigger))
            (aps#-instance-transitions instance))))]))

(module+ test
  (test-equal? "Null step is possible"
               (aps#-matching-steps
                (make-Σ# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                #f
                (term (timeout ,(single-instance-address 'Nat))))
               (list
                (list (make-Σ# (term ((define-state (A))))
                         (term (goto A))
                         (term ())
                         (term ()))
                      null)))

  (test-equal? "Multiple copies of output commitments are merged"
               (aps#-matching-steps
                (make-Σ# (term ((define-state (A r) [* -> (with-outputs ([r *]) (goto A r))])))
                         (term (goto A (obs-ext 0 Nat)))
                         null
                         (term (((obs-ext 0 Nat) (single *)))))
                #t
                (term (external-receive ,(single-instance-address 'Nat) (* Nat))))
               (list
                (list
                 (make-Σ# (term ((define-state (A r) [* -> (with-outputs ([r *]) (goto A r))])))
                          (term (goto A (obs-ext 0 Nat)))
                          null
                          (term (((obs-ext 0 Nat) (many *)))))
                 null))))

;; Returns the config updated by running the given transition, if it can be taken from the given
;; trigger, along with all configs spawned in the transition, or #f if the transition is not possible
;; from this trigger
(define (attempt-transition config transition from-observer? trigger)
  (define instance (first (aps#-config-instances config)))
  (match (match-trigger from-observer?
                        trigger
                        (aps#-instance-address instance)
                        (aps#-transition-trigger transition))
    [#f #f]
    [(list bindings ...)
     (define body-with-bindings (term (subst-n/aps# ,(aps#-transition-body transition) ,@bindings)))
     (match-define (list new-goto commitments spawn-infos) (aps#-eval body-with-bindings))
     (define updated-commitment-map
       (term
        (add-commitments
         ,(observe-addresses-from-subst
           (aps#-config-commitment-map config) bindings)
         ,@commitments)))
     (define stepped-current-config
       (term (((,(aps#-instance-state-defs instance)
                ,new-goto
                ,(aps#-instance-address instance)))
              ,(aps#-config-receptionists config)
              ,updated-commitment-map)))
     (fork-configs stepped-current-config spawn-infos)]))

;; exp -> goto-exp ([a po] ...) (<S ..., e, σ> ...)
;;
;; Evaluates the given spec expression for an instance at the given address and returns the results (a
;; goto exp, the new output commitments, the address of this instance, and spawn-info for any spawned
;; specs
(define (aps#-eval exp)
  (term (aps#-eval/mf ,exp)))

(define-metafunction aps#
  aps#-eval/mf : e-hat -> [(goto s a#ext ...) ([a#ext po] ...) (((S-hat ...) e-hat σ) ...)]
  [(aps#-eval/mf (goto s a#ext ...))
   ((goto s a#ext ...) () ())]
  [(aps#-eval/mf (with-outputs ([a#ext_1 po_1] any_rest ...) e-hat))
   ((goto s a#ext ...) ([a#ext_1 po_1] any_outputs ...) (any_spawns ...))
   (where [(goto s a#ext ...) (any_outputs ...) (any_spawns ...)]
          (aps#-eval/mf (with-outputs (any_rest ...) e-hat)))]
  [(aps#-eval/mf (with-outputs () e-hat))
   (aps#-eval/mf e-hat)]
  [(aps#-eval/mf (spawn-spec ((goto s a#ext ...) S-hat ...) e-hat))
   [any_goto (any_outputs ...) ([(S-hat ...) (goto s a#ext ...) UNKNOWN] any_spawns ...)]
   (where [any_goto (any_outputs ...) (any_spawns ...)]
          (aps#-eval/mf e-hat))])

;; Σ (((S-hat ...) e-hat σ) ...) -> Σ (Σ ...)
;;
;; Given the current configuration and the info needed to spawn new configs, splits information from
;; the current configuration off to form the new configurations
(define (fork-configs current-config spawn-infos)
  (redex-let aps# ([((z) any_receptionists O) current-config])
    (define-values (commitment-map spawned-configs)
      (for/fold ([current-commitment-map (term O)]
                 [spawned-configs null])
                ([spawn-info spawn-infos])
        (match-define (list state-defs goto address) spawn-info)
        (match-define (list remaining-map spawned-map)
          (fork-commitment-map current-commitment-map (externals-in (list state-defs goto))))
        (define new-instance (term (,state-defs ,goto ,address)))
        (values remaining-map
                (cons (term ((,new-instance) any_receptionists ,spawned-map))
                      spawned-configs))))
    (list (term ((z) any_receptionists ,commitment-map)) spawned-configs)))

(module+ test
  (test-equal? "Degenerate fork config case"
               (fork-configs (term (([((define-state (A))) (goto A) UNKNOWN]) () ())) null)
               (list (term (([((define-state (A))) (goto A) UNKNOWN]) () ())) null))

  (test-equal? "Basic fork config case"
    (fork-configs (term (([((define-state (A))) (goto A) UNKNOWN]) () ([(obs-ext 1 Nat) (single *)] [(obs-ext 2 Nat) (single (record))])))
                  (term ([((define-state (B r))) (goto B (obs-ext 2 Nat)) null])))
    (list (term (([((define-state (A))) (goto A) UNKNOWN]) () ([(obs-ext 1 Nat) (single *)])))
          (list (term (([((define-state (B r))) (goto B (obs-ext 2 Nat)) null]) () ([(obs-ext 2 Nat) (single (record))])))))))

(define (fork-commitment-map commitment-map addresses)
  (term (fork-commitment-map/mf ,commitment-map () ,addresses)))

;; Takes all entries from the first O that match an address in the given list and moves it to the
;; second O
(define-metafunction aps#
  fork-commitment-map/mf : O O (a#ext ...) -> (O O)
  [(fork-commitment-map/mf O_current O_new ())
   (O_current O_new)]
  [(fork-commitment-map/mf O_current (any_fork-entries ...) (a#ext any_rest ...))
   (fork-commitment-map/mf O_updated (any_fork-entries ... (a#ext any_pulled ...)) (any_rest ...))
   (where (O_updated (any_pulled ...)) (O-pull O_current a#ext))])

(define-metafunction aps#
  O-pull : O a#ext -> (O ([m po] ...))
  [(O-pull (any_1 ... (a#ext any_com ...) any_2 ...) a#ext)
   ((any_1 ... any_2 ...) (any_com ...))]
  [(O-pull O a#ext) (O ())])

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
  add-commitments : O [a#ext po] ... -> O
  [(add-commitments O) O]
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
(define (match-trigger from-observer? trigger instance-address pattern)
  (match
      (judgment-holds
       (match-trigger/j ,from-observer? ,trigger ,instance-address ,pattern any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (match-trigger/j I I I I O)
  #:contract (match-trigger/j boolean trigger# σ ε ([x v#] ...))

  [-----------------------------------------------------------
   (match-trigger/j _ (timeout _) _ unobs ())]

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
   (match-trigger #f '(timeout (init-addr 0 Nat)) '(init-addr 0 Nat) 'unobs)
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
  #:contract (aps#-matches-po?/j v# σ po σ (((S-hat ...) e-hat σ)  ...) (a#int ...))

  [-----
   (aps#-matches-po?/j v# σ * σ () ,(internals-in (term v#)))]

  [----
   (aps#-matches-po?/j a#int
                       σ
                       (spawn-spec e-hat S-hat ...)
                       σ
                       (((S-hat ...) e-hat a#int))
                       ())]

  [----
   (aps#-matches-po?/j a#int a#int self a#int () ())]

  [----
   (aps#-matches-po?/j a#int UNKNOWN self a#int () ())]

  [(aps#-list-matches-po?/j ((v# po) ...) σ any_self-addr any_spawns any_receptionists)
   ------
   (aps#-matches-po?/j (variant t v# ..._n)
                       σ
                       (variant t po ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  [(aps#-list-matches-po?/j (((* τ) po) ...) σ any_self-addr any_spawns any_receptionists)
   -----
   (aps#-matches-po?/j (* (Union _ ... [t τ ..._n] _ ...))
                       σ
                       (variant t po ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  ;; Records

  [(aps#-list-matches-po?/j ((v# po) ...) σ any_self-addr any_spawns any_receptionists)
   ------
   (aps#-matches-po?/j (record [l v#] ..._n)
                       σ
                       (record [l po] ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)]

  [(aps#-list-matches-po?/j (((* τ) po) ...) σ any_self-addr any_spawns any_receptionists)
   -----
   (aps#-matches-po?/j (* (Record [l τ] ..._n))
                       σ
                       (record [l po] ..._n)
                       any_self-addr
                       any_spawns
                       any_receptionists)])

(define-judgment-form aps#
  #:mode (aps#-list-matches-po?/j I I O O O)
  #:contract (aps#-list-matches-po?/j ((v# po) ...) σ σ (((S-hat ...) e-hat σ) ...) (a#int ...))

  [---------
   (aps#-list-matches-po?/j () any_addr any_addr () ())]

  [(aps#-matches-po?/j v# σ po any_addr1 (any_spawn-infos1 ...) (any_receptionists1 ...))
   (aps#-list-matches-po?/j (any_rest ...)
                            any_addr1
                            any_addr2
                            (any_spawn-infos2 ...)
                            (any_receptionists2 ...))
   ---------
   (aps#-list-matches-po?/j ((v# po) any_rest ...)
                            σ
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
  (check-false
   (aps#-match-po '(variant A (* Nat) (init-addr 2 Nat)) '(init-addr 1 Nat) '(variant A * self)))
  (test-equal? "Spawn match po test"
   (aps#-match-po '(spawn-addr 'foo NEW Nat)
                  'UNKNOWN
                  '(spawn-spec (goto B) (define-state (B))))
   (list 'UNKNOWN
         '([((define-state (B))) (goto B) (spawn-addr 'foo NEW Nat)])
         '()))
  (test-equal? "Full match po test"
   (aps#-match-po '(variant A (spawn-addr 'foo NEW Nat) (init-addr 2 Nat))
                  'UNKNOWN
                  '(variant A (spawn-spec (goto B) (define-state (B))) self))
   (list '(init-addr 2 Nat)
         '([((define-state (B))) (goto B) (spawn-addr 'foo NEW Nat)])
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

;; Σ ((a#ext v#) ...) ->  Σ (Σ ...) ([a po] ...)
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
             [self-address (aps#-instance-address (first (aps#-config-instances spec-config)))]
             [spawn-infos null]
             [added-unobs-receptionists null]
             [satisfied-commitments null]
             [remaining-outputs outputs])
    (match remaining-outputs
      [(list)
       (define old-instance (first (aps#-config-instances spec-config)))
       (define updated-instance
         (term (,(aps#-instance-state-defs old-instance)
                ,(aps#-instance-exp old-instance)
                ,self-address)))
       (define updated-config
         (term ((,updated-instance)
                ,(merge-receptionists (aps#-config-receptionists spec-config)
                                      added-unobs-receptionists)
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
                   ;; TODO: decide what "satisfied commitments" really means in the presence of
                   ;; many-of commitments
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
  (define dummy-instance (term (((define-state (DummyState))) (goto DummyState) UNKNOWN)))
  (test-false "resolve test 1"
   (aps#-resolve-outputs
    (term ((,dummy-instance) () (((obs-ext 1 Nat)))))
    (term (((obs-ext 1 Nat) (* Nat))))))
  (test-equal? "resolve test 2"
   (aps#-resolve-outputs
    (term ((,dummy-instance) ()  (((obs-ext 1 Nat) (single *)))))
    (term (((obs-ext 1 Nat) (* Nat)))))
   (term (((,dummy-instance) () (((obs-ext 1 Nat))))
          ()
          (((obs-ext 1 Nat) *)))))
  (test-equal? "resolve test 3"
   (aps#-resolve-outputs
    (term ((,dummy-instance) ()  (((obs-ext 1 Nat) (single *) (single (record))))))
    (term (((obs-ext 1 Nat) (* Nat)))))
   (term (((,dummy-instance) () (((obs-ext 1 Nat) (single (record)))))
          ()
          (((obs-ext 1 Nat) *)))))
  (test-equal? "resolve test 4"
   (aps#-resolve-outputs
    (term ((,dummy-instance) () (((obs-ext 1 Nat) (many *) (single (record))))))
    (term (((obs-ext 1 Nat) (* Nat)))))
   (term (((,dummy-instance) () (((obs-ext 1 Nat) (many *) (single (record)))))
          ()
          (((obs-ext 1 Nat) *)))))

  ;; TODO: test aps#-resolve-outputs for (along with normal cases):
  ;; * spec that observes an address but neither saves it nor has output commtiments for it
  ;; * POV unobservables
  ;; * wildcard unobservables
  )

(define (aps#-remove-commitment-pattern commitment-map address pat)
  (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

(define-metafunction aps#
  remove-commitment-pattern/mf : O a#ext po -> O
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

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-config-instances config)
  (term (config-instances/mf ,config)))

(define-metafunction aps#
  config-instances/mf : Σ -> (z ...)
  [(config-instances/mf ((z ...) _ _)) (z ...)])

(define (aps#-config-receptionists config)
  (term (config-receptionists/mf ,config)))

(define-metafunction aps#
  config-receptionists/mf : Σ -> (a#int ...)
  [(config-receptionists/mf (_ (a#int ...) _)) (a#int ...)])

(define (aps#-config-commitment-map config)
  (term (config-commitment-map/mf ,config)))

(define (aps#-config-only-instance-address config)
  (match (aps#-config-instances config)
    [(list instance) (aps#-instance-address instance)]
    [_ (error 'aps#-config-only-instance-address "More than one instance in config ~s" config)]))

(define-metafunction aps#
  config-commitment-map/mf : Σ -> O
  [(config-commitment-map/mf (_ _ O)) O])

(define (aps#-transition-pattern transition)
  (redex-let aps# ([(ε -> _) transition])
    (term ε)))

(define (aps#-transition-expression transition)
  (redex-let aps# ([(_ -> e-hat) transition])
    (term e-hat)))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (commitments-for-address commitment-map address)
  (term (commitments-for-address/mf ,commitment-map ,address)))

(define-metafunction aps#
  commitments-for-address/mf : O a#ext -> ((m po) ...) or #f
  [(commitments-for-address/mf (_ ... (a#ext_1 (m po) ...) _ ...)
                               a#ext_2)
   ((m po) ...)
   (judgment-holds (same-external-address-without-type? a#ext_1 a#ext_2))]
  [(commitments-for-address/mf _ _) #f])

(module+ test
  (define test-O
    (term (((obs-ext 1 Nat) (single *) (many (record)))
           ((obs-ext 2 Nat) (single (variant True)) (single (variant False))))))
  (check-equal?
   (commitments-for-address
    test-O
    (term (obs-ext 1 Nat)))
   (term ((single *) (many (record)))))
  (check-equal?
   (commitments-for-address
    test-O
    (term (obs-ext 2 Nat)))
   (term ((single (variant True)) (single (variant False)))))
  (check-false
   (commitments-for-address
    test-O
    (term (obs-ext 3 Nat)))))

(define (commitment-pattern commitment)
  (redex-let aps# ([(m po) commitment]) (term po)))

(define (aps#-instance-address z)
  (redex-let aps# ([(_ _ σ) z])
             (term σ)))

(define (aps#-instance-state-defs z)
  (redex-let aps# ([(any_state-defs _ _) z])
             (term any_state-defs)))

(define (aps#-instance-exp z)
  (redex-let aps# ([(_ any_exp _) z])
             (term any_exp)))

(define (aps#-instance-state z)
  (term (instance-state/mf ,z)))

(define-metafunction aps#
  instance-state/mf : z -> s
  [(instance-state/mf (_ (goto s _ ...) _)) s])

(define (aps#-instance-arguments z)
  (term (instance-arguments/mf ,z)))

(define-metafunction aps#
  instance-arguments/mf : z -> (a#ext ...)
  [(instance-arguments/mf (_ (goto _ u ...) _)) (u ...)])

(module+ test
  (test-equal? "instate-state check 1"
   (aps#-instance-state (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                               (goto Always (* (Addr Nat)) (obs-ext 1 Nat))
                               UNKNOWN)))
   (term Always))

  (test-equal? "instate-state check 2"
   (aps#-instance-arguments (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                                   (goto Always (* (Addr Nat)) (obs-ext 1 Nat))
                                   UNKNOWN)))
   (term ((* (Addr Nat)) (obs-ext 1 Nat)))))

(define (aps#-relevant-external-addrs Σ)
  (term (relevant-external-addrs/mf ,Σ)))

(define-metafunction aps#
  relevant-external-addrs/mf : Σ -> (a#ext ...)
  [(relevant-external-addrs/mf Σ)
   ,(remove-duplicates (term (any_args ... ... any_commitment-addr ...)))
   (where (any_z ...) (config-instances/mf Σ))
   (where ((any_args ...) ...) ((instance-arguments/mf any_z) ...))
   (where ((any_commitment-addr _ ...) ...) (config-commitment-map/mf Σ))])

(module+ test
  (check-equal?
   (aps#-relevant-external-addrs
    (redex-let* aps#
                ([z_1 (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                             (goto Always (obs-ext 1 Nat) (obs-ext 2 Nat))
                             UNKNOWN))]
                 [z_2 (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                             (goto Always (obs-ext 1 Nat) (obs-ext 3 Nat))
                             UNKNOWN))]
                 [O (term (((obs-ext 1 Nat)) ((obs-ext 3 Nat)) ((obs-ext 4 Nat))))]
                 [Σ (term ((z_1 z_2) () O))])
                (term Σ)))
   (term ((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))))

(define (aps#-transition-trigger transition)
  (redex-let aps# ([(ε -> _) transition])
             (term ε)))

(define (aps#-transition-body transition)
  (redex-let aps# ([(_ -> e-hat) transition])
             (term e-hat)))

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
  (define instance (first (aps#-config-instances config)))
  ;; A commitment map entry is "relevant" if it is used as a state argument
  (define-values (relevant-entries irrelevant-entries)
    (partition (lambda (entry)
                 (member (aps#-commitment-entry-address entry)
                         (aps#-instance-arguments instance)))
               (aps#-config-commitment-map config)))
  (define commitment-only-configs
    (map (curryr aps#-spec-from-commitment-entry
                 (aps#-config-only-instance-address config)
                 receptionists)
         irrelevant-entries))
  (cons (term ((,instance) ,receptionists ,relevant-entries))
        commitment-only-configs))

(module+ test
  (define simple-instance-for-split-test
    (term
     (((define-state (A x)
         [* -> (goto A x)]))
      (goto A (obs-ext 0 Nat))
      (init-addr 0 Nat))))

  (test-not-false "simple instance" (redex-match aps# z simple-instance-for-split-test))

  (test-equal? "split spec with one FSM gets same spec"
   (split-spec (term ((,simple-instance-for-split-test) () ())))
   (list (term ((,simple-instance-for-split-test) () ()))))

  (test-equal? "split with one related commit"
   (split-spec (term ((,simple-instance-for-split-test) () (((obs-ext 0 Nat) (single *))))))
   (list (term ((,simple-instance-for-split-test) () (((obs-ext 0 Nat) (single *)))))))

  (test-same-items? "split with unrelated commit"
   (split-spec (term ((,simple-instance-for-split-test) () (((obs-ext 1 Nat) (single *))))))
   (list (term ((,simple-instance-for-split-test) () ()))
         (term ((,aps#-no-transition-instance) ((init-addr 0 Nat)) (((obs-ext 1 Nat) (single *))))))))

;; A specification instance with an UNKNOWN address and an FSM with no transitions. Used for
;; specifications where only the commitments are important.
(define aps#-no-transition-instance
  (term [((define-state (DummySpecFsmState))) (goto DummySpecFsmState) UNKNOWN]))

;; Creates a spec config with a transition-less FSM and a commitment map with just the given
;; entry. The receptionists for the unobserved environment will be the given list plus the given FSM
;; address if it is not UNKONWN.
(define (aps#-spec-from-commitment-entry entry fsm-addr receptionists)
  (define all-receptionists
    (remove-duplicates
     (append receptionists
             (if (equal? fsm-addr 'UNKNOWN) '() (list fsm-addr)))))
  (term ((,aps#-no-transition-instance) ,all-receptionists ,(list entry))))

(module+ test
  (check-equal?
   (aps#-spec-from-commitment-entry (term ((obs-ext 0 Nat) (single *) (single (record [a *] [b *]))))  'UNKNOWN null)
   (term ((,aps#-no-transition-instance) () (((obs-ext 0 Nat) (single *) (single (record [a *] [b *])))))))

  (test-equal? "Commitment entry spec should also include old FSM address as unobs receptionist"
    (aps#-spec-from-commitment-entry (term ((obs-ext 0 Nat) (single *) (single (record [a *] [b *]))))
                                     '(init-addr 0 Nat)
                                     null)
    (term ((,aps#-no-transition-instance)
           ((init-addr 0 Nat))
           (((obs-ext 0 Nat) (single *) (single (record [a *] [b *]))))))))

;; ---------------------------------------------------------------------------------------------------
;; Blurring

;; Blurs the given specification configuration by removing all receptionists in the unobserved
;; environment interface with the wrong spawn flag
(define (aps#-blur-config config internals-to-blur)
  (redex-let aps# ([[([any_state-defs any_exp any_addr]) any_receptionists any_out-coms] config])
    (term [([any_state-defs any_exp any_addr])
           ,(remove-duplicates
             (csa#-blur-internal-addresses (term any_receptionists) internals-to-blur))
           any_out-coms])))

(module+ test
  (test-equal? "aps#-blur-config"
    (aps#-blur-config (term ((,aps#-no-transition-instance)
                             ((init-addr  0 Nat)
                              (spawn-addr 1 OLD Nat)
                              (spawn-addr 1 NEW Nat)
                              (spawn-addr 2 NEW Nat)
                              (blurred-spawn-addr 1 Nat)
                              (spawn-addr 2 OLD Nat))
                             ()))
                      (list (term (spawn-addr 1 NEW Nat))))
    (term ((,aps#-no-transition-instance)
           ((init-addr  0 Nat)
            (spawn-addr 1 OLD Nat)
            (blurred-spawn-addr 1 Nat)
            (spawn-addr 2 NEW Nat)
            (spawn-addr 2 OLD Nat))
           ()))))

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
;; conformance), canonical form. Specifically:
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
        (aps#-sort-receptionists renamed-spec-config)))

(module+ test
  (test-equal? "canonicalize 1"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((init-addr 0 Nat)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))))))
     (term
      (((((define-state (A a b c) [* -> (goto A)]))
         (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))
         (init-addr 0 Nat)))
       ()
       (((obs-ext 25 Nat)) ((obs-ext 42 Nat)) ((obs-ext 10 Nat))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0 Nat)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))))))
      (((((define-state (A a b c) [* -> (goto A)]))
         (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))
         (init-addr 0 Nat)))
       ()
       (((obs-ext 0 Nat)) ((obs-ext 1 Nat)) ((obs-ext 2 Nat)))))))

  (test-equal? "canonicalize 2"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((spawn-addr 0 OLD Nat)
             (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
              (goto A (obs-ext 10 Nat) (obs-ext 42 Nat) (obs-ext 25 Nat))))))
     (term
      (((((define-state (A c b a) [* -> (goto A)]))
         (goto A (obs-ext 25 Nat) (obs-ext 42 Nat) (obs-ext 10 Nat))
         (spawn-addr 0 OLD Nat)))
       ()
       (((obs-ext 25 Nat)) ((obs-ext 42 Nat)) ((obs-ext 10 Nat))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((spawn-addr 0 OLD Nat)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 2 Nat) (obs-ext 1 Nat) (obs-ext 0 Nat))))))
      (((((define-state (A c b a) [* -> (goto A)]))
         (goto A (obs-ext 0 Nat) (obs-ext 1 Nat) (obs-ext 2 Nat))
         (spawn-addr 0 OLD Nat)))
       ()
       (((obs-ext 0 Nat)) ((obs-ext 1 Nat)) ((obs-ext 2 Nat)))))))

  (test-equal? "canonicalize 3"
    (canonicalize-pair
     (make-single-actor-abstract-config
      (term ((spawn-addr 0 NEW Nat)
             (((define-state (A) (m) (goto A)))
              (goto A)))))
     (term
      (() () (((obs-ext 101 Nat) (single *))))))
    (term
     (,(make-single-actor-abstract-config
        (term ((spawn-addr 0 OLD Nat)
               (((define-state (A) (m) (goto A)))
                (goto A)))))
      (() () (((obs-ext 0 Nat) (single *))))))))

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
  (redex-let aps# ([(any_instances any_receptionists any_com) config])
    (term (any_instances ,(sort (term any_receptionists) sexp<?) any_com))))

(define (sexp<? a b)
  (string<? (sexp->string a) (sexp->string b)))

(define (sexp->string s)
  (define port (open-output-string))
  (fprintf port "~s" s)
  (get-output-string port))

(module+ test
  (check-true (sexp<? null 'a))
  (check-true (sexp<? 'a 'b))
  (check-false (sexp<? 'b 'a))
  (check-false (sexp<? 'a null)))

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (aps#-unknown-address? a)
  (equal? a 'UNKNOWN))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-Σ# defs goto receptionists out-coms)
  (term (((,defs ,goto (init-addr 0 Nat))) ,receptionists ,out-coms)))

(define (single-instance-address type) (term (init-addr 0 ,type)))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define (spec-config-without-state-defs config)
  (redex-let aps# ([((((S-hat ...) e-hat σ) ...) any_rec O) config])
             (term (((e-hat σ) ...) any_rec O))))
