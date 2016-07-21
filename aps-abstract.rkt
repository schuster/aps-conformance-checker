#lang racket

;; Defines the abstract APS configurations and helper functions

(provide
 aps#
 α-tuple
 ;; subst-n/aps#
 ;; aps#-current-transitions
 ;; aps#-null-transition
 aps#-steps-for-trigger
 step-spec-with-goto
 aps#-spec-from-commitment-entry
 aps#-spec-from-fsm-and-commitments
 aps#-resolve-outputs
 aps#-config-instances
 aps#-config-only-instance-address
 aps#-config-only-instance-state
 aps#-config-commitment-map
 ;; aps#-transition-pattern
 ;; aps#-transition-expression
 aps#-commitment-entry-address
 aps#-goto-state
 aps#-instance-state
 aps#-instance-arguments
 aps#-relevant-external-addrs
 aps#-external-addresses
 canonicalize-tuple
 aps#-config-has-commitment?

 ;; Testing helpers
 make-Σ#
 single-instance-address

 ;; Debugging helpers
 spec-config-without-state-defs)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "aps.rkt"
 "csa.rkt"
 "csa-abstract.rkt")

(module+ test
  (require rackunit))

(define-union-language aps-eval-with-csa#
  aps-eval csa#)

;; TODO: add sharps to all of these forms to distinguish from concrete forms
(define-extended-language aps#
  aps-eval-with-csa#
  (Σ ((z ...) O))
  (z ((S-hat ...) e-hat σ))
  (σ a# null)
  (u .... a#) ; TODO: make this a#ext instead; allowing saves of spawned addresses is future work
  (v-hat a# a-hat)
  ;; (O ((a#ext (po boolean) ...) ...))
  (O ((a#ext (m po) ...) ...))
  (m single many) ; m for "multiplicity"
  )

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

(define (α-tuple initial-prog-config
                 initial-spec-config
                 init-obs-receptionists
                 init-unobs-receptionists
                 max-depth)
  ;;    (where (a_internal ...) ((actor-address αn) ...))
  (define internal-addresses (csa-config-internal-addresses initial-prog-config))
  (list
   (α-config initial-prog-config internal-addresses max-depth)
   (aps#-α-Σ initial-spec-config internal-addresses)
   (α-typed-receptionist-list init-obs-receptionists)
   (α-typed-receptionist-list init-unobs-receptionists)))

;; TODO: change the language and conformance so that I don't have to do this little initial
;; abstraction
(define (aps#-α-Σ spec-config internal-addresses)
  ;; Doing a redex-let here just to add a codomain contract
  ;; TODO: figure out how to get redex-let to report its line number if this fails
  (redex-let aps# ([Σ (term (aps#-α-Σ/mf ,spec-config ,internal-addresses))])
             (term Σ)))

;; TODO: rewrite this and put a better contract on here once we put #'s on all the APS# non-terminals
(define-metafunction aps#
  aps#-α-Σ/mf : any (a ...) -> any
  [(aps#-α-Σ/mf a (a_internal ...))
   (α-e a (a_internal ...) 0)]
  [(aps#-α-Σ/mf (any ...) (a ...))
   ((aps#-α-Σ/mf any (a ...)) ...)]
  [(aps#-α-Σ/mf any _) any])

(module+ test
  (check-equal?
   (aps#-α-Σ (term (((((define-state (A x) (* -> (goto A x))))
                      (goto A (addr 1))
                      (addr 0)))
                    ()))
             (term ((addr 0))))
   (term (((((define-state (A x) (* -> (goto A x))))
            (goto A (obs-ext 1))
            (init-addr 0)))
          ()))))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps# : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps# e-hat) e-hat]
  [(subst-n/aps# e-hat (x v-hat) any_rest ...)
   (subst-n/aps# (subst/aps# e-hat x v-hat) any_rest ...)])

;; TODO: write tests for this substitution

(define-metafunction aps#
  subst/aps# : e-hat x v-hat -> e-hat
  [(subst/aps# (goto s u ...) x v-hat)
   (goto s (subst/aps#/u u x v-hat) ...)]
  [(subst/aps# (with-outputs ([u po] ...) e-hat) x v-hat)
   ;; TODO: figure out if I need to substitute into the patterns, for spawned specs
   (with-outputs ([(subst/aps#/u u x v-hat) po] ...) (subst/aps# e-hat x v-hat))]
  ;; TODO: write the other clauses
  )

(define-metafunction aps#
  subst/aps#/u : u x v-hat -> u
  [(subst/aps#/u x x v-hat) v-hat]
  [(subst/aps#/u x_2 x v-hat) x_2]
  [(subst/aps#/u a# x v-hat) a#])

(define-metafunction aps#
  subst/aps#/po : po x v-hat -> po
  [(subst/aps#/po x x v-hat) v-hat]
  [(subst/aps#/po x_2 x v-hat) x_2]
  [(subst/aps#/po a x v-hat) a]
  [(subst/aps#/po a-hat x v-hat) a-hat]
  ;; TODO: do this for variants, records, and or
  [(subst/aps#/po * x v-hat) *])

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

;; Non-deterministically evaluates the given specification configuration with either a single trigger
;; step, or no step, when given the specified trigger from the program on the actor with the given
;; address, returning a list of the possible stepped specification configuration
(define (aps#-steps-for-trigger spec-config from-observer? trigger)
  (match (aps#-config-instances spec-config)
    [(list) (list spec-config)]
    [(list instance)
     ;; evaluate all ways the trigger can hit a transition
     (define stepped-configs
       (filter values
        (for/list ([transition (aps#-instance-transitions instance)])
                 ;; TODO: refactor this; need better definition of triggers, patterns, etc.
          (match (match-program-trigger-to-spec-trigger from-observer? trigger (aps#-instance-address instance) (aps#-transition-trigger transition))
            [#f #f]
            [(list bindings ...)
             (define exp-subst (term (subst-n/aps# ,(aps#-transition-body transition) ,@bindings)))
             (update-config-with-effects
              (observe-addresses-from-subst spec-config bindings)
              (aps#-eval exp-subst))]))))
     (remove-duplicates stepped-configs)]))

(module+ test
  (test-equal? "Multiple copies of output commitments are merged"
               (aps#-steps-for-trigger
                (make-Σ# (term ((define-state (A r) [* -> (with-outputs ([r *]) (goto A r))])))
                         (term (goto A (obs-ext 0)))
                         (term (((obs-ext 0) (single *)))))
                #t
                (term (external-receive ,single-instance-address (* Nat))))
               (list
                (make-Σ# (term ((define-state (A r) [* -> (with-outputs ([r *]) (goto A r))])))
                         (term (goto A (obs-ext 0)))
                         (term (((obs-ext 0) (many *))))))))

(define (aps#-eval exp)
  (term (aps#-eval/mf ,exp)))

(define-metafunction aps#
  aps#-eval/mf : e-hat -> [(goto s a#ext ...) ([a#ext po] ...) (z ...)]
  [(aps#-eval/mf (goto s a#ext ...))
   ((goto s a#ext ...) () ())]
  [(aps#-eval/mf (with-outputs ([a#ext_1 po_1] any_rest ...) e-hat))
   ((goto s a#ext ...) ([a#ext_1 po_1] any_outputs ...) (any_spawns ...))
   ;; TODO: this is an example of a where clause I expect to always succeed. I should write a macro on
   ;; reduction-relation that enforces that
   (where [(goto s a#ext ...) (any_outputs ...) (any_spawns ...)]
          (aps#-eval/mf (with-outputs (any_rest ...) e-hat)))]
  [(aps#-eval/mf (with-outputs () e-hat))
   (aps#-eval/mf e-hat)])

;; TODO: test the eval function

;; Adds all addresses matched in the substitution (i.e. the set of bindings) as keys in the output
;; commitment map
;;
;; TODO: figure out whether some of these outputs will have been there already (I think I will have a
;; theorem that says they will not be)
(define (observe-addresses-from-subst spec-config the-subst)
  (redex-let aps# ([(any_instances (any_map-entries ...)) spec-config]
                   [([_ a#ext] ...) the-subst])
             (term (any_instances (any_map-entries ... (a#ext) ...)))))

;; NOTE: this may return #f if we have to add copies of existing commitments
(define (update-config-with-effects spec-config eval-result)
  (redex-let* aps#
              ([((z) O)  spec-config]
               [((goto s a#ext_arg ...) ([a#ext_com po] ...) (z_new ...))  eval-result]
               [((S-hat ...) _ σ) (term z)]
               [z_updated (term ((S-hat ...) (goto s a#ext_arg ...) σ))])
              (match (term (add-commitments O [a#ext_com po] ...))
                [#f #f]
                [new-O (term ((z_updated z_new ...) ,new-O))])))

(define (step-spec-with-goto spec-config goto-exp)
  (redex-let aps# ([((((S-hat ...) _ σ)) O) spec-config])
             (term ((((S-hat ...) ,goto-exp σ)) O))))

;; NOTE: assumes an entry has been added already (e.g. with observe-addresses-from-subst)
(define-metafunction aps#
  add-commitments : O [a#ext po] ... -> O or #f
  [(add-commitments O) O]
  ;; TODO: remove this clause when we support multiple copies of commitments
  [(add-commitments (any_1 ... (a#ext any_2 ... (_ po)    any_3 ...) any_4 ...)
                    [a#ext po] any_rest ...)
   (add-commitments (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)
                    any_rest ...)]
  [(add-commitments (any_1 ... (a#ext any_coms ...)             any_2 ...) [a#ext po] any_rest ...)
   (add-commitments (any_1 ... (a#ext any_coms ... (single po)) any_2 ...) any_rest ...)])

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

(define (match-program-trigger-to-spec-trigger from-observer? trigger instance-address pattern)
  (match
      (judgment-holds
       (trigger-matches-trigger-pattern ,from-observer?
                                        ,trigger
                                        ,instance-address
                                        ,pattern
                                        any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-program-trigger-to-spec-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (trigger-matches-trigger-pattern I I I I O)
  #:contract (trigger-matches-trigger-pattern boolean trigger# σ ε ([x v#] ...))

  [-----------------------------------------------------------
   (trigger-matches-trigger-pattern _ (timeout _) _ unobs ())]

  [----------------------------------------------------------------------
   (trigger-matches-trigger-pattern _ (internal-receive _ _) _ unobs ())]

  [-----------------------------------------------------------------------
   (trigger-matches-trigger-pattern #f (external-receive _ _) _ unobs ())]

  [(side-condition ,(not (equal? (term a#_1) (term a#_2))))
   -----------------------------------------------------------------------------
   (trigger-matches-trigger-pattern #t (external-receive a#_1 _) a#_2 unobs ())]

  [(aps#-match/j v# p any_bindings)
   --------------------------------------------------------------------------------
   (trigger-matches-trigger-pattern #t (external-receive a# v#) a# p any_bindings)])

(module+ test
  (check-equal?
   (match-program-trigger-to-spec-trigger #f '(timeout (init-addr 0)) '(init-addr 0) 'unobs)
   null)

  (check-equal?
   (match-program-trigger-to-spec-trigger #f '(external-receive (init-addr 0) (* Nat)) '(init-addr 0) 'unobs)
   null)

  (check-false
   (match-program-trigger-to-spec-trigger #t '(external-receive (init-addr 0) (* Nat)) '(init-addr 0) 'unobs))

  (check-equal?
   (match-program-trigger-to-spec-trigger #t '(external-receive (init-addr 0) (obs-ext 1)) '(init-addr 0) 'x)
   (list '(x (obs-ext 1))))

  (check-false
   (match-program-trigger-to-spec-trigger #f '(internal-receive (init-addr 0) (* Nat)) '(init-addr 0) 'x))

  (check-false
   (match-program-trigger-to-spec-trigger #t '(external-receive (init-addr 0) (* Nat)) '(init-addr 0) 'x))

  (check-equal?
   (match-program-trigger-to-spec-trigger #f '(internal-receive (init-addr 0) (* Nat)) '(init-addr 0) 'unobs)
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

(define (aps#-matches-po? value pattern)
  (judgment-holds (aps#-matches-po?/j ,value ,pattern)))

(define-judgment-form aps#
  #:mode (aps#-matches-po?/j I I)
  #:contract (aps#-matches-po?/j v# po)

  [-----
   (aps#-matches-po?/j _ *)]

  ;; TODO: make this rule match not quite everything
  [----
   (aps#-matches-po?/j _ x)]

  ;; TODO: self
  [----
   (aps#-matches-po?/j t t)]
  [----
   (aps#-matches-po?/j (* t) t)]

  [(aps#-matches-po?/j v# po) ...
   ------
   (aps#-matches-po?/j (variant t v# ..._n) (variant t po ..._n))]

  [(aps#-matches-po?/j (* τ) po) ...
   -----
   (aps#-matches-po?/j (* (Union _ ... [t τ ..._n] _ ...)) (variant t po ..._n))]

  [(aps#-matches-po?/j v# po)
   ------------------------------------------------------------
   (aps#-matches-po?/j v# (or _ ... po _ ...))])

(module+ test
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
  (check-true (aps#-matches-po? (term (variant A)) (term (or (variant A) (variant B)))))
  (check-true (aps#-matches-po? (term (variant B)) (term (or (variant A) (variant B)))))
  (check-false (aps#-matches-po? (term (variant C)) (term (or (variant A) (variant B))))))

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; Returns a pair of the specification config after having resolved all of the given outputs (removing
;; output commitments as necessary) and a list of the satisfied commitments, or #f if a resolution of
;; these outputs is not possible
;;
;; NOTE: for now, assuming there is at most one way to satisfy the given config's commitments with
;; these outputs, which may not necessarily be true
(define (aps#-resolve-outputs spec-config outputs)
  ;; TODO: deal with loop output

  (let loop ([commitment-map (aps#-config-commitment-map spec-config)]
             [satisfied-commitments null]
             [remaining-outputs outputs])
    (match remaining-outputs
      [(list)
       (list (term (,(aps#-config-instances spec-config) ,commitment-map)) satisfied-commitments)]
      [(list output remaining-outputs ...)
       (define address (csa#-output-address output))
       (match (commitments-for-address commitment-map address)
         ;; we can ignore outputs on unobserved addresses
         [#f (loop commitment-map satisfied-commitments remaining-outputs)]
         [commitments
          (define patterns (map commitment-pattern commitments))
          (match (findf (curry aps#-matches-po? (csa#-output-message output)) patterns)
            [#f #f]
            [pat
             (loop (aps#-remove-commitment-pattern commitment-map address pat)
                   ;; TODO: decide what "satisfied commitments" really means in the presence of
                   ;; many-of commitments
                   (append satisfied-commitments (list (term (,address ,pat))))
                   remaining-outputs)])])])))

(module+ test
  (check-false
   (aps#-resolve-outputs
    (term (() (((obs-ext 1)))))
    (term (((obs-ext 1) (* Nat))))))
  (check-equal?
   (aps#-resolve-outputs
    (term (() (((obs-ext 1) (single *)))))
    (term (((obs-ext 1) (* Nat)))))
   (term ((() (((obs-ext 1))))
          (((obs-ext 1) *)))))
  (check-equal?
   (aps#-resolve-outputs
    (term (() (((obs-ext 1) (single *) (single (record))))))
    (term (((obs-ext 1) (* Nat)))))
   (term ((() (((obs-ext 1) (single (record)))))
          (((obs-ext 1) *)))))
  (check-equal?
   (aps#-resolve-outputs
    (term (() (((obs-ext 1) (many *) (single (record))))))
    (term (((obs-ext 1) (* Nat)))))
   (term ((() (((obs-ext 1) (many *) (single (record)))))
          (((obs-ext 1) *)))))

  ;; TODO: test aps#-resolve-outputs for (along with normal cases):
  ;; * spec that observes an address but neither saves it nor has output commtiments for it
  ;; * POV unobservables
  ;; * wildcard unobservables
  )

(define (aps#-remove-commitment-pattern commitment-map address pat)
  (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

(define-metafunction aps#
  remove-commitment-pattern/mf : O a#ext po -> O
  [(remove-commitment-pattern/mf (any_1 ... (a#ext any_2 ... (single po) any_3 ...) any_4 ...)
                                 a#ext
                                 po)
   (any_1 ... (a#ext any_2 ... any_3 ...) any_4 ...)]
  [(remove-commitment-pattern/mf (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)
                                 a#ext
                                 po)
   (any_1 ... (a#ext any_2 ... (many po) any_3 ...) any_4 ...)])

(module+ test
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

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (aps#-spec-from-fsm-and-commitments instance commitments)
  (redex-let* aps# ([z instance]
                    [O commitments]
                    [Σ (term ((z) O))])
              (term Σ)))

(module+ test)

(define (aps#-spec-from-commitment-entry entry)
  (redex-let aps# ([(a#ext any_1 ...) entry])
             (term (() ((a#ext any_1 ...))))))

(module+ test
  (check-equal?
   (aps#-spec-from-commitment-entry (term ((obs-ext 0) (single *) (single (record [a *] [b *])))))
   (term (() (((obs-ext 0) (single *) (single (record [a *] [b *]))))))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-config-instances config)
  (term (config-instances/mf ,config)))

(define-metafunction aps#
  config-instances/mf : Σ -> (z ...)
  [(config-instances/mf ((z ...) _)) (z ...)])

(define (aps#-config-commitment-map config)
  (term (config-commitment-map/mf ,config)))

(define (aps#-config-only-instance-state config)
  (match (aps#-config-instances config)
    [(list instance) (aps#-instance-state instance)]
    [_ (error 'aps#-config-only-instance-state "More than one instance in config ~s" config)]))

(define (aps#-config-only-instance-address config)
  (match (aps#-config-instances config)
    [(list instance) (aps#-instance-address instance)]
    [_ (error 'aps#-config-only-instance-address "More than one instance in config ~s" config)]))

(define-metafunction aps#
  config-commitment-map/mf : Σ -> O
  [(config-commitment-map/mf (_ O)) O])

;; TODO: test these

(define (aps#-transition-pattern transition)
  (redex-let aps# ([(ε -> _) transition])
    (term ε)))

(define (aps#-transition-expression transition)
  (redex-let aps# ([(_ -> e-hat) transition])
    (term e-hat)))

(module+ test
  ;; TODO: rewrite these tests
  ;; (define transition (term [(tuple a b) -> (with-outputs ([a *]) (goto S))]))

  ;; (check-equal? (aps#-transition-pattern transition) (term (tuple a b)))
  ;; (check-equal? (aps#-transition-expression transition) (term (with-outputs ([a *]) (goto S))))
  ;; (define transition2 (term [unobs -> (with-outputs ([x *]) (goto S2))]))
  ;; (check-equal? (aps#-transition-pattern transition2) (term unobs))
  )

(define (aps#-goto-state goto-exp)
  (redex-let aps# ([(goto s _ ...) goto-exp])
             (term s)))

(module+ test
  (check-equal? (aps#-goto-state (term (goto A))) (term A))
  (check-equal? (aps#-goto-state (term (goto B (obs-ext 2) (obs-ext 1)))) (term B)))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (commitments-for-address commitment-map address)
  (term (commitments-for-address/mf ,commitment-map ,address)))

(define-metafunction aps#
  commitments-for-address/mf : O a#ext -> ((m po) ...) or #f
  [(commitments-for-address/mf (_ ... (a#ext (m po) ...) _ ...) a#ext) ((m po) ...)]
  [(commitments-for-address/mf _ _) #f])

(module+ test
  (define test-O
    (term (((obs-ext 1) (single *) (many (record)))
           ((obs-ext 2) (single (variant True)) (single (variant False))))))
  (check-equal?
   (commitments-for-address
    test-O
    (term (obs-ext 1)))
   (term ((single *) (many (record)))))
  (check-equal?
   (commitments-for-address
    test-O
    (term (obs-ext 2)))
   (term ((single (variant True)) (single (variant False)))))
  (check-false
   (commitments-for-address
    test-O
    (term (obs-ext 3)))))

(define (commitment-pattern commitment)
  (redex-let aps# ([(m po) commitment]) (term po)))

(define (aps#-instance-address z)
  (redex-let aps# ([(_ _ σ) z])
    (term σ)))

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
  (check-equal?
   (aps#-instance-state (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                               (goto Always (* (Addr Nat)) (obs-ext 1))
                               null)))
   (term Always))

  (check-equal?
   (aps#-instance-arguments (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                                   (goto Always (* (Addr Nat)) (obs-ext 1))
                                   null)))
   (term ((* (Addr Nat)) (obs-ext 1)))))

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
                             (goto Always (obs-ext 1) (obs-ext 2))
                             null))]
                 [z_2 (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                             (goto Always (obs-ext 1) (obs-ext 3))
                             null))]
                 [O (term (((obs-ext 1)) ((obs-ext 3)) ((obs-ext 4))))]
                 [Σ (term ((z_1 z_2) O))])
                (term Σ)))
   (term ((obs-ext 1) (obs-ext 2) (obs-ext 3) (obs-ext 4)))))

;; Returns all external addresses of the given term (with possible duplicates)
(define (aps#-external-addresses t)
  (term (external-addresses/mf ,t)))

(define-metafunction aps#
  external-addresses/mf : any -> (a#ext ...)
  [(external-addresses/mf a#ext) (a#ext)]
  [(external-addresses/mf (any ...))
   (a#ext ... ...)
   (where ((a#ext ...) ...) ((external-addresses/mf any) ...))]
  [(external-addresses/mf any) ()])

(module+ test
  (check-equal? (aps#-external-addresses (term (goto A))) null)
  (check-equal?
   (aps#-external-addresses (term (goto B (obs-ext 4) (obs-ext 5))))
   (term ((obs-ext 4) (obs-ext 5))))
    (check-equal?
     (aps#-external-addresses
      (term [* -> (with-outputs ([(obs-ext 3) *]) (goto C (obs-ext 7) (* (Addr Nat))))]))
     (term ((obs-ext 3) (obs-ext 7) (* (Addr Nat))))))

(define (aps#-transition-trigger transition)
  (redex-let aps# ([(ε -> _) transition])
             (term ε)))

(define (aps#-transition-body transition)
  (redex-let aps# ([(_ -> e-hat) transition])
             (term e-hat)))

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization (i.e. renaming)

;; TODO: move this up to main.rkt

;; Given a program config/spec config pair, rename the precise internal and external addresses in them
;; such that the first one in each set starts at 0, then the next is 1, then 2, etc.
;;
;; TODO: do the internal address part
(define (canonicalize-tuple tuple)
  (term (canonicalize-tuple/mf ,tuple)))

(define-metafunction aps#
  canonicalize-tuple/mf : (K# Σ (typed-a#int ...) (typed-a#int ...)) -> (K# Σ (typed-a#int ...) (typed-a#int ...))
  [(canonicalize-tuple/mf (K# Σ (typed-a#int_obs ...) (typed-a#int_unobs ...)))
   ((rename-addresses K# [natural_old natural_new] ...)
    (rename-addresses Σ [natural_old natural_new] ...)
    (rename-addresses (typed-a#int_obs ...) [natural_old natural_new] ...)
    (rename-addresses (typed-a#int_unobs ...) [natural_old natural_new] ...))
   (where ((z ...) ((a#ext_com _ ...) ...)) Σ)
   (where ((obs-ext natural_old) ...)
          ,(remove-duplicates (append* (term (a#ext_com ...))
                                       (term ((instance-arguments/mf z) ...)))))
   (where (natural_new ...) ,(build-list (length (term (natural_old ...))) values))])

(module+ test
  (check-equal?
   (canonicalize-tuple
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))))))
      (((((define-state (A a b c) [* -> (goto A)]))
         (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
         (init-addr 0)))
       ())
      ((init-addr 0 Nat))
      ())))
   (term
    (,(make-single-actor-abstract-config
       (term ((init-addr 0)
              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
               (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))))))
     (((((define-state (A a b c) [* -> (goto A)]))
        (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
        (init-addr 0)))
      ())
     ((init-addr 0 Nat))
     ())))

  (check-equal?
   (canonicalize-tuple
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0)
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 10) (obs-ext 42) (obs-ext 25))))))
      (((((define-state (A c b a) [* -> (goto A)]))
         (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
         (init-addr 0)))
       ())
      ()
      ())))
   (term
    (,(make-single-actor-abstract-config
       (term ((init-addr 0)
              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
               (goto A (obs-ext 2) (obs-ext 1) (obs-ext 0))))))
     (((((define-state (A c b a) [* -> (goto A)]))
        (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
        (init-addr 0)))
      ())
     ()
     ())))

  (check-equal?
   (canonicalize-tuple
    (term
     (,(make-single-actor-abstract-config
        (term ((init-addr 0)
               (((define-state (A) (m) (goto A)))
                (goto A)))))
      (() (((obs-ext 101) (single *))))
      ()
      ())))
   (term
    (,(make-single-actor-abstract-config
       (term ((init-addr 0)
              (((define-state (A) (m) (goto A)))
               (goto A)))))
     (() (((obs-ext 0) (single *))))
     ()
     ())))

  ;; TODO: test for an address that appears more than once in the spec (e.g. twice as a spec param)

  ;; TODO: write a test for a program config with recently spawned actors
  )

(define-metafunction aps#
  rename-addresses : any [natural_old natural_new] ... -> any
  [(rename-addresses (obs-ext natural_old) _ ... [natural_old natural_new] _ ...)
   (obs-ext natural_new)]
  [(rename-addresses (obs-ext natural_old) _ ...)
   (obs-ext natural_old)]
  [(rename-addresses (any ...) any_substs ...)
   ((rename-addresses any any_substs ...) ...)]
  [(rename-addresses any _ ...) any])

(module+ test
  (check-equal?
   (term (rename-addresses (some-term (obs-ext 2) (another-term (obs-ext 5)) (obs-ext 13))
                           [2 1] [13 2] [5 3]))
   (term (some-term (obs-ext 1) (another-term (obs-ext 3)) (obs-ext 2))))

  ;; TODO: rename spawned actors, too
  )

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (aps#-config-has-commitment? config commitment)
  (judgment-holds (config-has-commitment?/j ,config ,commitment)))

(define-judgment-form aps#
  #:mode (config-has-commitment?/j I I)
  #:contract (config-has-commitment?/j Σ [a#ext po])
  [(where (_ ... (a#ext _ ... (_ po) _ ...) _ ... ) O)
   ---------------------------------------------------
   (config-has-commitment?/j (_ O) [a#ext po])])

(module+ test
  (define commitment-map-test-config
    (term (()
           (((obs-ext 1) (single *))
            ((obs-ext 2))
            ((obs-ext 3) (single (record)) (single (variant True)))))))
  (check-not-false (redex-match aps# Σ commitment-map-test-config))

  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 1) *])))
  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) (record)])))
  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) (variant True)])))

  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 2) *])))
  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 1) (record)])))
  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) *]))))

;; ---------------------------------------------------------------------------------------------------
;; Testing Helpers

(define (make-Σ# defs goto out-coms)
  (term (((,defs ,goto (init-addr 0))) ,out-coms)))

(define single-instance-address (term (init-addr 0)))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define (spec-config-without-state-defs config)
  (redex-let aps# ([((((S-hat ...) e-hat σ) ...) O) config])
             (term (((e-hat σ) ...) O))))
