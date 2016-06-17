#lang racket

;; Defines the abstract APS configurations and helper functions

(provide
 aps#
 aps#-α-Σ
 ;; subst-n/aps#
 ;; aps#-current-transitions
 ;; aps#-null-transition
 aps#-step-for-trigger
 aps#-matches-po?
 step-spec-with-goto
 aps#-spec-from-commitment-entry
 aps#-spec-from-fsm-and-commitments
 aps#-resolve-outputs
 aps#-config-instances
 aps#-config-only-instance-state
 aps#-config-commitment-map
 aps#-config-commitments
 ;; aps#-transition-pattern
 ;; aps#-transition-expression
 aps#-commitment-address
 aps#-commitment-pattern
 aps#-commitment-entry-address
 aps#-goto-state
 aps#-instance-state
 aps#-instance-arguments
 aps#-relevant-external-addrs
 aps#-external-addresses
 canonicalize-tuple
 aps#-config-has-commitment?
 no-duplicate-commitments?
 unique-minimal-config)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "aps.rkt"
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
  (O ((a#ext po ...) ...)))

;; TODO: change the language and conformance so that I don't have to do this little initial
;; abstraction
(define (aps#-α-Σ spec-config)
  ;; Doing a redex-let here just to add a codomain contract
  ;; TODO: figure out how to get redex-let to report its line number if this fails
  (redex-let aps# ([Σ (term (aps#-α-Σ/mf ,spec-config))])
             (term Σ)))

(define-metafunction aps#
  aps#-α-Σ/mf : any -> any
  ;; TODO: deal with multiple initial actors; remove this hack; figure out how to differentiate
  ;; initially between internal and external addresses
  [(aps#-α-Σ/mf (addr 0)) SINGLE-ACTOR-ADDR]
  [(aps#-α-Σ/mf (addr natural))
   (obs-ext natural)]
  [(aps#-α-Σ/mf (any ...))
   ((aps#-α-Σ/mf any) ...)]
  [(aps#-α-Σ/mf any) any])

(module+ test
  (check-equal?
   (aps#-α-Σ (term (((((define-state (A x) (* -> (goto A x))))
                      (goto A (addr 1))
                      (addr 0)))
                    ())))
   (term (((((define-state (A x) (* -> (goto A x))))
            (goto A (obs-ext 1))
            SINGLE-ACTOR-ADDR))
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
;; step, or no stop, when given the specified trigger from the program, returning a list of the
;; possible stepped specification configuration
(define (aps#-step-for-trigger spec-config trigger)
  (match (aps#-config-instances spec-config)
    [(list) (list spec-config)]
    [(list instance)
     ;; evaluate all ways the trigger can hit a transition
     (define stepped-configs
       (filter values
        (for/list ([transition (aps#-instance-transitions instance)])
          (match (match-program-trigger-to-event-trigger trigger (aps#-transition-trigger transition))
            [#f #f]
            [(list bindings ...)
             (define exp-subst (term (subst-n/aps# ,(aps#-transition-body transition) ,@bindings)))
             (update-config-with-effects
              (observe-addresses-from-subst spec-config bindings)
              (aps#-eval exp-subst))]))))
     (remove-duplicates stepped-configs)]))

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

(define (observe-addresses-from-subst spec-config the-subst)
  (redex-let aps# ([(any_instances (any_map-entries ...)) spec-config]
                   [([_ a#ext] ...) the-subst])
             (term (any_instances (any_map-entries ... (a#ext) ...)))))

(define (update-config-with-effects spec-config eval-result)
  (redex-let* aps#
              ([((z) O)  spec-config]
               [((goto s a#ext_arg ...) ([a#ext_com po] ...) (z_new ...))  eval-result]
               [((S-hat ...) _ σ) (term z)]
               [z_updated (term ((S-hat ...) (goto s a#ext_arg ...) σ))])
              (term ((z_updated z_new ...) (add-commitments O [a#ext_com po] ...)))))

(define (step-spec-with-goto spec-config goto-exp)
  (redex-let aps# ([((((S-hat ...) _ σ)) O) spec-config])
             (term ((((S-hat ...) ,goto-exp σ)) O))))

;; NOTE: assumes an entry has been added already (e.g. with observe-addresses-from-subst)
(define-metafunction aps#
  add-commitments : O [a#ext po] ... -> O
  [(add-commitments O) O]
  [(add-commitments (any_1 ... (a#ext po_rest ...) any_2 ...) [a#ext po] any_rest ...)
   (add-commitments (any_1 ... (a#ext po_rest ... po) any_2 ...) any_rest ...)])

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

(define (match-program-trigger-to-event-trigger trigger trigger-pattern)
  (match
      (judgment-holds
       (trigger-matches-trigger-pattern ,trigger ,trigger-pattern any_bindings)
       any_bindings)
    [(list) #f]
    [(list binding-list) binding-list]
    [(list _ _ _ ...)
     (error 'match-program-trigger-to-event-trigger
            "Match resulted in multiple possible substitutions")]))

(define-judgment-form aps#
  #:mode (trigger-matches-trigger-pattern I I O)
  #:contract (trigger-matches-trigger-pattern trigger# ε ([x v#] ...))

  [---------------------------------------------------
   (trigger-matches-trigger-pattern timeout unobs ())]

  [---------------------------------------------------------------
   (trigger-matches-trigger-pattern (internal-message _) unobs ())]

  [----------------------------------------------------------------------------
   (trigger-matches-trigger-pattern (external-unobservable-message _) unobs ())]

  [(aps#-match/j v# p any_bindings)
   ----------------------------------------------------------------------------------
   (trigger-matches-trigger-pattern (external-observable-message v#) p any_bindings)])

(define-judgment-form aps#
  #:mode (aps#-match/j I I O)
  #:contract (aps#-match/j v# p ((x v#) ...))

  [-------------------
   (aps#-match/j _ * ())]

  ;; TODO: make a version of this that only matches external addresses, for the APS matching
  [-------------------
   (aps#-match/j v# x ([x v#]))]

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

;; TODO: rewrite these tests
;; (module+ test
;;   (check-equal? (aps#-match (term (* Nat)) (term *))
;;                 (list (term ())))
;;   (check-equal? (aps#-match (term (received-addr Always ADDR-HOLE 0 MOST-RECENT)) (term x))
;;                 (list (term ([x (received-addr Always ADDR-HOLE 0 MOST-RECENT)]))))
;;   (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a 'b)))
;;                 (list (term ())))
;;   ;; (displayln (redex-match csa# t (term 'a)))
;;   ;; (displayln (redex-match csa# v# (term 'a)))
;;   ;; (displayln (redex-match csa# x (term item)))
;;   ;; (displayln (build-derivations (aps#-match/j 'a item ())))
;;   (check-equal? (aps#-match (term 'a) (term item))
;;                 (list (term ([item 'a]))))
;;   (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a item)))
;;                 (list (term ([item 'b]))))
;;   (check-equal? (aps#-match (term (* (Tuple 'a 'b))) (term (tuple x 'b)))
;;                 (list (term ([x (* 'a)])))))

;; TODO: write tests for the above match

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

;; TODO: add tests for the match predicate

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; Returns the specification config after having resolved all of the given outputs (removing output
;; commitments as necessary), or #f if not possible
;;
;; NOTE: for now, assuming there is at most one way to satisfy commitments with these outputs, which
;; may not necessarily be true
(define (aps#-resolve-outputs spec-config outputs)
  ;; TODO: deal with loop output

  (let loop ([commitment-map (aps#-config-commitment-map spec-config)]
             [remaining-outputs outputs])
    (match remaining-outputs
      [(list) (term (,(aps#-config-instances spec-config) ,commitment-map))]
      [(list output remaining-outputs ...)
       (define address (csa#-output-address output))
       (match (commitment-patterns-for-address commitment-map address)
         ;; we can ignore outputs on unobserved addresses
         [#f (loop commitment-map remaining-outputs)]
         [patterns
          (match (findf (curry aps#-matches-po? (csa#-output-message output)) patterns)
            [#f #f]
            [pat (loop (aps#-remove-commitment-pattern commitment-map address pat)
                       remaining-outputs)])])])))

(module+ test
  (check-false
   (aps#-resolve-outputs
    (term (() (((obs-ext 1)))))
    (term (((obs-ext 1) (* Nat))))))
  (check-equal?
   (aps#-resolve-outputs
    (term (() (((obs-ext 1) *))))
    (term (((obs-ext 1) (* Nat)))))
   (term (() (((obs-ext 1))))))
  (check-equal?
   (aps#-resolve-outputs
    (term (() (((obs-ext 1) * (record)))))
    (term (((obs-ext 1) (* Nat)))))
   (term (() (((obs-ext 1) (record))))))

  ;; TODO: test aps#-resolve-outputs for (along with normal cases):
  ;; * spec that observes an address but neither saves it nor has output commtiments for it
  ;; * POV unobservables
  ;; * wildcard unobservables
  )

(define (aps#-remove-commitment-pattern commitment-map address pat)
  (term (remove-commitment-pattern/mf ,commitment-map ,address ,pat)))

(define-metafunction aps#
  remove-commitment-pattern/mf : O a#ext po -> O
  [(remove-commitment-pattern/mf (any_1 ... (a#ext po_all ...) any_2 ...) a#ext po)
   (any_1 ... (a#ext po_rest ...) any_2 ...)
   (where (po_rest ...) ,(remove (term po) (term (po_all ...))))])

(module+ test
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) *))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1)))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) * *))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1) *))))
  (check-equal?
   (aps#-remove-commitment-pattern
    (term (((obs-ext 1) * (record) *) ((obs-ext 2) *))) (term (obs-ext 1)) (term *))
   (term (((obs-ext 1) (record) *) ((obs-ext 2) *)))))

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (aps#-spec-from-fsm-and-commitments instance commitments)
  (redex-let* aps# ([z instance]
                    [O commitments]
                    [Σ (term ((z) O))])
              (term Σ)))

(module+ test)

(define (aps#-spec-from-commitment-entry entry)
  (redex-let aps# ([(a#ext po ...) entry])
             (term (() ((a#ext po ...))))))

(module+ test
  (check-equal?
   (aps#-spec-from-commitment-entry (term ((obs-ext 0) * (record [a *] [b *]))))
   (term (() (((obs-ext 0) * (record [a *] [b *])))))))

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
  (check-equal? (aps#-goto-state (term (goto B (SINGLE-ACTOR-ADDR SINGLE-ACTOR-ADDR)))) (term B)))

(define (aps#-commitment-address commitment)
  (term (commitment-address/mf ,commitment)))

(define-metafunction aps#
  commitment-address/mf : [a#ext po] -> a#ext
  [(commitment-address/mf [a#ext po]) a#ext])

(define (aps#-commitment-pattern commitment)
  (redex-let aps# ([[_ po] commitment])
    (term po)))

(module+ test
  (define commitment (term [(* (Addr Nat)) (variant Null *)]))
  (check-equal? (aps#-commitment-address commitment) (term (* (Addr Nat))))
  (check-equal? (aps#-commitment-pattern commitment) (term (variant Null *))))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (aps#-config-commitments config)
  (aps#-commitment-map-commitments (aps#-config-commitment-map config)))

(define (aps#-commitment-map-commitments commitment-map)
  (term (commitment-map-commitments/mf ,commitment-map)))

(define-metafunction aps#
  commitment-map-commitments/mf : O -> ([a#ext po] ...)
  [(commitment-map-commitments/mf ()) ()]
  [(commitment-map-commitments/mf ((a#ext po ...) any_rest ...))
   ((a#ext po) ... any_results ...)
   (where (any_results ...) (commitment-map-commitments/mf (any_rest ...)))])

(module+ test
  (check-equal?
   (aps#-commitment-map-commitments (term (((obs-ext 1) *) ((obs-ext 2) (record) (variant A)))))
   (term (((obs-ext 1) *)
          ((obs-ext 2) (record))
          ((obs-ext 2) (variant A))))))

(define (commitment-patterns-for-address commitment-map address)
  (term (commitment-patterns-for-address/mf ,commitment-map ,address)))

(define-metafunction aps#
  commitment-patterns-for-address/mf : O a#ext -> (po ...) or #f
  [(commitment-patterns-for-address/mf (_ ... (a#ext po ...) _ ...) a#ext) (po ...)]
  [(commitment-patterns-for-address/mf _ _) #f])

(module+ test
  (check-equal?
   (commitment-patterns-for-address
    (term (((obs-ext 1) * (record)) ((obs-ext 2) (variant True) (variant False))))
    (term (obs-ext 1)))
   (term (* (record))))
  (check-equal?
   (commitment-patterns-for-address
    (term (((obs-ext 1) * (record)) ((obs-ext 2) (variant True) (variant False))))
    (term (obs-ext 2)))
   (term ((variant True) (variant False))))
  (check-false
   (commitment-patterns-for-address
    (term (((obs-ext 1) * (record)) ((obs-ext 2) (variant True) (variant False))))
    (term (obs-ext 3)))))

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

;; Given a program config/spec config pair, rename the precise internal and external addresses in them
;; such that the first one in each set starts at 0, then the next is 1, then 2, etc.
;;
;; TODO: do the internal address part
(define (canonicalize-tuple tuple)
  (term (canonicalize-tuple/mf ,tuple)))

(define-metafunction aps#
  canonicalize-tuple/mf : (K# Σ) -> (K# Σ)
  [(canonicalize-tuple/mf (K# Σ))
   ((rename-addresses K# [natural_old natural_new] ...)
    (rename-addresses Σ [natural_old natural_new] ...))
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
        (term (SINGLE-ACTOR-ADDR
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))))))
      (((((define-state (A a b c) [* -> (goto A)]))
         (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
         SINGLE-ACTOR-ADDR))
       ()))))
   (term
    (,(make-single-actor-abstract-config
       (term (SINGLE-ACTOR-ADDR
              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
               (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))))))
     (((((define-state (A a b c) [* -> (goto A)]))
        (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
        SINGLE-ACTOR-ADDR))
      ()))))

  (check-equal?
   (canonicalize-tuple
    (term
     (,(make-single-actor-abstract-config
        (term (SINGLE-ACTOR-ADDR
               (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
                (goto A (obs-ext 10) (obs-ext 42) (obs-ext 25))))))
      (((((define-state (A c b a) [* -> (goto A)]))
         (goto A (obs-ext 25) (obs-ext 42) (obs-ext 10))
         SINGLE-ACTOR-ADDR))
       ()))))
   (term
    (,(make-single-actor-abstract-config
       (term (SINGLE-ACTOR-ADDR
              (((define-state (A [a (Addr Nat)] [b (Addr Nat)] [c (Addr Nat)]) (m) (goto A)))
               (goto A (obs-ext 2) (obs-ext 1) (obs-ext 0))))))
     (((((define-state (A c b a) [* -> (goto A)]))
        (goto A (obs-ext 0) (obs-ext 1) (obs-ext 2))
        SINGLE-ACTOR-ADDR))
      ()))))

  (check-equal?
   (canonicalize-tuple
    (term
     (,(make-single-actor-abstract-config
        (term (SINGLE-ACTOR-ADDR
               (((define-state (A) (m) (goto A)))
                (goto A)))))
      (() (((obs-ext 101) *))))))
   (term
    (,(make-single-actor-abstract-config
       (term (SINGLE-ACTOR-ADDR
              (((define-state (A) (m) (goto A)))
               (goto A)))))
     (() (((obs-ext 0) *))))))

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
  [(where (_ ... (a#ext _ ... po _ ...) _ ... ) O)
   -------------------------------------------------
   (config-has-commitment?/j (_ O) [a#ext po])])

(module+ test
  (define commitment-map-test-config
    (term (()
           (((obs-ext 1) *)
            ((obs-ext 2))
            ((obs-ext 3) (record) (variant True))))))
  (check-not-false (redex-match aps# Σ commitment-map-test-config))

  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 1) *])))
  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) (record)])))
  (check-true (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) (variant True)])))

  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 2) *])))
  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 1) (record)])))
  (check-false (aps#-config-has-commitment? commitment-map-test-config (term [(obs-ext 3) *]))))

(define (no-duplicate-commitments? config)
  (define commitment-lists
    (redex-let aps# ([(_ ((_ po ...) ...)) config])
               (term ((po ...) ...))))
  (andmap (lambda (l) (equal? l (remove-duplicates l))) commitment-lists))

;; TODO: remove this function; part of a hack
;;
;; Returns the unique config with the minimal number of output commitments, or false if no such config
;; exists
(define (unique-minimal-config spec-configs)
  (define count-map (make-hash))
  (for ([config spec-configs])
    (define commitment-count
      (redex-let aps# ([(_ ((_ po ...) ...)) config])
                 (length (append* (term ((po ...) ...))))))
    (hash-set! count-map commitment-count
     (cond
       [(hash-has-key? count-map commitment-count)
        (cons config (hash-ref count-map commitment-count))]
       [else (list config)])))
  (match (hash-keys count-map)
    [(list) #f]
    [keys
     (match (hash-ref count-map (apply min keys))
       [(list config) config]
       [_ #f])]))
