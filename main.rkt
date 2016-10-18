#lang racket

;; Implements the top-level function, "check-conformance", and includes the core of the
;; conformance-checking algorithm

(provide
 check-conformance

 ;; Needed only for debugging in other files
 ;; impl-steps-from
 ;; matching-spec-steps
 ;; debug-impl-step
 ;; check-conformance/config
 ;; prune-unsupported
 ;; partition-by-satisfaction
 )

(require
 ;; See README.md for a brief description of these files
 racket/fasl
 racket/date ; for debugging
 data/queue
 "aps.rkt"
 "aps-abstract.rkt"
 "checker-data-structures.rkt"
 "commitment-satisfaction.rkt"
 "csa.rkt"
 "csa-abstract.rkt"
 "graph.rkt"
 "queue-helpers.rkt"
 "set-helpers.rkt")

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   (for-syntax syntax/parse)
   "rackunit-helpers.rkt"))

;; ---------------------------------------------------------------------------------------------------
;; Top-level Algorithm

;; Returns the result of running the conformance-check algorithm below on the instantiated program and
;; specification.
(define/contract (check-conformance program specification)
  (-> csa-valid-program? aps-valid-spec? boolean?)

  (match-define (list impl-config spec-config) (instantiate-configs program specification))
    (check-conformance/config impl-config spec-config))

;; Given a concrete implementation configuration, a concrete specification configuration, returns #t
;; if the conformance-check algorithm can prove that the implementation conforms to the specification,
;; #f otherwise.
;;
;; The algorithm works by abstracting the given initial configurations into abstract configurations,
;; then constructing a graph-like structure that acts as a constructive proof of conformance for the
;; abstract pair (roughly, every vertex (pair of configurations) in the graph is in the conformance
;; relation, and every edge points to the pair that supports some necessary dependency of the source
;; pair. By the soundness theorem for abstract conformance, if conformance holds for the abstract
;; pairs (i.e. the pairs are in the graph), then it holds for the original concrete pairs, as well.
;;
;; To construct this structure, the algorithm first abstractly interprets the implementation and
;; specification to find configuration pairs in which the specification can simulate the
;; implementation up to one step (see find-rank1-simulation). This process also uncovers all edges and
;; vertices that related pairs would rely upon to be part of a full simulation relation. By removing
;; from the graph all pairs that depend on pairs outside the graph and propagating the results of
;; those removals backwards until we reach a greatest fixpoint (see prune-unsupported), we end up with
;; a proof graph whose vertices are all configuration pairs in the simulation.
;;
;; Next, we identify the the vertices in the graph whose implementation configurations are not
;; guaranteed to satisfy all of their commitments in every fair execution (see find-unsatisfying-pairs
;; below). By removing these nodes and again back-propagating the effects of those removals (with
;; prune-unsupported again), the resulting graph represents a proof that all of its members are in the
;; conformance relation.
(define/contract (check-conformance/config initial-impl-config initial-spec-config)
  (-> csa-valid-config? aps-valid-config? boolean?)

  (cond
    [(not (spec-interfaces-available? initial-impl-config initial-spec-config)) #f]
    [else
     (match (get-initial-abstract-pairs initial-impl-config initial-spec-config)
       [#f #f]
       [initial-pairs
        (match-define (list rank1-pairs
                            rank1-unrelated-successors
                            incoming-steps
                            rank1-related-spec-steps)
          (find-rank1-simulation initial-pairs))
        (match-define (list simulation-pairs simulation-related-spec-steps)
          (prune-unsupported rank1-pairs
                             incoming-steps
                             rank1-related-spec-steps
                             rank1-unrelated-successors))
        (match-define (list commitment-satisfying-pairs unsatisfying-pairs)
          (partition-by-satisfaction simulation-pairs incoming-steps simulation-related-spec-steps))
        (match-define (list conforming-pairs _)
          (prune-unsupported commitment-satisfying-pairs
                             incoming-steps
                             simulation-related-spec-steps
                             unsatisfying-pairs))
        (andmap (curry set-member? conforming-pairs) initial-pairs)])]))

;; Returns #t if all addresses mentioned in observable or unobservable interfaces in the spec are
;; receptionists; #f otherwise.
(define (spec-interfaces-available? impl-config spec-config)
  (define spec-receptionists (map csa-address-strip-type (aps-config-interface-addresses spec-config)))
  (define impl-receptionists (map csa-address-strip-type (csa-config-receptionists impl-config)))
  (and (andmap (curryr member impl-receptionists) spec-receptionists) #t))

(module+ test
  (test-false "spec address receptionist check 1"
    (spec-interfaces-available? (term ((((addr 1) (() (goto A)))) () () ()))
                                (term ((Nat (addr 1)) () (goto A) () ()))))
  (test-false "spec address receptionist check 2"
    (spec-interfaces-available? (term ((((addr 500) (() (goto A)))) () () ()))
                                (term ((Nat (addr 1)) () (goto A) () ()))))
  (test-not-false "spec address receptionist check 3"
    (spec-interfaces-available? (term ((((addr 1) (() (goto A)))) () ((Nat (addr 1))) ()))
                                (term ((Nat (addr 1)) () (goto A) () ()))))
  (test-not-false "spec address receptionist check 4"
    (spec-interfaces-available? (term ((((addr 1) (() (goto A)))) () ((Nat (addr 1))) ()))
                                (term (UNKNOWN () (goto A) () ()))))
  (test-false "spec address receptionist: unobserved addresses 1"
    (spec-interfaces-available? (term ((((addr 1) (() (goto A)))) () () ()))
                                (term (UNKNOWN ((Nat (addr 1))) (goto A) () ()))))
  (test-not-false "spec address receptionist: unobserved addresses 2"
    (spec-interfaces-available? (term ((((addr 1) (() (goto A)))) () ((Nat (addr 1))) ()))
                                (term (UNKNOWN ((Nat (addr 1))) (goto A) () ())))))

;; Abstracts and sbc's the initial pair, returning the list of initial abstract pairs, or #f if the
;; abstraction was not possible for some reason
(define (get-initial-abstract-pairs impl-config spec-config)
  (define internal-addresses (csa-config-internal-addresses impl-config))
  (match (csa#-abstract-config impl-config internal-addresses)
    [#f #f]
    [abstract-impl-config
     (map first (sbc (config-pair abstract-impl-config
                                  (aps#-abstract-config spec-config internal-addresses))))]))

;; ---------------------------------------------------------------------------------------------------
;; Simulation

;; (Setof config-pair) -> (List (Setof config-pair)
;;                              (Setof config-pair)
;;                              IncomingDict
;;                              RelatedSpecStepsDict)
;;
;; Finds a set of pairs that are related in the rank-1 conformance simulation by abstractly evaluating
;; implementation configs and finding matching specification transitions, starting from the given
;; initial pairs. Returns the set of related pairs along with other data structures that act as a
;; proof of the pairs' membership. Specifically, it returns:
;;
;; related-pairs: the set of pairs found to be in the rank-1 simulation
;;
;; unrelated-successors: pairs reachable by from a pair in related-pairs by a matching
;; impl-step/spec-step transition but are not themselves in the rank-1 simulation.
;;
;; incoming-steps: A dictionary from either a related pair or an unrelated successor to the set of
;; impl/spec steps that lead to it (as described in the "Type" Definitions section above)
;;
;; related-spec-steps: A dictionary from a related pair and an implementation step from that pair to
;; the set of specification steps that match the implementation step. See "Type" Definitions above for
;; more details.
(define (find-rank1-simulation initial-pairs)
  (define to-visit (apply queue initial-pairs))
  (define related-spec-steps (make-hash))
  (define incoming-steps (make-hash (map (lambda (t) (cons t (mutable-set))) initial-pairs)))

  ;; Debugging
  (define visited-pairs-count 0)
  (define visited-impl-configs (mutable-set))
  (define visited-spec-configs (mutable-set))
  (define log-file (open-log))
  (log-initial-pairs log-file initial-pairs)

  (let loop ([related-pairs (set)]
             [unrelated-successors (set)])
    (match (dequeue-if-non-empty! to-visit)
      [#f
       (close-log log-file)
       (list related-pairs unrelated-successors incoming-steps related-spec-steps)]
      [pair

       ;; Debugging
       (set! visited-pairs-count (add1 visited-pairs-count))
       (set-add! visited-impl-configs (config-pair-impl-config pair))
       (set-add! visited-spec-configs (config-pair-spec-config pair))
       ;; (printf "Current time: ~a\n" (date->string (seconds->date (current-seconds)) #t))
       ;; (printf "Pair config #: ~s\n" visited-pairs-count)
       ;; (printf "Unique impl configs so far: ~s\n" (set-count visited-impl-configs))
       ;; (printf "Unique spec configs so far: ~s\n" (set-count visited-spec-configs))
       ;; (printf "Queue size: ~s\n" (queue-length to-visit))
       ;; (printf "The impl config: ~s\n"
       ;;         (impl-config-without-state-defs (config-pair-impl-config pair)))
       ;; (printf "The full impl config: ~s\n" (config-pair-impl-config pair))
       ;; (printf "The spec config: ~s\n"
       ;;         (spec-config-without-state-defs (config-pair-spec-config pair)))
       ;; (printf "Incoming so far: ~s\n" (hash-ref incoming-steps pair))
       (flush-output)

       (log-exploring log-file pair)

       (define i (config-pair-impl-config pair))
       (define s (config-pair-spec-config pair))

       (match (impl-steps-from i s)
         [#f
          ;; Evaluation led to an unverifiable configuration, so we deem this pair unrelated, add it
          ;; to the unrelated-successors list, and move on to explore the next pair in our worklist.
          (loop related-pairs (set-add unrelated-successors pair))]
         [i-steps
          ;; Find the matching s-steps
          (define found-unmatchable-step? #f)
          (for ([i-step i-steps])
            ;; Debugging:
            ;; (printf "Impl step: ~s\n" (debug-impl-step i-step))

            (define matching-s-steps (matching-spec-steps s i-step))
            ;; Debugging:
            ;; (printf "Matching spec steps: ~s\n" matching-s-steps)

            (log-related-spec-steps log-file (list pair i-step) matching-s-steps)
            (hash-set! related-spec-steps (list pair i-step) matching-s-steps)
            (when (set-empty? matching-s-steps)
              (set! found-unmatchable-step? #t)))

          ;; Add this pair to either related or unrelated set; add new worklist items
          (cond
            [found-unmatchable-step?
             ;; Some impl step has no matching spec step, so this pair is unrelated. Therefore we add
             ;; it to the unrelated-successors list and do not further explore transitions from this
             ;; pair.

             ;; Debugging
             ;; (displayln "Unrelated pair")
             (log-unrelated log-file pair)
             (loop related-pairs (set-add unrelated-successors pair))]
            [else
             ;; This pair is in the rank-1 simulation (because all of its impl steps have matching
             ;; spec steps). We have to add it to the related-pairs set, sbc each of the matching
             ;; destination pairs and add them to the work-list so that we explore this pair's
             ;; successors, and add the incoming transitions for those destination pairs to
             ;; incoming-steps.

             ;; Debugging
             ;; (displayln "Related pair")
             (for ([i-step i-steps])
               (for ([s-step (hash-ref related-spec-steps (list pair i-step))])
                 (define successor-pairs
                   (for/list ([config (cons (spec-step-destination s-step) (spec-step-spawns s-step))])
                     (config-pair (impl-step-destination i-step) config)))

                 ;; Debugging only
                 ;; (for ([successor-pair successor-pairs])
                 ;;   (printf "pre-sbc: ~s\n" successor-pair)
                 ;;   (printf "post-sbc: ~s\n" (sbc successor-pair)))
                 (for ([sbc-result (sbc* successor-pairs)])
                   ;; TODO: add the address binding here, too, and adjust other uses of incoming
                   ;; (e.g. in prune-unsupported) to take that structure into account
                   (match-define (list sbc-pair rename-map) sbc-result)
                   (log-incoming log-file sbc-pair (list pair i-step s-step rename-map))
                   (dict-of-sets-add! incoming-steps sbc-pair (list pair i-step s-step rename-map))
                   (unless (or (member sbc-pair (queue->list to-visit))
                               (set-member? related-pairs sbc-pair)
                               (set-member? unrelated-successors sbc-pair)
                               (equal? sbc-pair pair))
                     (enqueue! to-visit sbc-pair)))))
             (log-related log-file pair)
             (loop (set-add related-pairs pair) unrelated-successors)])])])))

;; Returns all implementation steps possible from the given impl-config/spec-config pair, or #f if
;; some step leads to an unverifiable configuration. The spec config is used to determine whether
;; sending a message to a given receptionist in the implementation config can be observed, unobserved,
;; or both.
(define (impl-steps-from impl-config spec-config)
  (let/cc return-continuation
    ;; Certain evaluation steps can lead to an unverifiable configuration. When that happens, rather
    ;; than continuing to evaluate other possible steps from this configuration, we call this
    ;; continuation to abort the whole evaluation step.
    (define (abort) (return-continuation #f))

    (define (add-observed-flag transition observed?)
      (match transition
        [#f #f]
        [_
         (impl-step (csa#-transition-trigger transition)
                    observed?
                    (csa#-transition-outputs transition)
                    (csa#-transition-loop-outputs transition)
                    (csa#-transition-final-config transition))]))

  (define obs-interface (aps#-config-obs-interface spec-config))
  ;; TODO: (perf. improvement) share the results between the observed and unobserved external
  ;; receives, because often many of the results will be the same (because the same address might
  ;; receive messages from both the observed and unobserved environments)
  (define observed-external-receives
    (if (aps#-unknown-address? obs-interface)
        null
        (external-message-transitions impl-config obs-interface abort)))
  (define unobserved-external-receives
    (append*
     (for/list ([receptionist (aps#-config-receptionists spec-config)])
       (external-message-transitions impl-config receptionist abort))))

  (append (map (curryr add-observed-flag #t) observed-external-receives)
          (map (curryr add-observed-flag #f)
               (append
                unobserved-external-receives
                (csa#-handle-all-internal-actions impl-config abort))))))

;; Returns all possible transitions of the given implementation config caused by a received message to
;; the given receptionist address
(define (external-message-transitions impl-config typed-receptionist abort)
  (display-step-line "Enumerating abstract messages (typed)")
  (append*
   (for/list ([message (csa#-messages-of-type (csa#-address-type typed-receptionist))])
     (display-step-line "Evaluating a handler")
     (csa#-handle-external-message impl-config
                                   (csa#-address-strip-type typed-receptionist)
                                   message
                                   abort))))

;; Returns a set of the possible spec steps (see the struct above) from the given spec config that
;; match the given implementation step
(define (matching-spec-steps spec-config i-step)
  (define matched-stepped-configs (mutable-set))
  (for ([trigger-result (aps#-matching-steps spec-config
                                             (impl-step-from-observer? i-step)
                                             (impl-step-trigger i-step))])
    (match-define (list config spawns1) trigger-result)
    (match (aps#-resolve-outputs config (impl-step-outputs i-step) (impl-step-loop-outputs i-step))
      [#f (void)]
      [(list stepped-spec-config spawns2 satisfied-commitments)
       (set-add! matched-stepped-configs
                 (spec-step stepped-spec-config (append spawns1 spawns2) satisfied-commitments))]))
  matched-stepped-configs)

(module+ test
  (define null-spec-config (make-s# '((define-state (S))) '(goto S) null null))

  (test-case "Null transition okay for unobs"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (init-addr 0) (* Nat)) #f null null #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "Null transition not okay for observed input"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(external-receive (init-addr 0) (* Nat)) #t null null #f))
     (mutable-set)))
  (test-case "No match if trigger does not match"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A) [x -> () (goto A)])) '(goto A) null null)
      (impl-step '(external-receive (init-addr 0) (* Nat)) #t null null #f))
     (mutable-set)))
  (test-case "Unobserved outputs don't need to match"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (init-addr 0) (* Nat)) #f (list '((obs-ext 1) (* Nat))) null #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "No match if outputs do not match"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A))) '(goto A) null (list '((obs-ext 1))))
      (impl-step '(internal-receive (init-addr 0) (* Nat)) #f (list '((obs-ext 1) (* Nat))) null #f))
     (mutable-set)))
  (test-case "Output can be matched by previous commitment"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A))) '(goto A) null (list '((obs-ext 1) (single *))))
      (impl-step '(internal-receive (init-addr 0) (* Nat)) #f (list '((obs-ext 1) (* Nat))) null #f))
     (mutable-set (spec-step (make-s# '((define-state (A))) '(goto A) null (list '((obs-ext 1))))
                             null
                             (list `[(obs-ext 1) *])))))
  (test-case "Output can be matched by new commitment"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A) [x -> ([obligation x *]) (goto A)])) '(goto A) null null)
      (impl-step '(external-receive (init-addr 0) (Nat (obs-ext 1))) #t (list '((obs-ext 1) (* Nat))) null #f))
     (mutable-set (spec-step (make-s# '((define-state (A) [x -> ([obligation x *]) (goto A)]))
                                      '(goto A)
                                      null
                                      (list '((obs-ext 1))))
                             null
                             (list `[(obs-ext 1) *])))))
  (test-case "Multiple copies of same commitment get merged"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A x) [* -> ([obligation x *]) (goto A x)])) '(goto A (obs-ext 1)) null (list '[(obs-ext 1) (single *)]))
      (impl-step '(external-receive (init-addr 0) (* Nat)) #t null null #f))
     (mutable-set
      (spec-step (make-s# '((define-state (A x) [* -> ([obligation x *]) (goto A x)])) '(goto A (obs-ext 1)) null (list '[(obs-ext 1) (many *)]))
                 null
                 null)))))

;; Given a hash table whose values are sets, add val to the set in dict corresponding to key (or
;; create the hash-table entry with a set containing that val if no entry exists).
(define (dict-of-sets-add! dict key val)
  (match (hash-ref dict key #f)
    [#f
     (hash-set! dict key (mutable-set val))]
    [the-set
     (set-add! the-set val)]))

;; ---------------------------------------------------------------------------------------------------
;; Split/Blur/Canonicalize (SBC)

;; Performs the SBC (split/blur/canonicalize) operation on a config pair, returning its derivative
;; pairs along with an address-rename map with each pair. SBC entails the following:
;;
;; 1. For each address in the output commitment map that is *not* an argument to the current state,
;; split those commitments off into a new specification with a dummy FSM.
;;
;; 2. For each specification resulting from step 1, blur the implementation configuration according
;; to the addresses relevant to that spec. This means merging external addresses not used in the spec
;; into a single abstract value and choosing some subset of actors (up to some statically known
;; number) to remain precise while merging the others together.
;;
;; 3. Canonicalize the addresses in both configurations. That is, rename them to some canonical naming
;; so that we avoid the orbit problem with other similar pairs that we have already explored (or that
;; we will explore).
;;
;; SBC keeps our explored state-space finite. By creating a new spec for each no-longer-used
;; commitment address, we ensure that the number of adddresses in a spec config is no more than max(1,
;; maxStateParams), where maxStateParams is the maximum number of formal parameters for any state in
;; the original (static) specification. Blurring the implementation configuration according to the
;; new spec component keeps the state-space of the impl configs finite. Finally, canonicalize ensures
;; that the address values do not keep increasing towards infinity and instead stay within a bounded
;; space.
(define (sbc pair)
  (display-step-line "Splitting a specification config")
  (define spec-config-components (split-spec (config-pair-spec-config pair)))
  (define blur-results
    (for/list ([spec-config-component spec-config-components])
      (display-step-line "Blurring an implementation config")
      (blur-by-relevant-addresses (config-pair-impl-config pair) spec-config-component)))
  (for/list ([blur-result blur-results])
    (match-define (list blurred-impl blurred-spec) blur-result)
    (display-step-line "Canonicalizing the pair, adding to queue")
    (match-define (list canonicalized-impl canonicalized-spec rename-map)
      (canonicalize-pair blurred-impl blurred-spec))
    (list (config-pair canonicalized-impl canonicalized-spec) rename-map)))

;; Calls sbc on every pair and merges the results into one long list.
(define (sbc* pairs)
  (append* (map sbc pairs)))

;; impl-config spec-config -> (List impl-config spec-config)
;;
;; Blurs the given configurations into only the portions that are relevant to the specification
;; configuration, moving the rest of the configurations into the "imprecise" sections of the
;; abstraction.
;;
;; Specifically, this chooses actors with either the NEW or OLD flag to be more likely to match this
;; specification, then takes all actors with the same spawn location and opposite flag and merges
;; their behaviors into the set of behaviors for the "blurred" actors of that location.
(define (blur-by-relevant-addresses impl-config spec-config)
  (match-define (list blurred-impl-config blurred-internals)
    (csa#-blur-config impl-config
                      (choose-spawn-flag-to-blur impl-config spec-config)
                      (aps#-relevant-external-addrs spec-config)))
  (list
   blurred-impl-config
   (aps#-blur-config spec-config blurred-internals)))

(module+ test
  (test-equal? "check that messages with blurred addresses get merged together"
   (blur-by-relevant-addresses
    (term (()
           ()
           (((init-addr 2) (Nat (obs-ext 1)) single)
            ((init-addr 2) (Nat (obs-ext 2)) single)
            ((init-addr 2) (Nat (obs-ext 3)) single))))
    (aps#-make-no-transition-config '() '(((obs-ext 3)))))
   (list (term (()
                ()
                (((init-addr 2) (* (Addr Nat)) many)
                 ((init-addr 2) (Nat (obs-ext 3)) single))))
         (aps#-make-no-transition-config '() '(((obs-ext 3)))))))

;; Decides whether to blur spawn-addresses with the OLD or NEW flag based on the current impl and spec
;; configs, returning the flag for addresses that should be blurred.
(define (choose-spawn-flag-to-blur impl-config spec-config)
  ;; 1. if the spec address is a spawn-address, return its flag
  ;;
  ;; 2. if the spec address is unknown but only init-addr actors and actors with just one of the flags
  ;; have addresses from the output commitment set, blur the other flag
  ;;
  ;; 3. otherwise, just return OLD by default
  (cond
    [(csa#-spawn-address? (aps#-config-obs-interface spec-config))
     (csa#-spawn-address-flag (aps#-config-obs-interface spec-config))]
    [else ; must be the special "unknown" spec address
     (match (csa#-flags-that-know-externals impl-config (aps#-relevant-external-addrs spec-config))
       [(list 'OLD) 'NEW]
       [(list 'NEW) 'OLD]
       [_ 'OLD])]))

;; ---------------------------------------------------------------------------------------------------
;; Pair-removal back-propagation


;; (Setof config-pair) IncomingDict RelatedSpecStepsDict (Setof config-pair) ->
;;   (Setof config-pair) RelatedSpecStepsDict
;;
;; Removes from all-pairs those pairs whose proof of membership in a simulation (i.e. their matching
;; transitions in init-related-spec-steps) depends on a transition to a pair known to not be in the
;; relation (we call these "unsupported pairs"). The algorithm propagates the effects of these
;; removals backwards through the proof structure and removes further unsupported pairs until a
;; greatest fixpoint is reached, yielding a set of pairs whose members are all in the full simulation
;; relation.
;;
;; all-pairs: The initial set of pairs, assumed to all be in the rank-1 simulation
;;
;; incoming-steps: A dictionary from either a related pair or an unrelated successor to the set of
;; impl/spec steps that lead to it (as described in the "Type" Definitions section above). Must
;; include entries for all pairs in both all-pairs and init-unrelated-successors.
;;
;; init-related-spec-steps: A dictionary from a related pair and an implementation step from that pair
;; to the set of specification steps that match the implementation step. Must have an entry for every
;; possible implementation step from a pair in all-pairs, and there must be at least one matching spec
;; step per entry. See "Type" Definitions above for more details.
;;
;; init-unrelated-successors: A set of config-pairs that are known to *not* be in the rank-1 simulation. This list must include all
;;
;; Returns:
;;
;; simulation-pairs: The subset of all-pairs that the function was able to show are in the simulation.
;;
;; simulation-related-spec-steps: The RelatedSpecStepsDict that is a sub-dictionary of
;; init-related-spec-steps (i.e. the sets are subsets of those from init-related-spec-steps). This
;; dictionary consitutes a proof that all members of simulation-pairs are in the simulation relation.
(define (prune-unsupported all-pairs incoming-steps init-related-spec-steps init-unrelated-successors)
  ;; The function implements a worklist algorithm, with init-unrelated-successors forming the initial
  ;; worklist items. The objective is to remove unsupported items from remaining-pairs and
  ;; related-spec-steps so that at the end of the algorithm, they comprise a globally consistent
  ;; proof.
  (define unrelated-successors (apply queue (set->list init-unrelated-successors)))
  (define remaining-pairs (set-copy all-pairs))
  (define related-spec-steps (hash-copy init-related-spec-steps))

  ;; Loop invariant: For every pair in remaining-pairs and every impl-step possible from that pair,
  ;; related-spec-steps(pair, impl-step) = a non-empty set of matching specification transitions such
  ;; that the sbc-derivatives of (impl-step.destination, spec-step.destination) are all in
  ;; remaining-pairs or unrelated-successors.
  ;;
  ;; Termination argument: Every iteration of the loop processes one worklist item. We never process a
  ;; worklist item more than once (because they only come from remaining-pairs, and when an item is
  ;; queued into the worklist it is permanently removed from remaining-pairs). The total set of items
  ;; that might enter the worklist (all-pairs plus init-related-successors) is finite, so the queue is
  ;; eventually emptied and the loop terminates.
  (let loop ()
    (match (dequeue-if-non-empty! unrelated-successors)
      [#f (list (set-immutable-copy remaining-pairs) related-spec-steps)]
      [unrelated-pair
       (for ([transition (hash-ref incoming-steps unrelated-pair)])
         (match-define (list predecessor i-step s-step _) transition)
         ;; Only check for lack of support for pairs still in remaining pairs
         (when (set-member? remaining-pairs predecessor)
           (define spec-steps (hash-ref related-spec-steps (list predecessor i-step)))
           ;; Proceed to remove this spec step only if we have not already discovered that it is
           ;; unsupported (we may have found some other sbc-derivative of the same step that also led
           ;; to an unsupported pair)
           (when (set-member? spec-steps s-step)
             (set-remove! spec-steps s-step)
             (when (set-empty? spec-steps)
               ;; There are no matching spec steps for this impl step, so remove this pair from the
               ;; relation and add it to the worklist
               (set-remove! remaining-pairs predecessor)
               (enqueue! unrelated-successors predecessor)))))
       (loop)])))

(module+ test
  (require "hash-helpers.rkt")

  ;; Because prune-unsupported does not care about the actual content of the impl or spec
  ;; configurations, we replace them here with letters (A, B, C, etc. for impls and X, Y, Z, etc. for
  ;; specs) for simplification
  (define ax-pair (config-pair 'A 'X))
  (define by-pair (config-pair 'B 'Y))
  (define bz-pair (config-pair 'B 'Z))
  (define cw-pair (config-pair 'C 'W))

  (define aa-step (impl-step '(timeout (init-addr 0)) #f null null 'A))
  (define xx-step (spec-step 'X null null))
  (define ab-step (impl-step '(timeout (init-addr 0)) #f null null 'B))
  (define xy-step (spec-step 'Y null null))
  (define xz-step (spec-step 'Z null null))
  (define bc-step (impl-step '(timeout (init-addr 0)) #f null null 'C))
  (define yw-step (spec-step 'W null null))

  (test-equal? "Remove no pairs, because no list"
    (prune-unsupported
     (mutable-set ax-pair)
     ;; incoming-steps
     (mutable-hash [ax-pair (mutable-set (list ax-pair aa-step xx-step (hash)))])
     ;; related spec steps
     (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])
     ;; unrelated sucessors
     null)
    (list
     (set ax-pair)
     (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])))

  (test-equal? "Remove no pairs, because unrelated-matches contained only a redundant support"
    (prune-unsupported
     (set ax-pair bz-pair)
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
                   [bz-pair (mutable-set (list ax-pair ab-step xz-step (hash)))]
                   [ax-pair (mutable-set)])
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)])
     (list by-pair))
    (list
     (set ax-pair bz-pair)
     (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)])))

  (test-equal? "Remove last remaining pair"
    (prune-unsupported
     (mutable-set ax-pair)
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
                   [ax-pair (mutable-set)])
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)])
     (list by-pair))
    (list
     (set)
     (mutable-hash [(list ax-pair ab-step) (mutable-set)])))

  (test-equal? "Remove a redundant support"
    (prune-unsupported
     (mutable-set ax-pair bz-pair by-pair)
     ;; incoming-steps
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
                   [bz-pair (mutable-set (list ax-pair ab-step xz-step (hash)))]
                   [ax-pair (mutable-set)]
                   [cw-pair (mutable-set (list by-pair bc-step yw-step (hash)))])
     ;; matching spec steps
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)]
                   [(list by-pair bc-step) (mutable-set yw-step)])
     ;; unrelated successors
     (list cw-pair))
    (list
     (set ax-pair bz-pair)
     (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)]
                   [(list by-pair bc-step) (mutable-set)])))

    (test-equal? "Remove a non-redundant support"
      (prune-unsupported
       (mutable-set ax-pair by-pair)
       ;; incoming-steps
       (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
                     [ax-pair (mutable-set)]
                     [cw-pair (mutable-set (list by-pair bc-step yw-step (hash)))])
       ;; matching spec steps
       (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)]
                     [(list by-pair bc-step) (mutable-set yw-step)])
       ;; unrelated successors
       (list cw-pair))
      (list
       (set)
       (mutable-hash [(list ax-pair ab-step) (mutable-set)]
                     [(list by-pair bc-step) (mutable-set)]))))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define DISPLAY-STEPS #f)

(define (display-step-line msg)
  (when DISPLAY-STEPS (displayln msg)))

(define (pair->debug-pair pair)
  (list (impl-config-without-state-defs (config-pair-impl-config pair))
        (spec-config-without-state-defs (config-pair-spec-config pair))))

(define (debug-impl-step step)
  (list (impl-step-from-observer? step)
        (impl-step-trigger step)
        (impl-step-outputs step)))

;; ---------------------------------------------------------------------------------------------------
;; Logging

;; Change LOG-RUN to #t to write relevant checking data to a file so that the process of the check can
;; be recreated after the fact without creating the simulation graph all over again.
(define LOG-RUN #f)
(define LOG-FILE-PATH "checker_run_log.dat")

(define (open-log)
  (if LOG-RUN (open-output-file LOG-FILE-PATH #:exists 'replace) #f))

(define (close-log log-file)
  (when LOG-RUN (close-output-port log-file)))

;; NOTE: we flush the output after every entry so that there's something in the log even if the
;; checker crashes in mid-run.

(define (log-initial-pairs log-file initial-pairs)
  (when LOG-RUN
    (for ([pair initial-pairs])
      (s-exp->fasl `(initial-pair ,pair) log-file))
    (flush-output log-file)))

(define (log-exploring log-file pair)
  (when LOG-RUN
    (s-exp->fasl `(exploring ,pair) log-file)
    (flush-output log-file)))

(define (log-related-spec-steps log-file config-and-i-step related-steps)
  (when LOG-RUN
    (s-exp->fasl `(related-spec-step ,config-and-i-step ,(set->list related-steps)) log-file)
    (flush-output log-file)))

(define (log-unrelated log-file pair)
  (when LOG-RUN
    (s-exp->fasl `(unrelated ,pair) log-file)
    (flush-output log-file)))

(define (log-incoming log-file pair step)
  (when LOG-RUN
    (s-exp->fasl `(incoming ,pair ,step) log-file)
    (flush-output log-file)))

(define (log-related log-file pair)
  (when LOG-RUN
    (s-exp->fasl `(related ,pair) log-file)
    (flush-output log-file)))

;; ---------------------------------------------------------------------------------------------------
;; Top-level tests

(module+ test
  (define-simple-check (check-valid-actor? actual)
    (redex-match? csa-eval (τa b) actual))

  (define-syntax (test-valid-actor? stx)
    (syntax-parse stx
      [(_ name the-term)
       #`(test-case name
           #,(syntax/loc stx (check-valid-actor? the-term)))]
      [(_ the-term)
       #`(test-begin
           #,(syntax/loc stx (check-valid-actor? the-term)))]))

  (define-simple-check (check-valid-instance? actual)
    (redex-match? aps-eval ((Φ ...) (goto φ u ...) σ) actual))

  (define-syntax (test-valid-instance? stx)
    (syntax-parse stx
      [(_ name the-term)
       #`(test-case name
           #,(syntax/loc stx (check-valid-instance? the-term)))]
      [(_ the-term)
       #`(test-begin
           #,(syntax/loc stx (check-valid-instance? the-term)))]))

  ;;;; Ignore everything

  (define (make-ignore-all-config addr-type)
    (make-single-actor-config
     (term
      ((,addr-type (addr 0))
       (((define-state (Always) (m) (goto Always)))
        (goto Always))))))
  (define ignore-all-config (make-ignore-all-config 'Nat))
  (define (make-ignore-all-spec-instance addr-type)
    (term
     (((define-state (Always) [* -> () (goto Always)]))
      (goto Always)
      (,addr-type (addr 0)))))
  (define ignore-all-spec-instance
    (make-ignore-all-spec-instance 'Nat))
  (check-not-false (redex-match csa-eval i ignore-all-config))
  (test-valid-instance? ignore-all-spec-instance)

  (test-true "ignore all spec/test"
    (check-conformance/config ignore-all-config (make-exclusive-spec ignore-all-spec-instance)))

  ;;;; Send one message to a statically-known address per request

  (define (make-static-response-address type) (term (,type (addr 2))))
  (define untyped-static-response-address `(addr 2))
  (define static-response-address (make-static-response-address (term (Union (Ack Nat)))))
  (define static-response-actor
    (term
     ((Nat (addr 0))
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-actor
    (term
     ((Nat (addr 0))
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-response-spec
    (term
     (((define-state (Always response-dest)
         [* -> ([obligation response-dest *]) (goto Always response-dest)]))
      (goto Always ,untyped-static-response-address)
      (Nat (addr 0)))))
  (define ignore-all-with-addr-spec-instance
    (term
     (((define-state (Always response-dest) [* -> () (goto Always response-dest)]))
      (goto Always ,untyped-static-response-address)
      (Nat (addr 0)))))
  (define static-double-response-spec
    (term
     (((define-state (Always response-dest)
         [* -> ([obligation response-dest *]
                [obligation response-dest *])
               (goto Always response-dest)]))
      (goto Always ,untyped-static-response-address)
      (Nat (addr 0)))))

  (test-valid-actor? static-response-actor)
  (test-valid-actor? static-double-response-actor)
  (test-valid-instance? static-response-spec)
  (test-valid-instance? ignore-all-with-addr-spec-instance)
  (test-valid-instance? static-double-response-spec)

  (test-true "Static response works"
             (check-conformance/config (make-single-actor-config static-response-actor)
                          (make-exclusive-spec static-response-spec)))
  (test-false "Static response actor, ignore all spec"
              (check-conformance/config (make-single-actor-config static-response-actor)
                           (make-exclusive-spec ignore-all-with-addr-spec-instance)))
  (test-false "static double response actor"
              (check-conformance/config (make-single-actor-config static-double-response-actor)
                                        (make-exclusive-spec static-response-spec)))
  (test-false "Static response spec, ignore-all config"
               (check-conformance/config ignore-all-config
                                         (make-exclusive-spec static-response-spec)))
  ;; tests for non-conformance to spec configurations with many-of commitments
  (test-false "Static double response spec, ignore-all config"
    (check-conformance/config ignore-all-config
                              (make-exclusive-spec static-double-response-spec)))

  ;;;; Pattern matching tests, without dynamic channels

  (define pattern-match-spec
    (term
     (((define-state (Matching r)
         [(variant A *) -> ([obligation r (variant A *)]) (goto Matching r)]
         [(variant B *) -> ([obligation r (variant B *)]) (goto Matching r)]))
      (goto Matching ,untyped-static-response-address)
      ((Union [A Nat] [B Nat]) (addr 0)))))

  (define pattern-matching-actor
    (term
     (((Union [A Nat] [B Nat]) (addr 0))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A x)) (goto Always r))]
            [(B y) (begin (send r (variant B 0)) (goto Always r))])))
       (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

  (define reverse-pattern-matching-actor
    (term
     (((Union [A Nat] [B Nat]) (addr 0))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant B 0)) (goto Always r))]
            [(B y) (begin (send r (variant A y)) (goto Always r))])))
       (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

  (define partial-pattern-matching-actor
    (term
     (((Union [A Nat] [B Nat]) (addr 0))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A 0)) (goto Always r))]
            [(B y) (goto Always r)])))
       (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

  (test-valid-instance? pattern-match-spec)
  (test-valid-actor? pattern-matching-actor)
  (test-valid-actor? reverse-pattern-matching-actor)
  (test-valid-actor? partial-pattern-matching-actor)

  (test-true "Pattern matching"
    (check-conformance/config (make-single-actor-config pattern-matching-actor)
                              (make-exclusive-spec pattern-match-spec)))
  (test-false "Send on A but not B; should send on both"
              (check-conformance/config (make-single-actor-config partial-pattern-matching-actor)
                           (make-exclusive-spec pattern-match-spec)))
  (test-false "Pattern matching discriminates different patterns"
    (check-conformance/config (make-single-actor-config reverse-pattern-matching-actor)
                              (make-exclusive-spec  pattern-match-spec)))

  ;;;; "Or" pattern matching
  (define or-pattern-match-spec
    (term
     (((define-state (Matching r)
         [* -> ([obligation r (or (variant A *) (variant B *))]) (goto Matching r)]))
      (goto Matching ,untyped-static-response-address)
      ((Union [A Nat] [B Nat]) (addr 0)))))

  (define or-wrong-pattern-match-spec
    (term
     (((define-state (Matching r)
         [* -> ([obligation r (or (variant A *) (variant C *))]) (goto Matching r)]))
      (goto Matching ,untyped-static-response-address)
      ((Union [A Nat] [B Nat]) (addr 0)))))

  (test-valid-instance? or-pattern-match-spec)
  (test-valid-instance? or-wrong-pattern-match-spec)
  (test-true "Pattern match with or"
    (check-conformance/config (make-single-actor-config pattern-matching-actor)
                              (make-exclusive-spec or-pattern-match-spec)))
  (test-false "Pattern match with wrong or pattern"
    (check-conformance/config (make-single-actor-config pattern-matching-actor)
                              (make-exclusive-spec or-wrong-pattern-match-spec)))

  (define send-message-then-another
    (term
     ((Nat (addr 0))
      (((define-state (Init [r (Addr (Union [A] [B]))]) (m)
          (begin
            (send r (variant A))
            (goto SendOther r)))
        (define-state (SendOther [r (Addr (Union [A] [B]))]) (m)
          (begin
            (send r (variant A))
            (goto Done))
          [(timeout 5)
           (begin
             (send r (variant B))
             (goto Done))])
        (define-state (Done) (m) (goto Done)))
       (goto Init ((Union [A] [B]) (addr 1)))))))

  (define overlapping-patterns-spec
    (term
     (((define-state (Init r)
         [* -> ([obligation r (or (variant A) (variant B))]
                [obligation r (variant A)])
            (goto NoMoreSends)])
       (define-state (NoMoreSends)
         [* -> () (goto NoMoreSends)]))
      (goto Init (addr 1))
      (Nat (addr 0)))))

  ;; Non-deterministic/overlap pattern-matching is unsupported: we just pick for each output the first
  ;; pattern that can possibly match
  (test-valid-actor? send-message-then-another)
  (test-valid-instance? overlapping-patterns-spec)
  (test-false "Overlapping output patterns cause non-conformance"
    (check-conformance/config
     (make-single-actor-config send-message-then-another)
     (make-exclusive-spec overlapping-patterns-spec)))

  ;;;; Dynamic request/response

  (define request-response-spec
    (term
     (((define-state (Always)
         [response-target -> ([obligation response-target *]) (goto Always)]))
      (goto Always)
      ((Addr Nat) (addr 0)))))

  (define request-same-response-addr-spec
    (term
     (((define-state (Init)
         [response-target -> ([obligation response-target *]) (goto HaveAddr response-target)])
       (define-state (HaveAddr response-target)
         [new-response-target -> ([obligation response-target *]) (goto HaveAddr response-target)]))
      (goto Init)
      ((Addr Nat) (addr 0)))))
  (define request-response-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (Always [i Nat]) (response-target)
          (begin
            (send response-target i)
            (goto Always i))))
       (goto Always 0)))))
  (define respond-to-first-addr-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target i)
            (goto HaveAddr i response-target))))
       (goto Init)))))
  (define respond-to-first-addr-actor2
    (term
     (((Addr Nat) (addr 0))
      (((define-state (Always [original-addr (Union (NoAddr) (Original (Addr Nat)))]) (response-target)
          (begin
            (case original-addr
              [(NoAddr)
               (begin
                 (send response-target 0)
                 (goto Always (variant Original response-target)))]
              [(Original o)
               (begin
                 (send o 0)
                 (goto Always original-addr))]))))
       (goto Always (variant NoAddr))))))
  (define delay-saving-address-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target i)
            (goto HaveAddr i new-response-target))))
       (goto Init)))))
  (define double-response-actor
    `(((Addr Nat) (addr 0))
      (((define-state (Always [i Nat]) (response-dest)
          (begin
            (send response-dest i)
            (send response-dest i)
            (goto Always i))))
       (goto Always 0))))
  (define respond-once-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto NoMore)))
        (define-state (NoMore) (new-response-target)
          (goto NoMore)))
       (goto Init)))))
  (define delayed-send-no-timeout-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (NoAddr) (response-target)
          (goto HaveAddr response-target))
        (define-state (HaveAddr [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target 1)
            (goto HaveAddr new-response-target))))
       (goto NoAddr)))))
  (define delayed-send-with-timeout-actor
    (term
     (((Addr Nat) (addr 0))
      (((define-state (NoAddr) (response-target)
          (goto HaveAddr response-target))
        (define-state (HaveAddr [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target 1)
            (goto HaveAddr new-response-target))
          [(timeout 5)
           (begin
             (send response-target 2)
             (goto NoAddr))]))
       (goto NoAddr)))))

  (test-valid-instance? request-response-spec)
  (test-valid-instance? request-same-response-addr-spec)
  (test-valid-actor? request-response-actor)
  (test-valid-actor? respond-to-first-addr-actor)
  (test-valid-actor? respond-to-first-addr-actor2)
  (test-valid-actor? double-response-actor)
  (test-valid-actor? delay-saving-address-actor)
  (test-valid-actor? respond-once-actor)
  (test-valid-actor? delayed-send-no-timeout-actor)
  (test-valid-actor? delayed-send-with-timeout-actor)
  (test-true "request/response 1"
             (check-conformance/config (make-single-actor-config request-response-actor)
                          (make-exclusive-spec request-response-spec)))

  (test-false "request/response 2"
              (check-conformance/config (make-single-actor-config respond-to-first-addr-actor)
                           (make-exclusive-spec request-response-spec)))
  (test-false "request/response 3"
               (check-conformance/config (make-single-actor-config respond-to-first-addr-actor2)
                            (make-exclusive-spec request-response-spec)))
  (test-false "request/response 4"
               (check-conformance/config (make-single-actor-config request-response-actor)
                            (make-exclusive-spec request-same-response-addr-spec)))
  (test-false "ignore all actor does not satisfy request/response"
              (check-conformance/config (make-ignore-all-config (term (Addr Nat)))
                           (make-exclusive-spec request-response-spec)))
  (test-false "Respond-once actor does not satisfy request/response"
              (check-conformance/config (make-single-actor-config respond-once-actor)
                           (make-exclusive-spec request-response-spec)))
  (check-true (check-conformance/config (make-single-actor-config respond-to-first-addr-actor)
                           (make-exclusive-spec request-same-response-addr-spec)))
  (check-true (check-conformance/config (make-single-actor-config respond-to-first-addr-actor2)
                           (make-exclusive-spec request-same-response-addr-spec)))
  (check-false (check-conformance/config (make-single-actor-config double-response-actor)
                            (make-exclusive-spec request-response-spec)))
  (check-false (check-conformance/config (make-single-actor-config delay-saving-address-actor)
                            (make-exclusive-spec request-response-spec)))
  (test-false "Send only on next receive does not satisfy request/response"
               (check-conformance/config (make-single-actor-config delayed-send-no-timeout-actor)
                            (make-exclusive-spec request-response-spec)))
  (check-true (check-conformance/config (make-single-actor-config delayed-send-with-timeout-actor)
                           (make-exclusive-spec request-response-spec)))

  (define (make-self-send-response-actor addr-number)
    (let ([self-addr (term (addr ,addr-number (Union [FromEnv (Addr Nat)] [FromSelf (Addr Nat)])))])
      (term
       (,self-addr
        (((define-state (Always) (msg)
            (case msg
              [(FromEnv response-target)
               (begin
                 (send ,self-addr (variant FromSelf response-target))
                 (goto Always))]
              [(FromSelf response-target)
               (begin
                 (send response-target 0)
                 (goto Always))])))
         (goto Always))))))

  (define from-env-request-response-spec
    (term
     (((define-state (Always)
         [(variant FromEnv response-target) -> ([obligation response-target *]) (goto Always)]))
      (goto Always)
      (addr 0 (Union [FromEnv (Addr Nat)])))))

  (define from-env-wrapper
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Always [sender (Addr (Union [FromEnv (Addr Nat)]))]) (msg)
          (begin
            (send sender (variant FromEnv msg))
            (goto Always sender))))
       (goto Always (addr 1 (Union [FromEnv (Addr Nat)])))))))

  (test-valid-actor? (make-self-send-response-actor 0))
  (test-valid-instance? from-env-request-response-spec)
  (test-true "Can self-send, then send out to satisfy dynamic request/response"
    (check-conformance/config (make-single-actor-config (make-self-send-response-actor 0))
                              (make-exclusive-spec from-env-request-response-spec)))
  (test-true "From-env wrapper with self-send sender"
    (check-conformance/config (make-empty-queues-config (list from-env-wrapper)
                                                        (list (make-self-send-response-actor 1)))
                              (make-exclusive-spec request-response-spec)))

  ;; When given two choices to/from same state, have to take the one where the outputs match the
  ;; commitments
  (define reply-once-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (send r 0)
            (goto B)))
        (define-state (B) (r) (goto B)))
       (goto A)))))
  (define maybe-reply-spec
    (term
     (((define-state (A)
         [r -> ([obligation r *]) (goto B)]
         [r -> () (goto B)])
       (define-state (B)
         [* -> () (goto B)]))
      (goto A)
      (addr 0 (Addr Nat)))))

  (test-valid-actor? reply-once-actor)
  (test-valid-instance? maybe-reply-spec)
  (check-true (check-conformance/config (make-single-actor-config reply-once-actor)
                           (make-exclusive-spec maybe-reply-spec)))

  ;;;; Non-deterministic branching in spec

  (define zero-nonzero-spec
    (term
     (((define-state (S1 r)
         [* -> ([obligation r (variant Zero)])    (goto S1 r)]
         [* -> ([obligation r (variant NonZero)]) (goto S1 r)]))
      (goto S1 ,(make-static-response-address `(Union [NonZero] [Zero])))
      (addr 0 Nat))))
  (define zero-spec
    (term
     (((define-state (S1 r)
         [* -> ([obligation r (variant Zero)]) (goto S1 r)]))
      (goto S1 ,static-response-address)
      (addr 0 Nat))))
  (define primitive-branch-actor
    (term
     ((addr 0 Nat)
      (((define-state (S1 [dest (Addr (Union [NonZero] [Zero]))]) (i)
          (begin
            (case (< 0 i)
              [(True) (send dest (variant NonZero))]
              [(False) (send dest (variant Zero))])
            (goto S1 dest))))
       (goto S1 ,(make-static-response-address `(Union [NonZero] [Zero])))))))

  (test-valid-instance? static-response-spec)
  (test-valid-instance? zero-nonzero-spec)
  (test-valid-instance? zero-spec)
  (test-valid-actor? primitive-branch-actor)

  (test-true "Zero/NonZero"
    (check-conformance/config (make-single-actor-config primitive-branch-actor)
                              (make-exclusive-spec zero-nonzero-spec)))
  (test-false "Zero"
    (check-conformance/config (make-single-actor-config primitive-branch-actor)
                              (make-exclusive-spec zero-spec)))

  ;;;; Optional Commitments
  (define optional-commitment-spec
    (term
     (((define-state (Always r)
         [* -> ([obligation r *]) (goto Always r)]
         [* -> () (goto Always r)]))
      (goto Always (addr 1 (Addr Nat)))
      (addr 0 Nat))))

  (test-valid-instance? optional-commitment-spec)
  (check-true (check-conformance/config ignore-all-config (make-exclusive-spec optional-commitment-spec)))

  ;;;; Stuck states in concrete evaluation

  (define nat-to-nat-spec
    (term
     (((define-state (Always response-dest)
         [* -> ([obligation response-dest *]) (goto Always response-dest)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (define div-by-one-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 1))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define div-by-zero-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))

  (test-valid-instance? nat-to-nat-spec)
  (test-valid-actor? div-by-zero-actor)
  (test-valid-actor? div-by-one-actor)

  (test-true "Div by one vs. nat-to-nat spec"
             (check-conformance/config (make-single-actor-config div-by-one-actor)
                          (make-exclusive-spec nat-to-nat-spec)))
  (test-true "Div by zero vs. nat-to-nat spec"
              (check-conformance/config (make-single-actor-config div-by-zero-actor)
                           (make-exclusive-spec nat-to-nat-spec)))

  ;;;; Unobservable communication

  ;; wildcard unobservables are ignored for the purpose of output commitments
  (test-true "request/response actor vs. ignore-all spec"
             (check-conformance/config (make-single-actor-config request-response-actor)
                          (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))

  ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect
  ;; conformance
  (test-true "request response actor and spec, with unobs communication"
             (check-conformance/config (make-single-actor-config request-response-actor)
                          (make-spec request-response-spec (list '(addr 0 (Addr Nat))))))

  ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
  (test-false "static response with unobs communication"
              (check-conformance/config (make-single-actor-config static-response-actor)
                           (make-spec static-response-spec (list '(addr 0 Nat)))))

  ;; 3. Conformance regained for static req/resp when add an unobs transition
  (define static-response-spec-with-unobs
    (term
     (((define-state (Always response-dest)
         [*     -> ([obligation response-dest *]) (goto Always response-dest)]
         [unobs -> ([obligation response-dest *]) (goto Always response-dest)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (test-valid-instance? static-response-spec-with-unobs)

  (test-true "static response with unobs, incl in spec"
             (check-conformance/config (make-single-actor-config static-response-actor)
                          (make-spec static-response-spec-with-unobs (list '(addr 0 Nat)))))

  ;; 4. unobs causes a particular behavior (like connected/error in TCP)
  (define obs-unobs-static-response-address
    (make-static-response-address (term (Union (TurningOn) (TurningOff)))))
  (define unobs-toggle-spec
    (term (((define-state (Off r)
              [* -> ([obligation r (variant TurningOn)]) (goto On r)])
            (define-state (On r)
              [* -> () (goto On r)]
              [unobs -> ([obligation r (variant TurningOff)]) (goto Off r)]))
           (goto Off ,obs-unobs-static-response-address)
           (addr 0 (Union [FromObserver])))))
  (define unobs-toggle-actor
    (term
     ((addr 0 (Union [FromObserver] [FromUnobservedEnvironment]))
      (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver)
             (begin
               (send r (variant TurningOn))
               (goto On r))]
            [(FromUnobservedEnvironment) (goto Off r)]))
        (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto On r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOff))
               (goto Off r))])))
       (goto Off ,obs-unobs-static-response-address)))))
  (define unobs-toggle-actor-wrong1
    (term
     ((addr 0 (Union [FromObserver] [FromUnobservedEnvironment]))
      (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver)
             (begin
               (send r (variant TurningOn))
               ;; Going to Off instead of On
               (goto Off r))]
            [(FromUnobservedEnvironment) (goto Off r)]))
        (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto On r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOff))
               (goto Off r))])))
       (goto Off ,obs-unobs-static-response-address)))))
  (define unobs-toggle-actor-wrong2
    (term
     ((addr 0 (Union [FromObserver] [FromUnobservedEnvironment]))
      (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver)
             (begin
               (send r (variant TurningOn))
               (goto On r))]
            [(FromUnobservedEnvironment) (goto On r)]))
        (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto On r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOff))
               (goto Off r))])))
       (goto Off ,obs-unobs-static-response-address)))))
  (define unobs-toggle-actor-wrong3
    (term
     ((addr 0 (Union [FromObserver] [FromUnobservedEnvironment]))
      (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver)
             (begin
               (send r (variant TurningOn))
               (goto On r))]
            [(FromUnobservedEnvironment) (goto Off r)]))
        (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto On r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOff))
               (goto On r))])))
       (goto Off ,obs-unobs-static-response-address)))))
  (define unobs-toggle-actor-wrong4
    (term
     ((addr 0 (Union [FromObserver] [FromUnobservedEnvironment]))
      (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto Off r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOn))
               (goto On r))]))
        (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
          (case m
            [(FromObserver) (goto On r)]
            [(FromUnobservedEnvironment)
             (begin
               (send r (variant TurningOff))
               (goto Off r))])))
       (goto Off ,obs-unobs-static-response-address)))))

  (test-valid-instance? unobs-toggle-spec)
  (test-valid-actor? unobs-toggle-actor)
  (test-valid-actor? unobs-toggle-actor-wrong1)
  (test-valid-actor? unobs-toggle-actor-wrong2)
  (test-valid-actor? unobs-toggle-actor-wrong3)
  (test-valid-actor? unobs-toggle-actor-wrong4)

  (test-true "Obs/Unobs test"
             (check-conformance/config (make-single-actor-config unobs-toggle-actor)
                          (make-spec unobs-toggle-spec (list '(addr 0 (Union [FromUnobservedEnvironment]))))))

  (for ([actor (list unobs-toggle-actor-wrong1
                     unobs-toggle-actor-wrong2
                     unobs-toggle-actor-wrong3
                     unobs-toggle-actor-wrong4)])
    (test-false "Obs/Unobs bug-finding test(s)"
                (check-conformance/config (make-single-actor-config actor)
                             (make-spec unobs-toggle-spec (list '(addr 0 (Union [FromUnobservedEnvironment])))))))

  ;;;; Records

  (define record-req-resp-spec
    (term
     (((define-state (Always)
         [(record [dest dest] [msg (variant A)]) -> ([obligation dest (variant A)]) (goto Always)]
         [(record [dest dest] [msg (variant B)]) -> ([obligation dest (variant B)]) (goto Always)]))
      (goto Always)
      (addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])])))))
  (define record-req-resp-actor
    (term
     ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
      (((define-state (Always) (m)
          (begin
            (send (: m dest) (: m msg))
            (goto Always))))
       (goto Always)))))
  (define record-req-wrong-resp-actor
    (term
     ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
      (((define-state (Always) (m)
          (begin
            (send (: m dest) (variant A))
            (goto Always))))
       (goto Always)))))

  (test-valid-instance? record-req-resp-spec)
  (test-valid-actor? record-req-resp-actor)
  (test-valid-actor? record-req-wrong-resp-actor)

  (test-true "record 1"
             (check-conformance/config (make-single-actor-config record-req-resp-actor)
                          (make-exclusive-spec record-req-resp-spec)))
  (test-false "record 2"
              (check-conformance/config (make-single-actor-config record-req-wrong-resp-actor)
                           (make-exclusive-spec record-req-resp-spec)))

  ;;;; Recursive Types
  (define log-list-type (term (minfixpt LogList (Union [Null] [Cons Nat LogList]))))
  (define cons-inputs-echo
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-address (Addr Nat)]
                              [input-log ,log-list-type]) (m)
          (begin
            (send response-address (variant Ack 0))
            (goto Always
                  response-address
                  (fold ,log-list-type (variant Cons input-log))))))
       (goto Always ,static-response-address (folded ,log-list-type (variant Null)))))))

  (test-valid-actor? cons-inputs-echo)

  (test-true "Abstraction can deal with unboundedly large recursively typed values"
   (check-conformance/config
    (make-single-actor-config cons-inputs-echo)
    (make-exclusive-spec static-response-spec)))

  ;;;; Let
  (define static-response-let-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (let ([new-r response-dest])
            (begin
              (send new-r (variant Ack 0))
              (goto Always new-r)))))
       (goto Always ,static-response-address)))))
  (define static-double-response-let-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (let ([new-r response-dest])
            (begin
              (send new-r (variant Ack 0))
              (send new-r (variant Ack 0))
              (goto Always new-r)))))
       (goto Always ,static-response-address)))))

  (test-valid-actor? static-response-let-actor)
  (test-valid-actor? static-double-response-let-actor)

  (test-true "Let 1"
             (check-conformance/config (make-single-actor-config static-response-let-actor)
                          (make-exclusive-spec static-response-spec)))
  (test-false "Let 2"
              (check-conformance/config (make-single-actor-config static-double-response-let-actor)
                           (make-exclusive-spec static-response-spec)))

  ;; Check that = gives both results
  (define equal-actor-wrong1
    (term
     ((addr 0 Nat)
      (((define-state (A [dest (Addr Nat)]) (m)
          (begin
            (send dest 0)
            (case (= m 0)
              [(True) (goto A dest)]
              [(False) (goto B)])))
        (define-state (B) (m) (goto B)))
       (goto A ,static-response-address)))))
  (define equal-actor-wrong2
    (term
     ((addr 0 Nat)
      (((define-state (A [dest (Addr Nat)]) (m)
          (begin
            (send dest 0)
            (case (= m 0)
              [(True) (goto B)]
              [(False) (goto A dest)])))
        (define-state (B) (m) (goto B)))
       (goto A ,static-response-address)))))
    (define equal-actor
    (term
     ((addr 0 Nat)
      (((define-state (A [dest (Addr Nat)]) (m)
          (begin
            (send dest 0)
            (case (= m 0)
              [(True) (goto B dest)]
              [(False) (goto A dest)])))
        (define-state (B [dest (Addr Nat)]) (m)
          (begin
            (send dest 0)
            (goto B dest))))
       (goto A ,static-response-address)))))

  (test-valid-actor? equal-actor-wrong1)
  (test-valid-actor? equal-actor-wrong2)
  (test-valid-actor? equal-actor)

  (test-false "Equal actor wrong 1"
   (check-conformance/config (make-single-actor-config equal-actor-wrong1)
            (make-exclusive-spec static-response-spec)))
  (test-false "Equal actor wrong 2"
   (check-conformance/config (make-single-actor-config equal-actor-wrong2)
            (make-exclusive-spec static-response-spec)))
  (check-true
   (check-conformance/config (make-single-actor-config equal-actor)
                (make-exclusive-spec static-response-spec)))

  ;;;; For loops
  (define loop-do-nothing-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (m)
          (begin
            (for/fold ([folded-result 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define loop-send-unobs-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A [r (Addr Nat)]) (m)
          (begin
            (for/fold ([folded-result 0])
                      ([i (list 1 2 3)])
              (send r i))
            (goto A r))))
       (goto A ,static-response-address)))))
  (define send-before-loop-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (send r 0)
            (for/fold ([folded-result 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define send-inside-loop-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (for/fold ([folded-result 0])
                      ([r (list r)])
              (send r 0))
            (goto A))))
       (goto A)))))
  (define send-after-loop-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (for/fold ([folded-result 0])
                      ([i (list 1 2 3)])
              i)
            (send r 0)
            (goto A))))
       (goto A)))))

  (test-valid-actor? loop-do-nothing-actor)
  (test-valid-actor? loop-send-unobs-actor)
  (test-valid-actor? send-before-loop-actor)
  (test-valid-actor? send-inside-loop-actor)
  (test-valid-actor? send-after-loop-actor)

  (check-true (check-conformance/config (make-single-actor-config loop-do-nothing-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (check-conformance/config (make-single-actor-config loop-send-unobs-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (check-conformance/config (make-single-actor-config send-before-loop-actor)
                           (make-exclusive-spec request-response-spec)))
  (check-false (check-conformance/config (make-single-actor-config send-inside-loop-actor)
                           (make-exclusive-spec request-response-spec)))
  (check-true (check-conformance/config (make-single-actor-config send-after-loop-actor)
                           (make-exclusive-spec request-response-spec)))

  ;;;; Timeouts

  (define timeout-spec
    (term
     (((define-state (A r)
         [* -> ([obligation r (variant GotMessage)]) (goto A r)]
         [unobs -> ([obligation r (variant GotTimeout)]) (goto A r)]))
      (goto A ,(make-static-response-address `(Union (GotMessage) (GotTimeout))))
      (addr 0 Nat))))
  (define got-message-only-spec
    (term
     (((define-state (A r)
         [* -> ([obligation r (variant GotMessage)]) (goto A r)]))
      (goto A ,(make-static-response-address `(Union (GotMessage) (GotTimeout))))
      (addr 0 Nat))))
  (define timeout-and-send-actor
    (term
     ((addr 0 Nat)
      (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
          (begin
            (send r (variant GotMessage))
            (goto A r))
          [(timeout 5)
           (begin
             (send r (variant GotTimeout))
             (goto A r))]))
       (goto A ,(make-static-response-address `(Union (GotMessage) (GotTimeout))))))))
  (define timeout-to-send-actor
    (term
     ((addr 0 Nat)
      (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
          (goto SendOnTimeout r))
        (define-state (SendOnTimeout [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
          (begin
            (send r (variant GotMessage))
            (goto SendOnTimeout r))
          [(timeout 5)
           (begin
             (send r (variant GotMessage))
             (goto A r))]))
       (goto A ,(make-static-response-address `(Union (GotMessage) (GotTimeout))))))))
  (define spawn-timeout-sender-actor
    (term
     ((addr 0 Nat)
      (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
          (begin
            (spawn 3 Nat (goto B)
                   (define-state (B) (m)
                     (goto B)
                     [(timeout 5)
                      (begin
                        (send r (variant GotMessage))
                        (goto Done))])
                   (define-state (Done) (m)
                     (goto Done)))
            (goto A r))))
       (goto A ,(make-static-response-address `(Union (GotMessage) (GotTimeout))))))))

  (test-valid-instance? timeout-spec)
  (test-valid-instance? got-message-only-spec)
  (test-valid-actor? timeout-and-send-actor)
  (test-valid-actor? timeout-to-send-actor)
  (test-valid-actor? spawn-timeout-sender-actor)
  (test-true "Timeout and send vs. timeout spec"
    (check-conformance/config (make-single-actor-config timeout-and-send-actor)
                              (make-exclusive-spec timeout-spec)))
  (test-false "Timeout and send vs. got-messaage-only spec"
    (check-conformance/config (make-single-actor-config timeout-and-send-actor)
                              (make-exclusive-spec got-message-only-spec)))
  (test-false "Timeout to send vs. timeout spec"
    (check-conformance/config (make-single-actor-config timeout-to-send-actor)
                              (make-exclusive-spec timeout-spec)))
  ;; we would expect this to pass, except the abstraction is too coarse
  (test-false "Spawn timeout sender"
    (check-conformance/config (make-single-actor-config spawn-timeout-sender-actor)
                              (make-exclusive-spec timeout-spec)))

  ;; Multiple Disjoint Actors
  (define static-response-actor2
    (term
     ((addr 1 Nat)
      (((define-state (Always2 [response-dest (Addr (Union [Ack Nat]))]) (m)
             (begin
               (send response-dest (variant Ack 0))
               (goto Always2 response-dest))))
       (goto Always2 ,static-response-address)))))
  (define other-static-response-actor
    (term
     ((addr 1 Nat)
      (((define-state (Always2 [response-dest (Addr (Union [Ack Nat]))]) (m)
             (begin
               (send response-dest (variant Ack 0))
               (goto Always2 response-dest))))
       (goto Always2 (addr 3 (Union [Ack Nat])))))))
  (define static-response-with-extra-spec
    (term
     (((define-state (Always response-dest)
         [* -> ([obligation response-dest *]) (goto Always response-dest)]
         [unobs -> ([obligation response-dest *]) (goto Always response-dest)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))

  (test-valid-actor? static-response-actor2)
  (test-valid-actor? other-static-response-actor)
  (test-valid-instance? static-response-with-extra-spec)

  (test-false "Multi actor test 1"
              (check-conformance/config
                (make-empty-queues-config (list static-response-actor static-response-actor2) null)
                (make-spec static-response-spec (list '(addr 1 Nat)))))
  (test-true "Multi actor test 2"
             (check-conformance/config
              (make-empty-queues-config (list static-response-actor static-response-actor2) null)
              (make-spec static-response-with-extra-spec (list '(addr 1 Nat)))))
  (test-true "Multi actor test 3"
             (check-conformance/config
               (make-empty-queues-config (list static-response-actor other-static-response-actor) null)
               (make-spec static-response-spec (list '(addr 1 Nat)))))

  ;; Actors working together
  (define statically-delegating-responder-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A [responder (Addr (Addr Nat))]) (m)
          (begin
            (send responder m)
            (goto A responder))))
       (goto A (addr 1 (Addr Nat)))))))

  (define request-response-actor2
    (term
     ((addr 1 (Addr Nat))
      (((define-state (Always) (response-target)
          (begin
            (send response-target 0)
            (goto Always))))
       (goto Always)))))

  (test-valid-actor? statically-delegating-responder-actor)
  (test-valid-actor? request-response-actor2)

  (test-true "Multiple actors 3"
             (check-conformance/config
              (make-empty-queues-config (list request-response-actor2 statically-delegating-responder-actor) null)
              (make-exclusive-spec request-response-spec)))

  ;; TODO: tests for:
  ;; * commitment satisfied immediately
  ;; * satisfied in a later internal send
  ;; * satisfied only if another receive comes in
  ;; * never satisfied
  ;; * satisfied only if no other receive comes in

  ;; TODO: test for obs/unobs receptionists changing over time

  ;;;; Self Reveal
  (define self-reveal-spec
    (term
     (((define-state (Init r)
         [unobs -> ([obligation r self]) (goto Running)])
       (define-state (Running)
         [r -> ([obligation r *]) (goto Running)]))
      (goto Init (addr 1 (Addr (Addr Nat))))
      UNKNOWN)))

  (define self-reveal-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
          (goto Init r)
          [(timeout 5)
           (begin
             (send r (addr 0 (Addr Nat)))
             (goto Running))])
        (define-state (Running) (r)
          (begin
            (send r 1)
            (goto Running))))
       (goto Init (addr 1 (Addr (Addr Nat))))))))

  ;; TODO: redo this test in a type-correct way, with a second ignore-all actor
  ;; (define reveal-wrong-address-actor
  ;;   (term
  ;;    ((addr 0 (Addr Nat))
  ;;     (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
  ;;         (goto Init r)
  ;;         [(timeout 5)
  ;;          (begin
  ;;            (send r r)
  ;;            (goto Running))])
  ;;       (define-state (Running) (r)
  ;;         (begin
  ;;           (send r 1)
  ;;           (goto Running))))
  ;;      (goto Init (addr 1))))))

  (define reveal-self-double-output-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
          (goto Init r)
          [(timeout 5)
           (begin
             (send r (addr 0 (Addr Nat)))
             (goto Running))])
        (define-state (Running) (r)
          (begin
            (send r 1)
            (send r 1)
            (goto Running))))
       (goto Init (addr 1 (Addr (Addr Nat))))))))

  ;; TODO: do a version of this test with an ignore-all actor rather than double-send

  (test-valid-actor? self-reveal-actor)
  ;; TODO: redo this test later
  ;; (check-not-false ( reveal-wrong-address-actor))
  (test-valid-actor? reveal-self-double-output-actor)
  (test-valid-instance? self-reveal-spec)

  (test-true "Reveal self works"
             (check-conformance/config
              (make-single-actor-config self-reveal-actor)
              (make-exclusive-spec self-reveal-spec)))
  ;; TODO: redo this test later
  ;; (test-false "Catch self-reveal of wrong address"
  ;;             (check-conformance/config
  ;;              (make-single-actor-config reveal-wrong-address-actor)
  ;;              self-reveal-spec
  ;;              (term ((addr 0 (Addr (Addr (Addr Nat)))))) null
  ;;              (hash)))
  (test-false "Catch self-reveal of actor that doesn't follow its behavior"
              (check-conformance/config
               (make-single-actor-config reveal-self-double-output-actor)
               (make-exclusive-spec self-reveal-spec)))

  ;; TODO: write tests for when we try to reveal it twice, but the second time the address doesn't
  ;; match the first one

  ;;;; Spawn
  (define echo-spawning-actor
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always) (response-target)
          (begin
            ;; TODO: refactor this as a new use of the dynamic response actor above
            (let ([child
                   (spawn
                    echo-spawn
                    (Addr Nat)
                    (goto EchoResponse)
                    (define-state (EchoResponse) (echo-target)
                      (begin
                        (send echo-target 1)
                        (goto EchoResponse))))])
              (begin
                (send response-target child)
                (goto Always))))))
       (goto Always)))))

  (define double-response-spawning-actor
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always) (response-target)
          (begin
            ;; TODO: refactor this as a new use of the dynamic response actor above
            (let ([child
                   (spawn
                    double-response-spawn
                    (Addr Nat)
                    (goto DoubleResponse)
                    (define-state (DoubleResponse) (echo-target)
                      (begin
                        (send echo-target 1)
                        (send echo-target 1)
                        (goto NoResponse))))])
              (begin
                (send response-target child)
                (goto Always))))))
       (goto Always)))))

  (define echo-spawn-spec
    (term
     (((define-state (Always)
         [r -> ([obligation r (fork
                               (goto EchoResponse)
                               (define-state (EchoResponse)
                                 [er -> ([obligation er *]) (goto EchoResponse)]))])
               (goto Always)]))
      (goto Always)
      (addr 0 (Addr (Addr (Addr Nat)))))))

  (test-valid-actor? echo-spawning-actor)
  (test-valid-actor? double-response-spawning-actor)
  (test-valid-instance? echo-spawn-spec)

  (test-true "Spawned echo matches dynamic response spec"
             (check-conformance/config
              (make-single-actor-config echo-spawning-actor)
              (make-exclusive-spec echo-spawn-spec)))
  ;; TODO: also add a sink-spawning actor when commitment satisfaction is working
  (test-false "Spawned double-response actor does not match dynamic response spec"
              (check-conformance/config
               (make-single-actor-config double-response-spawning-actor)
               (make-exclusive-spec echo-spawn-spec)))

  ;;;; Initial spec address must have actor in the implmentation
  (define no-matching-address-spec
    (term
     (((define-state (DoAnything)
         [* -> () (goto DoAnything)]))
      (goto DoAnything)
      (addr 500 Nat))))
  (test-valid-instance? no-matching-address-spec)

  (test-false "Spec config address must have matching actor in implementation configuration"
   (check-conformance/config
    (make-single-actor-config static-response-actor)
    (make-exclusive-spec no-matching-address-spec)))

  (define spawn-and-retain
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always [maybe-child (Union [NoChild] [Child (Addr (Addr Nat))])]) (dest)
          (let ([new-child
                 (spawn
                  echo-spawn
                  (Addr Nat)
                  (goto EchoResponse)
                  (define-state (EchoResponse) (echo-target)
                    (begin
                      (send echo-target 1)
                      (goto EchoResponse))))])
            (case maybe-child
              [(NoChild)
               (begin
                 (send dest new-child)
                 (goto Always (variant Child new-child)))]
              [(Child old-child)
               (begin
                 (send dest old-child)
                 (goto Always (variant Child old-child)))]))))
       (goto Always (variant NoChild))))))

  (define spawn-and-retain-but-send-new
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always [maybe-child (Union [NoChild] [Child (Addr (Addr Nat))])]) (dest)
          (let ([new-child
                 (spawn
                  echo-spawn
                  (Addr Nat)
                  (goto EchoResponse)
                  (define-state (EchoResponse) (echo-target)
                    (begin
                      (send echo-target 1)
                      (goto EchoResponse))))])
            (case maybe-child
              [(NoChild)
               (begin
                 (send dest new-child)
                 (goto Always (variant Child new-child)))]
              [(Child old-child)
               (begin
                 (send dest new-child)
                 (goto Always (variant Child old-child)))]))))
       (goto Always (variant NoChild))))))

  (test-valid-actor? spawn-and-retain)
  (test-valid-actor? spawn-and-retain-but-send-new)

  (test-true "Both an old and new version of spawned echo child match stateless spec"
    (check-conformance/config
     (make-single-actor-config spawn-and-retain)
     (make-exclusive-spec echo-spawn-spec)))

  (test-true "Always sending new version of child matches echo-spawn"
    (check-conformance/config
     (make-single-actor-config spawn-and-retain-but-send-new)
     (make-exclusive-spec echo-spawn-spec)))

  ;; TODO: try variations on this test. E.g., send child address during its constructor rather than in
  ;; a later timeout, have spec have one state for child instead of two, etc.
  (define spawn-self-revealing-echo
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always) (response-target)
          (begin
            (spawn
             echo-spawn
             (Addr Nat)
             (goto Init response-target)
             (define-state (Init [response-target (Addr (Addr (Addr Nat)))]) (response-target)
               (goto Init response-target)
               [(timeout 0)
                (begin
                  (send response-target self)
                  (goto EchoResponse))])
             (define-state (EchoResponse) (echo-target)
               (begin
                 (send echo-target 1)
                 (goto EchoResponse))))
            (goto Always))))
       (goto Always)))))

  (define child-self-reveal-spec
    (term
     (((define-state (Always)
         [r -> ([fork (goto Init r)
                      (define-state (Init r)
                        [unobs -> ([obligation r self]) (goto EchoResponse)])
                      (define-state (EchoResponse)
                        [er -> ([obligation er *]) (goto EchoResponse)])])
            (goto Always)]))
      (goto Always)
      (addr 0 (Addr (Addr (Addr Nat)))))))

  (test-valid-actor? spawn-self-revealing-echo)
  (test-valid-instance? child-self-reveal-spec)
  (test-true "Spawned child can reveal self"
    (check-conformance/config
     (make-single-actor-config spawn-self-revealing-echo)
     (make-exclusive-spec child-self-reveal-spec)))

  ;;;; Blur Tests

  (define send-to-blurred-internal-actor-and-response
    ;; Third time through, send to that actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [static-output (Addr (Union [Ack Nat]))]
                              [saved-internal (Union [None]
                                                     [First (Addr (Addr (Union [Ack Nat])))]
                                                     [Second (Addr (Addr (Union [Ack Nat])))])]) (m)
          (let ([new-child
                 (spawn child-loc
                        (Addr (Union [Ack Nat]))
                        (goto InternalAlways)
                        (define-state (InternalAlways) (m)
                          (begin
                            (send m (variant Ack 1))
                          (goto InternalAlways))))])
            (begin
              (send static-output (variant Ack 0))
              (case saved-internal
                [(None) (goto Always static-output (variant First new-child))]
                [(First saved) (goto Always static-output (variant Second saved))]
                [(Second saved)
                 (begin
                   ;; at this point, "saved" should have already been blurred out
                   (send saved static-output)
                   (goto Always static-output (variant Second saved)))])))))
       (goto Always ,static-response-address (variant None))))))

  (test-valid-actor? send-to-blurred-internal-actor-and-response)

  (test-false "Sending precise address to blurred sending actor causes non-conformance"
    (check-conformance/config
     (make-single-actor-config send-to-blurred-internal-actor-and-response)
     (make-exclusive-spec static-response-spec)))

  (define send-to-blurred-internal-actor
    ;; Third time through, send to that actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [static-output (Addr (Union [Ack Nat]))]
                              [saved-internal (Union [None]
                                                     [First (Addr (Addr (Union [Ack Nat])))]
                                                     [Second (Addr (Addr (Union [Ack Nat])))])]) (m)
          (let ([new-child
                 (spawn child-loc
                        (Addr (Union [Ack Nat]))
                        (goto InternalAlways)
                        (define-state (InternalAlways) (m)
                          (begin
                            (send m (variant Ack 1))
                          (goto InternalAlways))))])
            (case saved-internal
              [(None) (goto Always static-output (variant First new-child))]
              [(First saved) (goto Always static-output (variant Second saved))]
              [(Second saved)
               (begin
                 ;; at this point, "saved" should have already been blurred out
                 (send saved static-output)
                 (goto Always static-output (variant Second saved)))]))))
       (goto Always ,static-response-address (variant None))))))

  (define never-send-spec
    (term
     (((define-state (Always r)
         [* -> () (goto Always r)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (define send-whenever-spec
    (term
     (((define-state (Always r)
         [* -> () (goto Always r)]
         [unobs -> ([obligation r *]) (goto Always r)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))

  (test-valid-actor? send-to-blurred-internal-actor)
  (test-valid-instance? send-whenever-spec)
  (test-valid-instance? never-send-spec)
  (test-true "Sending message to blurred-internal matches send-whenever spec"
    (check-conformance/config
     (make-single-actor-config send-to-blurred-internal-actor)
     (make-exclusive-spec send-whenever-spec)))
  (test-false "Sending message to blurred-internal does not match never-send spec"
    (check-conformance/config
     (make-single-actor-config send-to-blurred-internal-actor)
     (make-exclusive-spec never-send-spec)))

  (define self-send-responder-spawner
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Always) (dest)
          (begin
            (spawn child-loc
                   (Addr Nat)
                   (begin
                     (send self 1)
                     (goto AboutToSend dest))
                   (define-state (AboutToSend [dest (Addr Nat)]) (m)
                     (begin
                       (send dest 1)
                       (goto Done)))
                   (define-state (Done) (m) (goto Done)))
            (goto Always))))
       (goto Always)))))

  (test-valid-actor? self-send-responder-spawner)
  (test-true "Child can wait at least one handler-cycle before sending to destination"
    (check-conformance/config
     (make-single-actor-config self-send-responder-spawner)
     (make-exclusive-spec request-response-spec)))

  ;; Actor that creates a worker to handle each new request, where the worker then sends the result
  ;; back to another statically-known actor for sending back to the client
  ;;
  ;; TODO: do a version of this that sends to the actor instead of closing over the address
  (define forwarding-type (term (Record [result Nat] [dest (Addr Nat)])))
  (define (make-down-and-back-server child-behavior)
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Always [forwarding-server (Addr ,forwarding-type)]) (dest)
          (begin
            (spawn child-loc ,@child-behavior)
            (goto Always forwarding-server))))
       (goto Always (addr 1 ,forwarding-type))))))

  (define timeout-forwarding-child
    (term
     (Nat
      (goto AboutToSend forwarding-server)
      (define-state (AboutToSend [forwarding-server (Addr ,forwarding-type)]) (dummy)
        (goto AboutToSend forwarding-server)
        [(timeout 0)
         (begin
           (send forwarding-server (record [result 1] [dest dest]))
           (goto Done))])
      (define-state (Done) (dummy) (goto Done)))))

  (define self-send-forwarding-child
    (term
     (Nat
      (begin
        (send self 1)
        (goto AboutToSend forwarding-server))
      (define-state (AboutToSend [forwarding-server (Addr ,forwarding-type)]) (trigger)
        (begin
          (send forwarding-server (record [result 1] [dest dest]))
          (goto Done)))
      (define-state (Done) (dummy) (goto Done)))))

  (define forwarding-server
    (term
     ((addr 1 (Record [result Nat] [dest (Addr Nat)]))
      (((define-state (ServerAlways) (rec)
          (begin
            (send (: rec dest) (: rec result))
            (goto ServerAlways))))
       (goto ServerAlways)))))

  (test-valid-actor? (make-down-and-back-server timeout-forwarding-child))
  (test-valid-actor? forwarding-server)

  (test-true "Down-and-back server with timeout child fulfills the dynamic request/response spec"
    (check-conformance/config
     (make-empty-queues-config (list (make-down-and-back-server timeout-forwarding-child))
                               (list forwarding-server))
     (make-exclusive-spec request-response-spec)))

  (test-true "Down-and-back server with self-send child fulfills the dynamic request/response spec"
    (check-conformance/config
     (make-empty-queues-config (list (make-down-and-back-server self-send-forwarding-child))
                               (list forwarding-server))
     (make-exclusive-spec request-response-spec)))

  (define create-later-send-children-actor
    (term
     ((addr 1 (Addr (Addr Nat)))
      (((define-state (Always [r (Addr Nat)]) (other-dest)
          (begin
            (send other-dest
                  (spawn child-loc Nat
                         (goto Child1)
                         (define-state (Child1) (dummy)
                           (goto Child2))
                         (define-state (Child2) (dummy)
                           (begin
                             (send r 1)
                             (goto Child2)))))
            (goto Always r))))
       (goto Always (addr 2 Nat))))))

  (test-valid-actor? create-later-send-children-actor)
  (test-false "Child that sends response in second state does not match never-send"
    ;; tests that all reachable states of a blurred child are executed
    (check-conformance/config
     (make-single-actor-config create-later-send-children-actor)
     (make-exclusive-spec never-send-spec)))

  ;; step 1: spawn the forwarder; save it
  ;; step 2: spawn the new agent (spec follows it)
  ;; step 3: new agent uses forwarder to fulfill its dynamic request/response (can't do static yet)
  (define conflicts-only-test-actor
    (term
     ((addr 0 (Addr (Addr (Addr Nat))))
      (((define-state (Always [maybe-forwarder (Union [None] [Forwarder (Addr (Addr Nat))])]) (dest)
          (let ([forwarder
                 (case maybe-forwarder
                   [(None)
                    ;; The forwarder actor takes any address it's given and sends a message to it
                    (spawn forwarder-loc (Addr Nat)
                                  (goto Forwarding)
                                  (define-state (Forwarding) (r)
                                    (begin
                                      (send r 1)
                                      (goto Forwarding))))]
                   [(Forwarder the-addr) the-addr])])
            (begin
              (send dest
                    ;; the per-request child is sent back to the client. When the client sends a
                    ;; message to the child, the message is sent to the forwarder, who sends a message
                    ;; on it
                    (spawn surfaced-loc
                           (Addr Nat)
                           (goto Responding)
                           (define-state (Responding) (r)
                             (begin
                               (send forwarder r)
                               (goto Responding)))))
              (goto Always (variant Forwarder forwarder))))))
       (goto Always (variant None))))))

  (test-true "Only spawned actors with conflicts are blurred out"
    (check-conformance/config
     (make-single-actor-config conflicts-only-test-actor)
     (make-exclusive-spec echo-spawn-spec)))

  ;;;; Abstraction past max fold depth
  (test-case "Cannot test conformance if address found below max fold depth"
    (define nat-addr-list-type `(minfixpt NatAddrList (Union [Nil] [Cons (Addr Nat) NatAddrList])))
    (check-false
     (check-conformance/config
      `((((addr 0 Nat)
          (() (folded ,nat-addr-list-type
                      (variant Cons (addr 1 Nat)
                               (folded ,nat-addr-list-type
                                       (variant Cons (addr 2 Nat)
                                                (folded ,nat-addr-list-type
                                                        (variant Nil)))))))))
        () ((addr 0 Nat)) ())
      (make-exclusive-spec static-response-spec))))

  (test-case "Cannot test conformance if address is folded into a wildcard during handler evaluation"
    (define nat-addr-list-type `(minfixpt NatAddrList (Union [Nil] [ConsIt (Addr Nat) NatAddrList])))
    (define addr-list-actor
      ;; Idea: send to the received address, then add it to the address list, then send to the second
      ;; ddress in the list (should be below the max unfold depth) if it exists. This does not conform
      ;; to the request/response spec because of the extra send, but would only be caught by checking
      ;; for addresses getting folded into wildcard values.
      (term
       ((addr 0 Nat)
        (((define-state (Always [addrs ,nat-addr-list-type]) (new-addr)
            (let ([addrs (fold ,nat-addr-list-type (variant ConsIt new-addr addrs))])
              (begin
                (send new-addr 0)
                (case (unfold ,nat-addr-list-type addrs)
                  [(Nil) 0]
                  [(ConsIt the-addr addrs)
                   (case (unfold ,nat-addr-list-type addrs)
                     [(Nil) 0]
                     [(ConsIt the-addr addrs)
                      (begin
                        (send the-addr 1)
                        0)])])
                (goto Always addrs)))))
         (goto Always (folded ,nat-addr-list-type (variant Nil)))))))

    (check-valid-actor? addr-list-actor)
    (check-false
     (check-conformance/config
      (make-single-actor-config addr-list-actor)
      (make-exclusive-spec request-response-spec))))

  ;;;; Type Coercions

  (define ping-coercion-spawner
    (term
     ((addr 0 (Addr (Addr (Union [Ping (Addr (Union [Pong]))]))))
      (((define-state (Always) (dest)
          (begin
            (send dest
                 (spawn 1
                        (Union [Ping (Addr (Union [Pong]))] [InternalOnly])
                        (goto Ready)
                        (define-state (Ready) (msg)
                          (begin
                            (case msg
                              [(Ping response-dest) (send response-dest (variant Pong))]
                              [(InternalOnly) (variant Pong)])
                            (goto Ready)))))
            (goto Always))))
       (goto Always)))))

  (define ping-coercion-spawner-spec
    (term
     (((define-state (Always)
         [r -> ([obligation r (fork
                               (goto Ready)
                               (define-state (Ready)
                                 [(variant Ping r) -> ([obligation r (variant Pong)]) (goto Ready)]))])
            (goto Always)]))
      (goto Always)
      (addr 0 (Addr (Addr (Union [Ping (Addr (Union [Pong]))])))))))

  ;; make sure that
  (test-true "Exposed addresses only expose types according to the type of the address they were exposed through"
    (check-conformance/config
     (make-single-actor-config ping-coercion-spawner)
     (make-exclusive-spec ping-coercion-spawner-spec))))
