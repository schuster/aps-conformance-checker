#lang racket

;; Implements the top-level function, "check-conformance", and includes the core of the
;; conformance-checking algorithm

(provide check-conformance)

(require
 ;; See README.md for a brief description of these files
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
    [(spec-address-in-impl? initial-impl-config initial-spec-config) #f]
    [else
     (define initial-pairs (map first (sbc (abstract-pair initial-impl-config initial-spec-config))))
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
     (andmap (curry set-member? conforming-pairs) initial-pairs)]))

;; Returns #t if the self-address for the specification configuration belongs to an actor in the
;; implementation configuration (an initial requirement for conformance), #f otherwise.
(define (spec-address-in-impl? impl-config spec-config)
  (define spec-address (aps-config-only-instance-address spec-config))
  (and (not (aps#-unknown-address? spec-address))
       (andmap (lambda (a) (not (same-address-without-type? a spec-address)))
               (csa-config-receptionists impl-config))))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; Abstracts the given concrete implementation configuration and spec config
(define (abstract-pair impl-config spec-config)
  (define internal-addresses (csa-config-internal-addresses impl-config))
  (config-pair
   (csa#-abstract-config impl-config internal-addresses)
   (aps#-abstract-config spec-config internal-addresses)))

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
  (define log-file (if LOG-PAIRS (open-output-file "related_pair_log.dat" #:exists 'replace) #f))

  (let loop ([related-pairs (set)]
             [unrelated-successors (set)])
    (match (dequeue-if-non-empty! to-visit)
      [#f
       (when LOG-PAIRS (close-output-port log-file))
       (list related-pairs unrelated-successors incoming-steps related-spec-steps)]
      [pair

       ;; Debugging
       (set! visited-pairs-count (add1 visited-pairs-count))
       (set-add! visited-impl-configs (config-pair-impl-config pair))
       (set-add! visited-spec-configs (config-pair-spec-config pair))
       ;; (printf "Current time: ~s\n" (current-seconds))
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

       (when LOG-PAIRS
         (fprintf log-file
                  "PAIR ~s (~s). ~s\n"
                  visited-pairs-count (current-seconds) (pair->debug-pair pair))
         (flush-output log-file))

       (define i (config-pair-impl-config pair))
       (define s (config-pair-spec-config pair))
       (define i-steps (impl-steps-from i s))

       ; hash from a pair (i, s) to its sbc-derivatives. We save these derivatives because we first
       ; need to check that they exist (because the blur step might fail), then add them to our
       ; worklist
       (define saved-derivatives (make-hash))

       ;; Find the matching s-steps
       (define found-unmatchable-step? #f)
       (for ([i-step i-steps])
         (match i-step
           [#f (set! found-unmatchable-step? #t)]
           [_
            ;; Debugging:
            ;; (printf "Impl step: ~s\n" (debug-impl-step i-step))

            (define matching-s-steps (matching-spec-steps s i-step))
            ;; Debugging:
            ;; (printf "Matching spec steps: ~s\n" matching-s-steps)

            (hash-set! related-spec-steps (list pair i-step) matching-s-steps)
            (when (set-empty? matching-s-steps)
              (set! found-unmatchable-step? #t))
            ;; Get all derivatives. If sbc ever fails, that step is an unmatchable step
            (for ([s-step matching-s-steps])
              (define successor-pairs
                (for/list ([config (cons (spec-step-destination s-step) (spec-step-spawns s-step))])
                  (config-pair (impl-step-destination i-step) config)))
              (match (sbc* successor-pairs)
                [#f (set! found-unmatchable-step? #t)]
                [sbc-pairs (hash-set! saved-derivatives (config-pair i-step s-step) sbc-pairs)]))]))

       ;; Add this pair to either related or unrelated set; add new worklist items
       (cond
         [found-unmatchable-step?
          ;; Some impl step has no matching spec step (or an impl step goes to a known unverifiable
          ;; configuration), so this pair is unrelated. Therefore we add it to the
          ;; unrelated-successors list and do not further explore transitions from this pair.

          ;; Debugging
          ;; (displayln "Unrelated pair")
          (loop related-pairs (set-add unrelated-successors pair))]
         [else
          ;; This pair is in the rank-1 simulation (because all of its impl steps have matching spec
          ;; steps). We have to add it to the related-pairs set, sbc each of the matching destination
          ;; pairs and add them to the work-list so that we explore this pair's successors, and add
          ;; the incoming transitions for those destination pairs to incoming-steps.

          ;; Debugging
          ;; (displayln "Related pair")
          (for ([i-step i-steps])
            (for ([s-step (hash-ref related-spec-steps (list pair i-step))])
              ;; Debugging only
              ;; (for ([successor-pair successor-pairs])
              ;;   (printf "pre-sbc: ~s\n" successor-pair)
              ;;   (printf "post-sbc: ~s\n" (sbc successor-pair)))
              (for ([sbc-result (hash-ref saved-derivatives (config-pair i-step s-step))])
                ;; TODO: add the address binding here, too, and adjust other uses of incoming (e.g. in
                ;; prune-unsupported) to take that structure into account
                (match-define (list sbc-pair rename-map) sbc-result)
                (dict-of-sets-add! incoming-steps sbc-pair (list pair i-step s-step rename-map))
                (unless (or (member sbc-pair (queue->list to-visit))
                            (set-member? related-pairs sbc-pair)
                            (set-member? unrelated-successors sbc-pair)
                            (equal? sbc-pair pair))
                  (enqueue! to-visit sbc-pair)))))
          (loop (set-add related-pairs pair) unrelated-successors)])])))

;; Returns all implementation steps possible from the given impl-config/spec-config pair. The spec
;; config is used to determine whether sending a message to a given receptionist in the implementation
;; config can be observed, unobserved, or both.
(define (impl-steps-from impl-config spec-config)
  (define (add-observed-flag transition observed?)
    (match transition
      [#f #f]
      [_
       (impl-step (csa#-transition-trigger transition)
                  observed?
                  (csa#-transition-outputs transition)
                  (csa#-transition-final-config transition))]))

  (define addr (aps#-config-only-instance-address spec-config))
  (define observed-external-receives
    (if (aps#-unknown-address? addr)
        null
        (external-message-transitions impl-config addr)))
  (define unobserved-external-receives
    (append*
     (for/list ([receptionist (aps#-config-receptionists spec-config)])
       (external-message-transitions impl-config receptionist))))

  (append (map (curryr add-observed-flag #t) observed-external-receives)
          (map (curryr add-observed-flag #f)
               (append
                unobserved-external-receives
                (csa#-handle-all-internal-actions impl-config)))))

;; Returns all possible transitions of the given implementation config caused by a received message to
;; the given receptionist address
(define (external-message-transitions impl-config receptionist)
  (display-step-line "Enumerating abstract messages (typed)")
  (append*
   (for/list ([message (csa#-messages-of-address-type receptionist)])
     (display-step-line "Evaluating a handler")
     (csa#-handle-external-message impl-config receptionist message))))

;; Returns a set of the possible spec steps (see the struct above) from the given spec config that
;; match the given implementation step
(define (matching-spec-steps spec-config i-step)
  (define matched-stepped-configs (mutable-set))
  (for ([trigger-result (aps#-matching-steps spec-config
                                             (impl-step-from-observer? i-step)
                                             (impl-step-trigger i-step))])
    (match-define (list config spawns1) trigger-result)
    (match (aps#-resolve-outputs config (impl-step-outputs i-step))
      [#f (void)]
      [(list stepped-spec-config spawns2 satisfied-commitments)
       (set-add! matched-stepped-configs
                 (spec-step stepped-spec-config (append spawns1 spawns2) satisfied-commitments))]))
  matched-stepped-configs)

(module+ test
  (define null-spec-config (make-Σ# '((define-state (S))) '(goto S) null null))

  (test-case "Null transition okay for unobs"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (init-addr 0 Nat) (* Nat)) #f null #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "Null transition not okay for observed input"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(external-receive (init-addr 0 Nat) (* Nat)) #t null #f))
     (mutable-set)))
  (test-case "No match if trigger does not match"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A) [x -> (goto A)])) '(goto A) null null)
      (impl-step '(external-receive (init-addr 0 Nat) (* Nat)) #t null #f))
     (mutable-set)))
  (test-case "Unobserved outputs don't need to match"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (init-addr 0 Nat) (* Nat)) #f (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "No match if outputs do not match"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A))) '(goto A) null (list '((obs-ext 1 Nat))))
      (impl-step '(internal-receive (init-addr 0 Nat) (* Nat)) #f (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set)))
  (test-case "Output can be matched by previous commitment"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A))) '(goto A) null (list '((obs-ext 1 Nat) (single *))))
      (impl-step '(internal-receive (init-addr 0 Nat) (* Nat)) #f (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step (make-Σ# '((define-state (A))) '(goto A) null (list '((obs-ext 1 Nat))))
                             null
                             (list `[(obs-ext 1 Nat) *])))))
  (test-case "Output can be matched by new commitment"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))])) '(goto A) null null)
      (impl-step '(external-receive (init-addr 0 Nat) (obs-ext 1 Nat)) #t (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))]))
                                      '(goto A)
                                      null
                                      (list '((obs-ext 1 Nat))))
                             null
                             (list `[(obs-ext 1 Nat) *])))))
  (test-case "Multiple copies of same commitment get merged"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) null (list '[(obs-ext 1 Nat) (single *)]))
      (impl-step '(external-receive (init-addr 0 Nat) (* Nat)) #t null #f))
     (mutable-set
      (spec-step (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) null (list '[(obs-ext 1 Nat) (many *)]))
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

;; Calls sbc on every pair and merges the results into one long list. If sbc returns #f for any pair,
;; this function returns #f.
(define (sbc* pairs)
  (define sbc-results (map sbc pairs))
  (if (ormap false? sbc-results)
      #f
      (append* sbc-results)))

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
           (((init-addr 2 Nat) (obs-ext 1 Nat) 1)
            ((init-addr 2 Nat) (obs-ext 2 Nat) 1)
            ((init-addr 2 Nat) (obs-ext 3 Nat) 1))))
    (term ((,aps#-no-transition-instance) () (((obs-ext 3 Nat))))))
   (list (term (()
                ()
                (((init-addr 2 Nat) (* (Addr Nat)) *)
                 ((init-addr 2 Nat) (obs-ext 3 Nat) 1))))
         (term ((,aps#-no-transition-instance) () (((obs-ext 3 Nat))))))))

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
    [(csa#-spawn-address? (aps#-config-only-instance-address spec-config))
     (csa#-spawn-address-flag (aps#-config-only-instance-address spec-config))]
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

  (define aa-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'A))
  (define xx-step (spec-step 'X null null))
  (define ab-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'B))
  (define xy-step (spec-step 'Y null null))
  (define xz-step (spec-step 'Z null null))
  (define bc-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'C))
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

(define LOG-PAIRS #f)

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
;; Top-level tests

(module+ test
  (define-simple-check (check-valid-actor? actual)
    (redex-match? csa-eval αn actual))

  (define-syntax (test-valid-actor? stx)
    (syntax-parse stx
      [(_ name the-term)
       #`(test-case name
           #,(syntax/loc stx (check-valid-actor? the-term)))]
      [(_ the-term)
       #`(test-begin
           #,(syntax/loc stx (check-valid-actor? the-term)))]))

  (define-simple-check (check-valid-instance? actual)
    (redex-match? aps-eval z actual))

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
      ((addr 0 ,addr-type)
       (((define-state (Always) (m) (goto Always)))
        (goto Always))))))
  (define ignore-all-config (make-ignore-all-config 'Nat))
  (define (make-ignore-all-spec-instance addr-type)
    (term
     (((define-state (Always) [* -> (goto Always)]))
      (goto Always)
      (addr 0 ,addr-type))))
  (define ignore-all-spec-instance
    (make-ignore-all-spec-instance 'Nat))
  (check-not-false (redex-match csa-eval K ignore-all-config))
  (check-not-false (redex-match aps-eval z ignore-all-spec-instance))

  (check-true (check-conformance/config ignore-all-config (make-exclusive-spec ignore-all-spec-instance)))

  ;;;; Send one message to a statically-known address per request

  (define (make-static-response-address type) (term (addr 2 ,type)))
  (define static-response-address (make-static-response-address (term (Union (Ack Nat)))))
  (define static-response-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-actor
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-response-spec
    (term
     (((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (define ignore-all-with-addr-spec-instance
    (term
     (((define-state (Always response-dest) [* -> (goto Always response-dest)]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))

  (test-valid-actor? static-response-actor)
  (test-valid-actor? static-double-response-actor)
  (test-valid-instance? static-response-spec)
  (test-valid-instance? ignore-all-with-addr-spec-instance)

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

  ;;;; Pattern matching tests, without dynamic channels

  (define pattern-match-spec
    (term
     (((define-state (Matching r)
         [(variant A *) -> (with-outputs ([r (variant A *)]) (goto Matching r))]
         [(variant B *) -> (with-outputs ([r (variant B *)]) (goto Matching r))]))
      (goto Matching ,static-response-address)
      (addr 0 (Union [A Nat] [B Nat])))))

  (define pattern-matching-actor
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A x)) (goto Always r))]
            [(B y) (begin (send r (variant B 0)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define reverse-pattern-matching-actor
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant B 0)) (goto Always r))]
            [(B y) (begin (send r (variant A y)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define partial-pattern-matching-actor
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A 0)) (goto Always r))]
            [(B y) (goto Always r)])))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match aps-eval z pattern-match-spec))
  (check-not-false (redex-match csa-eval αn pattern-matching-actor))
  (check-not-false (redex-match csa-eval αn reverse-pattern-matching-actor))
  (check-not-false (redex-match csa-eval αn partial-pattern-matching-actor))

  (check-true (check-conformance/config (make-single-actor-config pattern-matching-actor)
                           (make-exclusive-spec pattern-match-spec)))
  (test-false "Send on A but not B; should send on both"
              (check-conformance/config (make-single-actor-config partial-pattern-matching-actor)
                           (make-exclusive-spec pattern-match-spec)))
  (check-false (check-conformance/config (make-single-actor-config reverse-pattern-matching-actor)
                            (make-exclusive-spec  pattern-match-spec)))

  ;;;; Dynamic request/response

  (define request-response-spec
    (term
     (((define-state (Always)
         [response-target -> (with-outputs ([response-target *]) (goto Always))]))
      (goto Always)
      (addr 0 (Addr Nat)))))

  (define request-same-response-addr-spec
    (term
     (((define-state (Init)
         [response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))])
       (define-state (HaveAddr response-target)
         [new-response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))]))
      (goto Init)
      (addr 0 (Addr Nat)))))
  (define request-response-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Always [i Nat]) (response-target)
          (begin
            (send response-target i)
            (goto Always i))))
       (goto Always 0)))))
  (define respond-to-first-addr-actor
    (term
     ((addr 0 (Addr Nat))
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
     ((addr 0 (Addr Nat))
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
     ((addr 0 (Addr Nat))
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
    `((addr 0 (Addr Nat))
      (((define-state (Always [i Nat]) (response-dest)
          (begin
            (send response-dest i)
            (send response-dest i)
            (goto Always i))))
       (goto Always 0))))
  (define respond-once-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto NoMore)))
        (define-state (NoMore) (new-response-target)
          (goto NoMore)))
       (goto Init)))))
    (define delayed-send-no-timeout-actor
      (term
       ((addr 0 (Addr Nat))
        (((define-state (NoAddr) (response-target)
            (goto HaveAddr response-target))
          (define-state (HaveAddr [response-target (Addr Nat)]) (new-response-target)
            (begin
              (send response-target 1)
              (goto HaveAddr new-response-target))))
         (goto NoAddr)))))
      (define delayed-send-with-timeout-actor
        (term
         ((addr 0 (Addr Nat))
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

  (check-not-false (redex-match aps-eval z request-response-spec))
  (check-not-false (redex-match aps-eval z request-same-response-addr-spec))
  (check-not-false (redex-match csa-eval αn request-response-actor))
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-actor))
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-actor2))
  (check-not-false (redex-match csa-eval αn double-response-actor))
  (check-not-false (redex-match csa-eval αn delay-saving-address-actor))
  (check-not-false (redex-match csa-eval αn respond-once-actor))
  (check-not-false (redex-match csa-eval αn delayed-send-no-timeout-actor))
  (check-not-false (redex-match csa-eval αn delayed-send-with-timeout-actor))
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
         [r -> (with-outputs ([r *]) (goto B))]
         [r -> (goto B)])
       (define-state (B)
         [* -> (goto B)]))
      (goto A)
      (addr 0 (Addr Nat)))))

  (check-not-false (redex-match csa-eval αn reply-once-actor))
  (check-not-false (redex-match aps-eval z maybe-reply-spec))
  (check-true (check-conformance/config (make-single-actor-config reply-once-actor)
                           (make-exclusive-spec maybe-reply-spec)))

  ;;;; Non-deterministic branching in spec

  (define zero-nonzero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r (variant Zero)])    (goto S1 r))]
         [* -> (with-outputs ([r (variant NonZero)]) (goto S1 r))]))
      (goto S1 ,static-response-address)
      (addr 0 Nat))))
  (define zero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r (variant Zero)])    (goto S1 r))]))
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
       (goto S1 ,static-response-address)))))

  (check-not-false (redex-match aps-eval z static-response-spec))
  (check-not-false (redex-match aps-eval z zero-nonzero-spec))
  (check-not-false (redex-match aps-eval z zero-spec))
  (check-not-false (redex-match csa-eval αn primitive-branch-actor))

  (check-true (check-conformance/config (make-single-actor-config primitive-branch-actor)
                           (make-exclusive-spec zero-nonzero-spec)))
  (check-false (check-conformance/config (make-single-actor-config primitive-branch-actor)
                            (make-exclusive-spec zero-spec)))

  ;;;; Optional Commitments
  (define optional-commitment-spec
    (term
     (((define-state (Always r)
         [* -> (with-outputs ([r *]) (goto Always r))]
         [* -> (goto Always r)]))
      (goto Always (addr 1 (Addr Nat)))
      (addr 0 Nat))))

  (check-not-false (redex-match aps-eval z optional-commitment-spec))
  (check-true (check-conformance/config ignore-all-config (make-exclusive-spec optional-commitment-spec)))

  ;;;; Stuck states in concrete evaluation

  (define nat-to-nat-spec
    (term
     (((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
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

  (check-not-false (redex-match aps-eval z nat-to-nat-spec))
  (check-not-false (redex-match csa-eval αn div-by-zero-actor))
  (check-not-false (redex-match csa-eval αn div-by-one-actor))

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
         [*     -> (with-outputs ([response-dest *]) (goto Always response-dest))]
         [unobs -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (check-not-false (redex-match aps-eval z static-response-spec-with-unobs))

  (test-true "static response with unobs, incl in spec"
             (check-conformance/config (make-single-actor-config static-response-actor)
                          (make-spec static-response-spec-with-unobs (list '(addr 0 Nat)))))

  ;; 4. unobs causes a particular behavior (like connected/error in TCP)
  (define obs-unobs-static-response-address
    (make-static-response-address (term (Union (TurningOn) (TurningOff)))))
  (define unobs-toggle-spec
    (term (((define-state (Off r)
              [* -> (with-outputs ([r (variant TurningOn)]) (goto On r))])
            (define-state (On r)
              [* -> (goto On r)]
              [unobs -> (with-outputs ([r (variant TurningOff)]) (goto Off r))]))
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

  (check-not-false (redex-match aps-eval z unobs-toggle-spec))
  (check-not-false (redex-match aps-eval αn unobs-toggle-actor))
  (check-not-false (redex-match aps-eval αn unobs-toggle-actor-wrong1))
  (check-not-false (redex-match aps-eval αn unobs-toggle-actor-wrong2))
  (check-not-false (redex-match aps-eval αn unobs-toggle-actor-wrong3))
  (check-not-false (redex-match aps-eval αn unobs-toggle-actor-wrong4))

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
         [(record [dest dest] [msg (variant A)]) -> (with-outputs ([dest (variant A)]) (goto Always))]
         [(record [dest dest] [msg (variant B)]) -> (with-outputs ([dest (variant B)]) (goto Always))]))
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

  (check-not-false (redex-match aps-eval z record-req-resp-spec))
  (check-not-false (redex-match csa-eval αn record-req-resp-actor))
  (check-not-false (redex-match csa-eval αn record-req-wrong-resp-actor))

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

  (check-not-false (redex-match csa-eval αn static-response-let-actor))
  (check-not-false (redex-match csa-eval αn static-double-response-let-actor))

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

  (check-not-false (redex-match csa-eval αn equal-actor-wrong1))
  (check-not-false (redex-match csa-eval αn equal-actor-wrong2))
  (check-not-false (redex-match csa-eval αn equal-actor))

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

  (check-not-false (redex-match csa-eval αn loop-do-nothing-actor))
  ;; TODO: figure out why this test works even when unobs stuff should be bad...
  (check-not-false (redex-match csa-eval αn loop-send-unobs-actor))
  (check-not-false (redex-match csa-eval αn send-before-loop-actor))
  (check-not-false (redex-match csa-eval αn send-inside-loop-actor))
  (check-not-false (redex-match csa-eval αn send-after-loop-actor))

  (check-true (check-conformance/config (make-single-actor-config loop-do-nothing-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (check-conformance/config (make-single-actor-config loop-send-unobs-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (check-conformance/config (make-single-actor-config send-before-loop-actor)
                           (make-exclusive-spec request-response-spec)))
  ;; TODO: get this test working again (need to at least check that none of the outputs in a loop were
  ;; observed)
  ;;
  ;; (check-false (check-conformance/config (make-single-actor-config send-inside-loop-actor)
  ;;                      request-response-spec
  ;;                      (term ((addr 0 (Addr Nat)))) null
  ;;                      (hash 'A 'Always)))
  (check-true (check-conformance/config (make-single-actor-config send-after-loop-actor)
                           (make-exclusive-spec request-response-spec)))

  ;;;; Timeouts

  ;; TODO: check the case where we rely on a timeout for the initial message. Should not be allowed,
  ;; because it might not happen. Similarly try the one where we have a second thing that times out,
  ;; and that *does* work

  (define timeout-spec
    (term
     (((define-state (A r)
         [* -> (with-outputs ([r (variant GotMessage)]) (goto A r))]
         [unobs -> (with-outputs ([r (variant GotTimeout)]) (goto A r))]))
      (goto A ,static-response-address)
      (addr 0 Nat))))
  (define got-message-only-spec
    (term
     (((define-state (A r)
         [* -> (with-outputs ([r (variant GotMessage)]) (goto A r))]))
      (goto A ,static-response-address)
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
       (goto A ,static-response-address)))))

  (check-not-false (redex-match aps-eval z timeout-spec))
  (check-not-false (redex-match aps-eval z got-message-only-spec))
  (check-not-false (redex-match csa-eval αn timeout-and-send-actor))
  (check-true (check-conformance/config (make-single-actor-config timeout-and-send-actor)
                           (make-exclusive-spec timeout-spec)))
  (check-false (check-conformance/config (make-single-actor-config timeout-and-send-actor)
                       (make-exclusive-spec got-message-only-spec)))

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
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]
         [unobs -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))

  (check-not-false (redex-match csa-eval αn static-response-actor2))
  (check-not-false (redex-match csa-eval αn other-static-response-actor))
  (check-not-false (redex-match aps-eval z static-response-with-extra-spec))

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

  ;; Multiple specifications
  (define other-static-response-spec
    (term
     (((define-state (Always2 response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always2 response-dest))]))
      (goto Always2 (addr 3 (Union [Ack Nat])))
      (addr 1 Nat))))

  (check-not-false (redex-match aps-eval z other-static-response-spec))

  ;; TODO: probably get rid of this test
  ;; (test-true "Multi-spec test"
  ;;            (check-conformance/config
  ;;             (make-empty-queues-config (list static-response-actor other-static-response-actor) null)
  ;;             (make-exclusive-spec (list static-response-spec other-static-response-spec))
  ;;             (term ((addr 0 Nat) (addr 1 Nat))) null))

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

  (check-not-false (redex-match csa-eval αn statically-delegating-responder-actor))
  (check-not-false (redex-match csa-eval αn request-response-actor2))

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
         [unobs -> (with-outputs ([r self]) (goto Running))])
       (define-state (Running)
         [r -> (with-outputs ([r *]) (goto Running))]))
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

  (check-not-false (redex-match csa-eval αn self-reveal-actor))
  ;; TODO: redo this test later
  ;; (check-not-false (redex-match csa-eval αn reveal-wrong-address-actor))
  (check-not-false (redex-match csa-eval αn reveal-self-double-output-actor))
  (check-not-false (redex-match aps-eval z self-reveal-spec))

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
         [r -> (with-outputs ([r (spawn-spec
                                  (goto EchoResponse)
                                  (define-state (EchoResponse)
                                    [er -> (with-outputs ([er *]) (goto EchoResponse))]))])
                 (goto Always))]))
      (goto Always)
      (addr 0 (Addr (Addr (Addr Nat)))))))

  (check-not-false (redex-match csa-eval αn echo-spawning-actor))
  (check-not-false (redex-match csa-eval αn double-response-spawning-actor))
  (check-not-false (redex-match aps-eval z echo-spawn-spec))

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
         [* -> (goto DoAnything)]))
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
         [r -> (spawn-spec ((goto Init r)
                            (define-state (Init r)
                              [unobs -> (with-outputs ([r self]) (goto EchoResponse))])
                            (define-state (EchoResponse)
                              [er -> (with-outputs ([er *]) (goto EchoResponse))]))
                           (goto Always))]))
      (goto Always)
      (addr 0 (Addr (Addr (Addr Nat)))))))

  (test-valid-actor? spawn-self-revealing-echo)
  (test-valid-instance? child-self-reveal-spec)
  (test-true "Spawned child can reveal self"
    (check-conformance/config
     (make-single-actor-config spawn-self-revealing-echo)
     (make-exclusive-spec child-self-reveal-spec)))

  ;;;; Blur Tests

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

  (test-valid-actor? send-to-blurred-internal-actor)

  (test-false "Sending precise address to blurred sending actor causes non-conformance"
    (check-conformance/config
     (make-single-actor-config send-to-blurred-internal-actor)
     (make-exclusive-spec static-response-spec)))

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

  (define never-send-spec
    (term
     (((define-state (Always r)
         [* -> (goto Always r)]))
      (goto Always ,(make-static-response-address 'Nat))
      (addr 0 Nat))))

  (test-valid-actor? create-later-send-children-actor)
  (test-valid-instance? never-send-spec)
  (test-false "Child that sends response in second state does not match never-send"
    ;; tests that all reachable states of a blurred child are executed
    (check-conformance/config
     (make-single-actor-config create-later-send-children-actor)
     (make-exclusive-spec never-send-spec)))

  ;; (define send-to-blurred-internal-actor
  ;;   (term
  ;;    ((addr 0 Nat)
  ;;     (((define-state (Always [static-output (Addr Nat)]
  ;;                             [saved-internal (Union [None] [Some (Addr Nat)])]) (m)
  ;;         (begin
  ;;           (case saved-internal
  ;;             [(None) 1]
  ;;             [(Some saved) (send saved 1)])
  ;;           (goto Always
  ;;                 static-output
  ;;                 (variant Some
  ;;                          (spawn internal-loc
  ;;                                 (Addr Nat)
  ;;                                 (goto InternalAlways)
  ;;                                 (define-state (InternalAlways) (m)
  ;;                                   (begin
  ;;                                     (send static-output 1)
  ;;                                     (goto InternalAlways)))))))))
  ;;      (goto Always ,static-response-address (variant None))))))


  ;; (define send-to-blurred-internal-actor
  ;;   (term
  ;;    ((addr 0 Nat)
  ;;     (((define-state (Always [static-output (Addr Nat)]
  ;;                             [saved-internal (Union [None] [Some (Addr Nat)])]) (m)
  ;;         (begin
  ;;           (case saved-internal
  ;;             [(None) 1]
  ;;             [(Some saved) (send saved 1)])
  ;;           (goto Always
  ;;                 static-output
  ;;                 (variant Some
  ;;                          (spawn internal-loc
  ;;                                 (Addr Nat)
  ;;                                 (goto InternalAlways)
  ;;                                 (define-state (InternalAlways) (m)
  ;;                                   (begin
  ;;                                     (send static-output 1)
  ;;                                     (goto InternalAlways)))))))))
  ;;      (goto Always ,static-response-address (variant None))))))
  ;; (define send-whenever-spec
  ;;   (term
  ;;    (((define-state (Always r)
  ;;        [* -> (goto Always r)]
  ;;        [unobs -> (with-outputs ([r *]) (goto Always r))]))
  ;;     (goto Always ,static-response-address)
  ;;     (addr 0 Nat))))
  ;; (define never-send-spec
  ;;   (term
  ;;    (((define-state (Always r)
  ;;        [* -> (goto Always r)]))
  ;;     (goto Always ,static-response-address)
  ;;     (addr 0 Nat))))

  ;; Tests:
  ;; blurred actor that closed over internal/external
  ;; blurred message that closed over internal/external
  ;; send message with internal/external to blurred

  ;; (test-true "Sending message to blurred-internal matches send-whenever spec"
  ;;   (check-conformance/config
  ;;    (make-single-actor-config send-to-blurred-internal-actor)
  ;;    (make-exclusive-spec send-whenever-spec)))
  ;; (test-false "Sending message to blurred-internal does not match never-send spec"
  ;;   (check-conformance/config
  ;;    (make-single-actor-config send-to-blurred-internal-actor)
  ;;    (make-exclusive-spec never-send-spec)))

  ;; step 1: spawn the forwarder; save it
  ;; step 2: spawn the new agent (spec follows it)
  ;; step 3: new agent uses forwarder to fulfill its dynamic request/response (can't do static yet)
  ;; (define conflicts-only-test-actor
  ;;   (term
  ;;    ((addr 0 (Addr (Addr (Addr Nat))))
  ;;     (((define-state (Always [maybe-forwarder (Union [None] [Forwarder (Addr (Addr Nat))])]) (dest)
  ;;         (let ([forwarder
  ;;                (case maybe-forwarder
  ;;                  [(None)
  ;;                   ;; The forwarder actor takes any address it's given and sends a message to it
  ;;                   (spawn forwarder-loc (Addr Nat)
  ;;                                 (goto Forwarding)
  ;;                                 (define-state (Forwarding) (r)
  ;;                                   (begin
  ;;                                     (send r 1)
  ;;                                     (goto Forwarding))))]
  ;;                  [(Forwarder the-addr) the-addr])])
  ;;           (begin
  ;;             (send dest
  ;;                   (spawn surfaced-loc
  ;;                          (Addr Nat)
  ;;                          (goto Responding)
  ;;                          (define-state (Responding) (r)
  ;;                            (begin
  ;;                              (send forwarder r)
  ;;                              (goto Responding)))))
  ;;             (goto Always (variant Forwarder forwarder))))))
  ;;      (goto Always (variant None))))))

  ;; (test-true "Only spawned actors with conflicts are blurred out"
  ;;   (check-conformance/config
  ;;    (make-single-actor-config conflicts-only-test-actor)
  ;;    (make-exclusive-spec echo-spawn-spec)))

  ;; first: do only for overlaps: on message A, spawn a forwarder (just once). on message B, either send directly or send to forwarder.

  ;; test idea: check that a config with blurred thing that has escaped address satisfies send-whenever, but not send-once/never
  ;;
  ;; can do similar for internal address by having a single forwarding actor

  ;; can send to obs address after blurred

  ;; can send to other internal address after blurred



  ;; (for both of these, it just sends the abstract wildcard value for that type)
  ;; actually, this won't work: that message to an internal might contain an *external* observable address. Need to think about that one a little bit

  ;; blur out only the *conflicting* actors

  ;; merge messages to blurred actors, too
  )
