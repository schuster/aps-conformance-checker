#lang racket

;; TODO: generally make all of the set-based code more functional

(provide model-check)

(require
 ;; See README.md for a brief description of these files
 data/queue
 "aps.rkt"
 "aps-abstract.rkt"
 "csa.rkt"
 "csa-abstract.rkt"
 "queue-helpers.rkt")

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   (for-syntax syntax/parse)
   "rackunit-helpers.rkt"))

;; ---------------------------------------------------------------------------------------------------
;; Data Structures

;; When the algorithm terminates, all remaining related-pairs <i, s> have the property that the
;; abstract implementation state i (abstractly) conforms to the abstract specification state s.
;;
;; These pairs are vertices of a dependency graph that constitutes a proof that all members of the
;; graph are in the conformance relation. Earlier in the algorithm, the graph is unsound, and the
;; algorithm uses a coinductive technique to remove the "local lies" and propagate the conseequences
;; of retracting these nodes, until we reach a sound fixpoint.
;;
;; We use this general technique for multiple relations, each of which is a subset of the previous
;; one, eventually leading to the spec conformance relation.
(struct related-pair (impl-config spec-config) #:transparent)

;; A possible transition step of an implementation configuration, representing the computation of a
;; single message/timeout handler. Fields are as follows:
;;
;; trigger: A representation of the message-receive or timeout that kicked off this
;; computation. Exact representation matches the trigger# form in csa#.
;;
;; from-observer?: A boolean indicating whether the trigger was caused by the "observer" portion of
;; the environment, as described in the conformance semantics. Can be true only for steps with
;; external-receive triggers.
;;
;; outputs: A list of abstract address/abstract value pairs indicating the messages sent to the
;; environment during the computation.
;;
;; dest-config: The implementation configuration reached at the end of this transition step
(struct impl-step (trigger from-observer? outputs dest-config) #:transparent)

;; A possible (weak) transition step of a specification configuration, representing the actions taken
;; to match some (handler-level) implementation transition step. Weak transitions correspond to the
;; general idea of weak simulations; see the dissertation for details. Fields are as follows:
;;
;; dest-config: The specification configuration reached at the end of the weak transition.
;;
;; spawned-specs: The set of specification configurations forked off by this transition
;; step. A conforming implementation configuration must conform to all of these configs in
;; addition to dest-config.
(struct spec-step (dest-config spawned-specs) #:transparent)

;; ---------------------------------------------------------------------------------------------------
;; Constants

;; The maximum number of times to unfold a recursive type while generating an exhaustive set of
;; abstract values for that type.
;;
;; This number is an arbitrary choice for now. Later it may make sense to base it off of the level of
;; detail in the spec or program.
(define MAX-RECURSION-DEPTH 1)

;; ---------------------------------------------------------------------------------------------------
;; Top-level Algorithm

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
;; those pairs from our proof graph and propagating the results of those removals backwards until we
;; reach a greatest fixpoint (see remove-unsupported), we end up with a proof graph whose vertices are
;; all configuration pairs in the simulation.
;;
;; Next, we identify the the vertices in the graph whose implementation configurations are not
;; guaranteed to satisfy all of their commitments in every fair execution (see find-unsatisfying-pairs
;; below). By removing these nodes and again back-propagating the effects of those removals (with
;; remove-unsupported again), the resulting graph represents a proof that all of its members are in
;; the conformance relation.
(define/contract (model-check initial-impl-config initial-spec-config)
  (-> csa-valid-config? aps-valid-config? boolean?)

  (define spec-address (aps-config-only-instance-address initial-spec-config))
  (cond
    [(and (not (aps#-unknown-address? spec-address))
          (andmap (lambda (a) (not (same-address-without-type? a spec-address)))
                  (csa-config-receptionists initial-impl-config)))
     #f]
    [else
     (define initial-pairs
       (spc
        (apply related-pair (α-pair initial-impl-config initial-spec-config MAX-RECURSION-DEPTH))))
     (match-define (list rank1-pairs incoming rank1-related-spec-steps rank1-unrelated-successors)
       (find-rank1-simulation initial-pairs))
     (match-define (list simulation-pairs simulation-related-spec-steps)
       (remove-unsupported rank1-pairs
                           incoming
                           rank1-related-spec-steps
                           rank1-unrelated-successors))
     (define commitment-satisfying-pairs
       (find-satisfying-pairs simulation-pairs simulation-related-spec-steps))
     (define unsatisfying-pairs (set-copy simulation-pairs))
     (set-symmetric-difference! unsatisfying-pairs commitment-satisfying-pairs)
     (match-define (list conforming-pairs _)
       (remove-unsupported commitment-satisfying-pairs
                           incoming
                           simulation-related-spec-steps
                           unsatisfying-pairs))
     (andmap (curry set-member? conforming-pairs) initial-pairs)]))

;; ---------------------------------------------------------------------------------------------------
;; Simulation

;; Builds a set of related pairs from the rank-1 conformance simulation by abstractly evaluating
;; implementation configs and finding matching specification transitions, starting from the given
;; initial pairs. Returns various data structures (see dissertation/model-checker-pseudocode.md for
;; details)
(define (find-rank1-simulation initial-pairs)
  ;; TODO: decide on mutable vs. immutable programming style
  (define to-visit (apply queue initial-pairs))
  (define related-spec-steps (make-hash))
  (define incoming (make-hash (map (lambda (t) (cons t (mutable-set))) initial-pairs)))

  ;; Debugging
  (define pairs-visited 0)
  (define log-file (if LOG-PAIRS (open-output-file "related_pair_log.dat" #:exists 'replace) #f))

  (let loop ([related-pairs (set)]
             [unrelated-successors (set)])
    (match (dequeue-if-non-empty! to-visit)
      [#f
       (when LOG-PAIRS (close-output-port log-file))
       (list related-pairs incoming related-spec-steps unrelated-successors)]
      [pair

       ;; Debugging
       (set! pairs-visited (add1 pairs-visited))
       ;; (printf "Current time: ~s\n" (current-seconds))
       ;; (printf "Implementation config #: ~s\n" pairs-visited)
       ;; (printf "Queue size: ~s\n" (queue-length to-visit))
       ;; (printf "The impl config: ~s\n" (impl-config-without-state-defs (related-pair-impl-config pair)))
       ;; (printf "The full impl config: ~s\n" (related-pair-impl-config pair))
       ;; (printf "The spec config: ~s\n" (spec-config-without-state-defs (related-pair-spec-config pair)))
       ;; (printf "Incoming so far: ~s\n" (hash-ref incoming pair))

       (when LOG-PAIRS
         (fprintf log-file "PAIR ~s (~s). ~s\n" pairs-visited (current-seconds) (pair->debug-pair pair))
         (flush-output log-file))

       (define i (related-pair-impl-config pair))
       (define s (related-pair-spec-config pair))
       (define i-steps (impl-steps-from i s))

       ;; Find the matching s-steps
       (define found-unmatchable-step? #f)
       (for ([i-step i-steps])
         ;; Debugging:
         ;; (printf "Impl step: ~s\n" (debug-impl-step i-step))

         ;; TODO: make sure the satisfied commitments are also recorded somewhere in here
         (define matching-s-steps (matching-spec-steps s i-step))
         ;; Debugging:
         ;; (printf "Matching spec steps: ~s\n" matching-s-steps)

         (hash-set! related-spec-steps (list pair i-step) matching-s-steps)
         (when (set-empty? matching-s-steps)
           (set! found-unmatchable-step? #t)))

       ;; Add this pair to appropriate list; add new worklist items
       (cond
         [found-unmatchable-step?
          ;; Debugging
          ;; (displayln "Unrelated pair")
          (loop related-pairs (set-add unrelated-successors pair))]
         [else
          ;; Debugging
          ;; (displayln "Related pair")
          (for ([i-step i-steps])
            (for ([s-step (hash-ref related-spec-steps (list pair i-step))])
              (define successor-pairs
                (for/list ([config (cons (spec-step-dest-config s-step) (spec-step-spawned-specs s-step))])
                  (related-pair (impl-step-dest-config i-step) config)))
              ;; Debugging only
              ;; (for ([successor-pair successor-pairs])
              ;;   (printf "pre-spc: ~s\n" successor-pair)
              ;;   (printf "post-spc: ~s\n" (spc successor-pair)))
              (for ([spc-pair (spc* successor-pairs)])
                (dict-of-sets-add! incoming spc-pair (list pair i-step s-step))
                (unless (or (member spc-pair (queue->list to-visit))
                            (set-member? related-pairs spc-pair)
                            (set-member? unrelated-successors spc-pair)
                            (equal? spc-pair pair))
                  (enqueue! to-visit spc-pair)))))
          (loop (set-add related-pairs pair) unrelated-successors)])])))

(define (impl-steps-from impl-config spec-config)
  (define (add-observed-flag transition observed?)
    (impl-step (csa#-transition-trigger transition)
               observed?
               (csa#-transition-outputs transition)
               (csa#-transition-final-config transition)))

  (define observed-external-receives
    (let ([addr (aps#-config-only-instance-address spec-config)])
      (if (aps#-unknown-address? addr) null (external-message-transitions impl-config addr))))
  (define unobserved-external-receives
    (append*
     (for/list ([receptionist (aps#-config-receptionists spec-config)])
       (external-message-transitions impl-config receptionist))))

  (append (map (curryr add-observed-flag #t) observed-external-receives)
          (map (curryr add-observed-flag #f)
               (append
                unobserved-external-receives
                (csa#-handle-all-internal-messages impl-config)
                (csa#-handle-all-timeouts impl-config)))))

;; Returns all possible transitions of the given implementation config caused by a received message to
;; the given receptionist address
(define (external-message-transitions impl-config receptionist)
  (display-step-line "Enumerating abstract messages (typed)")
  (append*
   (for/list ([message (generate-abstract-messages (csa#-receptionist-type receptionist) MAX-RECURSION-DEPTH)])
     (display-step-line "Evaluating a handler")
     (csa#-handle-message impl-config receptionist message))))

;; Returns a set of the possible spec steps (see the struct above) from the given spec config that
;; match the given implementation step
(define (matching-spec-steps spec-config i-step)
  (define matched-stepped-configs (mutable-set))
  (for ([(trigger-result) (aps#-matching-steps spec-config
                                               (impl-step-from-observer? i-step)
                                               (impl-step-trigger i-step))])
    (match-define (list config spawns1) trigger-result)
    (match (aps#-resolve-outputs config (impl-step-outputs i-step))
      [#f matched-stepped-configs]
      [(list stepped-spec-config spawns2 satisfied-commitments)
       ;; TODO: record the satisfied commitments somehow
       (set-add! matched-stepped-configs (spec-step stepped-spec-config (append spawns1 spawns2)))]))
  matched-stepped-configs)

(module+ test
  (define null-spec-config (make-Σ# '((define-state (S))) '(goto S) null null))

  (test-case "Null transition okay for unobs"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (init-addr 0 Nat) (* Nat)) #f null #f))
     (mutable-set (spec-step null-spec-config null))))
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
     (mutable-set (spec-step null-spec-config null))))
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
     (mutable-set (spec-step (make-Σ# '((define-state (A))) '(goto A) null (list '((obs-ext 1 Nat)))) null))))
  (test-case "Output can be matched by new commitment"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))])) '(goto A) null null)
      (impl-step '(external-receive (init-addr 0 Nat) (obs-ext 1 Nat)) #t (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))]))
                                      '(goto A)
                                      null
                                      (list '((obs-ext 1 Nat))))
                             null))))
  (test-case "Multiple copies of same commitment get merged"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) null (list '[(obs-ext 1 Nat) (single *)]))
      (impl-step '(external-receive (init-addr 0 Nat) (* Nat)) #t null #f))
     (mutable-set
      (spec-step (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) null (list '[(obs-ext 1 Nat) (many *)]))
                 null)))))

(define (dict-of-sets-add! dict key new-pair)
  (match (hash-ref dict key #f)
    [#f
     (hash-set! dict key (mutable-set new-pair))]
    [the-set
     (set-add! the-set new-pair)]))

;; Splits, projects, and canonicalizes the given related pair, returning the resulting pairs
(define (spc pair)
  (display-step-line "Splitting a specification config")
  (for/list ([spec-config-component (split-spec (related-pair-spec-config pair))])
    ;; TODO: make it an "error" for a non-precise address to match a spec state parameter
    (display-step-line "Projecting an implementation config")
    (match-define (list projected-impl projected-spec)
      (project-by-relevant-addresses (related-pair-impl-config pair) spec-config-component))
    (display-step-line "Canonicalizing the pair, adding to queue")
    (match-define (list canonicalized-impl canonicalized-spec)
      (canonicalize-pair (list projected-impl projected-spec)))
    (related-pair canonicalized-impl canonicalized-spec)))

;; Calls spc on every pair and merges the results into one long list
(define (spc* pairs)
  (append* (map spc pairs)))

;; Projects the given configurations into only the portions that are relevant to the specification
;; configuration, moving the rest of the configurations into the "imprecise" sections of the
;; abstraction
(define (project-by-relevant-addresses p s)
  (define spawn-flag-to-blur
    (let ([spec-address (aps#-config-only-instance-address s)])
      (if (or (csa#-new-spawn-address? spec-address)
              (aps#-unknown-address? spec-address))
          'OLD
          'NEW)))

  (list
   (csa#-merge-duplicate-messages
    (blur-externals
     (blur-irrelevant-actors p spawn-flag-to-blur)
     (aps#-relevant-external-addrs s)))
   (aps#-abstract-and-age s spawn-flag-to-blur)))

(module+ test
  (test-equal? "check that messages with blurred addresses get merged together"
   (project-by-relevant-addresses
    (term (()
           (((init-addr 2 Nat) (obs-ext 1 Nat) 1)
            ((init-addr 2 Nat) (obs-ext 2 Nat) 1)
            ((init-addr 2 Nat) (obs-ext 3 Nat) 1))
           ()
           ()))
    (term ((,aps#-no-transition-instance) () (((obs-ext 3 Nat))))))
   (list (term (()
                (((init-addr 2 Nat) (* (Addr Nat)) *)
                 ((init-addr 2 Nat) (obs-ext 3 Nat) 1))
                ()
                ()))
         (term ((,aps#-no-transition-instance) () (((obs-ext 3 Nat))))))))

;; Returns the list of split spec-configs from the given one, failing if any of the FSMs share an
;; address
;;
;; TODO: move this to the APS# module, since it has to deal so much with the internal representation
(define (split-spec config)
  (define receptionists (aps#-config-receptionists config))
  (define-values (fsm-specs remaining-commitment-map)
    (for/fold ([fsm-specs null]
               [remaining-commitment-map (aps#-config-commitment-map config)])
              ([instance (aps#-config-instances config)])
     (define (entry-relevant? entry)
       (member (aps#-commitment-entry-address entry)
               (aps#-instance-arguments instance)))
      (define relevant-entries (filter entry-relevant? remaining-commitment-map))
      (values
       ;; TODO: use redex "term" here instead of quasiquote, when I move this into the APS# module
       (cons `((,instance) ,receptionists ,relevant-entries) fsm-specs)
       (filter (negate entry-relevant?) remaining-commitment-map))))
  (append fsm-specs
          (for/list ([entry remaining-commitment-map])
            (aps#-spec-from-commitment-entry entry
                                             (aps#-config-only-instance-address config)
                                             receptionists))))

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

(define (remove-unsupported all-pairs incoming init-related-spec-steps init-unrelated-successors)
  (define remaining-pairs (set-copy all-pairs))
  (define unrelated-successors (apply queue (set->list init-unrelated-successors)))
  (define related-spec-steps (hash-copy init-related-spec-steps))

  (let loop ()
    (match (dequeue-if-non-empty! unrelated-successors)
      [#f (list remaining-pairs related-spec-steps)]
      [unrelated-pair
       (for ([transition (hash-ref incoming unrelated-pair)])
         (match-define (list predecessor i-step s-step) transition)
         (when (set-member? remaining-pairs predecessor)
           (define spec-steps (hash-ref related-spec-steps (list predecessor i-step)))
           (when (set-member? spec-steps s-step)
             (set-remove! spec-steps s-step)
             (when (set-empty? spec-steps)
               (set-remove! remaining-pairs predecessor)
               (enqueue! unrelated-successors predecessor)))))
       (loop)])))

(module+ test
  (require "hash-helpers.rkt")

  ;; Because remove-unsupported does not care about the actual content of the impl or spec
  ;; configurations, we replace them here with letters (A, B, C, etc. for impls and X, Y, Z, etc. for
  ;; specs) for simplification
  (define ax-pair (related-pair 'A 'X))
  (define by-pair (related-pair 'B 'Y))
  (define bz-pair (related-pair 'B 'Z))
  (define cw-pair (related-pair 'C 'W))

  (define aa-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'A))
  (define xx-step (spec-step 'X null))
  (define ab-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'B))
  (define xy-step (spec-step 'Y null))
  (define xz-step (spec-step 'Z null))
  (define bc-step (impl-step '(timeout (init-addr 0 Nat)) #f null 'C))
  (define yw-step (spec-step 'W null))

  (test-equal? "Remove no pairs, because no list"
    (remove-unsupported
     (mutable-set ax-pair)
     ;; incoming
     (mutable-hash [ax-pair (mutable-set (list ax-pair aa-step xx-step))])
     ;; related spec steps
     (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])
     ;; unrelated sucessors
     null)
    (list
     (mutable-set ax-pair)
     (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])))

  (test-equal? "Remove no pairs, because unrelated-matches contained only a redundant support"
    (remove-unsupported
     (mutable-set ax-pair bz-pair)
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step))]
                   [bz-pair (mutable-set (list ax-pair ab-step xz-step))]
                   [ax-pair (mutable-set)])
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)])
     (list by-pair))
    (list
     (mutable-set ax-pair bz-pair)
     (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)])))

  (test-equal? "Remove last remaining pair"
    (remove-unsupported
     (mutable-set ax-pair)
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step))]
                   [ax-pair (mutable-set)])
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)])
     (list by-pair))
    (list
     (mutable-set)
     (mutable-hash [(list ax-pair ab-step) (mutable-set)])))

  (test-equal? "Remove a redundant support"
    (remove-unsupported
     (mutable-set ax-pair bz-pair by-pair)
     ;; incoming
     (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step))]
                   [bz-pair (mutable-set (list ax-pair ab-step xz-step))]
                   [ax-pair (mutable-set)]
                   [cw-pair (mutable-set (list by-pair bc-step yw-step))])
     ;; matching spec steps
     (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)]
                   [(list by-pair bc-step) (mutable-set yw-step)])
     ;; unrelated successors
     (list cw-pair))
    (list
     (mutable-set ax-pair bz-pair)
     (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)]
                   [(list by-pair bc-step) (mutable-set)])))

    (test-equal? "Remove a non-redundant support"
      (remove-unsupported
       (mutable-set ax-pair by-pair)
       ;; incoming
       (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step))]
                     [ax-pair (mutable-set)]
                     [cw-pair (mutable-set (list by-pair bc-step yw-step))])
       ;; matching spec steps
       (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)]
                     [(list by-pair bc-step) (mutable-set yw-step)])
       ;; unrelated successors
       (list cw-pair))
      (list
       (mutable-set)
       (mutable-hash [(list ax-pair ab-step) (mutable-set)]
                     [(list by-pair bc-step) (mutable-set)]))))

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; TODO: when walking the edges, take care of edges that do an address rename (because the commitment
;; will also need to be renamed)

(define (find-satisfying-pairs simulation-pairs related-spec-steps)
  ;; TODO: implement this for real
  simulation-pairs)

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define DISPLAY-STEPS #f)

(define LOG-PAIRS #f)

(define (display-step-line msg)
  (when DISPLAY-STEPS (displayln msg)))

(define (pair->debug-pair pair)
  (list (impl-config-without-state-defs (related-pair-impl-config pair))
        (spec-config-without-state-defs (related-pair-spec-config pair))))

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
           (check-valid-actor? the-term))]
      [(_ the-term)
       #`(test-begin
           (check-valid-actor? the-term))]))

  (define-simple-check (check-valid-instance? actual)
    (redex-match? aps-eval z actual))

  (define-syntax (test-valid-instance? stx)
    (syntax-parse stx
      [(_ name the-term)
       #`(test-case name
           (check-valid-instance? the-term))]
      [(_ the-term)
       #`(test-begin
           (check-valid-instance? the-term))]))

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

  (check-true (model-check ignore-all-config (make-exclusive-spec ignore-all-spec-instance)))

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
             (model-check (make-single-actor-config static-response-actor)
                          (make-exclusive-spec static-response-spec)))
  (test-false "Static response actor, ignore all spec"
              (model-check (make-single-actor-config static-response-actor)
                           (make-exclusive-spec ignore-all-with-addr-spec-instance)))
  (test-false "static double response actor"
              (model-check (make-single-actor-config static-double-response-actor)
                           (make-exclusive-spec static-response-spec)))
  (test-false "Static response spec, ignore-all config"
               (model-check ignore-all-config
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

  (check-true (model-check (make-single-actor-config pattern-matching-actor)
                           (make-exclusive-spec pattern-match-spec)))
  (test-false "Send on A but not B; should send on both"
              (model-check (make-single-actor-config partial-pattern-matching-actor)
                           (make-exclusive-spec pattern-match-spec)))
  (check-false (model-check (make-single-actor-config reverse-pattern-matching-actor)
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
             (model-check (make-single-actor-config request-response-actor)
                          (make-exclusive-spec request-response-spec)))

  (test-false "request/response 2"
              (model-check (make-single-actor-config respond-to-first-addr-actor)
                           (make-exclusive-spec request-response-spec)))
  (test-false "request/response 3"
               (model-check (make-single-actor-config respond-to-first-addr-actor2)
                            (make-exclusive-spec request-response-spec)))
  (test-false "request/response 4"
               (model-check (make-single-actor-config request-response-actor)
                            (make-exclusive-spec request-same-response-addr-spec)))
  (test-false "ignore all actor does not satisfy request/response"
              (model-check (make-ignore-all-config (term (Addr Nat)))
                           (make-exclusive-spec request-response-spec)))
  (test-false "Respond-once actor does not satisfy request/response"
              (model-check (make-single-actor-config respond-once-actor)
                           (make-exclusive-spec request-response-spec)))
  (check-true (model-check (make-single-actor-config respond-to-first-addr-actor)
                           (make-exclusive-spec request-same-response-addr-spec)))
  (check-true (model-check (make-single-actor-config respond-to-first-addr-actor2)
                           (make-exclusive-spec request-same-response-addr-spec)))
  (check-false (model-check (make-single-actor-config double-response-actor)
                            (make-exclusive-spec request-response-spec)))
  (check-false (model-check (make-single-actor-config delay-saving-address-actor)
                            (make-exclusive-spec request-response-spec)))
  (test-false "Send only on next receive does not satisfy request/response"
               (model-check (make-single-actor-config delayed-send-no-timeout-actor)
                            (make-exclusive-spec request-response-spec)))
  (check-true (model-check (make-single-actor-config delayed-send-with-timeout-actor)
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
  (check-true (model-check (make-single-actor-config reply-once-actor)
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

  (check-true (model-check (make-single-actor-config primitive-branch-actor)
                           (make-exclusive-spec zero-nonzero-spec)))
  (check-false (model-check (make-single-actor-config primitive-branch-actor)
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
  (check-true (model-check ignore-all-config (make-exclusive-spec optional-commitment-spec)))

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
             (model-check (make-single-actor-config div-by-one-actor)
                          (make-exclusive-spec nat-to-nat-spec)))
  (test-true "Div by zero vs. nat-to-nat spec"
              (model-check (make-single-actor-config div-by-zero-actor)
                           (make-exclusive-spec nat-to-nat-spec)))

  ;;;; Unobservable communication

  ;; wildcard unobservables are ignored for the purpose of output commitments
  (test-true "request/response actor vs. ignore-all spec"
             (model-check (make-single-actor-config request-response-actor)
                          (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))

  ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect
  ;; conformance
  (test-true "request response actor and spec, with unobs communication"
             (model-check (make-single-actor-config request-response-actor)
                          (make-spec request-response-spec (list '(addr 0 (Addr Nat))))))

  ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
  (test-false "static response with unobs communication"
              (model-check (make-single-actor-config static-response-actor)
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
             (model-check (make-single-actor-config static-response-actor)
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
             (model-check (make-single-actor-config unobs-toggle-actor)
                          (make-spec unobs-toggle-spec (list '(addr 0 (Union [FromUnobservedEnvironment]))))))

  (for ([actor (list unobs-toggle-actor-wrong1
                     unobs-toggle-actor-wrong2
                     unobs-toggle-actor-wrong3
                     unobs-toggle-actor-wrong4)])
    (test-false "Obs/Unobs bug-finding test(s)"
                (model-check (make-single-actor-config actor)
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

  ;; TODO: figure out why this test fails when max-depth for the program and the messages is set to
  ;; 0
  (test-true "record 1"
             (model-check (make-single-actor-config record-req-resp-actor)
                          (make-exclusive-spec record-req-resp-spec)))
  (test-false "record 2"
              (model-check (make-single-actor-config record-req-wrong-resp-actor)
                           (make-exclusive-spec record-req-resp-spec)))

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
             (model-check (make-single-actor-config static-response-let-actor)
                          (make-exclusive-spec static-response-spec)))
  (test-false "Let 2"
              (model-check (make-single-actor-config static-double-response-let-actor)
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
   (model-check (make-single-actor-config equal-actor-wrong1)
            (make-exclusive-spec static-response-spec)))
  (test-false "Equal actor wrong 2"
   (model-check (make-single-actor-config equal-actor-wrong2)
            (make-exclusive-spec static-response-spec)))
  (check-true
   (model-check (make-single-actor-config equal-actor)
                (make-exclusive-spec static-response-spec)))

  ;;;; For loops
  (define loop-do-nothing-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (m)
          (begin
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define loop-send-unobs-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A [r (Addr Nat)]) (m)
          (begin
            (for/fold ([folded 0])
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
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define send-inside-loop-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (for/fold ([folded 0])
                      ([r (list r)])
              (send r 0))
            (goto A))))
       (goto A)))))
  (define send-after-loop-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (for/fold ([folded 0])
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

  (check-true (model-check (make-single-actor-config loop-do-nothing-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (model-check (make-single-actor-config loop-send-unobs-actor)
                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
  (check-true (model-check (make-single-actor-config send-before-loop-actor)
                           (make-exclusive-spec request-response-spec)))
  ;; TODO: get this test working again (need to at least check that none of the outputs in a loop were
  ;; observed)
  ;;
  ;; (check-false (model-check (make-single-actor-config send-inside-loop-actor)
  ;;                      request-response-spec
  ;;                      (term ((addr 0 (Addr Nat)))) null
  ;;                      (hash 'A 'Always)))
  (check-true (model-check (make-single-actor-config send-after-loop-actor)
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
  (check-true (model-check (make-single-actor-config timeout-and-send-actor)
                           (make-exclusive-spec timeout-spec)))
  (check-false (model-check (make-single-actor-config timeout-and-send-actor)
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
              (model-check
                (make-empty-queues-config (list static-response-actor static-response-actor2) null)
                (make-spec static-response-spec (list '(addr 1 Nat)))))
  (test-true "Multi actor test 2"
             (model-check
              (make-empty-queues-config (list static-response-actor static-response-actor2) null)
              (make-spec static-response-with-extra-spec (list '(addr 1 Nat)))))
  (test-true "Multi actor test 3"
             (model-check
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
  ;;            (model-check
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
             (model-check
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
             (model-check
              (make-single-actor-config self-reveal-actor)
              (make-exclusive-spec self-reveal-spec)))
  ;; TODO: redo this test later
  ;; (test-false "Catch self-reveal of wrong address"
  ;;             (model-check
  ;;              (make-single-actor-config reveal-wrong-address-actor)
  ;;              self-reveal-spec
  ;;              (term ((addr 0 (Addr (Addr (Addr Nat)))))) null
  ;;              (hash)))
  (test-false "Catch self-reveal of actor that doesn't follow its behavior"
              (model-check
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
             (model-check
              (make-single-actor-config echo-spawning-actor)
              (make-exclusive-spec echo-spawn-spec)))
  ;; TODO: also add a sink-spawning actor when commitment satisfaction is working
  (test-false "Spawned double-response actor does not match dynamic response spec"
              (model-check
               (make-single-actor-config double-response-spawning-actor)
               (make-exclusive-spec echo-spawn-spec)))

  ;;;; Initial spec address must have actor in the model checker
  (define no-matching-address-spec
    (term
     (((define-state (DoAnything)
         [* -> (goto DoAnything)]))
      (goto DoAnything)
      (addr 500 Nat))))
  (test-valid-instance? no-matching-address-spec)

  (test-false "Spec config address must have matching actor in implementation configuration"
   (model-check
    (make-single-actor-config static-response-actor)
    (make-exclusive-spec no-matching-address-spec))))
