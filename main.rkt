#lang racket

;; TODO: probably shouldn't call this file "main" if it's exporting something to something else in the
;; "package"

;; TODO: rename program/prog to implementation/impl

;; TODO: generally make all of the set-based code more functional

(provide analyze)

(require
 data/queue
 "queue-helpers.rkt"
 "aps.rkt"
 "aps-abstract.rkt"
 "csa.rkt"
 "csa-abstract.rkt"
 "graph.rkt")

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   "rackunit-helpers.rkt"))

;; TODO: rename "agents" to just actors

;; ---------------------------------------------------------------------------------------------------
;; Data definitions

;; There are 2 separate issues here. There's a graph-like structure (most easily understood as the
;; outgoing edges, the big tree-like thing I showed Olin with AND/OR edges), and there's the efficient
;; representation in code, which is something else.
;;
;; My thought: the range of the "incoming" dictionary should be sets of info-tuples that include *all*
;; the information needed to trace back to the previous related tuple.

;; Trigger is as listed in csa-abstract
;;
;; TODO: rename all of these
(struct simulation-node (prog-config spec-config obs-receptionists unobs-receptionists) #:transparent)

;; TODO: think about whether the ranges given here are really "unique": could we have duplicate steps
;; with the same data? Does that matter? (Very related to the DDD idea of "identity")

;; Incoming: dict from tuple to (mutable-setof (tuple, impl-step, spec-step)

;; related-spec-steps: dict from (tuple, impl-step) to (mutable-setof spec-step)

(struct impl-step (from-observer? trigger outputs final-state) #:transparent)

;; TODO: probably want to add satisfied commitments here
(struct spec-step (final-state spawned-specs revealed-addresses) #:transparent)

;; ---------------------------------------------------------------------------------------------------
;; Main functions

;; TODO: make this handle full configs, not just a single spec instance and agent instance

;; TODO: rename "analyze" to something like "check" or "verify" or "model-check"

;; TODO: add some sort of typechecker that runs ahead of the analyzer (but perhaps as part of it, for
;; the sake of tests) to prevent things like a goto to a state that doesn't exist (and make sure that
;; a specs's type matches the program)

;; TODO: add an initial mapping between the program and the spec (maybe? might need new definition of
;; conformance for that)

;; TODO: remove this function, or at least rename it
(define (analyze initial-prog-config
                 initial-spec-instance
                 init-obs-receptionists
                 init-unobs-receptionists)
  ;; TODO: make this into a contract
  (unless (aps-valid-instance? initial-spec-instance)
    (error 'analyze "Invalid initial specification instance ~s" initial-spec-instance))
  (model-check initial-prog-config
               (aps-config-from-instances (list initial-spec-instance))
               init-obs-receptionists
               init-unobs-receptionists))

;; TODO: rename "config" to "state"

;; Given a concrete program configuration, a concrete specification configuration, and a list of pairs
;; that specify the expected prog-state/spec-state matches, returns #t if the conformance check
;; algorithm can prove conformance, #f otherwise.

(define (model-check initial-prog-config
                     initial-spec-config
                     init-obs-receptionists ; TODO: shouldn't these be part of the spec config?
                     init-unobs-receptionists)
  ;; TODO: make these into contracts
  (unless (csa-valid-config? initial-prog-config)
    (error 'model-check "Invalid initial program configuration ~s" initial-prog-config))
  (unless (aps-valid-config? initial-spec-config)
    (error 'model-check "Invalid initial specification configuration ~s" initial-spec-config))
  (unless (csa-valid-receptionist-list? init-obs-receptionists)
    (error 'model-check "Invalid observable receptionist lists: ~s" init-obs-receptionists))
  (unless (csa-valid-receptionist-list? init-unobs-receptionists)
    (error 'model-check "Invalid unobservable receptionist lists: ~s" init-unobs-receptionists))

  (define initial-tuples
    (sbc
     ;; TODO: give a better value for max-tuple-depth, both here for the initial abstraction and for
     ;; message generation
     (apply simulation-node
            (α-tuple initial-prog-config
                     initial-spec-config
                     init-obs-receptionists
                     init-unobs-receptionists
                     10))))
  (match-define (list rank1-tuples incoming rank1-related-spec-steps rank1-unrelated-successors)
    (build-immediate-simulation initial-tuples))
  (match-define (list simulation-tuples simulation-related-spec-steps)
    (remove-unsupported-tuples rank1-tuples
                               incoming
                               rank1-related-spec-steps
                               rank1-unrelated-successors))
  (define commitment-satisfying-tuples
    (find-satisfying-tuples simulation-tuples simulation-related-spec-steps))
  (define unsatisfying-tuples (set-copy simulation-tuples))
  (set-symmetric-difference! unsatisfying-tuples commitment-satisfying-tuples)
  (match-define (list conforming-tuples _)
    (remove-unsupported-tuples commitment-satisfying-tuples
                               incoming
                               simulation-related-spec-steps
                               unsatisfying-tuples))
  (andmap (curry set-member? conforming-tuples) initial-tuples))

;; ---------------------------------------------------------------------------------------------------
;; Simulation

;; TODO: rename this function
;;
;; Builds a set of nodes from the rank-1 conformance simulation by abstractly evaluating program
;; states and finding matching specification transitions, starting from the given initial
;; tuples. Returns various data structures (see dissertation/model-checker-pseudocode.md for details)
(define (build-immediate-simulation initial-tuples)
  ;; TODO: find a way to make this function shorter

  ;; TODO: think about using queues from the pfds collection if I switch to Typed Racket (which would
  ;; avoid the performance issue associated with that package)
  ;;
  ;; TODO: decide on mutable vs. immutable programming style
  (define to-visit (apply queue initial-tuples))
  (define related-spec-steps (make-hash))
  (define incoming (make-hash (map (lambda (t) (cons t (mutable-set))) initial-tuples)))

  ;; Debugging
  (define nodes-visited 0)
  (define log-file (if LOG-TUPLES (open-output-file "tuple_log.dat" #:exists 'replace) #f))

  (let loop ([related-tuples (set)]
             [unrelated-successors (set)])
    (match (dequeue-if-non-empty! to-visit)
      [#f
       (when LOG-TUPLES (close-output-port log-file))
       (list related-tuples incoming related-spec-steps unrelated-successors)]
      ;; TODO: change this pattern if we change the tuple structure
      [tuple

       ;; Debugging
       (set! nodes-visited (add1 nodes-visited))
       ;; (printf "Program state #: ~s\n" nodes-visited)
       ;; (printf "Queue size: ~s\n" (queue-length to-visit))
       ;; (printf "The prog config: ~s\n" (prog-config-without-state-defs (simulation-node-prog-config tuple)))
       ;; (printf "The full prog config: ~s\n" (simulation-node-prog-config tuple))
       ;; (printf "The spec config: ~s\n" (simulation-node-spec-config tuple))
       ;; (printf "Observer-side receptionists: ~s\n" (simulation-node-obs-receptionists tuple))
       ;; (printf "Unobserved-side receptionists: ~s\n" (simulation-node-unobs-receptionists tuple))
       ;; (printf "Incoming so far: ~s\n" (hash-ref incoming tuple))

       (when LOG-TUPLES
         (fprintf log-file "TUPLE ~s. ~s\n" nodes-visited (tuple->debug-tuple tuple))
         (flush-output log-file))

       (define found-unmatchable-step? #f)
       (define i (simulation-node-prog-config tuple))
       (define i-steps
         (impl-steps-from i
                          (simulation-node-obs-receptionists tuple)
                          (simulation-node-unobs-receptionists tuple)))

       ;; Find the matching s-steps
       (for ([i-step i-steps])
         ;; TODO: make sure the satisfied commitments are also recorded somewhere in here
         (define matching-s-steps (matching-spec-steps (simulation-node-spec-config tuple) i-step))
         (hash-set! related-spec-steps (list tuple i-step) matching-s-steps)
         (when (set-empty? matching-s-steps)
           (set! found-unmatchable-step? #t)))

       ;; Add this tuple to appropriate list; add new worklist items
       (cond
         [found-unmatchable-step?
          ;; Debugging
          ;; (displayln "Unrelated node")
          (loop related-tuples (set-add unrelated-successors tuple))]
         [else
          ;; Debugging
          ;; (displayln "Related node")
          (for ([i-step i-steps])
            (for ([s-step (hash-ref related-spec-steps (list tuple i-step))])
              ;; TODO: simplify this new-tuple code (will be easier when receptionists are maintained
              ;; elsewhere)
              (define new-tuples
                (for/list ([config (cons (spec-step-final-state s-step) (spec-step-spawned-specs s-step))])
                  (simulation-node
                   (impl-step-final-state i-step)
                   config
                   ;; TODO: put the obs/unobs receptionists in the spec config
                   ;; TODO: canonicalize the receptionist set by sorting it after the rename
                   (remove-duplicates (append (simulation-node-obs-receptionists tuple) (spec-step-revealed-addresses s-step)))
                   (simulation-node-unobs-receptionists tuple))))
              ;; Debugging only
              ;; (for ([new-tuple new-tuples])
              ;;   (printf "pre-sbc: ~s\n" new-tuple)
              ;;   (printf "post-sbc: ~s\n" (sbc new-tuple)))
              (for ([sbc-tuple (append* (map sbc new-tuples))])
                (incoming-add! incoming sbc-tuple (list tuple i-step s-step))
                (unless (or (member sbc-tuple (queue->list to-visit))
                            (set-member? related-tuples sbc-tuple)
                            (set-member? unrelated-successors sbc-tuple)
                            (equal? sbc-tuple tuple))
                  (enqueue! to-visit sbc-tuple)))))
          (loop (set-add related-tuples tuple) unrelated-successors)])])))

;; TODO: add a test that the "incoming" dictionary is properly set up (this had a bug before)

(define (impl-steps-from impl-state obs-receptionists unobs-receptionists)
  (define (add-observed-flag transition observed?)
    (impl-step observed?
               (csa#-transition-trigger transition)
               (csa#-transition-outputs transition)
               (csa#-transition-final-config transition)))

  (append (map (curryr add-observed-flag #t)
               (external-message-transitions impl-state obs-receptionists #t))
          (map (curryr add-observed-flag #f)
               (append
                (external-message-transitions impl-state unobs-receptionists #f)
                (csa#-handle-all-internal-messages impl-state)
                (csa#-handle-all-timeouts impl-state)))))

;; Returns all possible transitions of the given program config caused by a received message to any of
;; the given receptionist addresses
(define (external-message-transitions prog-config receptionists observed?)
  (append*
   (for/list ([receptionist receptionists])
     (display-step-line "Enumerating abstract messages (typed)")
     (for/fold ([transitions-so-far null])
               ;; TODO: get the max depth from somewhere
               ([message (generate-abstract-messages (csa#-receptionist-type receptionist) 10)])
       (display-step-line "Evaluating a handler")
       ;; TODO: deal with the "observed?" flag
       (append transitions-so-far
               (csa#-handle-message prog-config receptionist message))))))

;; Returns a set of the possible spec steps (see the struct above) from the given spec config that
;; match the given implementation step
(define (matching-spec-steps spec-config i-step)
  (define matched-stepped-configs (mutable-set))
  (for ([(trigger-result) (aps#-steps-for-trigger spec-config
                                          (impl-step-from-observer? i-step)
                                          (impl-step-trigger i-step))])
    (match-define (list config spawns1) trigger-result)
    (match (aps#-resolve-outputs config (impl-step-outputs i-step))
      [#f matched-stepped-configs]
      [(list stepped-spec-config spawns2 revealed-addresses satisfied-commitments)
       ;; TODO: record the satisfied commitments somehow
       (set-add! matched-stepped-configs (spec-step stepped-spec-config
                                                    (append spawns1 spawns2)
                                                    revealed-addresses))]))
  matched-stepped-configs)

(module+ test
  (define null-spec-config (make-Σ# '((define-state (S))) '(goto S) null))

  (test-case "Null transition okay for unobs"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step #f '(internal-receive (init-addr 0 Nat) (* Nat)) null #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "Null transition not okay for observed input"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step #t '(external-receive (init-addr 0 Nat) (* Nat)) null #f))
     (mutable-set)))
  (test-case "No match if trigger does not match"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A) [x -> (goto A)])) '(goto A) null)
      (impl-step #t '(external-receive (init-addr 0 Nat) (* Nat)) null #f))
     (mutable-set)))
  (test-case "Unobserved outputs don't need to match"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step #f '(internal-receive (init-addr 0 Nat) (* Nat)) (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step null-spec-config null null))))
  (test-case "No match if outputs do not match"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A))) '(goto A) (list '((obs-ext 1 Nat))))
      (impl-step #f '(internal-receive (init-addr 0 Nat) (* Nat)) (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set)))
  (test-case "Output can be matched by previous commitment"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A))) '(goto A) (list '((obs-ext 1 Nat) (single *))))
      (impl-step #f '(internal-receive (init-addr 0 Nat) (* Nat)) (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step (make-Σ# '((define-state (A))) '(goto A) (list '((obs-ext 1 Nat)))) null null))))
  (test-case "Output can be matched by new commitment"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))])) '(goto A) null)
      (impl-step #t '(external-receive (init-addr 0 Nat) (obs-ext 1 Nat)) (list '((obs-ext 1 Nat) (* Nat))) #f))
     (mutable-set (spec-step (make-Σ# '((define-state (A) [x -> (with-outputs ([x *]) (goto A))]))
                              '(goto A)
                              (list '((obs-ext 1 Nat))))
                             null
                             null))))
  (test-case "Multiple copies of same commitment get merged"
    (check-equal?
     (matching-spec-steps
      (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) (list '[(obs-ext 1 Nat) (single *)]))
      (impl-step #t '(external-receive (init-addr 0 Nat) (* Nat)) null #f))
     (mutable-set
      (spec-step (make-Σ# '((define-state (A x) [* -> (with-outputs ([x *]) (goto A x))])) '(goto A (obs-ext 1 Nat)) (list '[(obs-ext 1 Nat) (many *)]))
                 null
                 null)))))

;; TODO: rename this function to something more generic (not incoming-based)
(define (incoming-add! incoming key new-tuple)
  (match (hash-ref incoming key #f)
    [#f
     (hash-set! incoming key (mutable-set new-tuple))]
    [the-set
     (set-add! the-set new-tuple)]))

;; Splits, blurs and canonicalizes the given tuple, returning the resulting tuple
(define (sbc tuple)
  (for/list ([spec-config-component (split-spec (simulation-node-spec-config tuple))])
    ;; TODO: make it an "error" for a non-precise address to match a spec state parameter
    (display-step-line "Abstracting a program")
    (match-define (list abstracted-prog-config
                        aged-spec
                        abstracted-obs-receptionists
                        abstracted-unobs-receptionists)
      (abstract-by-spec (simulation-node-prog-config tuple)
                        (simulation-node-obs-receptionists tuple)
                        (simulation-node-unobs-receptionists tuple)
                        spec-config-component))
    (display-step-line "Canonicalizing the tuple, adding to queue")
    (match-define (list canonicalized-prog
                        canonicalized-spec
                        canonicalized-obs-recs
                        canonicalized-unobs-recs)
      (canonicalize-tuple (list abstracted-prog-config
                                aged-spec
                                abstracted-obs-receptionists
                                abstracted-unobs-receptionists)))

    (simulation-node canonicalized-prog
                     canonicalized-spec
                     canonicalized-obs-recs
                     canonicalized-unobs-recs)))

;; Takes abstract prog config and abstract spec config; returns prog further abstracted according to
;; spec
;;
;; TODO: maybe rename this to "project", since it's a kind of projection (or just to "blur")
(define (abstract-by-spec p obs-receptionists unobs-receptionists s)
  (define spawn-flag-to-blur
    (let ([spec-address (aps#-config-only-instance-address s)])
      (if (or (csa#-new-spawn-address? spec-address)
              (aps#-null-address? spec-address))
          'OLD
          'NEW)))

  (list
   (csa#-merge-duplicate-messages
    (blur-externals
     (blur-irrelevant-actors p spawn-flag-to-blur)
     (aps#-relevant-external-addrs s)))
   (aps#-age-address s)
   (csa#-blur-and-age-receptionists obs-receptionists spawn-flag-to-blur)
   (csa#-blur-and-age-receptionists unobs-receptionists spawn-flag-to-blur)))

(module+ test
  (test-equal? "check that messages with blurred addresses get merged together"
   (abstract-by-spec (term (()
                            (((init-addr 2 Nat) (obs-ext 1 Nat) 1)
                             ((init-addr 2 Nat) (obs-ext 2 Nat) 1)
                             ((init-addr 2 Nat) (obs-ext 3 Nat) 1))
                            ()
                            ()))
                     null
                     null
                     (term ((,aps#-no-transition-instance) (((obs-ext 3 Nat))))))
   (list (term (()
                (((init-addr 2 Nat) (* (Addr Nat)) *)
                 ((init-addr 2 Nat) (obs-ext 3 Nat) 1))
                ()
                ()))
         (term ((,aps#-no-transition-instance) (((obs-ext 3 Nat)))))
         null
         null)))

;; Returns the list of split spec-configs from the given one, failing if any of the FSMs share an
;; address
;;
;; TODO: move this to the APS# module, since it has to deal so much with the internal representation
(define (split-spec config)
  (define-values (fsm-specs remaining-commitment-map)
    (for/fold ([fsm-specs null]
               [remaining-commitment-map (aps#-config-commitment-map config)])
              ([instance (aps#-config-instances config)])
     (define (entry-relevant? entry)
       (member (aps#-commitment-entry-address entry)
               (aps#-instance-arguments instance)))
      (define relevant-entries (filter entry-relevant? remaining-commitment-map))
      (values
       (cons (aps#-spec-from-fsm-and-commitments instance relevant-entries) fsm-specs)
       (filter (negate entry-relevant?) remaining-commitment-map))))
  (append fsm-specs (map aps#-spec-from-commitment-entry remaining-commitment-map)))

(module+ test
  (define simple-instance-for-split-test
    (term
     (((define-state (A x)
         [* -> (goto A x)]))
      (goto A (obs-ext 0 Nat))
      (init-addr 0 Nat))))

  (check-not-false (redex-match aps# z simple-instance-for-split-test))

  ;; split spec with one FSM gets same spec
  (check-equal?
   (split-spec (term ((,simple-instance-for-split-test) ())))
   (list (term ((,simple-instance-for-split-test) ()))))

  ;; split with one related commit
  (check-equal?
   (split-spec (term ((,simple-instance-for-split-test) (((obs-ext 0 Nat) (single *))))))
   (list (term ((,simple-instance-for-split-test) (((obs-ext 0 Nat) (single *)))))))

  ;; split with unrelated commit
  (check-same-items?
   (split-spec (term ((,simple-instance-for-split-test) (((obs-ext 1 Nat) (single *))))))
   (list (term ((,simple-instance-for-split-test) ()))
         (term ((,aps#-no-transition-instance) (((obs-ext 1 Nat) (single *))))))))

(define (remove-unsupported-tuples all-tuples incoming init-related-spec-steps init-unrelated-successors)
  (define remaining-tuples (set-copy all-tuples))
  (define unrelated-successors (apply queue (set->list init-unrelated-successors)))
  (define related-spec-steps (hash-copy init-related-spec-steps))

  (let loop ()
    (match (dequeue-if-non-empty! unrelated-successors)
      [#f (list remaining-tuples related-spec-steps)]
      [unrelated-tuple
       (for ([transition (hash-ref incoming unrelated-tuple)])
         (match-define (list predecessor i-step s-step) transition)
         (when (set-member? remaining-tuples predecessor)
           (define spec-steps (hash-ref related-spec-steps (list predecessor i-step)))
           (when (set-member? spec-steps s-step)
             (set-remove! spec-steps s-step)
             (when (set-empty? spec-steps)
               (set-remove! remaining-tuples predecessor)
               (enqueue! unrelated-successors predecessor)))))
       (loop)])))

(module+ test
  (require "hash-helpers.rkt")

  ;; Because remove-unsupported does not care about the actual content of the impl or spec
  ;; configurations, we replace them here with letters (A, B, C, etc. for impls and X, Y, Z, etc. for
  ;; specs) for simplification
  (define ax-tuple (simulation-node 'A 'X #f #f))
  (define by-tuple (simulation-node 'B 'Y #f #f))
  (define bz-tuple (simulation-node 'B 'Z #f #f))
  (define cw-tuple (simulation-node 'C 'W #f #f))

  (define aa-step (impl-step #f '(timeout (init-addr 0 Nat)) null 'A))
  (define xx-step (spec-step 'X null null))
  (define ab-step (impl-step #f '(timeout (init-addr 0 Nat)) null 'B))
  (define xy-step (spec-step 'Y null null))
  (define xz-step (spec-step 'Z null null))
  (define bc-step (impl-step #f '(timeout (init-addr 0 Nat)) null 'C))
  (define yw-step (spec-step 'W null null))

  (test-equal? "Remove no nodes, because no list"
    (remove-unsupported-tuples
     (mutable-set ax-tuple)
     ;; incoming
     (mutable-hash [ax-tuple (mutable-set (list ax-tuple aa-step xx-step))])
     ;; related spec steps
     (mutable-hash [(list ax-tuple aa-step) (mutable-set xx-step)])
     ;; unrelated sucessors
     null)
    (list
     (mutable-set ax-tuple)
     (mutable-hash [(list ax-tuple aa-step) (mutable-set xx-step)])))

  (test-equal? "Remove no nodes, because unrelated-matches contained only a redundant support"
    (remove-unsupported-tuples
     (mutable-set ax-tuple bz-tuple)
     (mutable-hash [by-tuple (mutable-set (list ax-tuple ab-step xy-step))]
                   [bz-tuple (mutable-set (list ax-tuple ab-step xz-step))]
                   [ax-tuple (mutable-set)])
     (mutable-hash [(list ax-tuple ab-step) (mutable-set xy-step xz-step)])
     (list by-tuple))
    (list
     (mutable-set ax-tuple bz-tuple)
     (mutable-hash [(list ax-tuple ab-step) (mutable-set xz-step)])))

  (test-equal? "Remove last remaining node"
    (remove-unsupported-tuples
     (mutable-set ax-tuple)
     (mutable-hash [by-tuple (mutable-set (list ax-tuple ab-step xy-step))]
                   [ax-tuple (mutable-set)])
     (mutable-hash [(list ax-tuple ab-step) (mutable-set xy-step)])
     (list by-tuple))
    (list
     (mutable-set)
     (mutable-hash [(list ax-tuple ab-step) (mutable-set)])))

  (test-equal? "Remove a redundant support"
    (remove-unsupported-tuples
     (mutable-set ax-tuple bz-tuple by-tuple)
     ;; incoming
     (mutable-hash [by-tuple (mutable-set (list ax-tuple ab-step xy-step))]
                   [bz-tuple (mutable-set (list ax-tuple ab-step xz-step))]
                   [ax-tuple (mutable-set)]
                   [cw-tuple (mutable-set (list by-tuple bc-step yw-step))])
     ;; matching spec steps
     (mutable-hash [(list ax-tuple ab-step) (mutable-set xy-step xz-step)]
                   [(list by-tuple bc-step) (mutable-set yw-step)])
     ;; unrelated successors
     (list cw-tuple))
    (list
     (mutable-set ax-tuple bz-tuple)
     (mutable-hash [(list ax-tuple ab-step) (mutable-set xz-step)]
                   [(list by-tuple bc-step) (mutable-set)])))

    (test-equal? "Remove a non-redundant support"
      (remove-unsupported-tuples
       (mutable-set ax-tuple by-tuple)
       ;; incoming
       (mutable-hash [by-tuple (mutable-set (list ax-tuple ab-step xy-step))]
                     [ax-tuple (mutable-set)]
                     [cw-tuple (mutable-set (list by-tuple bc-step yw-step))])
       ;; matching spec steps
       (mutable-hash [(list ax-tuple ab-step) (mutable-set xy-step)]
                     [(list by-tuple bc-step) (mutable-set yw-step)])
       ;; unrelated successors
       (list cw-tuple))
      (list
       (mutable-set)
       (mutable-hash [(list ax-tuple ab-step) (mutable-set)]
                     [(list by-tuple bc-step) (mutable-set)]))))

;; ---------------------------------------------------------------------------------------------------
;; Commitment Satisfaction

;; TODO: when walking the edges, take care of edges that do an address rename (because the commitment
;; will also need to be renamed)

(define (find-satisfying-tuples simulation-tuples related-spec-steps)
  ;; TODO: implement this for real
  simulation-tuples)

;; ---------------------------------------------------------------------------------------------------
;; Misc. Helpers

;; Returns the unique minimal element from the list according to the rank function, if there is such
;; an element, or #f otherwise
(define (unique-min elements rank)
  (cond
    [(null? elements) #f]
    [else
       (define rank-list (map (lambda (e) (cons (rank e) e)) elements))
       (define min-rank (apply min (map car rank-list)))
       (match (filter (lambda (re) (equal? (car re) min-rank)) rank-list)
         [(list re) (cdr re)]
         [_ #f])]))

(module+ test
  (check-false (unique-min null values))
  (check-equal? (unique-min (list 1 2 3) values) 1)
  (check-equal? (unique-min (list 3 2 1) values) 1)
  (check-false (unique-min (list 3 1 2 1) values))

  (check-false (unique-min (list "a" "aa" "b" "aaa") string-length))
  (check-equal? (unique-min (list "a" "aa" "aaa") string-length) "a"))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define DISPLAY-STEPS #f)

(define LOG-TUPLES #f)

(define (display-step-line msg)
  (when DISPLAY-STEPS (displayln msg)))

(define (tuple->debug-tuple tuple)
  (list (prog-config-without-state-defs (simulation-node-prog-config tuple))
        (spec-config-without-state-defs (simulation-node-spec-config tuple))
        (simulation-node-obs-receptionists tuple)
        (simulation-node-unobs-receptionists tuple)))

;; ---------------------------------------------------------------------------------------------------
;; Top-level tests

(module+ test
  ;;;; Ignore everything

  (define (make-ignore-all-config addr-type)
    (make-single-agent-config
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

  (check-true (analyze ignore-all-config
                       ignore-all-spec-instance
                       (term ((addr 0 Nat))) null))

  ;;;; Send one message to a statically-known address per request

  (define (make-static-response-address type) (term (addr 2 ,type)))
  (define static-response-address (make-static-response-address (term (Union (Ack Nat)))))
  (define static-response-agent
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-agent
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

  (check-not-false (redex-match csa-eval αn static-response-agent))
  (check-not-false (redex-match csa-eval αn static-double-response-agent))
  (check-not-false (redex-match aps-eval z static-response-spec))
  (check-not-false (redex-match aps-eval z ignore-all-with-addr-spec-instance))

  (test-true "Static response works"
             (analyze (make-single-agent-config static-response-agent)
                      static-response-spec
                      (term ((addr 0 Nat))) null))
  (test-false "Static response agent, ignore all spec"
              (analyze (make-single-agent-config static-response-agent)
                       ignore-all-with-addr-spec-instance
                       (term ((addr 0 Nat))) null))
  (test-false "static double response agent"
              (analyze (make-single-agent-config static-double-response-agent)
                       static-response-spec
                       (term ((addr 0 Nat))) null))
  (test-false "Static response spec, ignore-all config"
               (analyze ignore-all-config
                        static-response-spec
                        (term ((addr 0 Nat))) null))

  ;;;; Pattern matching tests, without dynamic channels

  (define pattern-match-spec
    (term
     (((define-state (Matching r)
         [(variant A *) -> (with-outputs ([r (variant A *)]) (goto Matching r))]
         [(variant B *) -> (with-outputs ([r (variant B *)]) (goto Matching r))]))
      (goto Matching ,static-response-address)
      (addr 0 (Union [A Nat] [B Nat])))))

  (define pattern-matching-agent
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A x)) (goto Always r))]
            [(B y) (begin (send r (variant B 0)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define reverse-pattern-matching-agent
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant B 0)) (goto Always r))]
            [(B y) (begin (send r (variant A y)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define partial-pattern-matching-agent
    (term
     ((addr 0 (Union [A Nat] [B Nat]))
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A 0)) (goto Always r))]
            [(B y) (goto Always r)])))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match aps-eval z pattern-match-spec))
  (check-not-false (redex-match csa-eval αn pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn reverse-pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn partial-pattern-matching-agent))

  (check-true (analyze (make-single-agent-config pattern-matching-agent)
                       pattern-match-spec
                       (term ((addr 0 (Union [A Nat] [B Nat])))) null))
  (test-false "Send on A but not B; should send on both"
              (analyze (make-single-agent-config partial-pattern-matching-agent)
                       pattern-match-spec
                       (term ((addr 0 (Union [A Nat] [B Nat])))) null))
  (check-false (analyze (make-single-agent-config reverse-pattern-matching-agent)
                        pattern-match-spec
                        (term ((addr 0 (Union [A Nat] [B Nat])))) null))

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
  (define request-response-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Always [i Nat]) (response-target)
          (begin
            (send response-target i)
            (goto Always i))))
       (goto Always 0)))))
  (define respond-to-first-addr-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: also try the case where we save new-response-target instead
            (goto HaveAddr i response-target))))
       (goto Init)))))
  (define respond-to-first-addr-agent2
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
  (define delay-saving-address-agent
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
  (define double-response-agent
    `((addr 0 (Addr Nat))
      (((define-state (Always [i Nat]) (response-dest)
          (begin
            (send response-dest i)
            (send response-dest i)
            (goto Always i))))
       (goto Always 0))))
  (define respond-once-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto NoMore)))
        (define-state (NoMore) (new-response-target)
          (goto NoMore)))
       (goto Init)))))

  (check-not-false (redex-match aps-eval z request-response-spec))
  (check-not-false (redex-match aps-eval z request-same-response-addr-spec))
  (check-not-false (redex-match csa-eval αn request-response-agent))
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-agent))
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-agent2))
  (check-not-false (redex-match csa-eval αn double-response-agent))
  (check-not-false (redex-match csa-eval αn delay-saving-address-agent))
  (check-not-false (redex-match csa-eval αn respond-once-agent))

  (check-true (analyze (make-single-agent-config request-response-agent)
                       request-response-spec
                       (term ((addr 0 (Addr Nat)))) null))
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent)
                        request-response-spec
                        (term ((addr 0 (Addr Nat)))) null))
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent2)
                        request-response-spec
                        (term ((addr 0 (Addr Nat)))) null))
  (check-false (analyze (make-single-agent-config request-response-agent)
                        request-same-response-addr-spec
                        (term ((addr 0 (Addr Nat)))) null))
  (test-false "ignore all actor does not satisfy request/response"
              (analyze (make-ignore-all-config (term (Addr Nat)))
                        request-response-spec
                        (term ((addr 0 (Addr Nat)))) null))
  (test-false "Respond-once actor does not satisfy request/response"
              (analyze (make-single-agent-config respond-once-agent)
                       request-response-spec
                       (term ((addr 0 (Addr Nat)))) null))
  (check-true (analyze (make-single-agent-config respond-to-first-addr-agent)
                       request-same-response-addr-spec
                       (term ((addr 0 (Addr Nat)))) null))
  (check-true (analyze (make-single-agent-config respond-to-first-addr-agent2)
                       request-same-response-addr-spec
                       (term ((addr 0 (Addr Nat)))) null))
  (check-false (analyze (make-single-agent-config double-response-agent)
                        request-response-spec
                        (term ((addr 0 (Addr Nat)))) null))
  (check-false (analyze (make-single-agent-config delay-saving-address-agent)
                        request-response-spec
                        (term ((addr 0 (Addr Nat)))) null))

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
  (check-true (analyze (make-single-agent-config reply-once-actor)
                       maybe-reply-spec
                       (term ((addr 0 (Addr Nat)))) null))

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
  (define primitive-branch-agent
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
  (check-not-false (redex-match csa-eval αn primitive-branch-agent))

  (check-true (analyze (make-single-agent-config primitive-branch-agent)
                       zero-nonzero-spec
                       (term ((addr 0 Nat))) null))
  (check-false (analyze (make-single-agent-config primitive-branch-agent)
                        zero-spec (term ((addr 0 Nat))) null))

  ;;;; Optional Commitments
  (define optional-commitment-spec
    (term
     (((define-state (Always r)
         [* -> (with-outputs ([r *]) (goto Always r))]
         [* -> (goto Always r)]))
      (goto Always (addr 1 (Addr Nat)))
      (addr 0 Nat))))

  (check-not-false (redex-match aps-eval z optional-commitment-spec))
  (check-true (analyze ignore-all-config
                       optional-commitment-spec
                       (term ((addr 0 Nat))) null))

  ;;;; Stuck states in concrete evaluation

  (define nat-to-nat-spec
    (term
     (((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (define div-by-one-agent
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 1))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define div-by-zero-agent
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match aps-eval z nat-to-nat-spec))
  (check-not-false (redex-match csa-eval αn div-by-zero-agent))
  (check-not-false (redex-match csa-eval αn div-by-one-agent))

  (test-true "Div by one vs. nat-to-nat spec"
             (analyze (make-single-agent-config div-by-one-agent)
                       nat-to-nat-spec
                       (term ((addr 0 Nat))) null))
  (test-true "Div by zero vs. nat-to-nat spec"
              (analyze (make-single-agent-config div-by-zero-agent)
                       nat-to-nat-spec
                       (term ((addr 0 Nat))) null))

  ;;;; Unobservable communication

  ;; wildcard unobservables are ignored for the purpose of output commitments
  (test-true "request/response actor vs. ignore-all spec"
             (analyze (make-single-agent-config request-response-agent)
                      (make-ignore-all-spec-instance '(Addr Nat))
                      (term ((addr 0 (Addr Nat)))) null))

  ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect conformance
  (test-true "request response actor and spec, with unobs communication"
             (analyze (make-single-agent-config request-response-agent)
                      request-response-spec
                      (term ((addr 0 (Addr Nat))))
                      (term ((addr 0 (Addr Nat))))))

  ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
  (test-false "static response with unobs communication"
              (analyze (make-single-agent-config static-response-agent)
                       static-response-spec
                       (term ((addr 0 Nat)))
                       (term ((addr 0 Nat)))))

  ;; 3. Conformance regained for static req/resp when add an unobs transition
  (define static-response-spec-with-unobs
    (term
     (((define-state (Always response-dest)
         [*     -> (with-outputs ([response-dest *]) (goto Always response-dest))]
         [unobs -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      (addr 0 Nat))))
  (check-not-false (redex-match aps-eval z static-response-spec-with-unobs))

  (check-true (analyze (make-single-agent-config static-response-agent)
                       static-response-spec-with-unobs
                       (term ((addr 0 Nat)))
                       (term ((addr 0 Nat)))))

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
           (addr 0 (Union [FromObserver] [FromUnobservedEnvironment])))))
  (define unobs-toggle-agent
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
  (define unobs-toggle-agent-wrong1
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
  (define unobs-toggle-agent-wrong2
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
  (define unobs-toggle-agent-wrong3
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
  (define unobs-toggle-agent-wrong4
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
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong1))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong2))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong3))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong4))

  (test-true "Obs/Unobs test"
             (analyze (make-single-agent-config unobs-toggle-agent)
                      unobs-toggle-spec
                      (term ((addr 0 (Union [FromObserver]))))
                      (term ((addr 0 (Union [FromUnobservedEnvironment]))))))

  (for ([agent (list unobs-toggle-agent-wrong1
                     unobs-toggle-agent-wrong2
                     unobs-toggle-agent-wrong3
                     unobs-toggle-agent-wrong4)])
    (test-false "Obs/Unobs bug-finding test(s)"
                (analyze (make-single-agent-config agent)
                         unobs-toggle-spec
                         (term ((addr 0 (Union [FromObserver]))))
                         (term ((addr 0 (Union [FromUnobservedEnvironment])))))))

  ;;;; Records

  (define record-req-resp-spec
    (term
     (((define-state (Always)
         [(record [dest dest] [msg (variant A)]) -> (with-outputs ([dest (variant A)]) (goto Always))]
         [(record [dest dest] [msg (variant B)]) -> (with-outputs ([dest (variant B)]) (goto Always))]))
      (goto Always)
      (addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])])))))
  (define record-req-resp-agent
    (term
     ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
      (((define-state (Always) (m)
          (begin
            (send (: m dest) (: m msg))
            (goto Always))))
       (goto Always)))))
  (define record-req-wrong-resp-agent
    (term
     ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
      (((define-state (Always) (m)
          (begin
            (send (: m dest) (variant A))
            (goto Always))))
       (goto Always)))))

  (check-not-false (redex-match aps-eval z record-req-resp-spec))
  (check-not-false (redex-match csa-eval αn record-req-resp-agent))
  (check-not-false (redex-match csa-eval αn record-req-wrong-resp-agent))

  ;; TODO: figure out why this test fails when max-depth for the program and the messages is set to
  ;; 0
  (check-true (analyze (make-single-agent-config record-req-resp-agent)
                       record-req-resp-spec
                       (term ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))))
                       null))
  (check-false (analyze (make-single-agent-config record-req-wrong-resp-agent)
                        record-req-resp-spec
                        (term ((addr 0 (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))))
                        null))

  ;;;; Let
  (define static-response-let-agent
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (let ([new-r response-dest])
            (begin
              (send new-r (variant Ack 0))
              (goto Always new-r)))))
       (goto Always ,static-response-address)))))
  (define static-double-response-let-agent
    (term
     ((addr 0 Nat)
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (let ([new-r response-dest])
            (begin
              (send new-r (variant Ack 0))
              (send new-r (variant Ack 0))
              (goto Always new-r)))))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match csa-eval αn static-response-let-agent))
  (check-not-false (redex-match csa-eval αn static-double-response-let-agent))

  (check-true (analyze (make-single-agent-config static-response-let-agent)
                       static-response-spec
                       (term ((addr 0 Nat))) null))
  (check-false (analyze (make-single-agent-config static-double-response-let-agent)
                        static-response-spec
                        (term ((addr 0 Nat))) null))

  ;; Check that = gives both results
  (define equal-agent-wrong1
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
  (define equal-agent-wrong2
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
    (define equal-agent
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

  (check-not-false (redex-match csa-eval αn equal-agent-wrong1))
  (check-not-false (redex-match csa-eval αn equal-agent-wrong2))
  (check-not-false (redex-match csa-eval αn equal-agent))

  (test-false "Equal agent wrong 1"
   (analyze (make-single-agent-config equal-agent-wrong1)
            static-response-spec
            (term ((addr 0 Nat))) null))
  (test-false "Equal agent wrong 2"
   (analyze (make-single-agent-config equal-agent-wrong2)
            static-response-spec
            (term ((addr 0 Nat))) null))
  (check-true
   (analyze (make-single-agent-config equal-agent)
            static-response-spec
            (term ((addr 0 Nat))) null))

  ;;;; For loops
  (define loop-do-nothing-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (m)
          (begin
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define loop-send-unobs-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A [r (Addr Nat)]) (m)
          (begin
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              (send r i))
            (goto A r))))
       (goto A ,static-response-address)))))
  (define send-before-loop-agent
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
  (define send-inside-loop-agent
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A) (r)
          (begin
            (for/fold ([folded 0])
                      ([r (list r)])
              (send r 0))
            (goto A))))
       (goto A)))))
  (define send-after-loop-agent
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

  (check-not-false (redex-match csa-eval αn loop-do-nothing-agent))
  ;; TODO: figure out why this test works even when unobs stuff should be bad...
  (check-not-false (redex-match csa-eval αn loop-send-unobs-agent))
  (check-not-false (redex-match csa-eval αn send-before-loop-agent))
  (check-not-false (redex-match csa-eval αn send-inside-loop-agent))
  (check-not-false (redex-match csa-eval αn send-after-loop-agent))

  (check-true (analyze (make-single-agent-config loop-do-nothing-agent)
                       (make-ignore-all-spec-instance '(Addr Nat))
                       (term ((addr 0 (Addr Nat))))
                       null))
  (check-true (analyze (make-single-agent-config loop-send-unobs-agent)
                       (make-ignore-all-spec-instance '(Addr Nat))
                       (term ((addr 0 (Addr Nat))))
                       null))
  (check-true (analyze (make-single-agent-config send-before-loop-agent)
                       request-response-spec
                       (term ((addr 0 (Addr Nat)))) null))
  ;; TODO: get this test working again (need to at least check that none of the outputs in a loop were
  ;; observed)
  ;;
  ;; (check-false (analyze (make-single-agent-config send-inside-loop-agent)
  ;;                      request-response-spec
  ;;                      (term ((addr 0 (Addr Nat)))) null
  ;;                      (hash 'A 'Always)))
  (check-true (analyze (make-single-agent-config send-after-loop-agent)
                       request-response-spec
                       (term ((addr 0 (Addr Nat)))) null))

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
  (define timeout-and-send-agent
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
  (check-not-false (redex-match csa-eval αn timeout-and-send-agent))
  (check-true (analyze (make-single-agent-config timeout-and-send-agent)
                       timeout-spec
                       (term ((addr 0 Nat))) null))
  (check-false (analyze (make-single-agent-config timeout-and-send-agent)
                       got-message-only-spec
                       (term ((addr 0 Nat))) null))

  ;; Multiple Disjoint Actors
  (define static-response-agent2
    (term
     ((addr 1 Nat)
      (((define-state (Always2 [response-dest (Addr (Union [Ack Nat]))]) (m)
             (begin
               (send response-dest (variant Ack 0))
               (goto Always2 response-dest))))
       (goto Always2 ,static-response-address)))))
  (define other-static-response-agent
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

  (check-not-false (redex-match csa-eval αn static-response-agent2))
  (check-not-false (redex-match csa-eval αn other-static-response-agent))
  (check-not-false (redex-match aps-eval z static-response-with-extra-spec))

  (test-false "Multi agent test 1"
              (analyze
                (make-empty-queues-config (list static-response-agent static-response-agent2) null)
                static-response-spec
                (term ((addr 0 Nat))) (term ((addr 1 Nat)))))
  (test-true "Multi agent test 2"
             (analyze
              (make-empty-queues-config (list static-response-agent static-response-agent2) null)
              static-response-with-extra-spec
              (term ((addr 0 Nat))) (term ((addr 1 Nat)))))
  (test-true "Multi agent test 3"
             (analyze
               (make-empty-queues-config (list static-response-agent other-static-response-agent) null)
               static-response-spec
               (term ((addr 0 Nat))) (term ((addr 1 Nat)))))

  ;; Multiple specifications
  (define other-static-response-spec
    (term
     (((define-state (Always2 response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always2 response-dest))]))
      (goto Always2 (addr 3 (Union [Ack Nat])))
      (addr 1 Nat))))

  (check-not-false (redex-match aps-eval z other-static-response-spec))

  (test-true "Multi-spec test"
             (model-check
              (make-empty-queues-config (list static-response-agent other-static-response-agent) null)
              (aps-config-from-instances (list static-response-spec other-static-response-spec))
              (term ((addr 0 Nat) (addr 1 Nat))) null))

  ;; Actors working together
  (define statically-delegating-responder-actor
    (term
     ((addr 0 (Addr Nat))
      (((define-state (A [responder (Addr (Addr Nat))]) (m)
          (begin
            (send responder m)
            (goto A responder))))
       (goto A (addr 1 (Addr Nat)))))))

  (define request-response-agent2
    (term
     ((addr 1 (Addr Nat))
      (((define-state (Always) (response-target)
          (begin
            (send response-target 0)
            (goto Always))))
       (goto Always)))))

  (check-not-false (redex-match csa-eval αn statically-delegating-responder-actor))
  (check-not-false (redex-match csa-eval αn request-response-agent2))

  (test-true "Multiple actors 3"
             (analyze
              (make-empty-queues-config (list request-response-agent2 statically-delegating-responder-actor) null)
              request-response-spec
              (term ((addr 0 (Addr Nat)))) null))

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
      null)))

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
             (analyze
              (make-single-agent-config self-reveal-actor)
              self-reveal-spec
              null null))
  ;; TODO: redo this test later
  ;; (test-false "Catch self-reveal of wrong address"
  ;;             (analyze
  ;;              (make-single-agent-config reveal-wrong-address-actor)
  ;;              self-reveal-spec
  ;;              (term ((addr 0 (Addr (Addr (Addr Nat)))))) null
  ;;              (hash)))
  (test-false "Catch self-reveal of actor that doesn't follow its behavior"
              (analyze
               (make-single-agent-config reveal-self-double-output-actor)
               self-reveal-spec
               null null))

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
             (analyze
              (make-single-agent-config echo-spawning-actor)
              echo-spawn-spec
              ;; Echo receives messages of type Addr Nat
              ;; The echo user receives message of type (Addr (Addr Nat))
              ;; The echo creator receives messages of type (Addr (Addr (Addr Nat)))
              (term ((addr 0 (Addr (Addr (Addr Nat)))))) null))
  ;; TODO: also add a sink-spawning actor when commitment satisfaction is working
  (test-false "Spawned double-response actor does not match dynamic response spec"
              (analyze
               (make-single-agent-config double-response-spawning-actor)
                echo-spawn-spec
                (term ((addr 0 (Addr (Addr (Addr Nat)))))) null)))
