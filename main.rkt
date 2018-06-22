#lang racket

;; Implements the top-level function, "check-conformance", and includes the core of the
;; conformance-checking algorithm

;; (provide
;;  check-conformance

;;  ;; Needed only for debugging in other files
;;  ;; impl-steps-from
;;  ;; matching-spec-steps
;;  ;; debug-impl-step
;;  ;; check-conformance/config
;;  ;; prune-unsupported
;;  ;; partition-by-satisfaction
;;  ;; impl-config-without-state-defs
;;  ;; spec-config-without-state-defs
;;  )

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
 "optimization-parameters.rkt"
 "queue-helpers.rkt"
 "set-helpers.rkt"
 "statistics.rkt")

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   (for-syntax syntax/parse)
   "rackunit-helpers.rkt"))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Top-level Algorithm

;; ;; Returns the result of running the conformance-check algorithm below on the instantiated program and
;; ;; specification.
;; (define/contract (check-conformance program specification
;;                                     #:use-widen? [use-widen? #t]
;;                                     #:memoize-eval-handler? [memoize-eval-handler? #t]
;;                                     #:use-eviction? [use-eviction? #t]
;;                                     #:stats-directory [stats-directory #f])
;;   (->* (csa-valid-program? aps-valid-spec?)
;;        (#:use-widen? boolean?
;;         #:memoize-eval-handler? boolean?
;;         #:use-eviction? boolean?
;;         #:stats-directory (or/c boolean? string?))
;;        boolean?)
;;   (parameterize ([USE-WIDEN? use-widen?]
;;                  [MEMOIZE-EVAL-HANDLER? memoize-eval-handler?]
;;                  [USE-EVICTION? use-eviction?])
;;     (printf "OPTIMIZATIONS:\n")
;;     (printf "Widening: ~s\n" use-widen?)
;;     (printf "Memoize eval-handler: ~s\n" memoize-eval-handler?)
;;     (printf "Eviction: ~s\n\n" use-eviction?)
;;     (match-define (list impl-config spec-config) (instantiate-configs program specification))
;;     (check-conformance/config impl-config spec-config #:stats-directory stats-directory)))

;; ;; Given a concrete implementation configuration, a concrete specification configuration, returns #t
;; ;; if the conformance-check algorithm can prove that the implementation conforms to the specification,
;; ;; #f otherwise.
;; ;;
;; ;; The algorithm works by abstracting the given initial configurations into abstract configurations,
;; ;; then constructing a graph-like structure that acts as a constructive proof of conformance for the
;; ;; abstract pair (roughly, every vertex (pair of configurations) in the graph is in the conformance
;; ;; relation, and every edge points to the pair that supports some necessary dependency of the source
;; ;; pair. By the soundness theorem for abstract conformance, if conformance holds for the abstract
;; ;; pairs (i.e. the pairs are in the graph), then it holds for the original concrete pairs, as well.
;; ;;
;; ;; To construct this structure, the algorithm first abstractly interprets the implementation and
;; ;; specification to find configuration pairs in which the specification can simulate the
;; ;; implementation up to one step (see find-rank1-simulation). This process also uncovers all edges and
;; ;; vertices that related pairs would rely upon to be part of a full simulation relation. By removing
;; ;; from the graph all pairs that depend on pairs outside the graph and propagating the results of
;; ;; those removals backwards until we reach a greatest fixpoint (see prune-unsupported), we end up with
;; ;; a proof graph whose vertices are all configuration pairs in the simulation.
;; ;;
;; ;; Next, we identify the the vertices in the graph whose implementation configurations are not
;; ;; guaranteed to satisfy all of their commitments in every fair execution (see find-unsatisfying-pairs
;; ;; below). By removing these nodes and again back-propagating the effects of those removals (with
;; ;; prune-unsupported again), the resulting graph represents a proof that all of its members are in the
;; ;; conformance relation.
;; (define/contract (check-conformance/config initial-impl-config initial-spec-config
;;                                            #:stats-directory [stats-directory #f])
;;   (->* (csa-valid-config? aps-valid-config?)
;;        (#:stats-directory (or/c boolean? string?))
;;        boolean?)

;;   (reset-statistics)
;;   (with-handlers
;;     ([exn:break?
;;       (lambda (ex)
;;         (print-statistics)
;;         (raise ex))])
;;     (stat-set! STAT-start-time (date->string (seconds->date (current-seconds)) #t))
;;     ;; this thread will automatically end when the job is terminated, so we don't have to wait for it
;;     (thread
;;      (lambda ()
;;        (when stats-directory
;;          (unless (directory-exists? stats-directory)
;;            (make-directory stats-directory))
;;          (let loop ()
;;            ;; write to two different files, so that we always have one good file if the job is
;;            ;; terminated while we're writing to the file
;;            (sleep 60)
;;            (with-output-to-file (build-path stats-directory "stats1.txt") print-statistics #:exists 'replace)
;;            (sleep 60)
;;            (with-output-to-file (build-path stats-directory "stats2.txt") print-statistics #:exists 'replace)
;;            (loop)))))
;;     (define final-result
;;       (cond
;;         [(not (spec-interfaces-available? initial-impl-config initial-spec-config)) #f]
;;         [else
;;          (match (get-initial-abstract-pairs initial-impl-config initial-spec-config)
;;            [#f #f]
;;            [unwidened-initial-pairs
;;             (define initial-pairs
;;               (if (USE-WIDEN?)
;;                   (map (curryr widen-pair #f 0 0 0) unwidened-initial-pairs)
;;                   unwidened-initial-pairs))
;;             (match-define (list rank1-pairs
;;                                 rank1-unrelated-successors
;;                                 incoming-steps
;;                                 rank1-related-spec-steps)
;;               (find-rank1-simulation initial-pairs))
;;             (stat-set! STAT-simulation-finish-time (date->string (seconds->date (current-seconds)) #t))
;;             (stat-set! STAT-rank1-simulation-size (set-count rank1-pairs))
;;             ;; (printf "Finished rank1 simulation at: ~a\n" (stat-value STAT-simulation-finish-time))
;;             (match-define (list simulation-pairs simulation-related-spec-steps)
;;               (prune-unsupported rank1-pairs
;;                                  incoming-steps
;;                                  rank1-related-spec-steps
;;                                  rank1-unrelated-successors))
;;             (stat-set! STAT-simulation-prune-finish-time (date->string (seconds->date (current-seconds)) #t))
;;             (stat-set! STAT-simulation-size (set-count simulation-pairs))
;;             ;; (printf "Finished simulation prune at: ~a\n" (stat-value STAT-simulation-prune-finish-time))
;;             (cond
;;               [(andmap (curry set-member? simulation-pairs) initial-pairs)
;;                (match-define (list commitment-satisfying-pairs unsatisfying-pairs)
;;                  (partition-by-satisfaction simulation-pairs incoming-steps simulation-related-spec-steps))
;;                (stat-set! STAT-obligation-check-finish-time
;;                           (date->string (seconds->date (current-seconds)) #t))
;;                (stat-set! STAT-obl-checked-size (set-count commitment-satisfying-pairs))
;;                ;; (printf "Finished obligation fulfillment check at: ~a\n" (stat-value STAT-obligation-check-finish-time))
;;                ;; (printf "Unsatisfying pairs: ~s\n"
;;                ;;         (for/list ([p unsatisfying-pairs])
;;                ;;           (cons
;;                ;;            (impl-config-without-state-defs (config-pair-impl-config p))
;;                ;;            (spec-config-without-state-defs (config-pair-spec-config p)))))
;;                (match-define (list conforming-pairs _)
;;                  (prune-unsupported commitment-satisfying-pairs
;;                                     incoming-steps
;;                                     simulation-related-spec-steps
;;                                     unsatisfying-pairs))
;;                (stat-set! STAT-obligation-prune-finish-time (date->string (seconds->date (current-seconds)) #t))
;;                (stat-set! STAT-conformance-size (set-count conforming-pairs))
;;                ;; (printf "Finished obligation fulfillment prune at: ~a\n"
;;                ;;         (stat-value STAT-obligation-prune-finish-time))
;;                (andmap (curry set-member? conforming-pairs) initial-pairs)]
;;               [else
;;                ;; (printf "At least one initial configuration pair was not in the simulation\n")
;;                #f])])]))
;;     (stat-set! STAT-finish-time (date->string (seconds->date (current-seconds)) #t))
;;     (print-statistics)
;;     final-result))

;; ;; Returns #t if all addresses mentioned in observable or unobservable interfaces in the spec are
;; ;; receptionists; #f otherwise.
;; (define (spec-interfaces-available? impl-config spec-config)
;;   (define spec-receptionists (map second (aps-config-receptionists spec-config)))
;;   (define impl-receptionists (map second (csa-config-receptionists impl-config)))
;;   (and (andmap (curryr member impl-receptionists) spec-receptionists) #t))

;; (module+ test
;;   (test-false "spec address receptionist check 1"
;;     (spec-interfaces-available? (term ((((addr 1 0) (() (goto A)))) () () ()))
;;                                 (term (((Nat (addr 1 0))) () (goto A) () ()))))
;;   (test-false "spec address receptionist check 2"
;;     (spec-interfaces-available? (term ((((addr 500) (() (goto A)))) () () ()))
;;                                 (term (((Nat (addr 1 0))) () (goto A) () ()))))
;;   (test-not-false "spec address receptionist check 3"
;;     (spec-interfaces-available? (term ((((addr 1 0) (() (goto A)))) () ((Nat (addr 1 0))) ()))
;;                                 (term (((Nat (addr 1 0))) () (goto A) () ()))))
;;   (test-not-false "spec address receptionist check 4"
;;     (spec-interfaces-available? (term ((((addr 1 0) (() (goto A)))) () ((Nat (addr 1 0))) ()))
;;                                 (term (() () (goto A) () ()))))
;;   (test-false "spec address receptionist: unobserved addresses 1"
;;     (spec-interfaces-available? (term ((((addr 1 0) (() (goto A)))) () () ()))
;;                                 (term (() ((Nat (addr 1 0))) (goto A) () ()))))
;;   (test-not-false "spec address receptionist: unobserved addresses 2"
;;     (spec-interfaces-available? (term ((((addr 1 0) (() (goto A)))) () ((Nat (addr 1 0))) ()))
;;                                 (term (() ((Nat (addr 1 0))) (goto A) () ())))))

;; ;; Abstracts and sbc's the initial pair, returning the list of initial abstract pairs, or #f if the
;; ;; abstraction was not possible for some reason
;; (define (get-initial-abstract-pairs impl-config spec-config)
;;   (match (csa#-abstract-config impl-config)
;;     [#f #f]
;;     [abstract-impl-config
;;      (map first (sbc (config-pair abstract-impl-config (aps#-abstract-config spec-config))))]))

;; ---------------------------------------------------------------------------------------------------
;; Simulation

;; ;; (Setof config-pair) -> (List (Setof config-pair)
;; ;;                              (Setof config-pair)
;; ;;                              IncomingDict
;; ;;                              RelatedSpecStepsDict)
;; ;;
;; ;; Finds a set of pairs that are related in the rank-1 conformance simulation by abstractly evaluating
;; ;; implementation configs and finding matching specification transitions, starting from the given
;; ;; initial pairs. Returns the set of related pairs along with other data structures that act as a
;; ;; proof of the pairs' membership. Specifically, it returns:
;; ;;
;; ;; related-pairs: the set of pairs found to be in the rank-1 simulation
;; ;;
;; ;; unrelated-successors: pairs reachable by from a pair in related-pairs by a matching
;; ;; impl-step/spec-step transition but are not themselves in the rank-1 simulation.
;; ;;
;; ;; incoming-steps: A dictionary from either a related pair or an unrelated successor to the set of
;; ;; impl/spec steps that lead to it (as described in the "Type" Definitions section above)
;; ;;
;; ;; related-spec-steps: A dictionary from a related pair and an implementation step from that pair to
;; ;; the set of specification steps that match the implementation step. See "Type" Definitions above for
;; ;; more details.
;; (define (find-rank1-simulation initial-pairs)
;;   ;; We use a mutable set for the to-visit worklist rather than a queue for (effectively)
;;   ;; constant-time membership checks just before adding a new pair
;;   ;;
;;   ;; invariant: every item in to-visit should already be widened
;;   (define to-visit (list->mutable-set initial-pairs))
;;   (define related-spec-steps (make-hash))
;;   (define incoming-steps (make-hash (map (lambda (t) (cons t (mutable-set))) initial-pairs)))

;;   ;; Statistics
;;   (define visited-impl-configs (mutable-set))
;;   (define visited-spec-configs (mutable-set))

;;   ;; Debugging
;;   (define log-file (open-log))
;;   (log-initial-pairs log-file initial-pairs)

;;   (let loop ([related-pairs (set)]
;;              [unrelated-successors (set)])
;;     (match (set-dequeue-if-non-empty! to-visit)
;;       [#f
;;        (close-log log-file)
;;        (list related-pairs unrelated-successors incoming-steps related-spec-steps)]
;;       [pair
;;        ;; Update statistics
;;        (stat-set! STAT-visited-pairs-count (add1 (stat-value STAT-visited-pairs-count)))
;;        (set-add! visited-impl-configs (config-pair-impl-config pair))
;;        (set-add! visited-spec-configs (config-pair-spec-config pair))
;;        (stat-set! STAT-unique-impl-configs-count (set-count visited-impl-configs))
;;        (stat-set! STAT-unique-spec-configs-count (set-count visited-spec-configs))

;;        ;; Debugging
;;        (printf "Current time: ~a\n" (date->string (seconds->date (current-seconds)) #t))
;;        (printf "Pair config #: ~s\n" (stat-value STAT-visited-pairs-count))
;;        (printf "Unique impl configs so far: ~s\n" (stat-value STAT-unique-impl-configs-count))
;;        (printf "Unique spec configs so far: ~s\n" (stat-value STAT-unique-spec-configs-count))
;;        (printf "Worklist size: ~s\n" (set-count to-visit))
;;        ;; (printf "The impl config: ~s\n"
;;        ;;         (impl-config-without-state-defs (config-pair-impl-config pair)))
;;        ;; (printf "The full impl config: ~s\n" (config-pair-impl-config pair))
;;        ;; (printf "The spec config: ~s\n"
;;        ;;         (spec-config-without-state-defs (config-pair-spec-config pair)))
;;        ;; (printf "Incoming so far: ~s\n" (hash-ref incoming-steps pair))
;;        (flush-output)

;;        (log-exploring log-file pair)

;;        (define i (config-pair-impl-config pair))
;;        (define s (config-pair-spec-config pair))

;;        (cond
;;          ;; Performance improvement: If the spec is a no-transition spec whose obligations have all
;;          ;; been met, and the impl doesn't even know about the obligation addresses anymore, then the
;;          ;; impl is guaranteed to conform to the spec. We can ignore any further steps and just call
;;          ;; this a related pair.
;;          [(and (aps#-completed-no-transition-config? s)
;;                (let ([known-externals (externals-in i)])
;;                  (for/and ([relevant-external (aps#-relevant-external-addrs s)])
;;                    (not (member relevant-external known-externals)))))
;;           (loop (set-add related-pairs pair) unrelated-successors)]
;;          [else
;;           (match (impl-steps-from i s)
;;             [#f
;;              ;; Evaluation led to an unverifiable configuration, so we deem this pair unrelated, add
;;              ;; it to the unrelated-successors list, and move on to explore the next pair in our
;;              ;; worklist.
;;              (loop related-pairs (set-add unrelated-successors pair))]
;;             [i-steps-with-obs/unobs
;;              ;; Find the matching s-steps
;;              (define found-unmatchable-step? #f)
;;              (widen-printf "Finding matching s-steps for ~s i-steps\n" (length i-steps-with-obs/unobs))
;;              (for ([i-step-with-obs/unobs i-steps-with-obs/unobs])
;;                (match-define (list i-step obs? unobs?) i-step-with-obs/unobs)
;;                ;; Debugging:
;;                ;; (printf "Impl step: ~s\n" (debug-impl-step i-step))

;;                (define matching-s-steps (matching-spec-steps s i-step obs? unobs?))
;;                ;; Debugging:
;;                ;; (printf "Matching spec steps: ~s\n" matching-s-steps)

;;                (log-related-spec-steps log-file (list pair i-step) matching-s-steps)
;;                (hash-set! related-spec-steps (list pair i-step) matching-s-steps)
;;                (when (set-empty? matching-s-steps)
;;                  ;; (printf "Unmatchable impl step: ~s\n" (debug-impl-step i-step))
;;                  (set! found-unmatchable-step? #t)))

;;              ;; Add this pair to either related or unrelated set; add new worklist items
;;              (cond
;;                [found-unmatchable-step?
;;                 ;; Some impl step has no matching spec step, so this pair is unrelated. Therefore we
;;                 ;; add it to the unrelated-successors list and do not further explore transitions from
;;                 ;; this pair.

;;                 ;; Debugging
;;                 ;; (displayln "Unrelated pair")
;;                 (log-unrelated log-file pair)
;;                 (loop related-pairs (set-add unrelated-successors pair))]
;;                [else
;;                 ;; This pair is in the rank-1 simulation (because all of its impl steps have matching
;;                 ;; spec steps). We have to add it to the related-pairs set, sbc each of the matching
;;                 ;; destination pairs and add them to the work-list so that we explore this pair's
;;                 ;; successors, and add the incoming transitions for those destination pairs to
;;                 ;; incoming-steps.

;;                 ;; Debugging
;;                 ;; (displayln "Related pair")
;;                 (widen-printf "Widening/sbc-ing ~s impl steps\n" (length i-steps-with-obs/unobs))
;;                 (define i-step-num 0)
;;                 (for ([i-step-with-obs/unobs i-steps-with-obs/unobs])
;;                   (match-define (list i-step obs? unobs?) i-step-with-obs/unobs)
;;                   (set! i-step-num (add1 i-step-num))
;;                   (for ([s-step (hash-ref related-spec-steps (list pair i-step))])
;;                     (define successor-pairs
;;                       (for/list ([config (spec-step-destinations s-step)])
;;                         (config-pair (impl-step-destination i-step) config)))

;;                     ;; Debugging only
;;                     ;; (for ([successor-pair successor-pairs])
;;                     ;;   (printf "pre-sbc: ~s\n" successor-pair)
;;                     ;;   (printf "post-sbc: ~s\n" (sbc successor-pair)))
;;                     (for ([sbc-result (sbc* successor-pairs)])
;;                       (match-define (list unwidened-sbc-pair rename-map) sbc-result)
;;                       (define (seen? new-pair)
;;                         (or (set-member? to-visit new-pair)
;;                             (set-member? related-pairs new-pair)
;;                             (set-member? unrelated-successors new-pair)
;;                             (equal? new-pair pair)))
;;                       (define sbc-pair
;;                         (if (and (USE-WIDEN?)
;;                                  ;; if we've already seen this pair, then we can assume it's already
;;                                  ;; been widened (this often happens when a blurred actor from a fully
;;                                  ;; widened config pair takes a transition step)
;;                                  (not (seen? unwidened-sbc-pair)))
;;                             (widen-pair unwidened-sbc-pair
;;                                         i-step-with-obs/unobs
;;                                         (stat-value STAT-visited-pairs-count)
;;                                         i-step-num
;;                                         (length i-steps-with-obs/unobs))
;;                             (begin
;;                               (widen-printf "Not widening an already-seen config pair\n")
;;                               unwidened-sbc-pair)))
;;                       (log-incoming log-file sbc-pair (list pair i-step s-step rename-map))
;;                       (dict-of-sets-add! incoming-steps sbc-pair (list pair i-step s-step rename-map))
;;                       ;; unless it's already in the queue, or we have already explored it (and
;;                       ;; therefore it's in either the related or unrelated set), add the new pair to
;;                       ;; the worklist
;;                       (unless (seen? sbc-pair)
;;                         (set-add! to-visit sbc-pair)))))
;;                 (log-related log-file pair)
;;                 (loop (set-add related-pairs pair) unrelated-successors)])])])])))

;; i# s# -> (listof i#)
;;
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
    (define triggers (impl-triggers-from impl-config spec-config))
    (widen-printf "Finding impl steps from ~s triggers\n" (length triggers))
    (append*
     (for/list ([trigger triggers])
       (widen-printf "Trigger: ~s\n" trigger)
       (flush-output)
       (define effects (csa#-eval-trigger impl-config trigger abort))
       (for/list ([effect effects])
         (apply-transition impl-config effect))))))

;; i# csa#-transition-effect -> impl-step
(define (apply-transition config effect observed? unobserved?)
  ;; REFACTOR: inline this whole method
  (define transition (csa#-apply-transition config effect))
  (impl-step (csa#-transition-trigger transition)
             (csa#-transition-outputs transition)
             (csa#-transition-spawn-locs effect)
             (csa#-transition-final-config transition)))

;; i# s# -> (Listof trigger#)
;;
;; Returns a list of all possible triggers from the given config pair, where the booleans associated
;; with each indicate whether the trigger can be observed, and the second whether it can be unobserved
(define (impl-triggers-from impl-config spec-config)
  (append
   (external-triggers-for-receptionists (csa#-config-receptionists impl-config))
   (csa#-enabled-internal-actions impl-config)))

;; (Listof τa) -> (Listof trigger#)
;;
;; Returns all possible external actions that would be allowed by the interface given by the typed
;; addresses
(define (external-triggers-for-receptionists receptionists)
  (append*
   (for/list ([receptionist receptionists])
     (match-define `[,type ,marked-address] receptionist)
     (for/list ([message (csa#-messages-of-type type)])
       (csa#-make-external-trigger marked-address message)))))

(module+ test
  (test-equal? "external-triggers-for-receptionists"
    (external-triggers-for-receptionists
     (list `[Nat (marked (addr 0 0) 1)]
           `[(Union [A] [B (Union [C] [D])]) (marked (addr 0 1) 2)]
           `[(Addr Nat) (marked (addr 0 2) 3)]))
    (list `(external-receive (marked (addr 0 0) 1) abs-nat)
          `(external-receive (marked (addr 0 1) 2) (variant A))
          `(external-receive (marked (addr 0 1) 2) (variant B (variant C)))
          `(external-receive (marked (addr 0 1) 2) (variant B (variant D)))
          `(external-receive (marked (addr 0 2) 3) (marked (collective-addr (env Nat)) 100)))))

;; Returns a set of the possible spec steps (see the struct above) from the given spec config that
;; match the given implementation step
(define (matching-spec-steps spec-config i-step)
  (define matched-stepped-configs (mutable-set))
  (for ([trigger-result (aps#-matching-steps spec-config (impl-step-trigger i-step))])
    (match (aps#-resolve-outputs trigger-result (impl-step-outputs i-step))
      [(list) (void)]
      [(list results ...)
       (for ([result results])
         (match-define `[,stepped-configs ,satisfied-commitments] result)
         (set-add! matched-stepped-configs (spec-step stepped-configs satisfied-commitments)))]))
  matched-stepped-configs)

(module+ test
  (define null-spec-config (make-s# '((define-state (S))) '(goto S) null))

  (test-case "Null transition okay for internal receive"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (addr 0 0) abs-nat single) null null #f))
     (mutable-set (spec-step (list null-spec-config) null))))
  (test-case "Null transition not okay for monitored external receive"
    (check-exn
     (lambda (exn) #t)
     (lambda ()
       (matching-spec-steps
        null-spec-config
        (impl-step '(external-receive (marked (addr 0 0) 0) abs-nat) null null #f)))))
  (test-case "No match if trigger does not match"
    (check-exn
     (lambda (exn) #t)
     (lambda ()
       (matching-spec-steps
        (make-s# '((define-state (A) [x -> () (goto A)])) '(goto A) null)
        (impl-step '(external-receive (marked (addr 0 0) 0) abs-nat) null null #f)))))
  (test-case "Unmonitored outputs don't need to match"
    (check-equal?
     (matching-spec-steps
      null-spec-config
      (impl-step '(internal-receive (addr 0 0) abs-nat single)
                 (list '((marked (addr (env Nat) 1) 1) abs-nat single))
                 null
                 #f))
     (mutable-set (spec-step (list null-spec-config) null))))
  (test-case "No match if outputs do not match"
    (check-equal?
     (matching-spec-steps
      (valid-s# `[(0) (1) (goto A) ((define-state (A))) ()])
      (impl-step '(internal-receive (addr 0 0) abs-nat single)
                 (list '((marked (addr (env Nat) 1) 1) abs-nat single))
                 null
                 #f))
     (mutable-set)))
  (test-case "Output can be matched by previous commitment"
    (check-equal?
     (matching-spec-steps
      (valid-s# `[(0) (1) (goto A) ((define-state (A))) ([1 *])])
      (impl-step '(internal-receive (addr 0 0) abs-nat single)
                 (list '((marked (addr (env Nat) 1) 1) abs-nat single))
                 null
                 #f))
     (mutable-set (spec-step (list (valid-s# `[(0) (1) (goto A) ((define-state (A))) ()]))
                             (list `[1 *])))))
  (test-case "Output can be matched by new commitment"
    (check-equal?
     (matching-spec-steps
      (make-s# '((define-state (A) [x -> ([obligation x *]) (goto A)])) '(goto A) null)
      (impl-step '(external-receive (marked (addr 0 0) 0) (marked (addr (env Nat) 1) 1))
                 (list '((marked (addr (env Nat) 1) 1) abs-nat single))
                 null
                 #f))
     (mutable-set (spec-step (list (valid-s# `[(0) (1) (goto A) ((define-state (A) [x -> ([obligation x *]) (goto A)])) ()]))
                             (list `[1 *])))))
  (test-case "Can't duplicate commitments"
    (check-equal?
     (matching-spec-steps
      (valid-s# '[(0) (1) (goto A 1) ((define-state (A x) [* -> ([obligation x *]) (goto A x)])) ([1 *])])
      (impl-step '(external-receive (marked (addr 0 0) 0) abs-nat) null null #f))
     (mutable-set))))

;; Given a hash table whose values are sets, add val to the set in dict corresponding to key (or
;; create the hash-table entry with a set containing that val if no entry exists).
(define (dict-of-sets-add! dict key val)
  (match (hash-ref dict key #f)
    [#f
     (hash-set! dict key (mutable-set val))]
    [the-set
     (set-add! the-set val)]))

;; [mutable-set-of X] -> #f or X
;;
;; Removes and returns an arbitrary element of the set, or returns #f if the set is already empty
(define (set-dequeue-if-non-empty! s)
  (cond
    [(set-empty? s) #f]
    [else
     (define e (set-first s))
     (set-remove! s e)
     e]))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Split/Blur/Canonicalize (SBC)

;; ;; Performs the SBC (split/blur/canonicalize) operation on a config pair, returning its derivative
;; ;; pairs along with an address-rename map with each pair. SBC entails the following:
;; ;;
;; ;; 1. For each address in the output commitment map that is *not* an argument to the current state,
;; ;; split those commitments off into a new specification with a dummy FSM.
;; ;;
;; ;; 2. For each specification resulting from step 1, blur the implementation configuration according
;; ;; to the addresses relevant to that spec. This means merging external addresses not used in the spec
;; ;; into a single abstract value and choosing some subset of actors (up to some statically known
;; ;; number) to remain precise while merging the others together.
;; ;;
;; ;; 3. Canonicalize the addresses in both configurations. That is, rename them to some canonical naming
;; ;; so that we avoid the orbit problem with other similar pairs that we have already explored (or that
;; ;; we will explore).
;; ;;
;; ;; SBC keeps our explored state-space finite. By creating a new spec for each no-longer-used
;; ;; commitment address, we ensure that the number of adddresses in a spec config is no more than max(1,
;; ;; maxStateParams), where maxStateParams is the maximum number of formal parameters for any state in
;; ;; the original (static) specification. Blurring the implementation configuration according to the
;; ;; new spec component keeps the state-space of the impl configs finite. Finally, canonicalize ensures
;; ;; that the address values do not keep increasing towards infinity and instead stay within a bounded
;; ;; space.
;; (define (sbc pair)
;;   ;; NOTE: eviction is added here now as well, as part of the general T transform
;;   (match-define (list evicted-i evicted-s)
;;     (if (USE-EVICTION?)
;;         (evict-pair (config-pair-impl-config pair) (config-pair-spec-config pair))
;;         (list (config-pair-impl-config pair) (config-pair-spec-config pair))))
;;   (display-step-line "Splitting a specification config")
;;   (define spec-config-components (split-spec evicted-s))
;;   (define blur-results
;;     (for/list ([spec-config-component spec-config-components])
;;       (display-step-line "Blurring an implementation config")
;;       (blur-by-relevant-addresses evicted-i spec-config-component)))
;;   (for/list ([blur-result blur-results])
;;     (match-define (list blurred-impl blurred-spec) blur-result)
;;     (display-step-line "Canonicalizing the pair, adding to queue")
;;     (match-define (list canonicalized-impl canonicalized-spec rename-map)
;;       (canonicalize-pair blurred-impl blurred-spec))
;;     (list (config-pair canonicalized-impl canonicalized-spec) rename-map)))

;; ;; Calls sbc on every pair and merges the results into one long list.
;; (define (sbc* pairs)
;;   (append* (map sbc pairs)))

;; ;; impl-config spec-config -> (List impl-config spec-config)
;; ;;
;; ;; Blurs the given configurations into only the portions that are relevant to the specification
;; ;; configuration, moving the rest of the configurations into the "imprecise" sections of the
;; ;; abstraction.
;; ;;
;; ;; Specifically, this chooses actors with either the NEW or OLD flag to be more likely to match this
;; ;; specification, then takes all actors with the same spawn location and opposite flag and merges
;; ;; their behaviors into the set of behaviors for the "blurred" actors of that location.
;; (define (blur-by-relevant-addresses impl-config spec-config)
;;   (match-define (list blurred-impl-config blurred-internals)
;;     (csa#-blur-config impl-config
;;                       (choose-id-to-blur impl-config spec-config)
;;                       (aps#-relevant-external-addrs spec-config)))
;;   (list
;;    blurred-impl-config
;;    (aps#-blur-config spec-config blurred-internals)))

;; (module+ test
;;   (test-equal? "blur OLD"
;;     (blur-by-relevant-addresses
;;      ;; spec config: lots of spawned actors with similar addresses
;;      '((((addr 2 1) (() (goto A)))
;;         ((addr 2 0) (() (goto A)))
;;         ((addr 3 1) (() (goto A)))
;;         ((addr 3 0) (() (goto A)))
;;         ((addr 4 1) (() (goto A)))
;;         ((addr 4 0) (() (goto A))))
;;        ()
;;        ())
;;      ;; spec config: all addresses in the unobs interface
;;      '(((Nat (addr 2 1)))
;;        ((Nat (addr 2 1))
;;         (Nat (addr 2 0))
;;         (Nat (addr 3 1))
;;         (Nat (addr 3 0))
;;         (Nat (addr 4 1))
;;         (Nat (addr 4 0)))
;;        (goto A)
;;        ()
;;        ()))
;;     (list
;;      ;; impl config result
;;      '((((addr 2 1) (() (goto A)))
;;         ((addr 3 1) (() (goto A)))
;;         ((addr 4 1) (() (goto A))))
;;        (((collective-addr 2) ((() (goto A))))
;;         ((collective-addr 3) ((() (goto A))))
;;         ((collective-addr 4) ((() (goto A)))))
;;        ())
;;      ;; spec config result
;;      '(((Nat (addr 2 1)))
;;        ((Nat (addr 2 1))
;;         (Nat (collective-addr 2))
;;         (Nat (addr 3 1))
;;         (Nat (collective-addr 3))
;;         (Nat (addr 4 1))
;;         (Nat (collective-addr 4)))
;;        (goto A)
;;        ()
;;        ())))
;;   (test-equal? "blur 1"
;;     (blur-by-relevant-addresses
;;      ;; spec config: lots of spawned actors with similar addresses
;;      '((((addr 2 1) (() (goto A)))
;;         ((addr 2 0) (() (goto A)))
;;         ((addr 3 1) (() (goto A)))
;;         ((addr 3 0) (() (goto A)))
;;         ((addr 4 1) (() (goto A)))
;;         ((addr 4 0) (() (goto A))))
;;        ()
;;        ())
;;      ;; spec config: all addresses in the unobs interface
;;      '(((Nat (addr 2 0)))
;;        ((Nat (addr 2 1))
;;         (Nat (addr 2 0))
;;         (Nat (addr 3 1))
;;         (Nat (addr 3 0))
;;         (Nat (addr 4 1))
;;         (Nat (addr 4 0)))
;;        (goto A)
;;        ()
;;        ()))
;;     (list
;;      ;; impl config result
;;      '((((addr 2 0) (() (goto A)))
;;         ((addr 3 0) (() (goto A)))
;;         ((addr 4 0) (() (goto A))))
;;        (((collective-addr 2) ((() (goto A))))
;;         ((collective-addr 3) ((() (goto A))))
;;         ((collective-addr 4) ((() (goto A)))))
;;        ())
;;      ;; spec config result
;;      '(((Nat (addr 2 0)))
;;        ((Nat (collective-addr 2))
;;         (Nat (addr 2 0))
;;         (Nat (collective-addr 3))
;;         (Nat (addr 3 0))
;;         (Nat (collective-addr 4))
;;         (Nat (addr 4 0)))
;;        (goto A)
;;        ()
;;        ()))))

;; (module+ test
;;   (test-equal? "check that messages with blurred addresses get merged together"
;;    (blur-by-relevant-addresses
;;     (term (()
;;            ()
;;            (((addr 2 0) (addr (env Nat) 1) single)
;;             ((addr 2 0) (addr (env Nat) 2) single)
;;             ((addr 2 0) (addr (env Nat) 3) single))))
;;     (aps#-make-no-transition-config '() '(((addr (env Nat) 3)))))
;;    (list (term (()
;;                 ()
;;                 (((addr 2 0) (collective-addr (env Nat)) many)
;;                  ((addr 2 0) (addr (env Nat) 3) single))))
;;          (aps#-make-no-transition-config '() '(((addr (env Nat) 3)))))))

;; ;; Decides whether to blur spawn-addresses with the OLD or NEW flag based on the current impl and spec
;; ;; configs, returning the flag for addresses that should be blurred.
;; (define (choose-id-to-blur impl-config spec-config)
;;   ;; 1. if there are no observable spec receptionists but only actors with just one of the flags have
;;   ;; addresses from the output commitment set, blur the other flag
;;   ;;
;;   ;; 2. if the observed receptionist is atomic and the address with opposite ID as the spec obs
;;   ;; receptionist exists, return the opposite of the obs receptionist ID
;;   ;;
;;   ;; 3. otherwise, just return OLD by default
;;   (define (other-flag f)
;;     (match f
;;        [0 1]
;;        [1 0]))
;;   (match (aps#-config-obs-receptionists spec-config)
;;     [(list)
;;      (match (csa#-ids-that-know-externals impl-config (aps#-relevant-external-addrs spec-config))
;;        [(list flag) (other-flag flag)] ; use "other" flag if exactly one flag knows externals
;;        [_ 0])]
;;     [(list `[,obs-rec-type ,obs-rec-addr])
;;      (if (and (csa#-atomic-address? obs-rec-addr)
;;               (csa#-actor-with-opposite-id-exists? impl-config obs-rec-addr))
;;          (other-flag (csa#-address-id obs-rec-addr))
;;          0)]))

;; (module+ test
;;   (test-equal? "choose spawn flag 1"
;;     (choose-id-to-blur '(([(addr 2 0) (() (goto A))] [(addr 2 1) (() (goto A))]) () ()) '(((Nat (addr 2 1))) () (goto A) () ()))
;;     0)
;;   (test-equal? "choose spawn flag 2"
;;     (choose-id-to-blur '(([(addr 2 0) (() (goto A))] [(addr 2 1) (() (goto A))]) () ()) '(((Nat (addr 2 0))) () (goto A) () ()))
;;     1)
;;   (test-equal? "choose spawn flag 3"
;;     (choose-id-to-blur '(([(addr 2 0) (() (goto A))] [(addr 2 1) (() (goto A))]) () ()) '(() () (goto A) () ()))
;;     0))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Widening

;; ;; config-pair (#f or (list i-step Boolean Boolean) Num Num Num -> config-pair
;; (define (widen-pair the-pair previous-step-with-obs/unobs pair-number i-step-number i-step-total)
;;   (widen-printf "Starting widen for pair ~s, i-step ~s of ~s\n" pair-number i-step-number i-step-total)
;;   (widen-printf "The impl config: ~s\n"
;;                 (impl-config-without-state-defs (config-pair-impl-config the-pair)))
;;   (widen-printf "The spec config: ~s\n"
;;                 (spec-config-without-state-defs (config-pair-spec-config the-pair)))

;;   ;; Algorithm:
;;   ;;
;;   ;; * Evaluate a subset of handlers (determined by those that were changed in the previous
;;   ;; transition) of this configuration and add each result (goto, spawns, internal messages, external
;;   ;; messages) to a worklist. A single handler may have many possible results because of the
;;   ;; non-determinism of the abstract interpretation.
;;   ;;
;;   ;; * In the worklist loop, determine whether the action of the transition is repeatable, whether
;;   ;; there exists a spec step that leads to the exact same spec config (modulo additions to the
;;   ;; observed or unobserved interface), and whether this transition *might* lead to a greater one
;;   ;; (using various heuristics). If not, throw this worklist item away (after marking it as applied),
;;   ;; and move on to the next loop iteration.
;;   ;;
;;   ;; * Otherwise, sbc the resulting impl and spec configs, apply the effects to the new impl config
;;   ;; again (must be possible because we already checked for repeatability), match it to the spec again
;;   ;; (should be the same spec step), sbc the results, and check whether *that* sbc'ed result is at
;;   ;; least as large as the previous configuration pair. Clear the work queue and instead fill it with
;;   ;; transitions we already said we'd check from previous config pairs along with transitions
;;   ;; resulting from any triggers that this transition might have changed.
;;   ;;
;;   ;; * When the worklist is empty, return the final "base" configuration pair as the widened pair.

;;   (define original-i (config-pair-impl-config the-pair))
;;   (define original-s (config-pair-spec-config the-pair))
;;   ;; We only want to try widening from the triggers that might actually lead to a bigger state;
;;   ;; otherwise we're wasting our time.
;;   ;;
;;   ;; NOTE: this needs to be a list, not a set, so that we can ensure the step taken before widen can
;;   ;; be repeated *first*. This is important because if that step spawned something, we want to spawn
;;   ;; it again immediately to blur it; otherwise, we might change its state with one transition and
;;   ;; *then* try to blur it, which might be invalid (e.g. if the original spawn had some messages sent
;;   ;; to it but the original one did not)
;;   (define triggers-to-try
;;     (let ([updated-triggers
;;            (filter
;;             (lambda (trigger)
;;               (if previous-step-with-obs/unobs
;;                   (trigger-updated-by-step? (first trigger) (first previous-step-with-obs/unobs) #f)
;;                   #t))
;;             (impl-triggers-from original-i original-s))])
;;       ;; previous trigger may not be valid in this state because of a new spec
;;       (define previous-trigger-with-obs/unobs
;;         (if previous-step-with-obs/unobs
;;             `[,(impl-step-trigger (first previous-step-with-obs/unobs))
;;               (second previous-step-with-obs/unobs)
;;               (third previous-step-with-obs/unobs)]
;;             #f))
;;       (if (and previous-step-with-obs/unobs (member previous-trigger-with-obs/unobs updated-triggers))
;;           (cons previous-trigger-with-obs/unobs updated-triggers)
;;           updated-triggers)))
;;   (define possible-transitions (apply queue (impl-transition-effects-from the-pair triggers-to-try)))
;;   (widen-printf "Starting widen with ~s transitions\n" (queue-length possible-transitions))
;;   (define processed-transitions (mutable-set))

;;   ;; for debugging
;;   (define init-loop-count (stat-value STAT-widen-loop-count))
;;   (define init-maybe-good-count (stat-value STAT-widen-maybe-good-count))
;;   (define init-attempt-count (stat-value STAT-widen-attempt-count))
;;   (define init-use-count (stat-value STAT-widen-use-count))

;;   (let worklist-loop ([widened-pair the-pair])
;;     (match (dequeue-if-non-empty! possible-transitions)
;;       [#f
;;        (widen-printf "Finished widen. Final config: ~s\n"
;;                      (impl-config-without-state-defs (config-pair-impl-config widened-pair)))
;;        widened-pair]
;;       [transition-result-with-obs/unobs
;;        (stat-set! STAT-widen-loop-count (add1 (stat-value STAT-widen-loop-count)))
;;        (cond
;;          [(set-member? processed-transitions transition-result-with-obs/unobs)
;;           ;; Skip this transition if we already processed it
;;           (widen-printf "Skipping transition\n")
;;           ;; (widen-printf "Trigger: ~s\n" (csa#-transition-effect-trigger (first transition-result-with-obs/unobs)))
;;           ;; (widen-printf "Outputs: ~s\n" (csa#-transition-effect-sends (first transition-result-with-obs/unobs)))

;;           (worklist-loop widened-pair)]
;;          [else
;;           (stat-set! STAT-widen-maybe-good-count (add1 (stat-value STAT-widen-maybe-good-count)))
;;           (widen-printf "Trying transition for pair ~s, i-step ~s of ~s\n" pair-number i-step-number i-step-total)
;;           (widen-printf "Loop count = ~s, maybe count = ~s, attempt count = ~s, use count = ~s, ~s remaining transitions\n"
;;                         (- (stat-value STAT-widen-loop-count) init-loop-count)
;;                         (- (stat-value STAT-widen-maybe-good-count) init-maybe-good-count)
;;                         (- (stat-value STAT-widen-attempt-count) init-attempt-count)
;;                         (- (stat-value STAT-widen-use-count) init-use-count)
;;                         (queue-length possible-transitions))
;;           (widen-printf "Trigger: ~s\n" (csa#-transition-effect-trigger (first transition-result-with-obs/unobs)))
;;           (widen-printf "Outputs: ~s\n" (csa#-transition-effect-sends (first transition-result-with-obs/unobs)))

;;           (set-add! processed-transitions transition-result-with-obs/unobs)
;;           (match-define (list transition-result obs? unobs?) transition-result-with-obs/unobs)
;;           (define i (config-pair-impl-config widened-pair))
;;           (cond
;;             ;; To avoid running the apply-and-sbc process too many times (a major bottleneck of the
;;             ;; checker), we first do some basic checks on the transition to see if it's even worth
;;             ;; exploring
;;             [(csa#-transition-maybe-good-for-widen? i transition-result)
;;              (stat-set! STAT-widen-attempt-count (add1 (stat-value STAT-widen-attempt-count)))
;;              (define trigger (csa#-transition-effect-trigger transition-result))
;;              ;; can ignore the obs/unobs here; they're the same as the ones passed in
;;              (match-define (list new-i-step _ _) (apply-transition i transition-result obs? unobs?))
;;              (match (first-spec-step-to-same-state (config-pair-spec-config widened-pair) new-i-step obs? unobs?)
;;                [#f
;;                 (widen-printf "Transition has no spec transition to same state\n")
;;                 (worklist-loop widened-pair)]
;;                [new-s
;;                 (stat-set! STAT-widen-spec-match-count (add1 (stat-value STAT-widen-spec-match-count)))
;;                 ;; If there's a possible way for a spec to match this step, then apply the transition
;;                 ;; once more to get "many-of" instances of new spawns and messages, so we have the
;;                 ;; best chance of this configuration being greater than its predecessor.
;;                 ;;
;;                 ;; We can ignore the rename-map: the spec doesn't change, so the rename-map doesn't
;;                 ;; change, either.
;;                 (define once-applied-pair
;;                   (first (first (sbc (config-pair (impl-step-destination new-i-step) new-s)))))
;;                 (cond
;;                   [(csa#-action-enabled? (config-pair-impl-config once-applied-pair) trigger)
;;                    (match-define (list repeated-i-step _ _) ; again, ignore obs/unobs
;;                      (apply-transition (config-pair-impl-config once-applied-pair)
;;                                        transition-result
;;                                        obs? unobs?))
;;                    (define repeated-s
;;                      (first-spec-step-to-same-state (config-pair-spec-config once-applied-pair)
;;                                                     repeated-i-step
;;                                                     obs? unobs?))
;;                    (define twice-applied-pair
;;                      (first
;;                       (first (sbc (config-pair (impl-step-destination repeated-i-step) repeated-s)))))
;;                    (widen-printf "After first apply, no sbc: ~s\n" (impl-config-without-state-defs (impl-step-destination new-i-step)))
;;                    (widen-printf "Twice-applied, sbc'ed:     ~s\n" (impl-config-without-state-defs (config-pair-impl-config twice-applied-pair)))
;;                    (cond
;;                      ;; OPTIMIZE: check first if the transitioned actor is even in the same state
;;                      [(csa#-config<? i (config-pair-impl-config twice-applied-pair))
;;                       (stat-set! STAT-widen-use-count (add1 (stat-value STAT-widen-use-count)))
;;                       (widen-printf "Widen: applied a transition for pair ~s, i-step ~s of ~s. Loop count = ~s, use count = ~s\n"
;;                                     pair-number i-step-number i-step-total (- (stat-value STAT-widen-loop-count) init-loop-count) (- (stat-value STAT-widen-use-count) init-use-count)
;;                                     ;; (debug-transition-result transition-result)
;;                                     ;; (impl-config-without-state-defs (config-pair-impl-config new-widened-pair))
;;                                     )
;;                       (define twice-i (config-pair-impl-config twice-applied-pair))
;;                       (define twice-s (config-pair-spec-config twice-applied-pair))
;;                       (widen-printf "Newly widened impl config: ~s\n" (impl-config-without-state-defs twice-i))
;;                       (widen-printf "Newly widened spec config: ~s\n" (spec-config-without-state-defs twice-s))
;;                       (widen-printf "Remaining transitions: ~s\n" (queue-length possible-transitions))
;;                       ;; We just throw away any remaining transitions, because the transitions from
;;                       ;; this configuration supercede those from a different one
;;                       (for ([trigger (impl-triggers-from twice-i twice-s)])
;;                         (when (and (not (member trigger triggers-to-try))
;;                                    (trigger-updated-by-step? (first trigger) new-i-step i))
;;                           (set! triggers-to-try (cons trigger triggers-to-try))))
;;                       (set! possible-transitions
;;                             (apply queue (impl-transition-effects-from twice-applied-pair triggers-to-try)))
;;                       (widen-printf "New queue has ~s transitions\n" (queue-length possible-transitions))
;;                       (worklist-loop twice-applied-pair)]
;;                      [else
;;                       (widen-printf "Transition is not valid for widen\n")
;;                       (worklist-loop widened-pair)])]
;;                   [else
;;                    (widen-printf "Transition is not repeatable\n")
;;                    (worklist-loop widened-pair)])])]
;;             [else
;;              (widen-printf "Transition failed maybe-good-for-widen\n")
;;              (worklist-loop widened-pair)])])])))

;; (module+ test
;;   (define init-widen-impl-config
;;     (term
;;      (
;;       (
;;        ;; single atomic actor
;;        [(addr child-loc 0)
;;         (((define-state (B) (m) (goto B))) (goto B))]
;;        [(addr 1 0)
;;         (((define-state (A) (m)
;;             (let ([child (spawn child-loc Nat (goto B)
;;                                 (define-state (B) (m) (goto B)))])
;;               (begin
;;                 (send child abs-nat)
;;                 (goto A)))))
;;          (goto A))])
;;       ()
;;       ([(addr child-loc 0) abs-nat single]))))

;;   (define expected-widened-config
;;     (term
;;      ((;; a one-of of the spawned child
;;        [(addr child-loc 0)
;;         (((define-state (B) (m) (goto B))) (goto B))]
;;        [(addr 1 0)
;;         (((define-state (A) (m)
;;             (let ([child (spawn child-loc Nat (goto B)
;;                                 (define-state (B) (m) (goto B)))])
;;               (begin
;;                 (send child abs-nat)
;;                 (goto A)))))
;;          (goto A))])
;;       (
;;        ;; a single collective actor
;;        (
;;         ;; a#int-collective
;;         (collective-addr child-loc)
;;         (
;;          ;; just one b#
;;          (((define-state (B) (m) (goto B))) (goto B)))
;;         ))
;;       (
;;        ;; the messages
;;        ((addr child-loc 0) abs-nat single)
;;        ((collective-addr child-loc) abs-nat many)))))

;;   (define widen-spec
;;     ;; Just a spec that observes only inputs and says nothing ever happens
;;     (term
;;      (((Nat (addr 1 0)))
;;       ()
;;       (goto SpecA)
;;       ((define-state (SpecA) [* -> () (goto SpecA)]))
;;       ())))

;;   (test-true "Init widen config is valid"     (redex-match? csa# i# init-widen-impl-config))
;;   (test-true "Expected widen config is valid" (redex-match? csa# i# expected-widened-config))
;;   (test-true "Valid spec for widen test" (redex-match? aps# s# widen-spec))
;;   (test-equal? "Basic widening test"
;;     (widen-pair (config-pair init-widen-impl-config widen-spec) #f 0 0 0)
;;     (config-pair expected-widened-config widen-spec)))

;; (define (trigger-updated-by-step? trigger i-step prev-i)
;;   (csa#-trigger-updated-by-step? trigger
;;                                  (impl-step-trigger i-step)
;;                                  prev-i
;;                                  (impl-step-spawn-locs i-step)))

;; ;; config-pair (List-of (list trigger Boolean Boolean)) -> (Listof (List csa#-transition-effect Boolean Boolean))
;; (define (impl-transition-effects-from the-pair triggers-with-obs/unobs)
;;   (match-define (config-pair i s) the-pair)
;;   (let/cc return-continuation
;;     (define (abort) (return-continuation null))
;;     (widen-printf "Widen: getting effects from ~s triggers\n" (length triggers-with-obs/unobs))
;;     (define trigger-count 0)
;;     (define final-results
;;      (append*
;;       (for/list ([trigger-with-obs/unobs triggers-with-obs/unobs])
;;         (match-define (list trigger obs? unobs?) trigger-with-obs/unobs)
;;         (set! trigger-count (add1 trigger-count))
;;         (widen-printf "Eval trigger (~s of ~s): ~s\n" trigger-count (length triggers-with-obs/unobs) trigger)
;;         (flush-output)
;;         (define results (map (curryr list obs? unobs?) (csa#-eval-trigger i trigger abort)))
;;         (widen-printf "Finished trigger, ~s transitions\n" (length results))
;;         results)))
;;     (widen-printf "Widen: Found ~s transitions\n" (length final-results))
;;     final-results))

;; ;; Returns the first spec step from this spec config that both matches the i-step and ends up in a
;; ;; configuration identical to the original one (with the exception of the unobserved interface, which
;; ;; is allowed to get bigger in the abstract interpretation sense)
;; (define (first-spec-step-to-same-state spec-config i-step obs? unobs?)
;;   (define matching-configs-after-split
;;     (for/list ([step (matching-spec-steps spec-config i-step obs? unobs?)])
;;       (first (split-spec (first (spec-step-destinations step))))))
;;   (findf (curry aps#-config<= spec-config) matching-configs-after-split))

;; (module+ test
;;   (define first-spec-step-test-config
;;     (redex-let aps# ([s#
;;                       `(([Nat (addr 1 0)])
;;                         ([Nat (addr 1 0)])
;;                         (goto A)
;;                         ((define-state (A)
;;                            [* -> () (goto A)]
;;                            [free -> () (goto B)])
;;                          (define-state (B)
;;                            [* -> () (goto A)]))
;;                         ())])
;;       (term s#)))

;;   (test-equal? "first-spec-step-to-same-state"
;;     (first-spec-step-to-same-state
;;      first-spec-step-test-config
;;      (impl-step `(external-receive (addr 1 0) abs-nat)
;;                 null
;;                 null
;;                 ;; impl config
;;                 `(([(addr 1 0) (() (goto S))])
;;                   ()
;;                   ()))
;;      #f #t)
;;     first-spec-step-test-config)

;;   (test-false "first-spec-step-to-same-state: no step"
;;     (first-spec-step-to-same-state
;;      ;; spec config:
;;      `(([Nat (addr 1 0)])
;;        ([Nat (addr 1 0)])
;;        (goto A)
;;        ((define-state (A)
;;           [* -> () (goto B)]
;;           [free -> () (goto B)])
;;         (define-state (B)
;;           [* -> () (goto A)]))
;;        ())
;;      (impl-step `(external-receive (addr 1 0) abs-nat)
;;                 null
;;                 null
;;                 ;; impl config
;;                 `(([(addr 1 0) (() (goto S))])
;;                   ()
;;                   ()))
;;      #t #f)))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Pair-removal back-propagation


;; ;; (Setof config-pair) IncomingDict RelatedSpecStepsDict (Setof config-pair) ->
;; ;;   (Setof config-pair) RelatedSpecStepsDict
;; ;;
;; ;; Removes from all-pairs those pairs whose proof of membership in a simulation (i.e. their matching
;; ;; transitions in init-related-spec-steps) depends on a transition to a pair known to not be in the
;; ;; relation (we call these "unsupported pairs"). The algorithm propagates the effects of these
;; ;; removals backwards through the proof structure and removes further unsupported pairs until a
;; ;; greatest fixpoint is reached, yielding a set of pairs whose members are all in the full simulation
;; ;; relation.
;; ;;
;; ;; all-pairs: The initial set of pairs, assumed to all be in the rank-1 simulation
;; ;;
;; ;; incoming-steps: A dictionary from either a related pair or an unrelated successor to the set of
;; ;; impl/spec steps that lead to it (as described in the "Type" Definitions section above). Must
;; ;; include entries for all pairs in both all-pairs and init-unrelated-successors.
;; ;;
;; ;; init-related-spec-steps: A dictionary from a related pair and an implementation step from that pair
;; ;; to the set of specification steps that match the implementation step. Must have an entry for every
;; ;; possible implementation step from a pair in all-pairs, and there must be at least one matching spec
;; ;; step per entry. See "Type" Definitions above for more details.
;; ;;
;; ;; init-unrelated-successors: A set of config-pairs that are known to *not* be in the rank-1 simulation. This list must include all
;; ;;
;; ;; Returns:
;; ;;
;; ;; simulation-pairs: The subset of all-pairs that the function was able to show are in the simulation.
;; ;;
;; ;; simulation-related-spec-steps: The RelatedSpecStepsDict that is a sub-dictionary of
;; ;; init-related-spec-steps (i.e. the sets are subsets of those from init-related-spec-steps). This
;; ;; dictionary consitutes a proof that all members of simulation-pairs are in the simulation relation.
;; (define (prune-unsupported all-pairs incoming-steps init-related-spec-steps init-unrelated-successors)
;;   ;; The function implements a worklist algorithm, with init-unrelated-successors forming the initial
;;   ;; worklist items. The objective is to remove unsupported items from remaining-pairs and
;;   ;; related-spec-steps so that at the end of the algorithm, they comprise a globally consistent
;;   ;; proof.
;;   (define unrelated-successors (apply queue (set->list init-unrelated-successors)))
;;   (define remaining-pairs (set-copy all-pairs))
;;   (define related-spec-steps (hash-copy init-related-spec-steps))

;;   ;; Loop invariant: For every pair in remaining-pairs and every impl-step possible from that pair,
;;   ;; related-spec-steps(pair, impl-step) = a non-empty set of matching specification transitions such
;;   ;; that the sbc-derivatives of (impl-step.destination, spec-step.destination) are all in
;;   ;; remaining-pairs or unrelated-successors.
;;   ;;
;;   ;; Termination argument: Every iteration of the loop processes one worklist item. We never process a
;;   ;; worklist item more than once (because they only come from remaining-pairs, and when an item is
;;   ;; queued into the worklist it is permanently removed from remaining-pairs). The total set of items
;;   ;; that might enter the worklist (all-pairs plus init-related-successors) is finite, so the queue is
;;   ;; eventually emptied and the loop terminates.
;;   (let loop ()
;;     (match (dequeue-if-non-empty! unrelated-successors)
;;       [#f (list (set-immutable-copy remaining-pairs) related-spec-steps)]
;;       [unrelated-pair
;;        (for ([transition (hash-ref incoming-steps unrelated-pair)])
;;          (match-define (list predecessor i-step s-step _) transition)
;;          ;; Only check for lack of support for pairs still in remaining pairs
;;          (when (set-member? remaining-pairs predecessor)
;;            (define spec-steps (hash-ref related-spec-steps (list predecessor i-step)))
;;            ;; Proceed to remove this spec step only if we have not already discovered that it is
;;            ;; unsupported (we may have found some other sbc-derivative of the same step that also led
;;            ;; to an unsupported pair)
;;            (when (set-member? spec-steps s-step)
;;              (set-remove! spec-steps s-step)
;;              (when (set-empty? spec-steps)
;;                ;; There are no matching spec steps for this impl step, so remove this pair from the
;;                ;; relation and add it to the worklist
;;                ;; (printf "Pruning pair: ~s ~s\n"
;;                ;;         (impl-config-without-state-defs (config-pair-impl-config predecessor))
;;                ;;         (spec-config-without-state-defs (config-pair-spec-config predecessor)))
;;                ;; (printf "Because of impl step: ~s\n" (debug-impl-step i-step))
;;                (set-remove! remaining-pairs predecessor)
;;                (enqueue! unrelated-successors predecessor)))))
;;        (loop)])))

;; (module+ test
;;   (require "hash-helpers.rkt")

;;   ;; Because prune-unsupported does not care about the actual content of the impl or spec
;;   ;; configurations, we replace them here with letters (A, B, C, etc. for impls and X, Y, Z, etc. for
;;   ;; specs) for simplification
;;   (define ax-pair (config-pair 'A 'X))
;;   (define by-pair (config-pair 'B 'Y))
;;   (define bz-pair (config-pair 'B 'Z))
;;   (define cw-pair (config-pair 'C 'W))

;;   (define aa-step (impl-step '(timeout (addr 0 0)) null null 'A))
;;   (define xx-step (spec-step (list 'X) null))
;;   (define ab-step (impl-step '(timeout (addr 0 0)) null null 'B))
;;   (define xy-step (spec-step (list 'Y) null))
;;   (define xz-step (spec-step (list 'Z) null))
;;   (define bc-step (impl-step '(timeout (addr 0 0)) null null 'C))
;;   (define yw-step (spec-step (list 'W) null))

;;   (test-equal? "Remove no pairs, because no list"
;;     (prune-unsupported
;;      (mutable-set ax-pair)
;;      ;; incoming-steps
;;      (mutable-hash [ax-pair (mutable-set (list ax-pair aa-step xx-step (hash)))])
;;      ;; related spec steps
;;      (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])
;;      ;; unrelated sucessors
;;      null)
;;     (list
;;      (set ax-pair)
;;      (mutable-hash [(list ax-pair aa-step) (mutable-set xx-step)])))

;;   (test-equal? "Remove no pairs, because unrelated-matches contained only a redundant support"
;;     (prune-unsupported
;;      (set ax-pair bz-pair)
;;      (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
;;                    [bz-pair (mutable-set (list ax-pair ab-step xz-step (hash)))]
;;                    [ax-pair (mutable-set)])
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)])
;;      (list by-pair))
;;     (list
;;      (set ax-pair bz-pair)
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)])))

;;   (test-equal? "Remove last remaining pair"
;;     (prune-unsupported
;;      (mutable-set ax-pair)
;;      (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
;;                    [ax-pair (mutable-set)])
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)])
;;      (list by-pair))
;;     (list
;;      (set)
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set)])))

;;   (test-equal? "Remove a redundant support"
;;     (prune-unsupported
;;      (mutable-set ax-pair bz-pair by-pair)
;;      ;; incoming-steps
;;      (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
;;                    [bz-pair (mutable-set (list ax-pair ab-step xz-step (hash)))]
;;                    [ax-pair (mutable-set)]
;;                    [cw-pair (mutable-set (list by-pair bc-step yw-step (hash)))])
;;      ;; matching spec steps
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step xz-step)]
;;                    [(list by-pair bc-step) (mutable-set yw-step)])
;;      ;; unrelated successors
;;      (list cw-pair))
;;     (list
;;      (set ax-pair bz-pair)
;;      (mutable-hash [(list ax-pair ab-step) (mutable-set xz-step)]
;;                    [(list by-pair bc-step) (mutable-set)])))

;;     (test-equal? "Remove a non-redundant support"
;;       (prune-unsupported
;;        (mutable-set ax-pair by-pair)
;;        ;; incoming-steps
;;        (mutable-hash [by-pair (mutable-set (list ax-pair ab-step xy-step (hash)))]
;;                      [ax-pair (mutable-set)]
;;                      [cw-pair (mutable-set (list by-pair bc-step yw-step (hash)))])
;;        ;; matching spec steps
;;        (mutable-hash [(list ax-pair ab-step) (mutable-set xy-step)]
;;                      [(list by-pair bc-step) (mutable-set yw-step)])
;;        ;; unrelated successors
;;        (list cw-pair))
;;       (list
;;        (set)
;;        (mutable-hash [(list ax-pair ab-step) (mutable-set)]
;;                      [(list by-pair bc-step) (mutable-set)]))))

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define DEBUG-WIDEN #f)

(define (widen-printf m . args)
  (when DEBUG-WIDEN
    (apply printf (format "~s: ~a" (date->string (seconds->date (current-seconds)) #t) m) args)))

(define DISPLAY-STEPS #f)

(define (display-step-line msg)
  (when DISPLAY-STEPS (displayln msg)))

(define (pair->debug-pair pair)
  (list (impl-config-without-state-defs (config-pair-impl-config pair))
        (spec-config-without-state-defs (config-pair-spec-config pair))))

(define (debug-impl-step step)
  (list (impl-step-trigger step)
        (impl-step-outputs step)))

(define (debug-transition-result result)
  (list (csa#-transition-effect-trigger result)
        (csa#-transition-effect-sends result)
        (csa#-transition-effect-spawns result)))

;; ---------------------------------------------------------------------------------------------------
;; Logging

;; Change LOG-RUN to #t to write relevant checking data to a file so that the process of the check can
;; be recreated after the fact without creating the simulation graph all over again.
(define LOG-RUN #f)
(define LOG-FILE-PATH "checker_run_log.fasl")

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

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Test Helpers

;; (module+ test
;;   (define-simple-check (check-valid-actor? actual)
;;     (redex-match? csa-eval ([τ a] b) actual))

;;   (define-syntax (test-valid-actor? stx)
;;     (syntax-parse stx
;;       [(_ name the-term)
;;        #`(test-case name
;;            #,(syntax/loc stx (check-valid-actor? the-term)))]
;;       [(_ the-term)
;;        #`(test-begin
;;            #,(syntax/loc stx (check-valid-actor? the-term)))]))

;;   (define-simple-check (check-valid-instance? actual)
;;     (redex-match? aps-eval ((Φ ...) (goto φ u ...) [τ a]) actual))

;;   (define-syntax (test-valid-instance? stx)
;;     (syntax-parse stx
;;       [(_ name the-term)
;;        #`(test-case name
;;            #,(syntax/loc stx (check-valid-instance? the-term)))]
;;       [(_ the-term)
;;        #`(test-begin
;;            #,(syntax/loc stx (check-valid-instance? the-term)))])))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Top-level tests

;; (module+ test
;;   ;;;; Ignore everything

;;   (define (make-ignore-all-config addr-type)
;;     (make-single-actor-config
;;      (term
;;       ((,addr-type (addr 0 0))
;;        (((define-state (Always) (m) (goto Always)))
;;         (goto Always))))))
;;   (define ignore-all-config (make-ignore-all-config 'Nat))
;;   (define (make-ignore-all-spec-instance addr-type)
;;     (term
;;      (((define-state (Always) [* -> () (goto Always)]))
;;       (goto Always)
;;       (,addr-type (addr 0 0)))))
;;   (define ignore-all-spec-instance
;;     (make-ignore-all-spec-instance 'Nat))
;;   (check-not-false (redex-match csa-eval i ignore-all-config))
;;   (test-valid-instance? ignore-all-spec-instance)

;;   (test-true "ignore all spec/test"
;;     (check-conformance/config ignore-all-config (make-exclusive-spec ignore-all-spec-instance)))

;;   ;;;; Send one message to a statically-known address per request

;;   (define (make-static-response-address type) (term (addr (env ,type) 2)))
;;   (define static-response-type (term (Union (Ack Nat))))
;;   (define static-response-address (make-static-response-address static-response-type))
;;   (define nat-static-response-address (make-static-response-address (term Nat)))
;;   (define static-response-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr ,static-response-type)]) (m)
;;           (begin
;;            (send response-dest (variant Ack 0))
;;            (goto Always response-dest))))
;;        (goto Always ,static-response-address)))))
;;   (define static-double-response-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr ,static-response-type)]) (m)
;;           (begin
;;            (send response-dest (variant Ack 0))
;;            (send response-dest (variant Ack 0))
;;            (goto Always response-dest))))
;;        (goto Always ,static-response-address)))))
;;   (define static-response-spec
;;     (term
;;      (((define-state (Always response-dest)
;;          [* -> ([obligation response-dest *]) (goto Always response-dest)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))
;;   (define ignore-all-with-addr-spec-instance
;;     (term
;;      (((define-state (Always response-dest) [* -> () (goto Always response-dest)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))
;;   (define static-double-response-spec
;;     (term
;;      (((define-state (Always response-dest)
;;          [* -> ([obligation response-dest *]
;;                 [obligation response-dest *])
;;                (goto Always response-dest)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))

;;   (test-valid-actor? static-response-actor)
;;   (test-valid-actor? static-double-response-actor)
;;   (test-valid-instance? static-response-spec)
;;   (test-valid-instance? ignore-all-with-addr-spec-instance)
;;   (test-valid-instance? static-double-response-spec)

;;   (test-true "Static response works"
;;              (check-conformance/config (make-single-actor-config static-response-actor)
;;                           (make-exclusive-spec static-response-spec)))
;;   (test-false "Static response actor, ignore all spec"
;;               (check-conformance/config (make-single-actor-config static-response-actor)
;;                            (make-exclusive-spec ignore-all-with-addr-spec-instance)))
;;   (test-false "static double response actor"
;;               (check-conformance/config (make-single-actor-config static-double-response-actor)
;;                                         (make-exclusive-spec static-response-spec)))
;;   (test-false "Static response spec, ignore-all config"
;;                (check-conformance/config ignore-all-config
;;                                          (make-exclusive-spec static-response-spec)))
;;   ;; tests for non-conformance to spec configurations with many-of commitments
;;   (test-false "Static double response spec, ignore-all config"
;;     (check-conformance/config ignore-all-config
;;                               (make-exclusive-spec static-double-response-spec)))

;;   ;;;; Pattern matching tests, without dynamic channels

;;   (define pattern-match-type `(Union [A Nat] [B Nat]))
;;   (define pattern-match-spec
;;     (term
;;      (((define-state (Matching r)
;;          [(variant A *) -> ([obligation r (variant A *)]) (goto Matching r)]
;;          [(variant B *) -> ([obligation r (variant B *)]) (goto Matching r)]))
;;       (goto Matching ,(make-static-response-address pattern-match-type))
;;       ((Union [A Nat] [B Nat]) (addr 0 0)))))

;;   (define pattern-matching-actor
;;     (term
;;      (((Union [A Nat] [B Nat]) (addr 0 0))
;;       (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
;;           (case m
;;             [(A x) (begin (send r (variant A x)) (goto Always r))]
;;             [(B y) (begin (send r (variant B 0)) (goto Always r))])))
;;        (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

;;   (define reverse-pattern-matching-actor
;;     (term
;;      (((Union [A Nat] [B Nat]) (addr 0 0))
;;       (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
;;           (case m
;;             [(A x) (begin (send r (variant B 0)) (goto Always r))]
;;             [(B y) (begin (send r (variant A y)) (goto Always r))])))
;;        (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

;;   (define partial-pattern-matching-actor
;;     (term
;;      (((Union [A Nat] [B Nat]) (addr 0 0))
;;       (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
;;           (case m
;;             [(A x) (begin (send r (variant A 0)) (goto Always r))]
;;             [(B y) (goto Always r)])))
;;        (goto Always ,(make-static-response-address `(Union [A Nat] [B Nat])))))))

;;   (test-valid-instance? pattern-match-spec)
;;   (test-valid-actor? pattern-matching-actor)
;;   (test-valid-actor? reverse-pattern-matching-actor)
;;   (test-valid-actor? partial-pattern-matching-actor)

;;   (test-true "Pattern matching"
;;     (check-conformance/config (make-single-actor-config pattern-matching-actor)
;;                               (make-exclusive-spec pattern-match-spec)))
;;   (test-false "Send on A but not B; should send on both"
;;               (check-conformance/config (make-single-actor-config partial-pattern-matching-actor)
;;                            (make-exclusive-spec pattern-match-spec)))
;;   (test-false "Pattern matching discriminates different patterns"
;;     (check-conformance/config (make-single-actor-config reverse-pattern-matching-actor)
;;                               (make-exclusive-spec  pattern-match-spec)))

;;   ;;;; "Or" pattern matching
;;   (define or-pattern-match-spec
;;     (term
;;      (((define-state (Matching r)
;;          [* -> ([obligation r (or (variant A *) (variant B *))]) (goto Matching r)]))
;;       (goto Matching ,(make-static-response-address `(Union [A Nat] [B Nat])))
;;       ((Union [A Nat] [B Nat]) (addr 0 0)))))

;;   (define or-wrong-pattern-match-spec
;;     (term
;;      (((define-state (Matching r)
;;          [* -> ([obligation r (or (variant A *) (variant C *))]) (goto Matching r)]))
;;       (goto Matching ,(make-static-response-address `(Union [A Nat] [B Nat])))
;;       ((Union [A Nat] [B Nat]) (addr 0 0)))))

;;   (test-valid-instance? or-pattern-match-spec)
;;   (test-valid-instance? or-wrong-pattern-match-spec)
;;   (test-true "Pattern match with or"
;;     (check-conformance/config (make-single-actor-config pattern-matching-actor)
;;                               (make-exclusive-spec or-pattern-match-spec)))
;;   (test-false "Pattern match with wrong or pattern"
;;     (check-conformance/config (make-single-actor-config pattern-matching-actor)
;;                               (make-exclusive-spec or-wrong-pattern-match-spec)))

;;   (define send-message-then-another
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Init [r (Addr (Union [A] [B]))]) (m)
;;           (begin
;;            (send r (variant A))
;;            (goto SendOther r)))
;;         (define-state (SendOther [r (Addr (Union [A] [B]))]) (m)
;;           (begin
;;            (send r (variant A))
;;            (goto Done))
;;           [(timeout 5)
;;            (begin
;;             (send r (variant B))
;;             (goto Done))])
;;         (define-state (Done) (m) (goto Done)))
;;        (goto Init (addr (env (Union [A] [B])) 0))))))

;;   (define overlapping-patterns-spec
;;     (term
;;      (((define-state (Init r)
;;          [* -> ([obligation r (or (variant A) (variant B))]
;;                 [obligation r (variant A)])
;;             (goto NoMoreSends)])
;;        (define-state (NoMoreSends)
;;          [* -> () (goto NoMoreSends)]))
;;       (goto Init (addr (env (Union [A] [B])) 0))
;;       (Nat (addr 0 0)))))

;;   ;; Non-deterministic/overlap pattern-matching is unsupported: we just pick for each output the first
;;   ;; pattern that can possibly match
;;   (test-valid-actor? send-message-then-another)
;;   (test-valid-instance? overlapping-patterns-spec)
;;   (test-true "Overlapping output patterns are okay"
;;     (check-conformance/config
;;      (make-single-actor-config send-message-then-another)
;;      (make-exclusive-spec overlapping-patterns-spec)))

;;   ;;;; Dynamic request/response

;;   (define request-response-spec
;;     (term
;;      (((define-state (Always)
;;          [response-target -> ([obligation response-target *]) (goto Always)]))
;;       (goto Always)
;;       ((Addr Nat) (addr 0 0)))))

;;   (define request-same-response-addr-spec
;;     (term
;;      (((define-state (Init)
;;          [response-target -> ([obligation response-target *]) (goto HaveAddr response-target)])
;;        (define-state (HaveAddr response-target)
;;          [new-response-target -> ([obligation response-target *]) (goto HaveAddr response-target)]))
;;       (goto Init)
;;       ((Addr Nat) (addr 0 0)))))
;;   (define request-response-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always [i Nat]) (response-target)
;;           (begin
;;            (send response-target i)
;;            (goto Always i))))
;;        (goto Always 0)))))
;;   (define respond-to-first-addr-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init) (response-target)
;;           (begin
;;            (send response-target 0)
;;            (goto HaveAddr 1 response-target)))
;;         (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
;;           (begin
;;            (send response-target i)
;;            (goto HaveAddr i response-target))))
;;        (goto Init)))))
;;   (define respond-to-first-addr-actor2
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always [original-addr (Union (NoAddr) (Original (Addr Nat)))]) (response-target)
;;           (begin
;;            (case original-addr
;;              [(NoAddr)
;;               (begin
;;                (send response-target 0)
;;                (goto Always (variant Original response-target)))]
;;              [(Original o)
;;               (begin
;;                (send o 0)
;;                (goto Always original-addr))]))))
;;        (goto Always (variant NoAddr))))))
;;   (define delay-saving-address-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init) (response-target)
;;           (begin
;;            (send response-target 0)
;;            (goto HaveAddr 1 response-target)))
;;         (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
;;           (begin
;;            (send response-target i)
;;            (goto HaveAddr i new-response-target))))
;;        (goto Init)))))
;;   (define double-response-actor
;;     `(((Addr Nat) (addr 0 0))
;;       (((define-state (Always [i Nat]) (response-dest)
;;           (begin
;;            (send response-dest i)
;;            (send response-dest i)
;;            (goto Always i))))
;;        (goto Always 0))))
;;   (define respond-once-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init) (response-target)
;;           (begin
;;            (send response-target 0)
;;            (goto NoMore)))
;;         (define-state (NoMore) (new-response-target)
;;           (goto NoMore)))
;;        (goto Init)))))
;;   (define delayed-send-no-timeout-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (NoAddr) (response-target)
;;           (goto HaveAddr response-target))
;;         (define-state (HaveAddr [response-target (Addr Nat)]) (new-response-target)
;;           (begin
;;            (send response-target 1)
;;            (goto HaveAddr new-response-target))))
;;        (goto NoAddr)))))
;;   (define delayed-send-with-timeout-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (NoAddr) (response-target)
;;           (goto HaveAddr response-target))
;;         (define-state (HaveAddr [response-target (Addr Nat)]) (new-response-target)
;;           (begin
;;            (send response-target 1)
;;            (goto HaveAddr new-response-target))
;;           [(timeout 5)
;;            (begin
;;             (send response-target 2)
;;             (goto NoAddr))]))
;;        (goto NoAddr)))))

;;   (test-valid-instance? request-response-spec)
;;   (test-valid-instance? request-same-response-addr-spec)
;;   (test-valid-actor? request-response-actor)
;;   (test-valid-actor? respond-to-first-addr-actor)
;;   (test-valid-actor? respond-to-first-addr-actor2)
;;   (test-valid-actor? double-response-actor)
;;   (test-valid-actor? delay-saving-address-actor)
;;   (test-valid-actor? respond-once-actor)
;;   (test-valid-actor? delayed-send-no-timeout-actor)
;;   (test-valid-actor? delayed-send-with-timeout-actor)
;;   (test-true "request/response 1"
;;              (check-conformance/config (make-single-actor-config request-response-actor)
;;                           (make-exclusive-spec request-response-spec)))

;;   (test-false "request/response 2"
;;               (check-conformance/config (make-single-actor-config respond-to-first-addr-actor)
;;                            (make-exclusive-spec request-response-spec)))
;;   (test-false "request/response 3"
;;                (check-conformance/config (make-single-actor-config respond-to-first-addr-actor2)
;;                             (make-exclusive-spec request-response-spec)))
;;   (test-false "request/response 4"
;;                (check-conformance/config (make-single-actor-config request-response-actor)
;;                             (make-exclusive-spec request-same-response-addr-spec)))
;;   (test-false "ignore all actor does not satisfy request/response"
;;               (check-conformance/config (make-ignore-all-config (term (Addr Nat)))
;;                            (make-exclusive-spec request-response-spec)))
;;   (test-false "Respond-once actor does not satisfy request/response"
;;               (check-conformance/config (make-single-actor-config respond-once-actor)
;;                            (make-exclusive-spec request-response-spec)))
;;   (test-true "check-conf misc. 1"
;;     (check-conformance/config (make-single-actor-config respond-to-first-addr-actor)
;;                               (make-exclusive-spec request-same-response-addr-spec)))
;;   (test-true "check-conf misc. 2"
;;     (check-conformance/config (make-single-actor-config respond-to-first-addr-actor2)
;;                               (make-exclusive-spec request-same-response-addr-spec)))
;;   (test-false "check-conf misc. 3"
;;     (check-conformance/config (make-single-actor-config double-response-actor)
;;                               (make-exclusive-spec request-response-spec)))
;;   (test-false "check-conf misc. 4"
;;     (check-conformance/config (make-single-actor-config delay-saving-address-actor)
;;                               (make-exclusive-spec request-response-spec)))
;;   (test-false "Send only on next receive does not satisfy request/response"
;;                (check-conformance/config (make-single-actor-config delayed-send-no-timeout-actor)
;;                             (make-exclusive-spec request-response-spec)))
;;   (test-true "check-conf misc. 5"
;;     (check-conformance/config (make-single-actor-config delayed-send-with-timeout-actor)
;;                               (make-exclusive-spec request-response-spec)))

;;   (define (make-self-send-response-actor addr-number)
;;     (term
;;      (((Union [FromEnv (Addr Nat)] [FromSelf (Addr Nat)]) (addr self-send-loc ,addr-number))
;;       (((define-state (Always) (msg)
;;           (case msg
;;             [(FromEnv response-target)
;;              (begin
;;                (send (addr self-send-loc ,addr-number) (variant FromSelf response-target))
;;                (goto Always))]
;;             [(FromSelf response-target)
;;              (begin
;;                (send response-target 0)
;;                (goto Always))])))
;;        (goto Always)))))

;;   (define from-env-request-response-spec
;;     (term
;;      (((define-state (Always)
;;          [(variant FromEnv response-target) -> ([obligation response-target *]) (goto Always)]))
;;       (goto Always)
;;       ((Union [FromEnv (Addr Nat)]) (addr self-send-loc 0)))))

;;   (define from-env-wrapper
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always [sender (Addr (Union [FromEnv (Addr Nat)]))]) (msg)
;;           (begin
;;             (send sender (variant FromEnv msg))
;;             (goto Always sender))))
;;        (goto Always (addr self-send-loc 0))))))

;;   (test-valid-actor? (make-self-send-response-actor 0))
;;   (test-valid-instance? from-env-request-response-spec)
;;   (test-true "Can self-send, then send out to satisfy dynamic request/response"
;;     (check-conformance/config (make-single-actor-config (make-self-send-response-actor 0))
;;                               (make-exclusive-spec from-env-request-response-spec)))
;;   (test-true "From-env wrapper with self-send sender"
;;     (check-conformance/config (make-empty-queues-config (list from-env-wrapper)
;;                                                         (list (make-self-send-response-actor 1)))
;;                               (make-exclusive-spec request-response-spec)))

;;   ;; When given two choices to/from same state, have to take the one where the outputs match the
;;   ;; commitments
;;   (define reply-once-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A) (r)
;;           (begin
;;             (send r 0)
;;             (goto B)))
;;         (define-state (B) (r) (goto B)))
;;        (goto A)))))
;;   (define maybe-reply-spec
;;     (term
;;      (((define-state (A)
;;          [r -> ([obligation r *]) (goto B)]
;;          [r -> () (goto B)])
;;        (define-state (B)
;;          [* -> () (goto B)]))
;;       (goto A)
;;       ((Addr Nat) (addr 0 0)))))

;;   (test-valid-actor? reply-once-actor)
;;   (test-valid-instance? maybe-reply-spec)
;;   (test-true "reply-once actor, maybe-reply spec"
;;     (check-conformance/config (make-single-actor-config reply-once-actor)
;;                               (make-exclusive-spec maybe-reply-spec)))

;;   ;;;; Non-deterministic branching in spec

;;   (define zero-nonzero-response-address (make-static-response-address `(Union [NonZero] [Zero])))
;;   (define zero-nonzero-spec
;;     (term
;;      (((define-state (S1 r)
;;          [* -> ([obligation r (variant Zero)])    (goto S1 r)]
;;          [* -> ([obligation r (variant NonZero)]) (goto S1 r)]))
;;       (goto S1 ,zero-nonzero-response-address)
;;       (Nat (addr 0 0)))))
;;   (define zero-spec
;;     (term
;;      (((define-state (S1 r)
;;          [* -> ([obligation r (variant Zero)]) (goto S1 r)]))
;;       (goto S1 ,zero-nonzero-response-address)
;;       (Nat (addr 0 0)))))
;;   (define primitive-branch-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (S1 [dest (Addr (Union [NonZero] [Zero]))]) (i)
;;           (begin
;;             (case (< 0 i)
;;               [(True) (send dest (variant NonZero))]
;;               [(False) (send dest (variant Zero))])
;;             (goto S1 dest))))
;;        (goto S1 ,zero-nonzero-response-address)))))

;;   (test-valid-instance? static-response-spec)
;;   (test-valid-instance? zero-nonzero-spec)
;;   (test-valid-instance? zero-spec)
;;   (test-valid-actor? primitive-branch-actor)

;;   (test-true "Zero/NonZero"
;;     (check-conformance/config (make-single-actor-config primitive-branch-actor)
;;                               (make-exclusive-spec zero-nonzero-spec)))
;;   (test-false "Zero"
;;     (check-conformance/config (make-single-actor-config primitive-branch-actor)
;;                               (make-exclusive-spec zero-spec)))

;;   ;;;; Optional Commitments
;;   (define optional-commitment-spec
;;     (term
;;      (((define-state (Always r)
;;          [* -> ([obligation r *]) (goto Always r)]
;;          [* -> () (goto Always r)]))
;;       (goto Always (addr (env Nat) 0))
;;       (Nat (addr 0 0)))))

;;   (test-valid-instance? optional-commitment-spec)
;;   (test-true "optional commitment spec"
;;     (check-conformance/config ignore-all-config (make-exclusive-spec optional-commitment-spec)))

;;   ;;;; Stuck states in concrete evaluation

;;   (define nat-to-nat-spec
;;     (term
;;      (((define-state (Always response-dest)
;;          [* -> ([obligation response-dest *]) (goto Always response-dest)]))
;;       (goto Always ,nat-static-response-address)
;;       (Nat (addr 0 0)))))
;;   (define div-by-one-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr Nat)]) (n)
;;           (begin
;;             (send response-dest (/ n 1))
;;             (goto Always response-dest))))
;;        (goto Always ,nat-static-response-address)))))
;;   (define div-by-zero-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr Nat)]) (n)
;;           (begin
;;             (send response-dest (/ n 0))
;;             (goto Always response-dest))))
;;        (goto Always ,nat-static-response-address)))))

;;   (test-valid-instance? nat-to-nat-spec)
;;   (test-valid-actor? div-by-zero-actor)
;;   (test-valid-actor? div-by-one-actor)

;;   (test-true "Div by one vs. nat-to-nat spec"
;;              (check-conformance/config (make-single-actor-config div-by-one-actor)
;;                           (make-exclusive-spec nat-to-nat-spec)))
;;   (test-true "Div by zero vs. nat-to-nat spec"
;;               (check-conformance/config (make-single-actor-config div-by-zero-actor)
;;                            (make-exclusive-spec nat-to-nat-spec)))

;;   ;;;; Unobservable communication

;;   ;; wildcard unobservables are ignored for the purpose of output commitments
;;   (test-true "request/response actor vs. ignore-all spec"
;;              (check-conformance/config (make-single-actor-config request-response-actor)
;;                           (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))

;;   ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect
;;   ;; conformance
;;   (test-true "request response actor and spec, with unobs communication"
;;              (check-conformance/config (make-single-actor-config request-response-actor)
;;                           (make-spec request-response-spec (list '((Addr Nat) (addr 0 0))))))

;;   ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
;;   (test-false "static response with unobs communication"
;;               (check-conformance/config (make-single-actor-config static-response-actor)
;;                            (make-spec static-response-spec (list '(Nat (addr 0 0))))))

;;   ;; 3. Conformance regained for static req/resp when add an unobs transition
;;   (define static-response-spec-with-unobs
;;     (term
;;      (((define-state (Always response-dest)
;;          [*     -> ([obligation response-dest *]) (goto Always response-dest)]
;;          [free -> ([obligation response-dest *]) (goto Always response-dest)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))
;;   (test-valid-instance? static-response-spec-with-unobs)

;;   (test-true "static response with unobs, incl in spec"
;;              (check-conformance/config (make-single-actor-config static-response-actor)
;;                           (make-spec static-response-spec-with-unobs (list '(Nat (addr 0 0))))))

;;   ;; 4. unobs causes a particular behavior (like connected/error in TCP)
;;   (define obs-unobs-static-response-address
;;     (make-static-response-address (term (Union (TurningOn) (TurningOff)))))
;;   (define unobs-toggle-spec
;;     (term (((define-state (Off r)
;;               [* -> ([obligation r (variant TurningOn)]) (goto On r)])
;;             (define-state (On r)
;;               [* -> () (goto On r)]
;;               [free -> ([obligation r (variant TurningOff)]) (goto Off r)]))
;;            (goto Off ,obs-unobs-static-response-address)
;;            ((Union [FromObserver]) (addr 0 0)))))
;;   (define unobs-toggle-actor
;;     (term
;;      (((Union [FromObserver] [FromUnobservedEnvironment]) (addr 0 0))
;;       (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver)
;;              (begin
;;                (send r (variant TurningOn))
;;                (goto On r))]
;;             [(FromUnobservedEnvironment) (goto Off r)]))
;;         (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto On r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOff))
;;                (goto Off r))])))
;;        (goto Off ,obs-unobs-static-response-address)))))
;;   (define unobs-toggle-actor-wrong1
;;     (term
;;      (((Union [FromObserver] [FromUnobservedEnvironment]) (addr 0 0))
;;       (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver)
;;              (begin
;;                (send r (variant TurningOn))
;;                ;; Going to Off instead of On
;;                (goto Off r))]
;;             [(FromUnobservedEnvironment) (goto Off r)]))
;;         (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto On r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOff))
;;                (goto Off r))])))
;;        (goto Off ,obs-unobs-static-response-address)))))
;;   (define unobs-toggle-actor-wrong2
;;     (term
;;      (((Union [FromObserver] [FromUnobservedEnvironment]) (addr 0 0))
;;       (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver)
;;              (begin
;;                (send r (variant TurningOn))
;;                (goto On r))]
;;             [(FromUnobservedEnvironment) (goto On r)]))
;;         (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto On r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOff))
;;                (goto Off r))])))
;;        (goto Off ,obs-unobs-static-response-address)))))
;;   (define unobs-toggle-actor-wrong3
;;     (term
;;      (((Union [FromObserver] [FromUnobservedEnvironment]) (addr 0 0))
;;       (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver)
;;              (begin
;;                (send r (variant TurningOn))
;;                (goto On r))]
;;             [(FromUnobservedEnvironment) (goto Off r)]))
;;         (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto On r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOff))
;;                (goto On r))])))
;;        (goto Off ,obs-unobs-static-response-address)))))
;;   (define unobs-toggle-actor-wrong4
;;     (term
;;      (((Union [FromObserver] [FromUnobservedEnvironment]) (addr 0 0))
;;       (((define-state (Off [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto Off r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOn))
;;                (goto On r))]))
;;         (define-state (On [r (Addr (Union [TurningOn] [TurningOff]))]) (m)
;;           (case m
;;             [(FromObserver) (goto On r)]
;;             [(FromUnobservedEnvironment)
;;              (begin
;;                (send r (variant TurningOff))
;;                (goto Off r))])))
;;        (goto Off ,obs-unobs-static-response-address)))))

;;   (test-valid-instance? unobs-toggle-spec)
;;   (test-valid-actor? unobs-toggle-actor)
;;   (test-valid-actor? unobs-toggle-actor-wrong1)
;;   (test-valid-actor? unobs-toggle-actor-wrong2)
;;   (test-valid-actor? unobs-toggle-actor-wrong3)
;;   (test-valid-actor? unobs-toggle-actor-wrong4)

;;   (test-true "Obs/Unobs test"
;;              (check-conformance/config (make-single-actor-config unobs-toggle-actor)
;;                           (make-spec unobs-toggle-spec (list '((Union [FromUnobservedEnvironment]) (addr 0 0))))))

;;   (for ([actor (list unobs-toggle-actor-wrong1
;;                      unobs-toggle-actor-wrong2
;;                      unobs-toggle-actor-wrong3
;;                      unobs-toggle-actor-wrong4)])
;;     (test-false "Obs/Unobs bug-finding test(s)"
;;                 (check-conformance/config (make-single-actor-config actor)
;;                           (make-spec unobs-toggle-spec (list '((Union [FromUnobservedEnvironment]) (addr 0 0)))))))

;;   ;;;; Records

;;   (define record-req-resp-spec
;;     (term
;;      (((define-state (Always)
;;          [(record [dest dest] [msg (variant A)]) -> ([obligation dest (variant A)]) (goto Always)]
;;          [(record [dest dest] [msg (variant B)]) -> ([obligation dest (variant B)]) (goto Always)]))
;;       (goto Always)
;;       ((Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]) (addr 0 0)))))
;;   (define record-req-resp-actor
;;     (term
;;      (((Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]) (addr 0 0))
;;       (((define-state (Always) (m)
;;           (begin
;;             (send (: m dest) (: m msg))
;;             (goto Always))))
;;        (goto Always)))))
;;   (define record-req-wrong-resp-actor
;;     (term
;;      (((Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]) (addr 0 0))
;;       (((define-state (Always) (m)
;;           (begin
;;             (send (: m dest) (variant A))
;;             (goto Always))))
;;        (goto Always)))))

;;   (test-valid-instance? record-req-resp-spec)
;;   (test-valid-actor? record-req-resp-actor)
;;   (test-valid-actor? record-req-wrong-resp-actor)

;;   (test-true "record 1"
;;              (check-conformance/config (make-single-actor-config record-req-resp-actor)
;;                           (make-exclusive-spec record-req-resp-spec)))
;;   (test-false "record 2"
;;               (check-conformance/config (make-single-actor-config record-req-wrong-resp-actor)
;;                            (make-exclusive-spec record-req-resp-spec)))

;;   ;;;; Let
;;   (define static-response-let-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr ,static-response-type)]) (m)
;;           (let ([new-r response-dest])
;;             (begin
;;               (send new-r (variant Ack 0))
;;               (goto Always new-r)))))
;;        (goto Always ,static-response-address)))))
;;   (define static-double-response-let-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [response-dest (Addr ,static-response-type)]) (m)
;;           (let ([new-r response-dest])
;;             (begin
;;               (send new-r (variant Ack 0))
;;               (send new-r (variant Ack 0))
;;               (goto Always new-r)))))
;;        (goto Always ,static-response-address)))))

;;   (test-valid-actor? static-response-let-actor)
;;   (test-valid-actor? static-double-response-let-actor)

;;   (test-true "Let 1"
;;              (check-conformance/config (make-single-actor-config static-response-let-actor)
;;                           (make-exclusive-spec static-response-spec)))
;;   (test-false "Let 2"
;;               (check-conformance/config (make-single-actor-config static-double-response-let-actor)
;;                            (make-exclusive-spec static-response-spec)))

;;   ;; Check that = gives both results
;;   (define equal-actor-wrong1
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [dest (Addr ,static-response-type)]) (m)
;;           (begin
;;             (send dest (variant Ack 0))
;;             (case (= m 0)
;;               [(True) (goto A dest)]
;;               [(False) (goto B)])))
;;         (define-state (B) (m) (goto B)))
;;        (goto A ,static-response-address)))))
;;   (define equal-actor-wrong2
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [dest (Addr ,static-response-type)]) (m)
;;           (begin
;;             (send dest (variant Ack 0))
;;             (case (= m 0)
;;               [(True) (goto B)]
;;               [(False) (goto A dest)])))
;;         (define-state (B) (m) (goto B)))
;;        (goto A ,static-response-address)))))
;;     (define equal-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [dest (Addr ,static-response-type)]) (m)
;;           (begin
;;             (send dest (variant Ack 0))
;;             (case (= m 0)
;;               [(True) (goto B dest)]
;;               [(False) (goto A dest)])))
;;         (define-state (B [dest (Addr ,static-response-type)]) (m)
;;           (begin
;;             (send dest (variant Ack 0))
;;             (goto B dest))))
;;        (goto A ,static-response-address)))))

;;   (test-valid-actor? equal-actor-wrong1)
;;   (test-valid-actor? equal-actor-wrong2)
;;   (test-valid-actor? equal-actor)

;;   (test-false "Equal actor wrong 1"
;;    (check-conformance/config (make-single-actor-config equal-actor-wrong1)
;;             (make-exclusive-spec static-response-spec)))
;;   (test-false "Equal actor wrong 2"
;;    (check-conformance/config (make-single-actor-config equal-actor-wrong2)
;;             (make-exclusive-spec static-response-spec)))
;;   (test-true "Equal actor"
;;    (check-conformance/config (make-single-actor-config equal-actor)
;;                 (make-exclusive-spec static-response-spec)))

;;   ;;;; For loops
;;   (define loop-do-nothing-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A) (m)
;;           (begin
;;             (for/fold ([folded-result 0])
;;                       ([i (list 1 2 3)])
;;               i)
;;             (goto A))))
;;        (goto A)))))
;;   (define loop-send-unobs-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A [r (Addr Nat)]) (m)
;;           (begin
;;             (for/fold ([folded-result 0])
;;                       ([i (list 1 2 3)])
;;               (send r i))
;;             (goto A r))))
;;        (goto A ,nat-static-response-address)))))
;;   (define send-before-loop-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A) (r)
;;           (begin
;;             (send r 0)
;;             (for/fold ([folded-result 0])
;;                       ([i (list 1 2 3)])
;;               i)
;;             (goto A))))
;;        (goto A)))))
;;   (define send-inside-loop-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A) (r)
;;           (begin
;;             (for/fold ([folded-result 0])
;;                       ([r (list r)])
;;               (send r 0))
;;             (goto A))))
;;        (goto A)))))
;;   (define send-after-loop-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A) (r)
;;           (begin
;;             (for/fold ([folded-result 0])
;;                       ([i (list 1 2 3)])
;;               i)
;;             (send r 0)
;;             (goto A))))
;;        (goto A)))))

;;   (test-valid-actor? loop-do-nothing-actor)
;;   (test-valid-actor? loop-send-unobs-actor)
;;   (test-valid-actor? send-before-loop-actor)
;;   (test-valid-actor? send-inside-loop-actor)
;;   (test-valid-actor? send-after-loop-actor)

;;   (test-true "loop do nothing"
;;     (check-conformance/config (make-single-actor-config loop-do-nothing-actor)
;;                               (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
;;   (test-true "loop send unobs"
;;     (check-conformance/config (make-single-actor-config loop-send-unobs-actor)
;;                               (make-exclusive-spec (make-ignore-all-spec-instance '(Addr Nat)))))
;;   (test-true "send before loop"
;;     (check-conformance/config (make-single-actor-config send-before-loop-actor)
;;                               (make-exclusive-spec request-response-spec)))
;;   (test-false "send inside loop"
;;     (check-conformance/config (make-single-actor-config send-inside-loop-actor)
;;                               (make-exclusive-spec request-response-spec)))
;;   (test-true "send after loop"
;;     (check-conformance/config (make-single-actor-config send-after-loop-actor)
;;                               (make-exclusive-spec request-response-spec)))

;;   ;;;; Timeouts

;;   (define timeout-response-address (make-static-response-address `(Union [GotTimeout] [GotMessage])))
;;   (define timeout-spec
;;     (term
;;      (((define-state (A r)
;;          [* -> ([obligation r (variant GotMessage)]) (goto A r)]
;;          [free -> ([obligation r (variant GotTimeout)]) (goto A r)]))
;;       (goto A ,timeout-response-address)
;;       (Nat (addr 0 0)))))
;;   (define got-message-only-spec
;;     (term
;;      (((define-state (A r)
;;          [* -> ([obligation r (variant GotMessage)]) (goto A r)]))
;;       (goto A ,timeout-response-address)
;;       (Nat (addr 0 0)))))
;;   (define timeout-and-send-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
;;           (begin
;;             (send r (variant GotMessage))
;;             (goto A r))
;;           [(timeout 5)
;;            (begin
;;              (send r (variant GotTimeout))
;;              (goto A r))]))
;;        (goto A ,timeout-response-address)))))
;;   (define timeout-to-send-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
;;           (goto SendOnTimeout r))
;;         (define-state (SendOnTimeout [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
;;           (begin
;;             (send r (variant GotMessage))
;;             (goto SendOnTimeout r))
;;           [(timeout 5)
;;            (begin
;;              (send r (variant GotMessage))
;;              (goto A r))]))
;;        (goto A ,timeout-response-address)))))
;;   (define spawn-timeout-sender-actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (A [r (Addr (Union (GotMessage) (GotTimeout)))]) (m)
;;           (begin
;;             (spawn 3 Nat (goto B)
;;                    (define-state (B) (m)
;;                      (goto B)
;;                      [(timeout 5)
;;                       (begin
;;                         (send r (variant GotMessage))
;;                         (goto Done))])
;;                    (define-state (Done) (m)
;;                      (goto Done)))
;;             (goto A r))))
;;        (goto A ,timeout-response-address)))))

;;   (test-valid-instance? timeout-spec)
;;   (test-valid-instance? got-message-only-spec)
;;   (test-valid-actor? timeout-and-send-actor)
;;   (test-valid-actor? timeout-to-send-actor)
;;   (test-valid-actor? spawn-timeout-sender-actor)
;;   (test-true "Timeout and send vs. timeout spec"
;;     (check-conformance/config (make-single-actor-config timeout-and-send-actor)
;;                               (make-exclusive-spec timeout-spec)))
;;   (test-false "Timeout and send vs. got-messaage-only spec"
;;     (check-conformance/config (make-single-actor-config timeout-and-send-actor)
;;                               (make-exclusive-spec got-message-only-spec)))
;;   (test-false "Timeout to send vs. timeout spec"
;;     (check-conformance/config (make-single-actor-config timeout-to-send-actor)
;;                               (make-exclusive-spec timeout-spec)))
;;   ;; we would expect this to pass, except the abstraction is too coarse
;;   (test-false "Spawn timeout sender"
;;     (check-conformance/config (make-single-actor-config spawn-timeout-sender-actor)
;;                               (make-exclusive-spec timeout-spec)))

;;   ;; Multiple Disjoint Actors
;;   (define static-response-actor2
;;     (term
;;      ((Nat (addr 1 0))
;;       (((define-state (Always2 [response-dest (Addr ,static-response-type)]) (m)
;;              (begin
;;                (send response-dest (variant Ack 0))
;;                (goto Always2 response-dest))))
;;        (goto Always2 ,static-response-address)))))
;;   (define other-static-response-actor
;;     (term
;;      ((Nat (addr 1 0))
;;       (((define-state (Always2 [response-dest (Addr ,static-response-type)]) (m)
;;              (begin
;;                (send response-dest (variant Ack 0))
;;                (goto Always2 response-dest))))
;;        (goto Always2 (addr (env ,static-response-type) 3))))))
;;   (define static-response-with-extra-spec
;;     (term
;;      (((define-state (Always response-dest)
;;          [* -> ([obligation response-dest *]) (goto Always response-dest)]
;;          [free -> ([obligation response-dest *]) (goto Always response-dest)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))

;;   (test-valid-actor? static-response-actor2)
;;   (test-valid-actor? other-static-response-actor)
;;   (test-valid-instance? static-response-with-extra-spec)

;;   (test-false "Multi actor test 1"
;;               (check-conformance/config
;;                 (make-empty-queues-config (list static-response-actor static-response-actor2) null)
;;                 (make-spec static-response-spec (list '(Nat (addr 1 0))))))
;;   (test-true "Multi actor test 2"
;;              (check-conformance/config
;;               (make-empty-queues-config (list static-response-actor static-response-actor2) null)
;;               (make-spec static-response-with-extra-spec (list '(Nat (addr 1 0))))))
;;   (test-true "Multi actor test 3"
;;              (check-conformance/config
;;                (make-empty-queues-config (list static-response-actor other-static-response-actor) null)
;;                (make-spec static-response-spec (list '(Nat (addr 1 0))))))

;;   ;; Actors working together
;;   (define statically-delegating-responder-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (A [responder (Addr (Addr Nat))]) (m)
;;           (begin
;;             (send responder m)
;;             (goto A responder))))
;;        (goto A (addr 1 0))))))

;;   (define request-response-actor2
;;     (term
;;      (((Addr Nat) (addr 1 0))
;;       (((define-state (Always) (response-target)
;;           (begin
;;             (send response-target 0)
;;             (goto Always))))
;;        (goto Always)))))

;;   (test-valid-actor? statically-delegating-responder-actor)
;;   (test-valid-actor? request-response-actor2)

;;   (test-true "Multiple actors 3"
;;              (check-conformance/config
;;               (make-empty-queues-config (list request-response-actor2 statically-delegating-responder-actor) null)
;;               (make-exclusive-spec request-response-spec)))


;;   ;;;; Self Reveal
;;   (define self-reveal-response-addr `(addr (env (Addr (Addr Nat))) 0))
;;   (define self-reveal-spec
;;     (term
;;      (((define-state (Init r)
;;          [free -> ([obligation r self]) (goto Running)])
;;        (define-state (Running)
;;          [r -> ([obligation r *]) (goto Running)]))
;;       (goto Init ,self-reveal-response-addr))))

;;   (define self-reveal-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
;;           (goto Init r)
;;           [(timeout 5)
;;            (begin
;;              (send r (addr 0 0))
;;              (goto Running))])
;;         (define-state (Running) (r)
;;           (begin
;;             (send r 1)
;;             (goto Running))))
;;        (goto Init ,self-reveal-response-addr)))))

;;   (define reveal-wrong-address-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
;;           (goto Init r)
;;           [(timeout 5)
;;            (begin
;;              (send r (addr 2 0))
;;              (goto Running))])
;;         (define-state (Running) (r)
;;           (begin
;;             (send r 1)
;;             (goto Running))))
;;        (goto Init ,self-reveal-response-addr)))))
;;   (define to-reveal-ignore-all-actor
;;     (term
;;      (((Addr Nat) (addr 2 0))
;;       (((define-state (IgnoreAll) (r) (goto IgnoreAll)))
;;        (goto IgnoreAll)))))

;;   (define reveal-self-double-output-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Init [r (Addr (Addr (Addr Nat)))]) (x)
;;           (goto Init r)
;;           [(timeout 5)
;;            (begin
;;              (send r (addr 0 0))
;;              (goto Running))])
;;         (define-state (Running) (r)
;;           (begin
;;             (send r 1)
;;             (send r 1)
;;             (goto Running))))
;;        (goto Init ,self-reveal-response-addr)))))

;;   (test-valid-actor? self-reveal-actor)
;;   (test-valid-actor? reveal-wrong-address-actor)
;;   (test-valid-actor? to-reveal-ignore-all-actor)
;;   (test-valid-actor? reveal-self-double-output-actor)
;;   ;; (test-valid-instance? self-reveal-spec)

;;   (test-true "Reveal self works"
;;              (check-conformance/config
;;               (make-single-actor-config self-reveal-actor)
;;               (make-unrevealed-exclusive-spec self-reveal-spec)))

;;   (test-false "Catch self-reveal of wrong address"
;;               (check-conformance/config
;;                (make-empty-queues-config null
;;                                          (list reveal-wrong-address-actor to-reveal-ignore-all-actor))
;;                (make-unrevealed-exclusive-spec self-reveal-spec)))

;;   (test-false "Catch self-reveal of actor that doesn't follow its behavior"
;;               (check-conformance/config
;;                (make-single-actor-config reveal-self-double-output-actor)
;;                (make-unrevealed-exclusive-spec self-reveal-spec)))

;;   ;;;; Spawn
;;   (define echo-spawning-actor
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always) (response-target)
;;           (begin
;;             (let ([child
;;                    (spawn
;;                     echo-spawn
;;                     (Addr Nat)
;;                     (goto EchoResponse)
;;                     (define-state (EchoResponse) (echo-target)
;;                       (begin
;;                         (send echo-target 1)
;;                         (goto EchoResponse))))])
;;               (begin
;;                 (send response-target child)
;;                 (goto Always))))))
;;        (goto Always)))))

;;   (define double-response-spawning-actor
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always) (response-target)
;;           (begin
;;             (let ([child
;;                    (spawn
;;                     double-response-spawn
;;                     (Addr Nat)
;;                     (goto DoubleResponse)
;;                     (define-state (DoubleResponse) (echo-target)
;;                       (begin
;;                         (send echo-target 1)
;;                         (send echo-target 1)
;;                         (goto DoubleResponse))))])
;;               (begin
;;                 (send response-target child)
;;                 (goto Always))))))
;;        (goto Always)))))

;;   (define echo-spawn-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> ([obligation r (delayed-fork
;;                                (goto EchoResponse)
;;                                (define-state (EchoResponse)
;;                                  [er -> ([obligation er *]) (goto EchoResponse)]))])
;;                (goto Always)]))
;;       (goto Always)
;;       ((Addr (Addr (Addr Nat))) (addr 0 0)))))

;;   (test-valid-actor? echo-spawning-actor)
;;   (test-valid-actor? double-response-spawning-actor)
;;   (test-valid-instance? echo-spawn-spec)

;;   (test-true "Spawned echo matches dynamic response spec"
;;              (check-conformance/config
;;               (make-single-actor-config echo-spawning-actor)
;;               (make-exclusive-spec echo-spawn-spec)))

;;   (test-false "Spawned double-response actor does not match dynamic response spec"
;;               (check-conformance/config
;;                (make-single-actor-config double-response-spawning-actor)
;;                (make-exclusive-spec echo-spawn-spec)))

;;   ;; Check that spec-fork addresses are added to unobs interface
;;   (define unobs-fork-response-addr1 `(addr (env (Addr Nat)) 1))
;;   (define unobs-fork-response-addr2 `(addr (env Nat) 2))
;;   (define unobs-fork-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always [child-response (Addr (Addr Nat))] [never-use (Addr Nat)]) (m)
;;           (let ([new-child
;;                  (spawn
;;                   child-loc
;;                   (Addr Nat)
;;                   (goto ChildAlways)
;;                   (define-state (ChildAlways) (m)
;;                     (begin
;;                       (send never-use 1)
;;                       (goto ChildAlways))))])
;;             (begin
;;               (send child-response new-child)
;;               (goto Always child-response never-use)))))
;;        (goto Always ,unobs-fork-response-addr1 ,unobs-fork-response-addr2)))))

;;   (define unobs-fork-spec
;;     (term
;;      (((define-state (Always child-response never-use)
;;          [* -> ([obligation child-response
;;                             (delayed-fork (goto ChildAlways)
;;                                           (define-state (ChildAlways)
;;                                             [* -> () (goto ChildAlways)]))])
;;             (goto Always child-response never-use)]))
;;       (goto Always ,unobs-fork-response-addr1 ,unobs-fork-response-addr2)
;;       (Nat (addr 0 0)))))

;;   (test-valid-actor? unobs-fork-actor)
;;   (test-valid-instance? unobs-fork-spec)
;;   (test-false "Forked specified actor in unobs interface can cause non-conformance"
;;     (check-conformance/config
;;      (make-single-actor-config unobs-fork-actor)
;;      (make-exclusive-spec unobs-fork-spec)))

;;   ;;;; Initial spec address must have actor in the implmentation
;;   (define no-matching-address-spec
;;     (term
;;      (((define-state (DoAnything)
;;          [* -> () (goto DoAnything)]))
;;       (goto DoAnything)
;;       (Nat (addr 500 0)))))
;;   (test-valid-instance? no-matching-address-spec)

;;   (test-false "Spec config address must have matching actor in implementation configuration"
;;    (check-conformance/config
;;     (make-single-actor-config static-response-actor)
;;     (make-exclusive-spec no-matching-address-spec)))

;;   (define spawn-and-retain
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always [maybe-child (Union [NoChild] [Child (Addr (Addr Nat))])]) (dest)
;;           (let ([new-child
;;                  (spawn
;;                   echo-spawn
;;                   (Addr Nat)
;;                   (goto EchoResponse)
;;                   (define-state (EchoResponse) (echo-target)
;;                     (begin
;;                       (send echo-target 1)
;;                       (goto EchoResponse))))])
;;             (case maybe-child
;;               [(NoChild)
;;                (begin
;;                  (send dest new-child)
;;                  (goto Always (variant Child new-child)))]
;;               [(Child old-child)
;;                (begin
;;                  (send dest old-child)
;;                  (goto Always (variant Child old-child)))]))))
;;        (goto Always (variant NoChild))))))

;;   (define spawn-and-retain-but-send-new
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always [maybe-child (Union [NoChild] [Child (Addr (Addr Nat))])]) (dest)
;;           (let ([new-child
;;                  (spawn
;;                   echo-spawn
;;                   (Addr Nat)
;;                   (goto EchoResponse)
;;                   (define-state (EchoResponse) (echo-target)
;;                     (begin
;;                       (send echo-target 1)
;;                       (goto EchoResponse))))])
;;             (case maybe-child
;;               [(NoChild)
;;                (begin
;;                  (send dest new-child)
;;                  (goto Always (variant Child new-child)))]
;;               [(Child old-child)
;;                (begin
;;                  (send dest new-child)
;;                  (goto Always (variant Child old-child)))]))))
;;        (goto Always (variant NoChild))))))

;;   (test-valid-actor? spawn-and-retain)
;;   (test-valid-actor? spawn-and-retain-but-send-new)

;;   (test-true "Both an old and new version of spawned echo child match stateless spec"
;;     (check-conformance/config
;;      (make-single-actor-config spawn-and-retain)
;;      (make-exclusive-spec echo-spawn-spec)))

;;   (test-true "Always sending new version of child matches echo-spawn"
;;     (check-conformance/config
;;      (make-single-actor-config spawn-and-retain-but-send-new)
;;      (make-exclusive-spec echo-spawn-spec)))

;;   (define spawn-self-revealing-echo
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always) (response-target)
;;           (begin
;;             (spawn
;;              echo-spawn
;;              (Addr Nat)
;;              (goto Init response-target)
;;              (define-state (Init [self-target (Addr (Addr (Addr Nat)))]) (response-target)
;;                (goto Init self-target)
;;                [(timeout 0)
;;                 (begin
;;                   (send self-target self)
;;                   (goto EchoResponse))])
;;              (define-state (EchoResponse) (echo-target)
;;                (begin
;;                  (send echo-target 1)
;;                  (goto EchoResponse))))
;;             (goto Always))))
;;        (goto Always)))))

;;   (define child-self-reveal-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> ([fork (goto Init r)
;;                       (define-state (Init r)
;;                         [free -> ([obligation r self]) (goto EchoResponse)])
;;                       (define-state (EchoResponse)
;;                         [er -> ([obligation er *]) (goto EchoResponse)])])
;;             (goto Always)]))
;;       (goto Always)
;;       ((Addr (Addr (Addr Nat))) (addr 0 0)))))

;;   (test-valid-actor? spawn-self-revealing-echo)
;;   (test-valid-instance? child-self-reveal-spec)
;;   (test-true "Spawned child can reveal self"
;;     (check-conformance/config
;;      (make-single-actor-config spawn-self-revealing-echo)
;;      (make-exclusive-spec child-self-reveal-spec)))

;;   ;;;; Blur Tests

;;   (define send-to-blurred-internal-actor-and-response
;;     ;; Third time through, send to that actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [static-output (Addr ,static-response-type)]
;;                               [saved-internal (Union [None]
;;                                                      [First (Addr (Addr ,static-response-type))]
;;                                                      [Second (Addr (Addr ,static-response-type))])]) (m)
;;           (let ([new-child
;;                  (spawn child-loc
;;                         (Addr ,static-response-type)
;;                         (goto InternalAlways)
;;                         (define-state (InternalAlways) (m)
;;                           (begin
;;                             (send m (variant Ack 1))
;;                           (goto InternalAlways))))])
;;             (begin
;;               (send static-output (variant Ack 0))
;;               (case saved-internal
;;                 [(None) (goto Always static-output (variant First new-child))]
;;                 [(First saved) (goto Always static-output (variant Second saved))]
;;                 [(Second saved)
;;                  (begin
;;                    ;; at this point, "saved" should have already been blurred out
;;                    (send saved static-output)
;;                    (goto Always static-output (variant Second saved)))])))))
;;        (goto Always ,static-response-address (variant None))))))

;;   (test-valid-actor? send-to-blurred-internal-actor-and-response)

;;   (test-false "Sending precise address to blurred sending actor causes non-conformance"
;;     (check-conformance/config
;;      (make-single-actor-config send-to-blurred-internal-actor-and-response)
;;      (make-exclusive-spec static-response-spec)))

;;   (define send-to-blurred-internal-actor
;;     ;; Third time through, send to that actor
;;     (term
;;      ((Nat (addr 0 0))
;;       (((define-state (Always [static-output (Addr ,static-response-type)]
;;                               [saved-internal (Union [None]
;;                                                      [First (Addr (Addr ,static-response-type))]
;;                                                      [Second (Addr (Addr ,static-response-type))])]) (m)
;;           (let ([new-child
;;                  (spawn child-loc
;;                         (Addr ,static-response-type)
;;                         (goto InternalAlways)
;;                         (define-state (InternalAlways) (m)
;;                           (begin
;;                             (send m (variant Ack 1))
;;                           (goto InternalAlways))))])
;;             (case saved-internal
;;               [(None) (goto Always static-output (variant First new-child))]
;;               [(First saved) (goto Always static-output (variant Second saved))]
;;               [(Second saved)
;;                (begin
;;                  ;; at this point, "saved" should have already been blurred out
;;                  (send saved static-output)
;;                  (goto Always static-output (variant Second saved)))]))))
;;        (goto Always ,static-response-address (variant None))))))

;;   (define never-send-spec
;;     (term
;;      (((define-state (Always r)
;;          [* -> () (goto Always r)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))
;;   (define send-whenever-spec
;;     (term
;;      (((define-state (Always r)
;;          [* -> () (goto Always r)]
;;          [free -> ([obligation r *]) (goto Always r)]))
;;       (goto Always ,static-response-address)
;;       (Nat (addr 0 0)))))

;;   (test-valid-actor? send-to-blurred-internal-actor)
;;   (test-valid-instance? send-whenever-spec)
;;   (test-valid-instance? never-send-spec)
;;   (test-true "Sending message to blurred-internal matches send-whenever spec"
;;     (check-conformance/config
;;      (make-single-actor-config send-to-blurred-internal-actor)
;;      (make-exclusive-spec send-whenever-spec)))
;;   (test-false "Sending message to blurred-internal does not match never-send spec"
;;     (check-conformance/config
;;      (make-single-actor-config send-to-blurred-internal-actor)
;;      (make-exclusive-spec never-send-spec)))

;;   (define self-send-responder-spawner
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always) (dest)
;;           (begin
;;             (spawn child-loc
;;                    (Addr Nat)
;;                    (begin
;;                      (send self 1)
;;                      (goto AboutToSend dest))
;;                    (define-state (AboutToSend [dest (Addr Nat)]) (m)
;;                      (begin
;;                        (send dest 1)
;;                        (goto Done)))
;;                    (define-state (Done) (m) (goto Done)))
;;             (goto Always))))
;;        (goto Always)))))

;;   (test-valid-actor? self-send-responder-spawner)
;;   (test-true "Child can wait at least one handler-cycle before sending to destination"
;;     (check-conformance/config
;;      (make-single-actor-config self-send-responder-spawner)
;;      (make-exclusive-spec request-response-spec)))

;;   ;; Actor that creates a worker to handle each new request, where the worker then sends the result
;;   ;; back to another statically-known actor for sending back to the client
;;   (define forwarding-type (term (Record [result Nat] [dest (Addr Nat)])))
;;   (define (make-down-and-back-server child-behavior)
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always [forwarding-server (Addr ,forwarding-type)]) (dest)
;;           (begin
;;             (spawn child-loc ,@child-behavior)
;;             (goto Always forwarding-server))))
;;        (goto Always (addr 1 0))))))

;;   (define timeout-forwarding-child
;;     (term
;;      (Nat
;;       (goto AboutToSend forwarding-server)
;;       (define-state (AboutToSend [forwarding-server (Addr ,forwarding-type)]) (dummy)
;;         (goto AboutToSend forwarding-server)
;;         [(timeout 0)
;;          (begin
;;            (send forwarding-server (record [result 1] [dest dest]))
;;            (goto Done))])
;;       (define-state (Done) (dummy) (goto Done)))))

;;   (define self-send-forwarding-child
;;     (term
;;      (Nat
;;       (begin
;;         (send self 1)
;;         (goto AboutToSend forwarding-server))
;;       (define-state (AboutToSend [forwarding-server (Addr ,forwarding-type)]) (trigger)
;;         (begin
;;           (send forwarding-server (record [result 1] [dest dest]))
;;           (goto Done)))
;;       (define-state (Done) (dummy) (goto Done)))))

;;   (define forwarding-server
;;     (term
;;      (((Record [result Nat] [dest (Addr Nat)]) (addr 1 0))
;;       (((define-state (ServerAlways) (rec)
;;           (begin
;;             (send (: rec dest) (: rec result))
;;             (goto ServerAlways))))
;;        (goto ServerAlways)))))

;;   (test-valid-actor? (make-down-and-back-server timeout-forwarding-child))
;;   (test-valid-actor? forwarding-server)

;;   (test-true "Down-and-back server with timeout child fulfills the dynamic request/response spec"
;;     (check-conformance/config
;;      (make-empty-queues-config (list (make-down-and-back-server timeout-forwarding-child))
;;                                (list forwarding-server))
;;      (make-exclusive-spec request-response-spec)))

;;   (test-true "Down-and-back server with self-send child fulfills the dynamic request/response spec"
;;     (check-conformance/config
;;      (make-empty-queues-config (list (make-down-and-back-server self-send-forwarding-child))
;;                                (list forwarding-server))
;;      (make-exclusive-spec request-response-spec)))

;;   (define create-later-send-children-actor
;;     (term
;;      (((Addr (Addr Nat)) (addr 1 0))
;;       (((define-state (Always [r (Addr Nat)]) (other-dest)
;;           (begin
;;             (send other-dest
;;                   (spawn child-loc Nat
;;                          (goto Child1)
;;                          (define-state (Child1) (dummy)
;;                            (goto Child2))
;;                          (define-state (Child2) (dummy)
;;                            (begin
;;                              (send r (variant Ack 1))
;;                              (goto Child2)))))
;;             (goto Always r))))
;;        (goto Always ,static-response-address)))))

;;   (test-valid-actor? create-later-send-children-actor)
;;   (test-false "Child that sends response in second state does not match never-send"
;;     ;; tests that all reachable states of a blurred child are executed
;;     (check-conformance/config
;;      (make-single-actor-config create-later-send-children-actor)
;;      (make-exclusive-spec never-send-spec)))

;;   ;; step 1: spawn the forwarder; save it
;;   ;; step 2: spawn the new agent (spec follows it)
;;   ;; step 3: new agent uses forwarder to fulfill its dynamic request/response (can't do static yet)
;;   (define conflicts-only-test-actor
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always [maybe-forwarder (Union [None] [Forwarder (Addr (Addr Nat))])]) (dest)
;;           (let ([forwarder
;;                  (case maybe-forwarder
;;                    [(None)
;;                     ;; The forwarder actor takes any address it's given and sends a message to it
;;                     (spawn forwarder-loc (Addr Nat)
;;                                   (goto Forwarding)
;;                                   (define-state (Forwarding) (r)
;;                                     (begin
;;                                       (send r 1)
;;                                       (goto Forwarding))))]
;;                    [(Forwarder the-addr) the-addr])])
;;             (begin
;;               (send dest
;;                     ;; the per-request child is sent back to the client. When the client sends a
;;                     ;; message to the child, the message is sent to the forwarder, who sends a message
;;                     ;; on it
;;                     (spawn surfaced-loc
;;                            (Addr Nat)
;;                            (goto Responding)
;;                            (define-state (Responding) (r)
;;                              (begin
;;                                (send forwarder r)
;;                                (goto Responding)))))
;;               (goto Always (variant Forwarder forwarder))))))
;;        (goto Always (variant None))))))

;;   (test-true "Only spawned actors with conflicts are blurred out"
;;     (check-conformance/config
;;      (make-single-actor-config conflicts-only-test-actor)
;;      (make-exclusive-spec echo-spawn-spec)))

;;   ;; Master creates workers, each worker reveals itself after timeout, sends response to next message
;;   ;; and dies. The worker is stateful, so this models an error I found in the authN example
;;   (define worker-spawner
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (MasterLoop) (child-dest)
;;          (begin
;;            (spawn child-loc
;;                   (Addr Nat)
;;                   (goto Init)
;;                   (define-state (Init) (m)
;;                     (goto Init)
;;                     [(timeout 0)
;;                      (begin
;;                        (send child-dest self)
;;                        (goto Running))])
;;                   (define-state (Running) (m)
;;                     (begin
;;                       (send m 0)
;;                       (goto Done)))
;;                   (define-state (Done) (m)
;;                     (goto Done)))
;;            (goto MasterLoop))))
;;        (goto MasterLoop)))))
;;   (define worker-spawner-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> ([obligation r (delayed-fork
;;                                (goto Running)
;;                                (define-state (Running)
;;                                  [nr -> ([obligation nr *]) (goto Done)])
;;                                (define-state (Done)
;;                                  [nr -> () (goto Done)]))])
;;             (goto Always)]))
;;       (goto Always)
;;       ((Addr (Addr (Addr Nat))) (addr 0 0)))))

;;   (test-valid-actor? worker-spawner)
;;   (test-valid-instance? worker-spawner-spec)
;;   (test-true "Stateful generated worker satisfies spec"
;;     (check-conformance/config
;;      (make-single-actor-config worker-spawner)
;;      (make-exclusive-spec worker-spawner-spec)))

;;   ;;;; Type Coercions

;;   (define ping-coercion-spawner
;;     (term
;;      (((Addr (Addr (Union [Ping (Addr (Union [Pong]))]))) (addr 0 0))
;;       (((define-state (Always) (dest)
;;           (begin
;;             (send dest
;;                  (spawn 1
;;                         (Union [Ping (Addr (Union [Pong]))] [InternalOnly])
;;                         (goto Ready)
;;                         (define-state (Ready) (msg)
;;                           (begin
;;                             (case msg
;;                               [(Ping response-dest) (send response-dest (variant Pong))]
;;                               [(InternalOnly) (variant Pong)])
;;                             (goto Ready)))))
;;             (goto Always))))
;;        (goto Always)))))

;;   (define ping-coercion-spawner-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> ([obligation r (delayed-fork
;;                                (goto Ready)
;;                                (define-state (Ready)
;;                                  [(variant Ping r) -> ([obligation r (variant Pong)]) (goto Ready)]))])
;;             (goto Always)]))
;;       (goto Always)
;;       ((Addr (Addr (Union [Ping (Addr (Union [Pong]))]))) (addr 0 0)))))

;;   ;; make sure that
;;   (test-true "Exposed addresses only expose types according to the type of the address they were exposed through"
;;     (check-conformance/config
;;      (make-single-actor-config ping-coercion-spawner)
;;      (make-exclusive-spec ping-coercion-spawner-spec)))

;;   ;;;; Widening

;;   ;; A counterexample that shows why widening with a spawn that didn't exist before is unsound: On
;;   ;; receiving an external message, the main actor spawns a child. The child, on timeout, sends a
;;   ;; message back to its parent, and the parent sends a message to fulfill the obligation. If the
;;   ;; external message is never sent, the obligation is never fulfilled.
;;   (define new-spawn-impl-config
;;     (term (([(addr 1 0)
;;              (((define-state (Start [target (Addr Nat)]) (m)
;;                  (case m
;;                    [(FromEnv)
;;                     (let ([parent (addr 1 0)])
;;                       (begin
;;                         (spawn child-loc
;;                                (Addr (Union [FromChild]))
;;                                (goto Waiting)
;;                                (define-state (Waiting) (m)
;;                                  (goto Waiting)
;;                                  [(timeout 5)
;;                                   (begin
;;                                     (send parent (variant FromChild))
;;                                     (goto Done))])
;;                                (define-state (Done) (m) (goto Done)))
;;                         (goto Start target)))]
;;                    [(FromChild)
;;                     (begin
;;                       (send target 1)
;;                       (goto ParentDone))]))
;;                (define-state (ParentDone) (m) (goto ParentDone)))
;;               (goto Start (addr (env Nat) 2)))])
;;            ()
;;            (((Union [FromEnv]) (addr 1 0)))
;;            ((Nat (addr (env Nat) 2))))))
;;   ;; Spec with no real transitions, but a commitment on address 2
;;   (define new-spawn-spec-config
;;     (term ((((Union [FromEnv]) (addr 1 0)))
;;            ()
;;            (goto Always)
;;            ((define-state (Always)
;;               [* -> () (goto Always)]))
;;            (((addr (env Nat) 2) *)))))
;;   (check-true (redex-match? csa-eval i new-spawn-impl-config))
;;   (check-true (redex-match? aps-eval s new-spawn-spec-config))
;;   (test-false "Widen new-spawn counterexample"
;;     (check-conformance/config new-spawn-impl-config new-spawn-spec-config))

;;   ;;;; Loop Spawns

;;   (define loop-spawn-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (Always) (response-target)
;;           (begin
;;             (for/fold ([x 0])
;;                       ([y (list 1)])
;;               (spawn child
;;                      Nat
;;                      (goto ChildAlways)
;;                      (define-state (ChildAlways) (x)
;;                        (goto ChildAlways)
;;                        ([timeout 0]
;;                         (begin
;;                           (send response-target 0)
;;                           (goto ChildAlways))))))
;;             (goto Always))))
;;        (goto Always)))))

;;   (define dynamic-never-respond-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> () (goto Always)]))
;;       (goto Always)
;;       ((Addr Nat) (addr 0 0)))))

;;   (test-valid-actor? loop-spawn-actor)
;;   (test-valid-instance? dynamic-never-respond-spec)
;;   (test-false "Loop spawn actor sends too many responses"
;;     (check-conformance/config
;;      (make-single-actor-config loop-spawn-actor)
;;      (make-exclusive-spec dynamic-never-respond-spec)))

;;   ;;;; Test for dead-observable optimization (this had a bug at one point)
;;   (define send-in-next-state-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (NoAddr) (response-target)
;;           (goto HaveAddr response-target))
;;         (define-state (HaveAddr [response-target (Addr Nat)]) (x)
;;           (begin
;;             (send response-target 0)
;;             (goto Done))
;;           [(timeout 0)
;;            (begin
;;              (send response-target 0)
;;              (goto Done))])
;;         (define-state (Done) (x) (goto Done)))
;;        (goto NoAddr)))))

;;   (test-valid-actor? send-in-next-state-actor)
;;   (test-false "Dead-observable optimization does not kick in if address still exists"
;;     (check-conformance/config
;;      (make-single-actor-config send-in-next-state-actor)
;;      (make-exclusive-spec dynamic-never-respond-spec)))

;;   ;;;; Test for external addresses escaping to environment
;;   (define escape-actor
;;     (term
;;      (((Record [a (Addr Nat)] [b (Addr (Addr Nat))]) (addr 0 0))
;;       (((define-state (Always) (m)
;;            (begin
;;              (send (: m b) (: m a))
;;              (goto Always))))
;;         (goto Always)))))

;;   (define dynamic-never-respond-spec-escape
;;     (term
;;      (((define-state (Always)
;;          [* -> () (goto Always)]))
;;       (goto Always)
;;       ((Record [a (Addr Nat)] [b (Addr (Addr Nat))]) (addr 0 0)))))
;;   (define obs-escape-spec1
;;     (term (((define-state (Always)
;;               [(record [a a] [b b]) -> () (goto Always)]))
;;            (goto Always)
;;            ((Record [a (Addr Nat)] [b (Addr (Addr Nat))]) (addr 0 0)))))
;;   (define obs-escape-spec2
;;     (term (((define-state (Always)
;;               [(record [a a] [b b]) -> ([obligation b *]) (goto Always)]))
;;            (goto Always)
;;            ((Record [a (Addr Nat)] [b (Addr (Addr Nat))]) (addr 0 0)))))

;;   (test-valid-actor? escape-actor)
;;   (test-valid-instance? dynamic-never-respond-spec-escape)
;;   (test-valid-instance? obs-escape-spec1)
;;   (test-valid-instance? obs-escape-spec2)
;;   (test-true "Sending unobs external addr to environment is okay"
;;     (check-conformance/config
;;      (make-single-actor-config escape-actor)
;;      (make-exclusive-spec dynamic-never-respond-spec-escape)))
;;   (test-exn "Sending extrnal addr to environment is not allowed (1)"
;;     (lambda (exn) #t)
;;     (lambda ()
;;       (check-conformance/config
;;        (make-single-actor-config escape-actor)
;;        (make-exclusive-spec obs-escape-spec1))))
;;   (test-exn "Sending external addr to environment is not allowed (2)"
;;     (lambda (exn) #t)
;;     (lambda ()
;;       (check-conformance/config
;;        (make-single-actor-config escape-actor)
;;        (make-exclusive-spec obs-escape-spec2))))

;;   ;;;; Fairness for timeouts/externals

;;   ;; The old fairness constraint said that if there were no internal messages for an actor, that
;;   ;; actor's timeout would have to eventually run. However, that's not necessarily true: we could have
;;   ;; an infinite stream of messages from the environment that prevent the timeout from
;;   ;; running. Fairness just says that the actor is eventually run at some point if it has work to do.
;;   ;;
;;   ;; As an example, this actor will only send a response to its request if its timeout fires, and the
;;   ;; spec says that it must respond to its first request. This test should fail because of the
;;   ;; scenario described above.
;;   (define send-after-timeout-actor
;;     (term
;;      (((Addr Nat) (addr 0 0))
;;       (((define-state (WaitingForRequest) (m)
;;           (goto AboutToSend m))
;;         (define-state (AboutToSend [dest (Addr Nat)]) (m)
;;           (goto AboutToSend dest)
;;           [(timeout 5)
;;            (begin
;;              (send dest 1)
;;              (goto Done))])
;;         (define-state (Done) (m) (goto Done)))
;;        (goto WaitingForRequest)))))

;;   (define reply-to-first-request-spec
;;     (term
;;      (((define-state (FirstState)
;;          [r -> ([obligation r *]) (goto Done)])
;;        (define-state (Done)
;;          [* -> () (goto Done)]))
;;       (goto FirstState)
;;       ((Addr Nat) (addr 0 0)))))

;;   (test-valid-actor? send-after-timeout-actor)
;;   (test-valid-instance? reply-to-first-request-spec)
;;   (test-false "External messages can prevent timeout from firing"
;;     (check-conformance/config
;;      (make-single-actor-config send-after-timeout-actor)
;;      (make-exclusive-spec reply-to-first-request-spec)))

;;   ;;;; New "self" obligation on every step, never fulfilled

;;   (define never-respond-with-self-actor
;;     (term
;;      (((Addr (Addr Nat)) (addr 0 0))
;;       (((define-state (Always) (r) (goto Always)))
;;        (goto Always)))))

;;   (define new-self-obligations-spec
;;     (term
;;      (((define-state (Always)
;;          [r -> ([obligation r self]) (goto Always)]))
;;       (goto Always)
;;       ((Addr (Addr Nat)) (addr 0 0)))))

;;   (test-valid-actor? never-respond-with-self-actor)
;;   (test-valid-instance? new-self-obligations-spec)
;;   (test-false "New self obligation on every message, never fulfilled"
;;     (check-conformance/config
;;      (make-single-actor-config never-respond-with-self-actor)
;;      (make-exclusive-spec new-self-obligations-spec)))

;;   ;;;; "Free" forks inside for loops should not cause infinite loop
;;   (define forks-in-for-loop-actor
;;     (term
;;      (((Addr (Addr (Addr Nat))) (addr 0 0))
;;       (((define-state (Always) (m) (goto Always)
;;           [(timeout 0)
;;            (begin
;;              (for/fold ([dummy 0])
;;                        ([item (list 1 2 3)])
;;                (begin
;;                  (send (addr (env (Addr (Addr Nat))) 1)
;;                        (spawn this-loc (Addr Nat)
;;                               (goto A)
;;                               (define-state (A) (r)
;;                                 (begin
;;                                   (send r 1)
;;                                   (goto A)))))
;;                  0))
;;             (goto Always))]))
;;        (goto Always)))))

;;   (define forks-in-loop-spec
;;     (term
;;      (((define-state (Always r)
;;          [* -> () (goto Always r)]
;;          [free -> ([obligation r (delayed-fork
;;                                    (goto A)
;;                                    (define-state (A)
;;                                      [r2 -> ([obligation r2 *]) (goto A)]))])
;;                 (goto Always r)]))
;;       (goto Always (addr (env (Addr (Addr Nat))) 1))
;;       ((Addr (Addr (Addr Nat))) (addr 0 0)))))

;;   (test-valid-actor? forks-in-for-loop-actor)
;;   (test-valid-instance? forks-in-loop-spec)
;;   (test-true "Forks in for loops are okay"
;;     (check-conformance/config
;;      (make-single-actor-config forks-in-for-loop-actor)
;;      (make-exclusive-spec forks-in-loop-spec))))
