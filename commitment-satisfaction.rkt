#lang racket

;; Defines the commitment-satisfaction-check algorithm

(provide
 partition-by-satisfaction)

(require
 data/queue
 "aps-abstract.rkt"
 "csa-abstract.rkt"
 "checker-data-structures.rkt"
 "graph.rkt"
 "hash-helpers.rkt"
 "queue-helpers.rkt"
 "set-helpers.rkt")

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt"))

;; ---------------------------------------------------------------------------------------------------
;; Data Structures for Commitment Satisfaction

;; OutgoingStepsDict : (Hash ConfigPair (MutableSetof FullStep)
;;
;; For each config pair, gives the set of outgoing steps from that pair, where each step has an
;; impl-step, a matching spec-step, and all the derivatives of that pair. Intuitively, this is the
;; IncomingStepsDict in the reverse direction - we construct it because we want to traverse forward
;; edges more efficiently that doing backwards lookups through an IncomingSpecStepsDict.

;; A full-step represents a possible implementation step and matching specification step from a given
;; configuration, and also contains all mapped-derivatives of the pair of destination configurations
;; of those steps.
;;
;; derivatives : (MutableSetof mapped-derivative)
(struct full-step (impl-step spec-step derivatives)
  #:transparent
  ;; NOTE: implementing custom equality here to work around Racket bug
  ;; http://bugs.racket-lang.org/query/?cmd=view&pr=15342
  #:methods gen:equal+hash
  [(define (equal-proc s1 s2 rec?)
     (and (rec? (full-step-impl-step s1)
                (full-step-impl-step s2))
          (rec? (full-step-spec-step s1)
                (full-step-spec-step s2))
          (rec? (list->set (set->list (full-step-derivatives s1)))
                (list->set (set->list (full-step-derivatives s2))))))
   (define (hash-proc s rec)
     (+ (rec (full-step-impl-step s))
        (rec (full-step-spec-step s))
        (rec (list->set (set->list (full-step-derivatives s))))))
   (define (hash2-proc s rec)
     (+ (rec (full-step-impl-step s))
        (rec (full-step-spec-step s))
        (rec (list->set (set->list (full-step-derivatives s))))))])

;; A mapped-derivative represents a possible sbc-derivative of some impl-step/spec-step pair. It
;; contains the new configuration pair itself as well as a hash table from addresses to addresses
;; representing the address-substitution done during the canonicalization phase.
(struct mapped-derivative (config-pair address-map) #:transparent)

;; ---------------------------------------------------------------------------------------------------
;; Algorithm

;; (Setof config-pair) IncomingDict RelatedSpecStepsDict
;; -> (List (Setof related-pair) (Setof related-pair)
;;
;; Partitions simulation pairs into the set in which every fair execution of the impl-config satisfies
;; all commitments in the spec-config, and the set in which that is unable to be determined (the set
;; of satisfying pairs is the first element of the returned list).
;;
;; Preconditions:
;;
;; * simulation-pairs should consist only of pairs in the conformance simulation, with incoming and
;; related-spec-steps acting as a proof of their membership, similar to the preconditions for
;; prune-unsupported.
;;
;; * the address-map in each entry in incoming should give the mapping such that one of the split and
;; assimilated derivatives of the entry's result-config can be canonicalized to the entry's key by
;; using the mapping as the rename-map for the external addresses.
(define (partition-by-satisfaction simulation-pairs incoming related-spec-steps)
  ;; Sets of pairs of configuration-pairs and commitments (address/pattern pairs), where the
  ;; implementation configurations in the first set always satisfy their associated commitment, while
  ;; the algorithm was not able to determine satisfaction for those in the second (so we
  ;; conservatively say they were unsatisfied). These two sets should be disjoint.
  (define satisfied-config-commitments (mutable-set))
  (define unsatisfied-config-commitments (mutable-set))

  (define outgoing (build-outgoing-dict incoming related-spec-steps))
  (define enabled-necessary-actions (catalog-enabled-necessary-actions outgoing))

  (define-values (satisfying-pairs unsatisfying-pairs)
    (for/fold ([satisfying-pairs (set)]
               [unsatisfying-pairs (set)])
              ([pair simulation-pairs])
      (define spec-config (config-pair-spec-config pair))
      (define all-commitments-satisfied?
        (and
         ;; many-of abstract commitments can never be satisfied
         (null? (aps#-config-many-of-commitments spec-config))
         (for/and ([commitment (aps#-config-singleton-commitments spec-config)])
           ;; Within a configuration pair, each commitment is checked individually. The checking
           ;; process by necessity checks other commitments as well, so we add all of those
           ;; results to satisfied-config-commitments/unsatisfied-config-commitments so we may
           ;; reuse the results later rather than rebuilding and reanalyzing the graph every time.
           (define configs-commitment-pair (list pair commitment))
           (cond
             [(set-member?   satisfied-config-commitments configs-commitment-pair) #t]
             [(set-member? unsatisfied-config-commitments configs-commitment-pair) #f]
             [else
              (match-define (list new-satisfied-config-commitments new-unsatisfied-config-commitments)
                (find-sat/unsat-pairs configs-commitment-pair
                                      incoming
                                      outgoing
                                      related-spec-steps
                                      enabled-necessary-actions))
              (set-union! satisfied-config-commitments   new-satisfied-config-commitments)
              (set-union! unsatisfied-config-commitments new-unsatisfied-config-commitments)
              (set-member? new-satisfied-config-commitments configs-commitment-pair)]))))
     (if all-commitments-satisfied?
         (values (set-add satisfying-pairs pair) unsatisfying-pairs)
         (values satisfying-pairs (set-add unsatisfying-pairs pair)))))

  (list satisfying-pairs unsatisfying-pairs))

(module+ test
  (define (make-com-sat-ext-address number) `(obs-ext ,number))
  (define (sat-test-node name commitment-address-number commitment-patterns)
    (define mult-patterns (map (lambda (pat) `(single (variant ,pat))) commitment-patterns))
    (config-pair name
                 `(UNKNOWN
                   ()
                   (goto A)
                   ()
                   ([,(make-com-sat-ext-address commitment-address-number) ,@mult-patterns]))))
  (define (sat-other-derivative-node name)
    (config-pair name `(UNKNOWN () (goto A) () ())))
  (define (sat-impl-step trigger) (impl-step trigger #f null null #f))
  (define (letters->sat-list addr sat-letters)
    (map (lambda (letter) `((obs-ext ,addr) (variant ,letter)))
         sat-letters))
  (define (sat-spec-step com-addr-number . satisfied-commitment-letters)
    (spec-step #f #f (letters->sat-list com-addr-number satisfied-commitment-letters)))
  (define (sat-alt-spec-step com-addr-number . satisfied-commitment-letters)
    (spec-step #t #f (letters->sat-list com-addr-number satisfied-commitment-letters)))

  ;; These are the structures used for most of the tests for commitment satisfaction
  (define a-node (sat-test-node 'A 1 (list 'W 'X 'Y 'Z)))
  (define b-node (sat-test-node 'B 1 (list 'X 'Z)))
  (define c-node (sat-test-node 'C 1 (list 'X 'Z)))
  (define d-node (sat-test-node 'D 1 (list 'X 'Z)))
  (define e-node (sat-test-node 'E 1 (list 'Z)))
  (define f-node (sat-test-node 'F 1 (list 'Z)))
  (define g-node (sat-test-node 'G 2 (list 'W 'Z)))
  (define h-node (sat-test-node 'H 2 (list 'W 'Z)))
  (define i-node (sat-test-node 'I 3 (list 'X 'Z)))
  (define j-node (sat-test-node 'J 3 (list 'X 'Z)))
  (define k-node (sat-test-node 'K 4 (list 'X 'Z)))
  (define l-node (sat-test-node 'L 5 (list 'W 'Z)))
  (define m-node (sat-other-derivative-node 'M))

  ;; en stands for "enabled necessary", others use 'ue' for enabled unnecessary
  (define sat-en-trigger1 `(timeout/empty-queue (init-addr 1)))
  (define sat-en-trigger2 `(internal-receive (init-addr 2) (* Nat) single))
  (define sat-en-trigger3 `(internal-receive (init-addr 3) (* Nat) single))
  (define sat-en-trigger4 `(internal-receive (init-addr 4) (* Nat) single))

  (define sat-eu-trigger1 `(external-receive (init-addr 1) (* Nat)))

  (define ag-impl-step (sat-impl-step sat-en-trigger1))
  (define ai-impl-step (sat-impl-step sat-en-trigger2))
  (define akm-impl-step (sat-impl-step sat-en-trigger3))
  (define al-impl-step (sat-impl-step sat-en-trigger4))
  (define ba-impl-step (sat-impl-step sat-en-trigger1))
  (define b-cd-impl-step (sat-impl-step sat-en-trigger2))
  (define b-ef-impl-step (sat-impl-step sat-en-trigger3))
  (define gh-impl-step (sat-impl-step sat-en-trigger1))
  (define hg-impl-step (sat-impl-step sat-en-trigger1))
  (define ia-impl-step (sat-impl-step sat-en-trigger2))
  (define ij-impl-step (sat-impl-step sat-en-trigger1))
  (define ja-impl-step (sat-impl-step sat-en-trigger2))
  (define ji-impl-step (sat-impl-step sat-en-trigger1))
  (define la-impl-step (sat-impl-step sat-eu-trigger1))

  (define ag-spec-step (sat-spec-step 1 'X 'Y))
  (define ai-spec-step (sat-spec-step 1 'W 'Y))
  (define akm-spec-step (sat-spec-step 1 'W 'Y))
  (define al-spec-step (sat-spec-step 1 'X 'Y))
  (define ba-spec-step (sat-spec-step 1))
  (define bc-spec-step (sat-spec-step 1))
  (define bd-spec-step (sat-alt-spec-step 1))
  (define be-spec-step (sat-spec-step 1 'X))
  (define bf-spec-step (sat-alt-spec-step 1 'X))
  (define gh-spec-step (sat-spec-step 2))
  (define hg-spec-step (sat-spec-step 2))
  (define ia-spec-step (sat-spec-step 3 'X))
  (define ij-spec-step (sat-spec-step 3))
  (define ja-spec-step (sat-spec-step 3 'X))
  (define ji-spec-step (sat-spec-step 3))
  (define la-spec-step (sat-spec-step 5))

  (define (make-com-sat-map old new)
    (list (list old new)))

  (define com-sat-incoming
    (mutable-hash
     [a-node (mutable-set (list b-node ba-impl-step ba-spec-step (make-com-sat-map 1 1))
                          (list i-node ia-impl-step ia-spec-step (make-com-sat-map 3 1))
                          (list j-node ja-impl-step ja-spec-step (make-com-sat-map 3 1))
                          (list l-node la-impl-step la-spec-step (make-com-sat-map 5 1)))]
     [b-node (mutable-set)]
     [c-node (mutable-set (list b-node b-cd-impl-step bc-spec-step (make-com-sat-map 1 1)))]
     [d-node (mutable-set (list b-node b-cd-impl-step bd-spec-step (make-com-sat-map 1 1)))]
     [e-node (mutable-set (list b-node b-ef-impl-step be-spec-step (make-com-sat-map 1 1)))]
     [f-node (mutable-set (list b-node b-ef-impl-step bf-spec-step (make-com-sat-map 1 1)))]
     [g-node (mutable-set (list a-node ag-impl-step ag-spec-step (make-com-sat-map 1 2))
                          (list h-node hg-impl-step hg-spec-step (make-com-sat-map 2 2)))]
     [h-node (mutable-set (list g-node gh-impl-step gh-spec-step (make-com-sat-map 2 2)))]
     [i-node (mutable-set (list a-node ai-impl-step ai-spec-step (make-com-sat-map 1 3))
                          (list j-node ji-impl-step ji-spec-step (make-com-sat-map 3 3)))]
     [j-node (mutable-set (list i-node ij-impl-step ij-spec-step (make-com-sat-map 3 3)))]
     [k-node (mutable-set (list a-node akm-impl-step akm-spec-step (make-com-sat-map 1 4)))]
     [m-node (mutable-set (list a-node akm-impl-step akm-spec-step null))]
     [l-node (mutable-set (list a-node al-impl-step al-spec-step (make-com-sat-map 1 5)))]))

  (define com-sat-related-steps
    (mutable-hash
     [(list a-node ag-impl-step) (mutable-set ag-spec-step)]
     [(list a-node ai-impl-step) (mutable-set ai-spec-step)]
     [(list a-node akm-impl-step) (mutable-set akm-spec-step)]
     [(list a-node al-impl-step) (mutable-set al-spec-step)]
     [(list b-node ba-impl-step) (mutable-set ba-spec-step)]
     [(list b-node b-cd-impl-step) (mutable-set bc-spec-step bd-spec-step)]
     [(list b-node b-ef-impl-step) (mutable-set be-spec-step bf-spec-step)]
     [(list g-node gh-impl-step) (mutable-set gh-spec-step)]
     [(list h-node hg-impl-step) (mutable-set hg-spec-step)]
     [(list i-node ia-impl-step) (mutable-set ia-spec-step)]
     [(list i-node ij-impl-step) (mutable-set ij-spec-step)]
     [(list j-node ja-impl-step) (mutable-set ja-spec-step)]
     [(list j-node ji-impl-step) (mutable-set ji-spec-step)]
     [(list l-node la-impl-step) (mutable-set la-spec-step)]))

  (define (single-match-step i-step s-step derivative addr-map)
    (full-step
     i-step
     s-step
     (mutable-set (mapped-derivative derivative addr-map))))

  (define com-sat-outgoing
    (mutable-hash
     [a-node
      (mutable-set
       (single-match-step ag-impl-step ag-spec-step g-node (make-com-sat-map 1 2))
       (single-match-step ai-impl-step ai-spec-step i-node (make-com-sat-map 1 3))
       (full-step
        akm-impl-step
        akm-spec-step
        (mutable-set
         (mapped-derivative k-node (make-com-sat-map 1 4))
         (mapped-derivative m-node null)))
       (single-match-step al-impl-step al-spec-step l-node (make-com-sat-map 1 5)))]
     [b-node
      (mutable-set
       (single-match-step ba-impl-step ba-spec-step a-node (make-com-sat-map 1 1))
       (full-step
        b-cd-impl-step
        bc-spec-step
        (mutable-set (mapped-derivative c-node (make-com-sat-map 1 1))))
       (full-step
        b-cd-impl-step
        bd-spec-step
        (mutable-set (mapped-derivative d-node (make-com-sat-map 1 1))))
       (full-step
        b-ef-impl-step
        be-spec-step
        (mutable-set (mapped-derivative e-node (make-com-sat-map 1 1))))
       (full-step
        b-ef-impl-step
        bf-spec-step
        (mutable-set (mapped-derivative f-node (make-com-sat-map 1 1)))))]
     [c-node (mutable-set)]
     [d-node (mutable-set)]
     [e-node (mutable-set)]
     [f-node (mutable-set)]
     [g-node
      (mutable-set (single-match-step gh-impl-step gh-spec-step h-node (make-com-sat-map 2 2)))]
     [h-node
      (mutable-set (single-match-step hg-impl-step hg-spec-step g-node (make-com-sat-map 2 2)))]
     [i-node
      (mutable-set (single-match-step ia-impl-step ia-spec-step a-node (make-com-sat-map 3 1))
                   (single-match-step ij-impl-step ij-spec-step j-node (make-com-sat-map 3 3)))]
     [j-node
      (mutable-set (single-match-step ja-impl-step ja-spec-step a-node (make-com-sat-map 3 1))
                   (single-match-step ji-impl-step ji-spec-step i-node (make-com-sat-map 3 3)))]
     [k-node (mutable-set)]
     [l-node
      (mutable-set (single-match-step la-impl-step la-spec-step a-node (make-com-sat-map 5 1)))]
     [m-node (mutable-set)]))

  (test-equal? "partition-by-satisfaction"
    (partition-by-satisfaction (set a-node
                                    b-node
                                    c-node
                                    d-node
                                    e-node
                                    f-node
                                    g-node
                                    h-node
                                    i-node
                                    j-node
                                    k-node
                                    l-node
                                    m-node)
                               com-sat-incoming
                               com-sat-related-steps)
    (list (set m-node)
          (set a-node
               b-node
               c-node
               d-node
               e-node
               f-node
               g-node
               h-node
               i-node
               j-node
               k-node
               l-node)))

  (test-case "partition-by-satisfaction: no satisfaction for many-of commitments"
    (define a-node (config-pair 'A `(UNKNOWN () (goto A) () ([(obs-ext 1) (many *)]))))
    (define a-node2 (config-pair 'A `(UNKNOWN () (goto A) () ([(obs-ext 1) (single *)]))))
    (define aa-impl-step
      (impl-step `(internal-receive (init-addr 1) (* Nat) single) #f null null #f))
    (define aa-spec-step (spec-step #f #f (list `((obs-ext 1) *))))
    (check-equal?
     (partition-by-satisfaction
      (set a-node)
      ;; incoming
      (mutable-hash [a-node (mutable-set (list a-node aa-impl-step aa-spec-step `([1 1])))])
      ;; related-spec-steps
      (mutable-hash [(list a-node aa-impl-step) (mutable-set aa-spec-step)]))
     (list (set) (set a-node)))
    ;; if we change the many-of for a single-of, it should now conform
    (check-equal?
     (partition-by-satisfaction
      (set a-node2)
      ;; incoming
      (mutable-hash [a-node2 (mutable-set (list a-node2 aa-impl-step aa-spec-step `([1 1])))])
      ;; related-spec-steps
      (mutable-hash [(list a-node2 aa-impl-step) (mutable-set aa-spec-step)]))
     (list (set a-node2) (set)))))

;; Builds an OutgoingStepsDict from the given dictionaries
(define (build-outgoing-dict incoming related-spec-steps)
  (define outgoing (make-hash))

  (for ([(config-pair this-pair-incoming-steps) incoming])
    ;; 1. add entry for current config pair if it doesn't exist yet
    (unless (hash-has-key? outgoing config-pair)
      (hash-set! outgoing config-pair (mutable-set)))

    (for ([incoming-step this-pair-incoming-steps])
      (match-define (list pred-pair impl-step spec-step address-map) incoming-step)
      ;; 2. add entry for predecessor config pair if it doesn't exist yet
      (define full-steps
        (match (hash-ref outgoing pred-pair #f)
          [#f
           (define steps (mutable-set))
           (hash-set! outgoing pred-pair steps)
           steps]
          [steps steps]))
      (when (set-member? (hash-ref related-spec-steps (list pred-pair impl-step)) spec-step)
        ;; 3. add this full step if it doesn't exist yet
        (define the-full-step
          (match (set-findf (lambda (s) (and (equal? (full-step-impl-step s) impl-step)
                                             (equal? (full-step-spec-step s) spec-step)))
                            full-steps)
            [#f
             (define the-full-step (full-step impl-step spec-step (mutable-set)))
             (set-add! full-steps the-full-step)
             the-full-step]
            [the-step the-step]))
        ;; 5. add this derivative of the spec step
        (set-add! (full-step-derivatives the-full-step)
                  (mapped-derivative config-pair address-map)))))
  outgoing)

(module+ test
  (test-hash-of-msets-equal? "super-simple build-outgoing test 1"
    (build-outgoing-dict (immutable-hash [(list 'a 'x) (mutable-set)])
                         (immutable-hash))
    (mutable-hash [(list 'a 'x) (mutable-set)]))

  (test-hash-of-msets-equal? "super-simple build-outgoing test 2"
    (build-outgoing-dict
     (immutable-hash [(list 'a 'x) (mutable-set)]
                     [(list 'b 'y) (mutable-set (list (list 'a 'x) 'impl1 'spec1 null))])
     (immutable-hash [(list (list 'a 'x) 'impl1) (mutable-set 'spec1)]))
    (mutable-hash [(list 'a 'x) (mutable-set
                                 (full-step
                                  'impl1
                                  'spec1
                                  (mutable-set (mapped-derivative (list 'b 'y) null))))]
                  [(list 'b 'y) (mutable-set)]))

  (test-hash-of-msets-equal? "build-outgoing test with unrelated spec step"
    (build-outgoing-dict
     (immutable-hash [(list 'a 'x) (mutable-set)]
                     [(list 'b 'y) (mutable-set (list (list 'a 'x) 'impl1 'spec1 null)
                                                (list (list 'a 'x) 'impl1 'spec2 null))])
     (immutable-hash [(list (list 'a 'x) 'impl1) (mutable-set 'spec1)]))
    (mutable-hash [(list 'a 'x) (mutable-set
                                 (full-step
                                  'impl1
                                  'spec1
                                  (mutable-set (mapped-derivative (list 'b 'y) null))))]
                  [(list 'b 'y) (mutable-set)]))

  (test-hash-of-msets-equal? "build-outgoing-dict: big test"
    (build-outgoing-dict com-sat-incoming com-sat-related-steps)
    com-sat-outgoing))

;; OutgoingDict -> (Hash impl-config (Setof Trigger))
;;
;; Returns a hash table that gives the enabled necessary actions for each implementation config in
;; outgoing.
(define (catalog-enabled-necessary-actions outgoing)
  (for/hash ([(config-pair full-steps) outgoing])
    (define all-actions
      (for/list ([full-step full-steps])
        (impl-step-trigger (full-step-impl-step full-step))))
    (values (config-pair-impl-config config-pair)
            (list->set (filter necessary-action? all-actions)))))

(module+ test
  (define com-sat-en-actions
    (immutable-hash ['A (set sat-en-trigger1 sat-en-trigger2 sat-en-trigger3 sat-en-trigger4)]
                    ['B (set sat-en-trigger1 sat-en-trigger2 sat-en-trigger3)]
                    ['C (set)]
                    ['D (set)]
                    ['E (set)]
                    ['F (set)]
                    ['G (set sat-en-trigger1)]
                    ['H (set sat-en-trigger1)]
                    ['I (set sat-en-trigger1 sat-en-trigger2)]
                    ['J (set sat-en-trigger1 sat-en-trigger2)]
                    ['K (set)]
                    ['L (set)]
                    ['M (set)]))
  (test-equal? "catalog-enabled-necessary-actions"
    (catalog-enabled-necessary-actions com-sat-outgoing) com-sat-en-actions))

;; Type:
;;
;; (List (List impl-config spec-config) (List Address Pattern))
;; IncomingDict
;; OutgoingDict
;; RelatedSpecStepsDict
;; (Setof impl-config)
;; ->
;; (List
;;   (Setof (List (List impl-config spec-config) (List Address Pattern))
;;   (Setof (List (List impl-config spec-config) (List Address Pattern))
;;
;; For all pairs in the graph implied by by incoming and related-spec-steps that have some path to or
;; from the given pair (including the pair itself) that have the same commitment but do not satisfy it
;; on that path, partitions them into two lists: those that satisfy the commitment in all fair
;; executions (the first returned list), and those that do not (the second returned list).
(define (find-sat/unsat-pairs config-commitment-pair
                              incoming
                              outgoing
                              related-spec-steps
                              enabled-necessary-actions)

  ;; The algorithm first builds the graph of all execution paths through the given configuration pair
  ;; in which every configuration has the commitment, and no edge (i.e. step) in the graph satisfies
  ;; it (this is a subgraph of the full execution graph). It then computes the strongly connected
  ;; components of this graph and finds those that are fair (a fair SCC is an SCC in which for every
  ;; enabled necessary action in each of its vertices, either there exists a vertex in the SCC where
  ;; the action is disabled, or there is an edge between two vertices in the SCC that takes that
  ;; action). Every fair SCC either represents a fair cycle or contains a quiescent configuration (or
  ;; both). The configurations that can reach a vertex in a fair SCC, then, are those that have some
  ;; fair execution that does not satisfy the given commitment; all other vertices in the graph do
  ;; satisfy the commitment in every execution.

  ;; 1. create the graph of unsatisfying steps from the given pair
  (define unsat-graph
    (build-unsatisfying-graph config-commitment-pair incoming outgoing related-spec-steps))
  ;; 2. find all vertices in fair strongly-connected components
  (define sccs (graph-find-sccs unsat-graph))
  (define fair-scc-vertices
    (for/fold ([fair-scc-vertices (set)])
              ([scc sccs] #:when (fair-scc? scc enabled-necessary-actions))
      (set-union fair-scc-vertices scc)))
  ;; 3. Find all vertices that can reach a vertex in a fair SCC
  (define unsat-vertices-set (vertices-reaching unsat-graph fair-scc-vertices))
  (define unsat-pairs-set (list->set (set-map unsat-vertices-set vertex-value)))
  (list
   (set-subtract (list->set (map vertex-value (graph-vertices unsat-graph))) unsat-pairs-set)
   unsat-pairs-set))

(module+ test
  (define (make-config-commitment-pair configs address-number variant-tag)
    (list configs (list (make-com-sat-ext-address address-number) `(variant ,variant-tag))))

  (test-equal? "all reachable pairs satisfy the commitment"
    (find-sat/unsat-pairs (make-config-commitment-pair a-node 1 'Y)
                          com-sat-incoming
                          com-sat-outgoing
                          com-sat-related-steps
                          com-sat-en-actions)
    (list (set (make-config-commitment-pair a-node 1 'Y))
          (set)))

  (test-equal? "no reachable pair satisfies"
    (find-sat/unsat-pairs (make-config-commitment-pair a-node 1 'Z)
                          com-sat-incoming
                          com-sat-outgoing
                          com-sat-related-steps
                          com-sat-en-actions)
    (list (set)
          (set (make-config-commitment-pair a-node 1 'Z)
               (make-config-commitment-pair b-node 1 'Z)
               (make-config-commitment-pair c-node 1 'Z)
               (make-config-commitment-pair d-node 1 'Z)
               (make-config-commitment-pair e-node 1 'Z)
               (make-config-commitment-pair f-node 1 'Z)
               (make-config-commitment-pair g-node 2 'Z)
               (make-config-commitment-pair h-node 2 'Z)
               (make-config-commitment-pair i-node 3 'Z)
               (make-config-commitment-pair j-node 3 'Z)
               (make-config-commitment-pair k-node 4 'Z)
               (make-config-commitment-pair l-node 5 'Z))))

  (test-equal? "some satisfied, some not"
    (find-sat/unsat-pairs (make-config-commitment-pair a-node 1 'X)
                          com-sat-incoming
                          com-sat-outgoing
                          com-sat-related-steps
                          com-sat-en-actions)
    (list (set
           (make-config-commitment-pair i-node 3 'X)
           (make-config-commitment-pair j-node 3 'X))
          (set (make-config-commitment-pair a-node 1 'X)
               (make-config-commitment-pair b-node 1 'X)
               (make-config-commitment-pair c-node 1 'X)
               (make-config-commitment-pair d-node 1 'X)
               (make-config-commitment-pair k-node 4 'X))))

  (test-equal? "check satisfaction: A with W"
    (find-sat/unsat-pairs (make-config-commitment-pair a-node 1 'W)
                          com-sat-incoming
                          com-sat-outgoing
                          com-sat-related-steps
                          com-sat-en-actions)
    (list (set)
          (set (make-config-commitment-pair a-node 1 'W)
               (make-config-commitment-pair g-node 2 'W)
               (make-config-commitment-pair h-node 2 'W)
               (make-config-commitment-pair l-node 5 'W)))))

;; ---------------------------------------------------------------------------------------------------
;; Unsatisfied commitments graph construction

;; (List config-pair (List address pattern)) IncomingDict OutgoingDict RelatedSpecStepsDict
;; -> Graph
;;
;; Builds a graph whose vertices are pairs of configuation pairs and commitments such that there is an
;; edge from v1 to v2 iff there is a step of v1's impl-config to v2's impl-config that does not
;; satisfy the commitment in v1, and v2's commitment is the possibly renamed version of v1's
;; commitment.
(define (build-unsatisfying-graph init-config-commitment-pair incoming outgoing related-spec-steps)
  (define G (make-graph))
  (define init-vertex (graph-add-vertex! G init-config-commitment-pair))
  (define worklist (queue init-vertex))

  ;; Loop invariants:
  ;; * every pair in the worklist has a corresponding vertex in G
  ;;
  ;; * every pair in G but not in the worklist has an edge in G for every possible step to or from the
  ;; pair that does not satisfy its commitment. This is exactly the visited set.
  (let loop ([visited (set)])
    (match (dequeue-if-non-empty! worklist)
      [#f (void)]
      [vertex
       (define pair (vertex-value vertex))
       ;; 1. check if this pair has already been visited
       (cond
         [(set-member? visited pair)
          (loop visited)]
         [else
          ;; 2. For each impl-step from this node that does not satisfy the commitment, add its edges
          ;; that do not satisfy the commitment
          (define config-pair (first pair))
          (define commitment (second pair))
          (define commitment-address (first commitment))
          (define pattern (second commitment))

          ;; Add vertices and edges from walking backwards
          (for ([incoming-entry (hash-ref incoming config-pair)])
            (match-define (list prev-config-pair i-step s-step addr-map) incoming-entry)
            (define prev-address (reverse-rename-address addr-map commitment-address))
            (define prev-commitment (list prev-address pattern))
            (when (and (aps#-config-has-commitment? (config-pair-spec-config prev-config-pair)
                                                    prev-address pattern)
                       (not (member prev-commitment (spec-step-satisfied-commitments s-step))))
              (define pred-vertex
                (graph-find-or-add-vertex! G (list prev-config-pair prev-commitment)))
              (graph-add-edge-if-new! G (list i-step s-step) pred-vertex vertex)
              (enqueue! worklist pred-vertex)))

          ;; Add vertices and edges from walking forwards
          (for ([the-full-step (hash-ref outgoing config-pair)])
            (match-define (full-step impl-step spec-step derivatives) the-full-step)
            (unless (member commitment (spec-step-satisfied-commitments spec-step))
              (match-define (list derivative successor-commitment)
                (find-carrying-derivative derivatives commitment))
              (define successor-vertex
                (graph-find-or-add-vertex! G (list derivative successor-commitment)))
              (graph-add-edge-if-new! G (list impl-step spec-step) vertex successor-vertex)
              (enqueue! worklist successor-vertex)))
          (loop (set-add visited pair))])]))
  G)

(module+ test
  ;; Tests for graph: I think just something that tests a little of everything: only do the non-sat
  ;; edges, record triggers in edges, backwards and forwards, multiple spec steps, etc.

  (test-graph-equal? "build-unsatisfying-graph: G with pattern W"
    (build-unsatisfying-graph (make-config-commitment-pair g-node 2 'W)
                              com-sat-incoming
                              com-sat-outgoing
                              com-sat-related-steps)
    (graph-literal (vertices [a (make-config-commitment-pair a-node 1 'W)]
                             [g (make-config-commitment-pair g-node 2 'W)]
                             [h (make-config-commitment-pair h-node 2 'W)]
                             [l (make-config-commitment-pair l-node 5 'W)])
                   (edges [(list ag-impl-step ag-spec-step) a g]
                          [(list gh-impl-step gh-spec-step) g h]
                          [(list hg-impl-step hg-spec-step) h g]
                          [(list al-impl-step al-spec-step) a l]
                          [(list la-impl-step la-spec-step) l a])))

  (define com-sat-w-on-a-graph
    (graph-literal (vertices [a (make-config-commitment-pair a-node 1 'W)]
                             [g (make-config-commitment-pair g-node 2 'W)]
                             [h (make-config-commitment-pair h-node 2 'W)]
                             [l (make-config-commitment-pair l-node 5 'W)])
                   (edges [(list ag-impl-step ag-spec-step) a g]
                          [(list gh-impl-step gh-spec-step) g h]
                          [(list hg-impl-step hg-spec-step) h g]
                          [(list al-impl-step al-spec-step) a l]
                          [(list la-impl-step la-spec-step) l a])))

  (test-graph-equal? "build-unsatisfying-graph: A with pattern W"
    (build-unsatisfying-graph (make-config-commitment-pair a-node 1 'W)
                              com-sat-incoming
                              com-sat-outgoing
                              com-sat-related-steps)
    com-sat-w-on-a-graph)

  (define com-sat-x-on-a-graph
    (graph-literal
     (vertices [a (make-config-commitment-pair a-node 1 'X)]
               [b (make-config-commitment-pair b-node 1 'X)]
               [c (make-config-commitment-pair c-node 1 'X)]
               [d (make-config-commitment-pair d-node 1 'X)]
               [i (make-config-commitment-pair i-node 3 'X)]
               [j (make-config-commitment-pair j-node 3 'X)]
               [k (make-config-commitment-pair k-node 4 'X)])
     (edges [(list ai-impl-step ai-spec-step) a i]
            [(list akm-impl-step akm-spec-step) a k]
            [(list ba-impl-step ba-spec-step) b a]
            [(list b-cd-impl-step bc-spec-step) b c]
            [(list b-cd-impl-step bd-spec-step) b d]
            [(list ij-impl-step ij-spec-step) i j]
            [(list ji-impl-step ji-spec-step) j i])))

  (test-graph-equal? "build-unsatisfying-graph: A with pattern X"
    (build-unsatisfying-graph (make-config-commitment-pair a-node 1 'X)
                              com-sat-incoming
                              com-sat-outgoing
                              com-sat-related-steps)
    com-sat-x-on-a-graph)

  (define com-sat-z-on-a-graph
    (graph-literal
     (vertices [a (make-config-commitment-pair a-node 1 'Z)]
               [b (make-config-commitment-pair b-node 1 'Z)]
               [c (make-config-commitment-pair c-node 1 'Z)]
               [d (make-config-commitment-pair d-node 1 'Z)]
               [e (make-config-commitment-pair e-node 1 'Z)]
               [f (make-config-commitment-pair f-node 1 'Z)]
               [g (make-config-commitment-pair g-node 2 'Z)]
               [h (make-config-commitment-pair h-node 2 'Z)]
               [i (make-config-commitment-pair i-node 3 'Z)]
               [j (make-config-commitment-pair j-node 3 'Z)]
               [k (make-config-commitment-pair k-node 4 'Z)]
               [l (make-config-commitment-pair l-node 5 'Z)])
     (edges [(list ag-impl-step ag-spec-step) a g]
            [(list ai-impl-step ai-spec-step) a i]
            [(list akm-impl-step akm-spec-step) a k]
            [(list al-impl-step al-spec-step) a l]
            [(list ba-impl-step ba-spec-step) b a]
            [(list b-cd-impl-step bc-spec-step) b c]
            [(list b-cd-impl-step bd-spec-step) b d]
            [(list b-ef-impl-step be-spec-step) b e]
            [(list b-ef-impl-step bf-spec-step) b f]
            [(list gh-impl-step gh-spec-step) g h]
            [(list hg-impl-step hg-spec-step) h g]
            [(list ia-impl-step ia-spec-step) i a]
            [(list ij-impl-step ij-spec-step) i j]
            [(list ja-impl-step ja-spec-step) j a]
            [(list ji-impl-step ji-spec-step) j i]
            [(list la-impl-step la-spec-step) l a])))

    (test-graph-equal? "build-unsatisfying-graph: A with pattern Z"
    (build-unsatisfying-graph (make-config-commitment-pair a-node 1 'Z)
                              com-sat-incoming
                              com-sat-outgoing
                              com-sat-related-steps)
    com-sat-z-on-a-graph))

;; mapped-derivative (List address pattern) -> (List config-pair (List address pattern))
;;
;; Finds the derivative within the given list that carries the given commitment from the previous
;; configuration pair, returning both the derivative config pair as well as the new commitment
;; (i.e. the commitment that has the address renamed to match the new config)
(define (find-carrying-derivative derivatives commitment)
  (define com-address (first commitment))
  (let loop ([derivatives (set->list derivatives)])
    (match derivatives
      [(list derivative derivatives ...)
       (match (try-rename-address (mapped-derivative-address-map derivative) com-address)
         [#f (loop derivatives)]
         [new-address (list (mapped-derivative-config-pair derivative)
                            (list new-address (second commitment)))])]
      [(list) (error 'find-carrying-derivative
                     "Unable to find carrying derivative for ~s in ~s"
                     commitment
                     derivatives)])))

(module+ test
  (check-equal?
   (find-carrying-derivative (list (mapped-derivative 'A null)
                                   (mapped-derivative 'B (list `[2 3]))
                                   (mapped-derivative 'C (list `[1 4] `[5 2]))
                                   (mapped-derivative 'D (list `[6 1]`[3 2])))
                             `((obs-ext 3) *))
   (list 'D `((obs-ext 2) *))))

;; Returns the vertex with the given value in the graph, or adds such a vertex if none exists and
;; returns it
(define (graph-find-or-add-vertex! g val)
  (match (graph-find-vertex g val)
    [#f (graph-add-vertex! g val)]
    [v v]))

;; Adds an edge with the given value, source, and destination to the given graph if such an edge does
;; not already exist
(define (graph-add-edge-if-new! g val src dest)
  (define (target-edge? e)
    (and (equal? (edge-value e) val)
         (equal? (vertex-value (edge-source e)) (vertex-value src))
         (equal? (vertex-value (edge-destination e)) (vertex-value dest))))
  (unless (findf target-edge? (vertex-outgoing src))
    (graph-add-edge! g val src dest)))

(module+ test
  (test-graph-equal? "graph-add-edge-if-new!"
    (let ()
      (define g (graph-literal (vertices [a 'a] [b 'b]) (edges [1 a b])))
      (graph-add-edge-if-new! g 1 (graph-find-vertex g 'a) (graph-find-vertex g 'b))
      g)
    (graph-literal (vertices [a 'a] [b 'b]) (edges [1 a b])))

  (test-graph-equal? "graph-add-edge-if-new! 2"
    (let ()
      (define g (graph-literal (vertices [a 'a] [b 'b]) (edges [1 a b])))
      (graph-add-edge-if-new! g 2 (graph-find-vertex g 'a) (graph-find-vertex g 'b))
      g)
    (graph-literal (vertices [a 'a] [b 'b]) (edges [1 a b] [2 a b]))))

;; ---------------------------------------------------------------------------------------------------
;; Graph helpers

;; Graph (Listof Vertex) -> (Setof Vertex)
;;
;; Returns the set of vertices in g that can reach a vertex in target-vertices (including
;; target-vertices themselves). Assumes that target-vertices are all vertices of g.
(define (vertices-reaching g target-vertices)
  ;; Returns the given reaching set updated with the vertices reaching start
  (define (dfs start reaching)
    (cond
      [(set-member? reaching start) reaching]
      [else
       (for/fold ([reaching (set-add reaching start)])
                 ([in-edge (vertex-incoming start)])
         (dfs (edge-source in-edge) reaching))]))

  ;; Does a DFS from each given vertex to compute the reaching vertices
  (for/fold ([reaching (set)])
            ([start target-vertices])
    (dfs start reaching)))

(module+ test
  (let ()
    (define reaching-test-graph
      (graph-literal
       [vertices [a 'a] [b 'b] [c 'c] [d 'd] [e 'e] [f 'f] [g 'g]]
       [edges ['ac a c]
              ['ae a e]
              ['ba b a]
              ['cb c b]
              ['cd c d]
              ['de d e]
              ['fe f e]
              ['gf g f]]))
    (define a-vert (graph-find-vertex reaching-test-graph 'a))
    (define b-vert (graph-find-vertex reaching-test-graph 'b))
    (define c-vert (graph-find-vertex reaching-test-graph 'c))
    (define d-vert (graph-find-vertex reaching-test-graph 'd))
    (define e-vert (graph-find-vertex reaching-test-graph 'e))
    (define f-vert (graph-find-vertex reaching-test-graph 'f))
    (define g-vert (graph-find-vertex reaching-test-graph 'g))

    (test-equal? "vertices-reaching 1"
      (vertices-reaching reaching-test-graph (list c-vert))
      (set a-vert b-vert c-vert))

    (test-equal? "vertices-reaching 2"
      (vertices-reaching reaching-test-graph (list f-vert))
      (set f-vert g-vert))

    (test-equal? "vertices-reaching 3"
      (vertices-reaching reaching-test-graph (list e-vert g-vert))
      (set a-vert b-vert c-vert d-vert e-vert f-vert g-vert))

    (test-equal? "vertices-reaching 4"
      (vertices-reaching reaching-test-graph (list f-vert c-vert))
      (set a-vert b-vert c-vert f-vert g-vert))

    (test-equal? "vertices-reaching 5"
      (vertices-reaching reaching-test-graph (list))
      (set))

    (test-equal? "vertices-reaching 6"
      (vertices-reaching reaching-test-graph (list g-vert))
      (set g-vert))))

;; Returns #t if the given strongly-connected component of the given graph is fair; #f otherwise.  A
;; fair SCC is an SCC in which for every enabled necessary action in each of its vertices, either
;; there exists a vertex in the SCC where the action is disabled, or there is an edge between two
;; vertices in the SCC that takes that action).
(define (fair-scc? scc enabled-necessary-actions)
  (define all-enabled-necessary-actions
    (for/fold ([all-en-actions (set)])
              ([vertex scc])
      (set-union all-en-actions
                 (list->set (hash-ref enabled-necessary-actions (vertex-impl-config vertex))))))
  (for/and ([action all-enabled-necessary-actions])
    ;; action is disabled or taken in some state
    (or
     ;; action is disabled in some vertex
     (for/or ([v scc])
       (not (set-member? (hash-ref enabled-necessary-actions (vertex-impl-config v)) action)))
     ;; there exists an edge between two vertices of the SCC that takes the action
     (for/or ([v scc])
       (for/or ([out-edge (vertex-outgoing v)])
         (define edge-impl-step (first (edge-value out-edge)))
         (and (equal? (impl-step-trigger edge-impl-step) action)
              (set-member? scc (edge-destination out-edge))))))))

(module+ test
  (define (make-com-sat-scc g . vals)
    (apply set (map (lambda (val) (graph-find-vertex g val)) vals)))

  (test-false "fair-scc? 1"
    (fair-scc? (make-com-sat-scc com-sat-x-on-a-graph
                                 (make-config-commitment-pair i-node 3 'X)
                                 (make-config-commitment-pair j-node 3 'X))
               com-sat-en-actions))

  (test-true "fair-scc? 2"
    (fair-scc? (make-com-sat-scc com-sat-w-on-a-graph
                                 (make-config-commitment-pair g-node 2 'W)
                                 (make-config-commitment-pair h-node 2 'W))
               com-sat-en-actions))

  (test-true "fair-scc? 3"
    (fair-scc? (make-com-sat-scc com-sat-z-on-a-graph
                                 (make-config-commitment-pair a-node 1 'Z)
                                 (make-config-commitment-pair i-node 3 'Z)
                                 (make-config-commitment-pair j-node 3 'Z)
                                 (make-config-commitment-pair l-node 5 'Z))
               com-sat-en-actions)))

;; Small helper; returns the implementation configuration associated with the given vertex of an
;; unsat-graph
(define (vertex-impl-config v)
  (config-pair-impl-config (first (vertex-value v))))
