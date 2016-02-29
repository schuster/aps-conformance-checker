#|

Remaining big challenges I see in the analysis:
* how to verify output commitments that are satisfied in a different handler than they were incurred (esp. if commitment is delegated to another actor, e.g. the session child in the TCP example)
* how to verify multi-actor programs (no clue on this one yet - need more good examples) (disjoint lemma can help, but won't always be possible)
* how to verify outputs when there's ambiguity as to which send matches which commitment
* how to verify cases where the transmission match is ambiguous (need constraint solver instead of BFS?)

|#


#lang racket

(require
 data/queue
 "queue-helpers.rkt"
 "aps-abstract.rkt"
 "csa.rkt"
 "csa-abstract.rkt")

;; TODO: test 1: the actor that just loops on itself conforms to the spec that does the same thing
;; (all observable actions)

(struct spec-config (instances commitments))

;; TODO: make this handle full configs, not just a single spec instance and agent instance

;; TODO: rename "analyze" to something like "check" or "verify" or "model-check"

;; TODO: test this method separately, apart from the idea of visiting a transition (just check the BFS
;; implementation

;; TODO: add some sort of typechecker that runs ahead of the analyzer (but perhaps as part of it, for
;; the sake of tests) to prevent things like a goto to a state that doesn't exist

;; TODO: add an initial mapping between the program and the spec (maybe? might need new definition of
;; conformance for that)

;; Given a concrete program configuration, a concrete specification configuration, and a list of pairs
;; that specify the expected prog-state/spec-state matches, returns #t if the conformance check
;; algorithm can prove conformance, #f otherwise.
;;
;; NOTE: this currently handles only programs consisting of a single actor that does not spawn other
;; actors. Also assumes that the spec starts in a state in which it has no state parameters.
(define (analyze initial-prog-config
                 initial-spec-instance
                 obs-sendable-type
                 unobs-sendable-type
                 state-matches)
  (unless (csa-valid-config? initial-prog-config)
    (error 'analyze "Invalid initial program configuration ~s" initial-prog-config))
  (unless (aps-valid-instance? initial-spec-instance)
    (error 'analyze "Invalid initial specification instance ~s" initial-spec-instance))
  ;; TODO: do a check for the state mapping

  (let/cc return-early
    ;; TODO: to-visit is now an imperative queue, so probably shouldn't use it as a loop parameter
    ;; TODO: give a better value for max-tuple-depth, both here for the initial abstraction and for
    ;; message generation
    (let loop ([to-visit (queue (cons (α-config initial-prog-config 0) (aps#-α-z initial-spec-instance)))]
               [visited (set)])
      (cond
        [(queue-empty? to-visit) #t]
        [else
         (define next-pair (dequeue! to-visit))
         (cond
           [(set-member? visited next-pair)
            (loop to-visit visited)]
           [else
            ;; TODO: rename this function. A better name will help me with the general terminology with
            ;; which I describe my technique
            (match-define (cons prog spec) next-pair)
            (define the-actor (csa#-config-only-actor prog))
            ;; TODO: rename this idea of transition: there's some other "thing" that this is, like a
            ;; transmission result. Define this data definition in the code somewhere, because it should
            ;; really be a type (it's a new kind of data in my domain that needs to be defined and
            ;; named)
            (define possible-transitions
              ;; TODO: get the max depth from somewhere
              (for/fold ([eval-results null])
                        ([message (generate-abstract-messages obs-sendable-type (csa#-actor-current-state the-actor) 0)])
                (append eval-results (csa#-eval-transition prog (csa#-actor-address the-actor) message))))
            (for ([possible-transition possible-transitions])
              (match (find-matching-spec-transition possible-transition spec state-matches)
                [(list)
                 ;; (printf "couldn't find any match\n")
                 (return-early #f)]
                [(list spec-goto-exp)
                 (enqueue! to-visit
                           (cons (step-prog-final-behavior prog (csa#-transition-behavior-exp possible-transition))
                                 (step-spec-with-goto spec spec-goto-exp)))]
                [_ (error "too many possible matches") ;; TODO: call a continuation instead
                   ]))
            (loop to-visit (set-add visited next-pair))])]))))

;; TODO: I probably need some canonical representation of program and spec configs so that otherwise
;; equivalent configs are not considered different by the worklist algorithm

;; NOTE: only supports spec configs with a single actor/spec
;;
;; Given a program transition, the current spec config, and the hash table mapping prog states to spec
;; states, returns the list of spec gotos for all possible matching transitions
(define (find-matching-spec-transition prog-transition spec-instance state-matches)
  (define match-results
    ;; TODO: rewrite this as a for/list
    (map
     (lambda (spec-transition)
       (prog-transition-matches-spec-transition? prog-transition spec-transition state-matches))
     (aps#-current-transitions spec-instance)))
  (filter values match-results))

;; Prog-trans is the above struct, spec-trans is the syntax of the expression
;;
;; Returns #f for no match, or the spec's goto expression with prog values if there is a match
;;
;; TODO: test this function
(define (prog-transition-matches-spec-transition? prog-trans spec-trans state-matches)

  ;; TODO: have this function return some kind of message/information about what went wrong

  ;; TODO: rename this function, because it's not just a predicate: returns something other than #t

  ;; (printf "Checking value ~s against pattern ~s\n" (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
  (match (aps#-match (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
    [(list)
     ;; No matches, so the whole predicate fails
     ;; (printf "Found no matches for received message ~s to pattern ~s\n" (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
     #f]
    [(list subst1 subst2 subst-rest ...)
     ;; (printf "too many matches for value ~s and pattern ~s\n" (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
     #f]
    [(list some-subst)
     (match-define (list spec-goto commitments)
       (aps#-eval (aps#-transition-expression spec-trans) some-subst))
     ;; (printf "Outputs: ~s\n" (csa#-transition-outputs prog-trans))
     ;; (printf "Commitments: ~s\n" commitments)
     (if (and (outputs-match-commitments? (csa#-transition-outputs prog-trans) commitments)
              (equal? (hash-ref state-matches (csa#-transition-next-state prog-trans))
                      (aps#-goto-state spec-goto)))
         spec-goto
         #f)]))

;; Returns #t if the given commitments fully account for the observable transmissions in outputs; #f
;; otherwise
;;
;; TODO: test this
(define (outputs-match-commitments? outputs commitments)
  (let/cc return-early
    (define unmatched-commitments
      (for/fold ([remaining-commitments commitments])
                ([output outputs])
        ;; TODO: check whether the output is observable according to the spec
        (match (findf (curry output-satisfies-commitment? output) remaining-commitments)
          ;; TODO: figure out how to deal with addresses that are precisely abstracted but not observed by the spec
          [#f
           ;; (printf "No match for output in the commitments.\nOutput: ~s\nCommitments: ~s\n"
           ;;         output
           ;;         remaining-commitments)
           (return-early #f)]
          [commitment (remove commitment remaining-commitments)])))
    (empty? unmatched-commitments)))

;; TODO: test this function
(define (output-satisfies-commitment? output commitment)
  ;; (printf "aps match attempt: ~s ~s\n" (csa#-output-message output) (aps#-commitment-pattern commitment))
  ;; (printf "aps match result: ~s\n" (aps#-matches-po? (csa#-output-message output) (aps#-commitment-pattern commitment)))
  (and (equal? (csa#-output-address output) (aps#-commitment-address commitment))
       (aps#-matches-po? (csa#-output-message output) (aps#-commitment-pattern commitment))))

;; TODO: tests for the above transition matching predicates/search functions

;; TODO: consider defining the spec semantics completely independently of concrete addresses, and
;; provide a mapping in the spec instead (the spec semantics would probably look something like HD
;; automata)

;; ---------------------------------------------------------------------------------------------------
;; Top-level tests

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   "csa.rkt")

  (define single-agent-concrete-addr (term (addr 0)))

  ;;;; Ignore everything

  (define ignore-all-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always) (m) (goto Always)))
       (goto Always)))))
  (define ignore-all-config (make-single-agent-config ignore-all-agent))
  (define ignore-all-spec-instance
    (term
     (((define-state (Always) [* -> (goto Always)]))
      (goto Always)
      ,single-agent-concrete-addr)))

  (check-not-false (redex-match csa-eval αn ignore-all-agent))
  (check-not-false (redex-match csa-eval K ignore-all-config))
  (check-not-false (redex-match aps-eval z ignore-all-spec-instance))

  ;; TODO: supply concrete specs and programs to the checker, not abstract ones
  (check-true (analyze ignore-all-config ignore-all-spec-instance (term Nat) (term (Union)) (hash 'Always 'Always)))

  ;;;; Send one message to a statically-known address per request

  ;; TODO: remove the redundancy between the state defs and the current expression
  (define static-response-address (term (addr 2)))
  (define static-response-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always response-dest) (m)
          (begin
            (send response-dest 'ack)
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always response-dest) (m)
          (begin
            (send response-dest 'ack)
            (send response-dest 'ack)
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-response-spec
    (term
     (((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      ,single-agent-concrete-addr)))

  (check-not-false (redex-match csa-eval αn static-response-agent))
  (check-not-false (redex-match csa-eval αn static-double-response-agent))
  (check-not-false (redex-match aps-eval z static-response-spec))

  (check-true (analyze (make-single-agent-config static-response-agent)
                       static-response-spec
                       (term (Addr 'ack)) (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-response-agent)
                        ignore-all-spec-instance
                        (term (Addr 'ack)) (term (Union))
                        (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-double-response-agent)
                        static-response-spec
                        (term (Addr 'ack)) (term (Union))
                        (hash 'Always 'Always)))
  (check-false (analyze ignore-all-config
                        static-response-spec
                        (term Nat) (term (Union))
                        (hash 'Always 'Always)))

  ;;;; Pattern matching tests, without dynamic channels

  (define pattern-match-spec
    (term
     (((define-state (Matching r)
         ['a -> (with-outputs ([r 'a]) (goto Matching r))]
         [(tuple 'b *) -> (with-outputs ([r (tuple 'b *)]) (goto Matching r))]))
      (goto Matching ,static-response-address)
      ,single-agent-concrete-addr)))

  (define pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always r) (m)
          (match m
            ['a (begin (send r 'a) (goto Always r))]
            [(tuple 'b *) (begin (send r (tuple 'b 0)) (goto Always r))]
            [* (goto Always r)])))
       (goto Always ,static-response-address)))))

  (define reverse-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always r) (m)
          (match m
            ['a (begin (send r (tuple 'b 0)) (goto Always r))]
            [(tuple 'b *) (begin (send r 'a) (goto Always r))]
            [* (goto Always r)])))
       (goto Always ,static-response-address)))))

  (define partial-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always r) (m)
          (match m
            ['a (begin (send r 'a) (goto Always r))]
            [(tuple 'b *) (goto Always r)]
            [* (goto Always r)])))
       (goto Always ,static-response-address)))))

  (define pattern-matching-map (hash 'Always 'Matching))

  (check-not-false (redex-match aps-eval z pattern-match-spec))
  (check-not-false (redex-match csa-eval αn pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn reverse-pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn partial-pattern-matching-agent))

  (check-true (analyze (make-single-agent-config pattern-matching-agent)
                       pattern-match-spec
                       (term (Union 'a (Tuple 'b Nat))) (term (Union))
                       pattern-matching-map))
  (check-false (analyze (make-single-agent-config partial-pattern-matching-agent)
                        pattern-match-spec
                        (term (Union 'a (Tuple 'b Nat))) (term (Union))
                        pattern-matching-map))
  (check-false (analyze (make-single-agent-config reverse-pattern-matching-agent)
                        pattern-match-spec
                        (term (Union 'a (Tuple 'b Nat))) (term (Union))
                        pattern-matching-map))

  ;;;; Dynamic request/response

  (define request-response-spec
    (term
     (((define-state (Always)
         [response-target -> (with-outputs ([response-target *]) (goto Always))]))
      (goto Always)
      ,single-agent-concrete-addr)))

  (define request-same-response-addr-spec
    (term
     (((define-state (Init)
         [response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))])
       (define-state (HaveAddr response-target)
         [new-response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))]))
      (goto Init)
      ,single-agent-concrete-addr)))
  (define request-response-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always i) (response-target)
          (begin
            (send response-target i)
            ;; TODO: implement addition and make this a counter
            ;; (goto Always (+ i 1))
            (goto Always i))))
       (goto Always 0)))))
  (define respond-to-first-addr-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr i response-target) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: also try the case where we save new-response-target instead
            ;; TODO: implement addition and make this a counter
            ;; (goto HaveAddr (+ i 1) response-target)
            (goto HaveAddr i response-target))))
       (goto Init)))))
  (define delay-saving-address-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr i response-target) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: implement addition and make this a counter
            ;; (goto HaveAddr (+ i 1) response-target)
            (goto HaveAddr i new-response-target))))
       (goto Init)))))
  (define double-response-agent
    `(,single-agent-concrete-addr
      (((define-state (Always i) (response-dest)
          (begin
            (send response-dest i)
            (send response-dest i)
            ;; TODO: implement addition and make this a counter
            ;; (goto Always (+ i 1))
            (goto Always i))))
       (goto Always 0))))

  (check-not-false (redex-match aps-eval z request-response-spec))
  (check-not-false (redex-match aps-eval z request-same-response-addr-spec))
  (check-not-false (redex-match csa-eval αn request-response-agent))
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-agent))
  (check-not-false (redex-match csa-eval αn double-response-agent))
  (check-not-false (redex-match csa-eval αn delay-saving-address-agent))

  (check-true (analyze (make-single-agent-config request-response-agent)
                       request-response-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent)
                        request-response-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Init 'Always 'HaveAddr 'Always)))

  (check-false (analyze (make-single-agent-config request-response-agent)
                        request-same-response-addr-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Always 'Init)))
  (check-true (analyze (make-single-agent-config respond-to-first-addr-agent)
                       request-same-response-addr-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'Init 'Init 'HaveAddr 'HaveAddr)))

  (check-false (analyze (make-single-agent-config double-response-agent)
                        request-response-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config delay-saving-address-agent)
                        request-response-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Init 'Always 'HaveAddr 'Always)))

  ;;;; Non-deterministic branching in spec

  (define zero-nonzero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r 'Zero])    (goto S1 r))]
         [* -> (with-outputs ([r 'NonZero]) (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define zero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r 'Zero])    (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define primitive-branch-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (S1 dest) (i)
          (begin
            (match (< 0 i)
              ['True (send dest 'NonZero)]
              ['False (send dest 'Zero)])
            (goto S1 dest))))
       (goto S1 ,static-response-address)))))

  (check-not-false (redex-match aps-eval z static-response-spec))
  (check-not-false (redex-match aps-eval z zero-nonzero-spec))
  (check-not-false (redex-match aps-eval z zero-spec))
  (check-not-false (redex-match csa-eval αn primitive-branch-agent))

  (check-true (analyze (make-single-agent-config primitive-branch-agent) zero-nonzero-spec (term Nat) (term (Union)) (hash 'S1 'S1)))
  (check-false (analyze (make-single-agent-config primitive-branch-agent) zero-spec (term Nat) (term (Union)) (hash 'S1 'S1)))

  ;;;; Stuck states in concrete evaluation

  (define nat-to-nat-spec
    (term
     (((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      ,single-agent-concrete-addr)))
  (define div-by-one-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always response-dest) (n)
          (begin
            (send response-dest (/ n 1))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define div-by-zero-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always response-dest) (n)
          (begin
            (send response-dest (/ n 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match aps-eval z nat-to-nat-spec))
  (check-not-false (redex-match csa-eval αn div-by-zero-agent))
  (check-not-false (redex-match csa-eval αn div-by-one-agent))

  (check-true (analyze (make-single-agent-config div-by-one-agent) nat-to-nat-spec (term Nat) (term Union) (hash 'Always 'Always)))
  (check-true (analyze (make-single-agent-config div-by-zero-agent) nat-to-nat-spec (term Nat) (term Union) (hash 'Always 'Always)))

  ;;;; Unobservable communication

  ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect conformance
  ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
  ;; (check-false (analyze (make-single-agent-config static-response-agent)
  ;;                       static-response-spec
  ;;                       (Addr 'ack)
  ;;                       (Addr 'ack)
  ;;                       (hash 'Always 'Always)))
  ;; 3. Conformance regained for static req/resp. when add an unobs transition


  ;; 4. unobs causes a particular behavior (like connected/error in TCP)


  ;; TODO: write a test where the unobs input messages for pattern matching matter
  )
