#|

Remaining big challenges I see in the analysis:
* how to verify output commitments that are satisfied in a different handler than they were incurred (esp. if commitment is delegated to another actor, e.g. the session child in the TCP example)
* how to verify multi-actor programs (no clue on this one yet - need more good examples) (disjoint lemma can help, but won't always be possible)
* how to verify outputs when there's ambiguity as to which send matches which commitment
* how to verify cases where the transmission match is ambiguous (need constraint solver instead of BFS?)

|#


#lang racket


;; TODO: probably shouldn't call this file "main" if it's exporting something to something else in the
;; "package"
(provide analyze)

(require
 data/queue
 "queue-helpers.rkt"
 "aps.rkt"
 "aps-abstract.rkt"
 "csa.rkt"
 "csa-abstract.rkt")

(module+ test
  (require
   rackunit
   redex/reduction-semantics
   "rackunit-helpers.rkt"))

;; TODO: rename "agents" to just actors, or otherwise decide what these things should be called

;; ---------------------------------------------------------------------------------------------------
;; Data definitions

(struct spec-config (instances commitments))

;; Program transition is defined in csa-abstract

;; ---------------------------------------------------------------------------------------------------
;; Main functions

;; TODO: make this handle full configs, not just a single spec instance and agent instance

;; TODO: rename "analyze" to something like "check" or "verify" or "model-check"

;; TODO: test this method separately, apart from the idea of visiting a transition (just check the BFS
;; implementation

;; TODO: add some sort of typechecker that runs ahead of the analyzer (but perhaps as part of it, for
;; the sake of tests) to prevent things like a goto to a state that doesn't exist (and make sure that
;; a specs's type matches the program)

;; TODO: add an initial mapping between the program and the spec (maybe? might need new definition of
;; conformance for that)

;; TODO: remove this function, or at least rename it
(define (analyze initial-prog-config
                 initial-spec-instance
                 init-obs-type
                 init-unobs-type
                 state-matches)
  (unless (aps-valid-instance? initial-spec-instance)
    (error 'analyze "Invalid initial specification instance ~s" initial-spec-instance))
  (check initial-prog-config
         (aps-config-from-instance initial-spec-instance)
         init-obs-type
         init-unobs-type
         state-matches))

;; TODO: rename "config" to "state"

;; Given a concrete program configuration, a concrete specification configuration, and a list of pairs
;; that specify the expected prog-state/spec-state matches, returns #t if the conformance check
;; algorithm can prove conformance, #f otherwise.
;;
;; NOTE: this currently handles only programs consisting of a single actor that does not spawn other
;; actors. Also assumes that the spec starts in a state in which it has no state parameters.
(define (check initial-prog-config
               initial-spec-config
               init-obs-type
               init-unobs-type
               state-matches)
  (unless (csa-valid-config? initial-prog-config)
    (error 'check "Invalid initial program configuration ~s" initial-prog-config))
  (unless (aps-valid-config? initial-spec-config)
    (error 'check "Invalid initial specification configuration ~s" initial-spec-config))
  ;; TODO: do a check for the state mapping

  (let/cc return-early
    ;; TODO: to-visit is now an imperative queue, so probably shouldn't use it as a loop parameter
    ;; TODO: give a better value for max-tuple-depth, both here for the initial abstraction and for
    ;; message generation
    ;; TODO: canonicalize the initial tuple
    (define initial-tuple
      ;; TODO: get the max depth from somewhere
      (list (α-config initial-prog-config (aps-config-observable-addresses initial-spec-config) 10)
            (aps#-α-Σ initial-spec-config)
            init-obs-type
            init-unobs-type))
    (define program-transitions-checked 0) ; for diagnostics only
    (let loop ([to-visit (queue initial-tuple)]
               [visited (set)])
      (cond
        [(queue-empty? to-visit) #t]
        [else
         (define current-tuple (dequeue! to-visit))
         ;; TODO: rename this function. A better name will help me with the general terminology
         ;; with which I describe my technique
         (match-define (list prog spec obs-type unobs-type) current-tuple)
         ;; TODO: rename this idea of transition: there's some other "thing" that this is, like a
         ;; transmission result. Define this data definition in the code somewhere, because it
         ;; should really be a type (it's a new kind of data in my domain that needs to be defined
         ;; and named)

         ;; Debugging
         (set! program-transitions-checked (add1 program-transitions-checked))
         ;; (printf "Program state #: ~s\n" program-transitions-checked)
         ;; (printf "Queue size: ~s\n" (queue-length to-visit))
         ;; (printf "The prog config: ~s\n" (prog-config-without-state-defs prog))
         ;; (printf "The full prog config: ~s\n" prog)

         (display-step-line "Evaluating possible program transitions")
         ;; TODO: handle multiple actors here
         (define possible-transitions
           (append (transitions-from-message-of-type prog obs-type #t)
                   (transitions-from-message-of-type prog unobs-type #f)
                   (csa#-handle-any-timeouts prog)))
         (for ([possible-transition possible-transitions])
           (display-step-line "Finding a matching spec transition")

           ;; TODO: rewrite find-matching-spec-transition; probably remove or refactor the
           ;; hints. Should also just return the full config, because output commitment won't be
           ;; satisfied immediately
           (match (matching-spec-transitions possible-transition spec state-matches)
             [(list)
              ;; (printf "couldn't find any match for ~s from program state ~s, in spec state ~s\n"
              ;;         possible-transition
              ;;         prog
              ;;         spec)
              (return-early #f)]
             [(list (list _ spec-goto))
              (display-step-line "Stepping the spec config")
              ;; TODO: adjust this stepping stuff to acount for commit-only specs
              (define stepped-spec-config (step-spec-with-goto spec spec-goto))
              (display-step-line "Stepping the prog config")
              (define stepped-prog-config (step-prog-final-behavior prog (csa#-transition-behavior-exp possible-transition)))
              (display-step-line "Splitting the spec config")
              (for ([spec-config-component (split-spec stepped-spec-config)])

                ;; TODO: make it an "error" for a non-precise address to match a spec state parameter

                (display-step-line "Abstracting a program")
                (define abstracted-prog-config (abstract-prog-config-by-spec stepped-prog-config spec-config-component))
                (display-step-line "Canonicalizing the tuple, adding to queue")
                (define next-tuple
                  (canonicalize-tuple ; i.e. rename the addresses
                   (list abstracted-prog-config spec-config-component
                         ;; TODO: allow these types to change over time
                         obs-type
                         unobs-type)))
                (unless (or (set-member? visited next-tuple)
                            (member next-tuple (queue->list to-visit))
                            (equal? current-tuple next-tuple))
                  ;; (printf "Adding state: ~s\n" (prog-config-goto (car next-tuple)))
                  (enqueue! to-visit next-tuple)))]
             [(list (list multiple-transitions _) ...)
              (displayln "Too many possible matches")
              (printf "Program transition: ~s\n" possible-transition)
              (for ([s multiple-transitions])
                (printf "A spec transition: ~s\n" s))
              ;; TODO: call a continuation instead
              (return-early #f)]))
         (loop to-visit (set-add visited current-tuple))]))))

;; TODO: I probably need some canonical representation of program and spec configs so that otherwise
;; equivalent configs are not considered different by the worklist algorithm

;; TODO: adjust this function to allow for multiple possible actors
;;
;; Returns all possible transitions of the given program config caused by a received message to the of
;; the given type
(define (transitions-from-message-of-type prog-config type observed?)
  (define the-actor (csa#-config-only-actor prog-config))

  ;; Debugging
  ;; (printf "Message type: ~s\n" type)
  ;; (printf "Number of generated messages: ~s\n" (length (generate-abstract-messages type (csa#-actor-current-state the-actor) 10 observed?)))

  (display-step-line "Enumerating abstract messages (typed)")
  (for/fold ([transitions-so-far null])
            ;; TODO: get the max depth from somewhere
            ([message (generate-abstract-messages type (csa#-actor-current-state the-actor) 10 observed?)])
    (define the-address (csa#-actor-address the-actor))
    ;; TODO: remove the call to age-addresses here
    (display-step-line "Evaluating a handler")
    (define new-transitions (csa#-handle-message prog-config
                                                 the-address
                                                 message
                                                 observed?))
    (append transitions-so-far new-transitions)))

;; Given a program transition, the current spec config, and the hash table mapping prog states to spec
;; states, returns the list of spec transitions for all possible matching transitions
(define (matching-spec-transitions prog-transition spec-config state-matches)
  ;; TODO: write this for a spec *config*, not an instance
  ;;
  ;; Rough initial idea of algorithm for multi-FSM specs (to be implemented): transition the spec FSM
  ;; only when (a) an observed message is received, or (b) when no output commitment can satisfy a
  ;; current output

  ;; TODO: figure out if I should support instances where a single transition of the program uses
  ;; multiple transitions of the spec (I think this probably won't happen in practice)

  ;; (printf "the program trans: ~s\n" prog-transition)

  (define match-results
    ;; TODO: rewrite this as a for/list
    (map
     (lambda (spec-transition)
       (match-spec-transition-against-prog-transition prog-transition spec-transition state-matches))
     (cons (aps#-null-transition spec-config) (aps#-current-transitions spec-config))))
  (filter values match-results))

;; Prog-trans is the above struct, spec-trans is the syntax of the expression
;;
;; Returns #f for no match, or the spec's remaining transition expression if there is a match
;;
;; TODO: test this function
(define (match-spec-transition-against-prog-transition prog-trans spec-trans state-matches)
  ;; Debugging only
  ;; (printf "prog trans: ~s\n" prog-trans)
  ;; (printf "spec trans: ~s\n" spec-trans)

  ;; (printf "the spec trans: ~s\n" spec-trans)

  (let/cc return-early
   (define valid-substitutions
     (cond
       [(and (csa#-transition-observed? prog-trans) (aps#-transition-observed? spec-trans))
        (aps#-match (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))]
       [(and (not (csa#-transition-observed? prog-trans))
             (not (aps#-transition-observed? spec-trans)))
        (list (list))]
       [else (return-early #f)]))

   ;; (printf "Checking value ~s against pattern ~s\n"
   ;;         (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
   (match valid-substitutions
     [(list)
      ;; No matches, so the whole predicate fails
      ;; (printf "Found no matches for received message ~s to pattern ~s\n"
      ;;         (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
      #f]
     [(list subst1 subst2 subst-rest ...)
      ;; TODO: test/enforce that aps#-match produces at most one way to match the pattern (will this
      ;; still be true if we allow "or" patterns?)

      ;; (printf "too many matches for value ~s and pattern ~s\n"
      ;;         (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
      #f]
     [(list some-subst)
      (match-define (list spec-goto commitments)
        (aps#-eval (aps#-transition-expression spec-trans) some-subst))

      ;; TODO: actually get the full list of output addresses the spec is observing (from the output
      ;; commitment map), rather than this hack of using both new and old goto expressions and the
      ;; current new set of commitments
      (define observed-addresses
        (remove-duplicates (append (cdr spec-goto) (map aps#-commitment-address commitments))))

      ;; (printf "the goto: ~s, comms: ~s\n" spec-goto commitments)
      ;; (printf "Outputs: ~s\n" (csa#-transition-outputs prog-trans))
      ;; (printf "Commitments: ~s\n" commitments)
      (if (and
           ;; TODO: deal with loop output
           ;; (null? (filter csa#-observable-output? (csa#-transition-loop-outputs prog-trans)))
           (outputs-match-commitments?
            (filter
             (lambda (o) (member (csa#-output-address o) observed-addresses))
             (csa#-transition-outputs prog-trans))
            commitments)
           (equal? (hash-ref state-matches (csa#-transition-next-state prog-trans))
                   (aps#-goto-state spec-goto)))
          (list spec-trans spec-goto)
          #f)])))

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

(module+ test

  ;; TODO: test outputs-match-commitments for (along with normal cases):
  ;; * spec that observes an address but neither saves it nor has output commtiments for it
  ;; * POV unobservables
  ;; * wildcard unobservables
  )

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

;; Takes abstract prog config and abstract spec config; returns prog further abstracted according to
;; spec
(define (abstract-prog-config-by-spec p s)
  ;; How do we decide whether to keep the old or new stuff? Is that a different part of the
  ;; abstraction from blurring out the addresses irrelevant to the current spec config?

  ;; Where do I change other addresses to dead-observable?

  ;; TODO: blur out certain internal actors

  (blur-externals p (aps#-relevant-external-addrs s)))

;; Returns the list of split spec-configs from the given one, failing if any of the FSMs share an
;; address
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
      (goto A (obs-ext 0))
      SINGLE-ACTOR-ADDR)))

  (check-not-false (redex-match aps# z simple-instance-for-split-test))

  ;; split spec with one FSM gets same spec
  (check-equal?
   (split-spec (term ((,simple-instance-for-split-test) ())))
   (list (term ((,simple-instance-for-split-test) ()))))

  ;; split with one related commit
  (check-equal?
   (split-spec (term ((,simple-instance-for-split-test) (((obs-ext 0) *)))))
   (list (term ((,simple-instance-for-split-test) (((obs-ext 0) *))))))

  ;; split with unrelated commit
  (check-same-items?
   (split-spec (term ((,simple-instance-for-split-test) (((obs-ext 1) *)))))
   (list (term ((,simple-instance-for-split-test) ()))
         (term (() (((obs-ext 1) *))))))

  ;; TODO: check that none of the FSMs share an address
  )

;; ---------------------------------------------------------------------------------------------------
;; Debugging

(define DISPLAY-STEPS #f)

(define (display-step-line msg)
  (when DISPLAY-STEPS (displayln msg)))

;; ---------------------------------------------------------------------------------------------------
;; Top-level tests

(module+ test
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
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (begin
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-agent
    (term
     (,single-agent-concrete-addr
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
      ,single-agent-concrete-addr)))
  (define ignore-all-with-addr-spec-instance
    (term
     (((define-state (Always response-dest) [* -> (goto Always response-dest)]))
      (goto Always ,static-response-address)
      ,single-agent-concrete-addr)))

  (check-not-false (redex-match csa-eval αn static-response-agent))
  (check-not-false (redex-match csa-eval αn static-double-response-agent))
  (check-not-false (redex-match aps-eval z static-response-spec))
  (check-not-false (redex-match aps-eval z ignore-all-with-addr-spec-instance))

  (check-true (analyze (make-single-agent-config static-response-agent)
                       static-response-spec
                       (term Nat) (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-response-agent)
                        ignore-all-with-addr-spec-instance
                        (term Nat) (term (Union))
                        (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-double-response-agent)
                        static-response-spec
                        (term Nat) (term (Union))
                        (hash 'Always 'Always)))
  (check-false (analyze ignore-all-config
                        static-response-spec
                        (term Nat) (term (Union))
                        (hash 'Always 'Always)))

  ;;;; Pattern matching tests, without dynamic channels

  (define pattern-match-spec
    (term
     (((define-state (Matching r)
         [(variant A *) -> (with-outputs ([r (variant A *)]) (goto Matching r))]
         [(variant B *) -> (with-outputs ([r (variant B *)]) (goto Matching r))]))
      (goto Matching ,static-response-address)
      ,single-agent-concrete-addr)))

  (define pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A x)) (goto Always r))]
            [(B y) (begin (send r (variant B 0)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define reverse-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant B 0)) (goto Always r))]
            [(B y) (begin (send r (variant A y)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define partial-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always [r (Union [A Nat] [B Nat])]) (m)
          (case m
            [(A x) (begin (send r (variant A 0)) (goto Always r))]
            [(B y) (goto Always r)])))
       (goto Always ,static-response-address)))))

  (define pattern-matching-map (hash 'Always 'Matching))

  (check-not-false (redex-match aps-eval z pattern-match-spec))
  (check-not-false (redex-match csa-eval αn pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn reverse-pattern-matching-agent))
  (check-not-false (redex-match csa-eval αn partial-pattern-matching-agent))

  (check-true (analyze (make-single-agent-config pattern-matching-agent)
                       pattern-match-spec
                       (term (Union [A Nat] [B Nat])) (term (Union))
                       pattern-matching-map))
  (check-false (analyze (make-single-agent-config partial-pattern-matching-agent)
                        pattern-match-spec
                        (term (Union [A Nat] [B Nat])) (term (Union))
                        pattern-matching-map))
  (check-false (analyze (make-single-agent-config reverse-pattern-matching-agent)
                        pattern-match-spec
                        (term (Union [A Nat] [B Nat])) (term (Union))
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
      (((define-state (Always [i Nat]) (response-target)
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
        (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: also try the case where we save new-response-target instead
            ;; TODO: implement addition and make this a counter
            ;; (goto HaveAddr (+ i 1) response-target)
            (goto HaveAddr i response-target))))
       (goto Init)))))
  (define respond-to-first-addr-agent2
    (term
     (,single-agent-concrete-addr
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
     (,single-agent-concrete-addr
      (((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr [i Nat] [response-target (Addr Nat)]) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: implement addition and make this a counter
            ;; (goto HaveAddr (+ i 1) response-target)
            (goto HaveAddr i new-response-target))))
       (goto Init)))))
  (define double-response-agent
    `(,single-agent-concrete-addr
      (((define-state (Always [i Nat]) (response-dest)
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
  (check-not-false (redex-match csa-eval αn respond-to-first-addr-agent2))
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
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent2)
                        request-response-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Always 'Always)))

  (check-false (analyze (make-single-agent-config request-response-agent)
                        request-same-response-addr-spec
                        (term (Addr Nat)) (term (Union))
                        (hash 'Always 'Init)))
  (check-true (analyze (make-single-agent-config respond-to-first-addr-agent)
                       request-same-response-addr-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'Init 'Init 'HaveAddr 'HaveAddr)))
  ;; TODO: figure out some way to get this test to work (won't right now because agent's Always state
  ;; corresponds to both states of the spec, depending on its parameter
  ;; (check-true (analyze (make-single-agent-config respond-to-first-addr-agent2)
  ;;                       request-same-response-addr-spec
  ;;                       (term (Addr Nat)) (term (Union))
  ;;                       (hash 'Always 'Always)))

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
         [* -> (with-outputs ([r (variant Zero)])    (goto S1 r))]
         [* -> (with-outputs ([r (variant NonZero)]) (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define zero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r (variant Zero)])    (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define primitive-branch-agent
    (term
     (,single-agent-concrete-addr
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
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 1))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define div-by-zero-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always [response-dest (Addr Nat)]) (n)
          (begin
            (send response-dest (/ n 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))

  (check-not-false (redex-match aps-eval z nat-to-nat-spec))
  (check-not-false (redex-match csa-eval αn div-by-zero-agent))
  (check-not-false (redex-match csa-eval αn div-by-one-agent))

  (check-true (analyze (make-single-agent-config div-by-one-agent) nat-to-nat-spec (term Nat) (term (Union)) (hash 'Always 'Always)))
  (check-true (analyze (make-single-agent-config div-by-zero-agent) nat-to-nat-spec (term Nat) (term (Union)) (hash 'Always 'Always)))

  ;;;; Unobservable communication

  ;; wildcard unobservables are ignored for the purpose of output commitments
  (check-true (analyze (make-single-agent-config request-response-agent)
                       ignore-all-spec-instance
                       (term (Addr Nat)) (term (Union))
                       (hash 'Always 'Always)))

  ;; 1. In dynamic req/resp, allowing unobserved perspective to send same messages does not affect conformance
  (check-true (analyze (make-single-agent-config request-response-agent)
                       request-response-spec
                       (term (Addr Nat))
                       (term (Addr Nat))
                       (hash 'Always 'Always)))

  ;; 2. Allowing same messages from unobs perspective violates conformance for static req/resp.
  (check-false (analyze (make-single-agent-config static-response-agent)
                        static-response-spec
                        (term Nat)
                        (term Nat)
                        (hash 'Always 'Always)))

  ;; 3. Conformance regained for static req/resp when add an unobs transition
  (define static-response-spec-with-unobs
    (term
     (((define-state (Always response-dest)
         [*     -> (with-outputs ([response-dest *]) (goto Always response-dest))]
         [unobs -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always ,static-response-address)
      ,single-agent-concrete-addr)))
  (check-not-false (redex-match aps-eval z static-response-spec-with-unobs))

  (check-true (analyze (make-single-agent-config static-response-agent)
                       static-response-spec-with-unobs
                       (term Nat)
                       (term Nat)
                       (hash 'Always 'Always)))

  ;; 4. unobs causes a particular behavior (like connected/error in TCP)
  (define unobs-toggle-spec
    (term (((define-state (Off r)
              [* -> (with-outputs ([r (variant TurningOn)]) (goto On r))])
            (define-state (On r)
              [* -> (goto On r)]
              [unobs -> (with-outputs ([r (variant TurningOff)]) (goto Off r))]))
           (goto Off ,static-response-address)
           ,single-agent-concrete-addr)))
  (define unobs-toggle-agent
    (term
     (,single-agent-concrete-addr
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
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong1
    (term
     (,single-agent-concrete-addr
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
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong2
    (term
     (,single-agent-concrete-addr
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
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong3
    (term
     (,single-agent-concrete-addr
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
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong4
    (term
     (,single-agent-concrete-addr
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
       (goto Off ,static-response-address)))))

  (check-not-false (redex-match aps-eval z unobs-toggle-spec))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong1))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong2))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong3))
  (check-not-false (redex-match aps-eval αn unobs-toggle-agent-wrong4))

  (check-true (analyze (make-single-agent-config unobs-toggle-agent)
                       unobs-toggle-spec
                       (term (Union [FromObserver]))
                       (term (Union [FromUnobservedEnvironment]))
                       (hash 'On 'On 'Off 'Off)))

  (for ([agent (list unobs-toggle-agent-wrong1
                     unobs-toggle-agent-wrong2
                     unobs-toggle-agent-wrong3
                     unobs-toggle-agent-wrong4)])
    (check-false (analyze (make-single-agent-config agent)
                          unobs-toggle-spec
                          (term (Union [FromObserver]))
                          (term (Union [FromUnobservedEnvironment]))
                          (hash 'On 'On 'Off 'Off))))

  ;;;; Records

  (define record-req-resp-spec
    (term
     (((define-state (Always)
         [(record [dest dest] [msg (variant A)]) -> (with-outputs ([dest (variant A)]) (goto Always))]
         [(record [dest dest] [msg (variant B)]) -> (with-outputs ([dest (variant B)]) (goto Always))]))
      (goto Always)
      ,single-agent-concrete-addr)))
  (define record-req-resp-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always) (m)
          (begin
            (send (: m dest) (: m msg))
            (goto Always))))
       (goto Always)))))
  (define record-req-wrong-resp-agent
    (term
     (,single-agent-concrete-addr
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
                       (term (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
                       (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config record-req-wrong-resp-agent)
                        record-req-resp-spec
                        (term (Record [dest (Addr (Union [A] [B]))] [msg (Union [A] [B])]))
                        (term (Union))
                        (hash 'Always 'Always)))

  ;;;; Let
  (define static-response-let-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always [response-dest (Addr (Union [Ack Nat]))]) (m)
          (let ([new-r response-dest])
            (begin
              (send new-r (variant Ack 0))
              (goto Always new-r)))))
       (goto Always ,static-response-address)))))
  (define static-double-response-let-agent
    (term
     (,single-agent-concrete-addr
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
                       (term Nat) (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-double-response-let-agent)
                        static-response-spec
                        (term Nat) (term (Union))
                        (hash 'Always 'Always)))

  ;; Check that = gives both results
  (define equal-agent-wrong1
    (term
     (,single-agent-concrete-addr
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
     (,single-agent-concrete-addr
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
     (,single-agent-concrete-addr
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

  (check-false
   (analyze (make-single-agent-config equal-agent-wrong1)
            static-response-spec
            (term Nat) (term (Union))
            (hash 'A 'Always 'B 'Always)))
  (check-false
   (analyze (make-single-agent-config equal-agent-wrong2)
            static-response-spec
            (term Nat) (term (Union))
            (hash 'A 'Always 'B 'Always)))
  (check-true
   (analyze (make-single-agent-config equal-agent)
            static-response-spec
            (term Nat) (term (Union))
            (hash 'A 'Always 'B 'Always)))

  ;;;; For loops
  (define loop-do-nothing-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (A) (m)
          (begin
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              i)
            (goto A))))
       (goto A)))))
  (define loop-send-unobs-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (A [r (Addr Nat)]) (m)
          (begin
            (for/fold ([folded 0])
                      ([i (list 1 2 3)])
              (send r i))
            (goto A r))))
       (goto A ,static-response-address)))))
  (define send-before-loop-agent
    (term
     (,single-agent-concrete-addr
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
     (,single-agent-concrete-addr
      (((define-state (A) (r)
          (begin
            (for/fold ([folded 0])
                      ([r (list r)])
              (send r 0))
            (goto A))))
       (goto A)))))
  (define send-after-loop-agent
    (term
     (,single-agent-concrete-addr
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
                       ignore-all-spec-instance
                       (term Nat)
                       (term (Union))
                       (hash 'A 'Always)))
  (check-true (analyze (make-single-agent-config loop-send-unobs-agent)
                       ignore-all-spec-instance
                       (term Nat)
                       (term (Union))
                       (hash 'A 'Always)))
  (check-true (analyze (make-single-agent-config send-before-loop-agent)
                       request-response-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'A 'Always)))
  (check-false (analyze (make-single-agent-config send-inside-loop-agent)
                       request-response-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'A 'Always)))
  (check-true (analyze (make-single-agent-config send-after-loop-agent)
                       request-response-spec
                       (term (Addr Nat)) (term (Union))
                       (hash 'A 'Always)))

  ;;;; Timeouts
  (define timeout-spec
    (term
     (((define-state (A r)
         [* -> (with-outputs ([r (variant GotMessage)]) (goto A r))]
         [unobs -> (with-outputs ([r (variant GotTimeout)]) (goto A r))]))
      (goto A ,static-response-address)
      ,single-agent-concrete-addr)))
  (define got-message-only-spec
    (term
     (((define-state (A r)
         [* -> (with-outputs ([r (variant GotMessage)]) (goto A r))]))
      (goto A ,static-response-address)
      ,single-agent-concrete-addr)))
  (define timeout-and-send-agent
    (term
     (,single-agent-concrete-addr
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
                       (term Nat) (term (Union))
                       (hash 'A 'A)))
  (check-false (analyze (make-single-agent-config timeout-and-send-agent)
                       got-message-only-spec
                       (term Nat) (term (Union))
                       (hash 'A 'A)))

  ;; Multiple Actors
  ;; (define statically-delegating-responder-actor
  ;;   (term
  ;;    (,some-other-address ; TODO: this line
  ;;     (((define-state (A [responder (Addr (Addr Nat))]) (m)
  ;;         (begin
  ;;           (send responder m)
  ;;           (goto A responder))))
  ;;      ;; TODO: put the real address here
  ;;      (goto A ,yet-another-address)))))

  ;; (check-not-false (redex-match csa-eval αn statically-delegating-responder-actor))
  ;; (check-true (analyze (make-config not-sure-what-goes-here) ;; TODO: this line
  ;;                      request-response-target
  ;;                      (term (Addr Nat)) (term (Union))
  ;;                      ;; TODO: hints?
  ;;                      ))
  )
