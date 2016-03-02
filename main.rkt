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

;; TODO: rename "agents" to just actors, or otherwise decide what these things should be called

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
                 init-obs-type
                 init-unobs-type
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
    (define initial-tuple
      ;; TODO: get the max depth from somewhere
      (list (α-config initial-prog-config 10)
            (aps#-α-z initial-spec-instance)
            init-obs-type
            init-unobs-type))
    (let loop ([to-visit (queue initial-tuple)]
               [visited (set)])
      (cond
        [(queue-empty? to-visit) #t]
        [else
         (define current-tuple (dequeue! to-visit))
         (cond
           [(set-member? visited current-tuple)
            (loop to-visit visited)]
           [else
            ;; TODO: rename this function. A better name will help me with the general terminology
            ;; with which I describe my technique
            (match-define (list prog spec obs-type unobs-type) current-tuple)
            ;; TODO: rename this idea of transition: there's some other "thing" that this is, like a
            ;; transmission result. Define this data definition in the code somewhere, because it
            ;; should really be a type (it's a new kind of data in my domain that needs to be defined
            ;; and named)
            (define possible-transitions
              (append (transitions-from-message-of-type prog obs-type #t)
                      (transitions-from-message-of-type prog unobs-type #f)))
            (for ([possible-transition possible-transitions])
              (match (find-matching-spec-transition possible-transition spec state-matches)
                [(list)
                 ;; (printf "couldn't find any match for ~s\n" possible-transition)
                 (return-early #f)]
                [(list spec-goto-exp)
                 (enqueue! to-visit
                           (list (step-prog-final-behavior prog (csa#-transition-behavior-exp possible-transition))
                                 (step-spec-with-goto spec spec-goto-exp)
                                 ;; TODO: allow these types to change over time
                                 obs-type
                                 unobs-type))]
                [_ (error "too many possible matches") ;; TODO: call a continuation instead
                   ]))
            (loop to-visit (set-add visited current-tuple))])]))))

;; TODO: I probably need some canonical representation of program and spec configs so that otherwise
;; equivalent configs are not considered different by the worklist algorithm

;; TODO: adjust this function to allow for multiple possible actors
;;
;; Returns all possible transitions of the given program config caused by a received message to the of the
;; given type
(define (transitions-from-message-of-type prog-config type observed?)
  (define the-actor (csa#-config-only-actor prog-config))
  (for/fold ([transitions-so-far null])
            ;; TODO: get the max depth from somewhere
            ([message (generate-abstract-messages type (csa#-actor-current-state the-actor) 10 observed?)])
    (define eval-results (csa#-eval-transition prog-config (csa#-actor-address the-actor) message))
    (define new-transitions
      (for/list ([result eval-results])
        (match-define (list behavior-exp outputs) result)
        (csa#-transition message observed? outputs behavior-exp)))
    (append transitions-so-far new-transitions)))

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
     (cons (aps#-null-transition spec-instance) (aps#-current-transitions spec-instance))))
  (filter values match-results))

;; Prog-trans is the above struct, spec-trans is the syntax of the expression
;;
;; Returns #f for no match, or the spec's goto expression with prog values if there is a match
;;
;; TODO: test this function
(define (prog-transition-matches-spec-transition? prog-trans spec-trans state-matches)

  ;; TODO: have this function return some kind of message/information about what went wrong

  ;; TODO: rename this function, because it's not just a predicate: returns something other than #t
  (let/cc return-early
   (define valid-substitutions
     (cond
       [(and (csa#-transition-observed? prog-trans) (aps#-transition-observed? spec-trans))
        (aps#-match (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))]
       [(and (not (csa#-transition-observed? prog-trans)) (not (aps#-transition-observed? spec-trans)))
        (list (list))]
       [else (return-early #f)]))
     ;; (printf "Checking value ~s against pattern ~s\n" (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
   (match valid-substitutions
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
      (if (and (outputs-match-commitments? (filter csa#-observable-output? (csa#-transition-outputs prog-trans)) commitments)
               (equal? (hash-ref state-matches (csa#-transition-next-state prog-trans))
                       (aps#-goto-state spec-goto)))
          spec-goto
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
            (send response-dest (variant Ack 0))
            (goto Always response-dest))))
       (goto Always ,static-response-address)))))
  (define static-double-response-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always response-dest) (m)
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

  (check-not-false (redex-match csa-eval αn static-response-agent))
  (check-not-false (redex-match csa-eval αn static-double-response-agent))
  (check-not-false (redex-match aps-eval z static-response-spec))

  (check-true (analyze (make-single-agent-config static-response-agent)
                       static-response-spec
                       (term Nat) (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config static-response-agent)
                        ignore-all-spec-instance
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
      (((define-state (Always r) (m)
          (case m
            [A x (begin (send r (variant A x)) (goto Always r))]
            [B y (begin (send r (variant B 0)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define reverse-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always r) (m)
          (case m
            [A x (begin (send r (variant B 0)) (goto Always r))]
            [B y (begin (send r (variant A y)) (goto Always r))])))
       (goto Always ,static-response-address)))))

  (define partial-pattern-matching-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Always r) (m)
          (case m
            [A x (begin (send r (variant A 0)) (goto Always r))]
            [B y (goto Always r)])))
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
         [* -> (with-outputs ([r (variant Zero *)])    (goto S1 r))]
         [* -> (with-outputs ([r (variant NonZero *)]) (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define zero-spec
    (term
     (((define-state (S1 r)
         [* -> (with-outputs ([r (variant Zero *)])    (goto S1 r))]))
      (goto S1 ,static-response-address)
      ,single-agent-concrete-addr)))
  (define primitive-branch-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (S1 dest) (i)
          (begin
            (case (< 0 i)
              [True dummy (send dest (variant NonZero 0))]
              [False dummy (send dest (variant Zero 0))])
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

  (check-true (analyze (make-single-agent-config div-by-one-agent) nat-to-nat-spec (term Nat) (term (Union)) (hash 'Always 'Always)))
  (check-true (analyze (make-single-agent-config div-by-zero-agent) nat-to-nat-spec (term Nat) (term (Union)) (hash 'Always 'Always)))

  ;;;; Unobservable communication

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
              [* -> (with-outputs ([r (variant TurningOn *)]) (goto On r))])
            (define-state (On r)
              [* -> (goto On r)]
              [unobs -> (with-outputs ([r (variant TurningOff *)]) (goto Off r))]))
           (goto Off ,static-response-address)
           ,single-agent-concrete-addr)))
  (define unobs-toggle-agent
    (term
     (,single-agent-concrete-addr
      (((define-state (Off r) (m)
          (case m
            [FromObserver dummy
             (begin
               (send r (variant TurningOn 0))
               (goto On r))]
            [FromUnobservedEnvironment dummy (goto Off r)]))
        (define-state (On r) (m)
          (case m
            [FromObserver dummy (goto On r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOff 0))
               (goto Off r))])))
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong1
    (term
     (,single-agent-concrete-addr
      (((define-state (Off r) (m)
          (case m
            [FromObserver dummy
             (begin
               (send r (variant TurningOn 0))
               ;; Going to Off instead of On
               (goto Off r))]
            [FromUnobservedEnvironment dummy (goto Off r)]))
        (define-state (On r) (m)
          (case m
            [FromObserver dummy (goto On r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOff 0))
               (goto Off r))])))
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong2
    (term
     (,single-agent-concrete-addr
      (((define-state (Off r) (m)
          (case m
            [FromObserver dummy
             (begin
               (send r (variant TurningOn 0))
               (goto On r))]
            [FromUnobservedEnvironment dummy (goto On r)]))
        (define-state (On r) (m)
          (case m
            [FromObserver dummy (goto On r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOff 0))
               (goto Off r))])))
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong3
    (term
     (,single-agent-concrete-addr
      (((define-state (Off r) (m)
          (case m
            [FromObserver dummy
             (begin
               (send r (variant TurningOn 0))
               (goto On r))]
            [FromUnobservedEnvironment dummy (goto Off r)]))
        (define-state (On r) (m)
          (case m
            [FromObserver dummy (goto On r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOff 0))
               (goto On r))])))
       (goto Off ,static-response-address)))))
  (define unobs-toggle-agent-wrong4
    (term
     (,single-agent-concrete-addr
      (((define-state (Off r) (m)
          (case m
            [FromObserver dummy (goto Off r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOn 0))
               (goto On r))]))
        (define-state (On r) (m)
          (case m
            [FromObserver dummy (goto On r)]
            [FromUnobservedEnvironment dummy
             (begin
               (send r (variant TurningOff 0))
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
                       (term (Union [FromObserver Nat]))
                       (term (Union [FromUnobservedEnvironment Nat]))
                       (hash 'On 'On 'Off 'Off)))

  (for ([agent (list unobs-toggle-agent-wrong1
                     unobs-toggle-agent-wrong2
                     unobs-toggle-agent-wrong3
                     unobs-toggle-agent-wrong4)])
    (check-false (analyze (make-single-agent-config agent)
                          unobs-toggle-spec
                          (term (Union [FromObserver Nat]))
                          (term (Union [FromUnobservedEnvironment Nat]))
                          (hash 'On 'On 'Off 'Off))))

  ;;;; Records

  (define record-req-resp-spec
    (term
     (((define-state (Always)
         [(record [dest dest] [msg (variant A *)]) -> (with-outputs ([dest (variant A *)]) (goto Always))]
         [(record [dest dest] [msg (variant B *)]) -> (with-outputs ([dest (variant B *)]) (goto Always))]))
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
            (send (: m dest) (variant A 0))
            (goto Always))))
       (goto Always)))))

  (check-not-false (redex-match aps-eval z record-req-resp-spec))
  (check-not-false (redex-match csa-eval αn record-req-resp-agent))
  (check-not-false (redex-match csa-eval αn record-req-wrong-resp-agent))

  ;; TODO: figure out why this test fails when max-depth for the program and the messages is set to
  ;; 0
  (check-true (analyze (make-single-agent-config record-req-resp-agent)
                       record-req-resp-spec
                       (term (Record [dest (Addr (Union [A Nat] [B Nat]))] [msg (Union [A Nat] [B Nat])]))
                       (term (Union))
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config record-req-wrong-resp-agent)
                        record-req-resp-spec
                        (term (Record [dest (Addr (Union [A Nat] [B Nat]))] [msg (Union [A Nat] [B Nat])]))
                        (term (Union))
                        (hash 'Always 'Always))))
