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
 redex/reduction-semantics
 "queue-helpers.rkt"
 "aps-abstract.rkt"
 "csa-abstract.rkt"
 "csa-helpers.rkt")

;; TODO: take the dependency on Redex out of this file

;; TODO: test 1: the actor that just loops on itself conforms to the spec that does the same thing
;; (all observable actions)

(struct spec-config (instances commitments))

;; TODO: make this handle full configs, not just a single spec instance and agent instance

;; TODO: rename "analyze" to something like "check" or "verify" or "model-check"

;; TODO: test this method separately, apart from the idea of visiting a transition (just check the BFS
;; implementation

;; TODO: add an initial mapping between the program and the spec (maybe? might need new definition of
;; conformance for that)

;; Given a concrete program configuration, a concrete specification configuration, and a list of pairs
;; that specify the expected prog-state/spec-state matches, returns #t if the conformance check
;; algorithm can prove conformance, #f otherwise.
;;
;; NOTE: this currently handles only programs consisting of a single actor that does not spawn other
;; actors. Also assumes that the spec starts in a state in which it has no state parameters.
(define (analyze initial-prog-config initial-spec-instance state-matches)
  ;; TODO: to-visit is now an imperative queue, so probably shouldn't use it as a loop parameter
  (let loop ([to-visit (queue (cons (α-config initial-prog-config) initial-spec-instance))]
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
          (define the-actor (config-only-actor prog))
          ;; TODO: rename this idea of transition: there's some other "thing" that this is, like a
          ;; transmission result. Define this data definition in the code somewhere, because it should
          ;; really be a type (it's a new kind of data in my domain that needs to be defined and
          ;; named)
          (define possible-transitions
            ;; TODO: figure out where to abstract the addresses
            ;; TODO: get the max depth from somewhere
            (for/fold ([eval-results null])
                      ([message (generate-abstract-messages (actor-message-type the-actor) (actor-current-state the-actor) 0)])
              (append eval-results (csa#-eval-transition prog (actor-address the-actor) message))))
          (for ([possible-transition possible-transitions])
            (match (find-matching-spec-transition possible-transition spec state-matches)
              [(list) (error "couldn't find any match") ;; TODO: call a continuation to return #f here instead
               ]
              [(list spec-goto-exp)
               (enqueue! to-visit
                         (cons (step-prog-with-goto prog (program-transition-goto-exp possible-transition))
                               (step-spec-with-goto spec spec-goto-exp)))]
              [_ (error "too many possible matches") ;; TODO: call a continuation instead
                 ]))
          (loop to-visit (set-add visited next-pair))])])))

;; TODO: hide this function in a separate module and make it less susceptible to breaking because of changes in the config's structure
(define (step-prog-with-goto prog-config goto-exp)
  (redex-let csa# ([(((SINGLE-ACTOR-ADDR (τ (S# ...) _)))
                     ()
                     (SINGLE-ACTOR-ADDR)
                     ;; TODO: update χ# or just get rid of it
                     ())
                    prog-config])
             (term
              (((SINGLE-ACTOR-ADDR (τ (S# ...) ,goto-exp)))
               ()
               (SINGLE-ACTOR-ADDR)
               ;; TODO: update χ# or just get rid of it
               ()))))

(define (step-spec-with-goto spec-instance goto-exp)
  (redex-let aps# ([((S-hat ...) _ σ) spec-instance])
             (term ((S-hat ...) ,goto-exp σ))))

;; TODO: I probably need some canonical representation of program and spec configs so that otherwise
;; equivalent configs are not considered different by the worklist algorithm

;; NOTE: only supports spec configs with a single actor/spec
;;
;; Given a program transition, the current spec config, and the hash table mapping prog states to spec
;; states, returns the list of spec gotos for all possible matching transitions
(define (find-matching-spec-transition prog-transition spec-instance state-matches)
  (define match-results
    (map
     (lambda (spec-transition)
       (prog-transition-matches-spec-transition? prog-transition spec-transition state-matches))
     (aps#-current-transitions spec-instance)))
  (filter values match-results))

;; Prog-trans is the above struct, spec-trans is the syntax of the expression
;;
;; Returns #f for no match, or the spec's goto expression with prog values if there is a match
(define (prog-transition-matches-spec-transition? prog-trans spec-trans state-matches)
  ;; so, prog transition must have: message received, obs vs unobs, outputs, and the goto
  (redex-let aps# ([(p_spec-pat -> e-hat) spec-trans])
             ;; 1. Check pattern vs. received message
             ;; TODO: check for obs vs. unobs
    (match (csa#-match (program-transition-message prog-trans) (term p_spec-pat))
      [(list)
       ;; No matches, so the whole predicate fails
       (printf "Found no matches for received message ~s to pattern ~s\n" (program-transition-message prog-trans) (term p_spec-pat))
       #f]
      [(list subst1 subst2 subst-rest ...)
       (error "too many matches for value ~s and pattern ~s" (program-transition-message prog-trans) (term p_spec-pat))]
      [(list some-subst)
       (redex-let* aps#
                   ([([x a#ext] ...) some-subst]
                    [e-hat (term (subst-n/aps# e-hat (x a#ext) ...))]
                    [((goto s_spec v# ...) ([a#ext po] ...)) (aps#-eval (term e-hat))])
                   ;; 2. Check outputs (check each prog output aginst commitments and check there are
                   ;; no commitments left)
                   ;;
                   ;; NOTE: this does not check for multiple possible ways to match the outputs
                   (let ([unmatched-commitments
                          (for/fold ([remaining-commitments (term ([a#ext po] ...))])
                                    ([output (program-transition-outputs prog-trans)])
                            ;; TODO: test this function separately
                            (define (satisfied? commitment)
                              (redex-let aps# ([[a#ext_prog v#] output]
                                               [[a#ext_spec po] commitment]
                                               )
                                         (and (equal? (term a#ext_prog) (term a#ext_spec))
                                              (aps-matches-po? (term v#) (term po)))))
                            (match (findf satisfied? remaining-commitments)
                              ;; TODO: figure out how to deal with addresses that are precisely abstracted but not observed by the spec
                              [#f (error "No match for output in the commitments")]
                              [commitment (remove commitment remaining-commitments)]))])
                     (match unmatched-commitments
                       [(list c1 c-rest ...)
                        (displayln "Found unmatched commitments")
                        #f]
                       [_
                        ;; 3. Check the gotos (annotated)
                        (redex-let aps# ([(in-hole E# (goto s_prog _ ...)) (program-transition-goto-exp prog-trans)])
                                   (if (equal? (hash-ref state-matches (term s_prog)) (term s_spec))
                                       ;; 4. Return transitioned spec config
                                       (term (goto s_spec v# ...))
                                       (begin
                                         (printf "State names didn't match: ~s ~s ~s\n" (term s_prog) (hash-ref state-matches (term s_prog)) (term s_spec))
                                         #f)))])))])))

;; TODO: tests for the above transition matching predicates/search functions

(define pattern-group-pattern car)
(define pattern-group-exps cadr)

;; Returns #f if any of prog's immediate transitions violate conformance to spec (by sending/failing
;; to send some message); otherwise, it returns the list of program/specification configuration pairs
;; remaining to check to prove conformance for the given pair. This is the "visit" method for our
;; graph search algorithm.
;;
;; prog: program configuration
;; spec: specification configuration
;; (define (check-immediate-transitions prog spec)
;;   ;; Gather all possible inputs according to the spec (including non-specified ones) and run each one
;;   ;; abstractly through the handler. For each result, check if it satisfies a transition, and add the
;;   ;; next state to the to-visit queue if it's not there already (or add it anyway, I think...)

;;   ;; TODO: deal with commitments from previous transitions

;;   ;; TODO: figure out the actual source of input patterns here
;;   ;; TODO: also process the unobserved patterns
;;   (for/fold ([next-state-pairs null])
;;             ([input-pattern-group (spec-input-pattern-groups spec)]
;;              #:break (not next-state-pairs))
;;     ;; (printf "group: ~s\n" input-pattern-group)
;;     ;; TODO: add in the real address and message here

;;     (for/fold ([next-state-pairs null])
;;               ;; TODO: change the address and message here to be *real* values
;;               ([result-config (handle-message prog '(addr 1) ''sample-value)]
;;                ;; [result-config (handle-message prog '(addr 1) (pattern-group-pattern input-pattern-group))]
;;                #:break (not next-state-pairs))

;;       ;; Check all of its outputs and see if it matches *some* transition

;;       ;; TODO: check that we're not in a stuck state (or maybe I just do this ahead of time with a
;;       ;; type-system-like thing

;;       ;; TODO: add primitive predicates to match patterns to check if something is an address, a
;;       ;; symbol, a number, or some other primitive

;;       ;; TODO: check each result to see if it matches a spec transition, and if so, add the next
;;       ;; state to the to-visit list

;;       ;; TODO: change this code to account for more than one possible transition
;;       ;;
;;       ;; TODO: change this code to allow for multiple possible ways to match the outputs against the
;;       ;; available commitments
;;       (match-define (list external-packets wiped-config) (extract-external-sends result-config))
;;       ;; TODO: deal with spec instance addresses communicated to the outside world

;;       ;; Returns the list of commitments still unsatisfied in the spec
;;       (define possible-transitions (pattern-group-exps input-pattern-group))
;;       (define match-results (match-sends-to-commitments external-packets possible-transitions))
;;       ;; TODO: remove this debug line and inline match-results definition
;;       ;; (printf "match results: ~s\n" match-results)
;;       (match match-results
;;         [#f #f] ; if matching up the outputs failed, then the whole transition definitely fails
;;         [(list)
;;          ;; TODO: get the list of new state pairs that we've transitioned to and now want to check
;;          (list)]
;;         ;; TODO: find a way to check on the commitments that aren't immediately satisfied
;;         [_ #f]))))

;; Returns #f if any of the given message packets does not have a matching commitment in the given
;; transitions; otherwise, returns the list of remaining (unmatched) commitments.
;; (define (match-sends-to-commitments external-packets possible-transitions)

;;   ;; TODO: make this handle more than 1 possible transition in the spec (may require a constraint
;;   ;; solver instead of BFS, to allow for backtracking)

;;   ;; TODO: make this handle all possible orderings of matches

;;   ;; TODO: make this work with abstract address values

;;   ;; TODO: make this allow for unobserved communication

;;   ;; TODO: also get the pre-existing commitments from the spec config

;;   ;; TODO: figure out what to do when the spec is mal-formed and doesn't give us a proper list of
;;   ;; commitments

;;   ;; (printf "external packets: ~s\n" external-packets)
;;   ;; (printf "commitments: ~s\n" (get-spec-commitments (car possible-transitions)))
;;   (define-values (conformance-violated? remaining-commitments)
;;     (for/fold ([conformance-violated? #f]
;;                [remaining-commitments (get-spec-commitments (car possible-transitions))])
;;         ([packet external-packets]
;;          #:break conformance-violated?)
;;       (match-define `(,packet-address <= ,packet-message) packet)
;;       ;; (printf "address: ~s, message: ~s\n" packet-address packet-message)
;;       (match (findf
;;               (lambda (commitment)
;;                 (match-define `(,commitment-address ,pattern) commitment)
;;                 ;; (printf "commitment address: ~s, pattern: ~s\n" commitment-address pattern)

;;                 ;; TODO: make pattern matching also do the variable-binding thing
;;                 (and (equal? commitment-address packet-address)
;;                      (matches-output-pattern? packet-message pattern)))
;;               remaining-commitments)
;;         [#f (values #t remaining-commitments)]
;;         [pattern (values #f (remove pattern remaining-commitments))])))

;;   (if conformance-violated? #f remaining-commitments))

;; TODO: write tests for analyze-state-pair-transitions

(module+ test
  (require rackunit
           redex/reduction-semantics
           csa/model

           ;; also run the submodule tests here
           ;; TODO: remove these?
           ;; (submod ".." language-eval test)
           ;; (submod ".." spec-eval test)
           )

  (define ignore-all-agent
    '(SINGLE-ACTOR-ADDR
      (Nat
       ((define-state (Always) (m) (goto Always)))
       (goto Always))))
  (define ignore-all-config (make-single-agent-config ignore-all-agent))
  (define ignore-all-spec-instance
    '(((define-state (Always) [* -> (goto Always)]))
      (goto Always)
      SINGLE-ACTOR-ADDR))

  (check-not-false (redex-match csa# α#n ignore-all-agent))
  (check-not-false (redex-match csa# K# ignore-all-config))
  (check-not-false (redex-match aps# z ignore-all-spec-instance))

  ;; TODO: supply concrete specs and programs to the checker, not abstract ones
  (check-true (analyze ignore-all-config ignore-all-spec-instance (hash 'Always 'Always)))

  ;; TODO: remove the redundancy between the state defs and the current expression
  (define static-response-agent
    `((addr 1)
      (((define-state (Always response-dest) (m)
          (begin
            (send response-dest 'ack)
            (goto Always response-dest))))
       (rcv (m)
         (begin
           (send (addr 2) 'ack)
           (goto Always (addr 2)))))))
  (define static-double-response-agent
    `((addr 1)
      (((define-state (Always response-dest) (m)
          (begin
            (send response-dest 'ack)
            (send response-dest 'ack)
            (goto Always response-dest))))
       (rcv (m)
         (begin
           (send (addr 2) 'ack)
           (send (addr 2) 'ack)
           (goto Always (addr 2)))))))
  (define static-response-spec
    '(((define-state (Always response-dest)
         [* -> (with-outputs ([response-dest *]) (goto Always response-dest))]))
      (goto Always (addr 2))
      (addr 1)))

  (check-not-false (redex-match csa-eval (a ((S ...) e)) static-response-agent))
  (check-not-false (redex-match csa-eval (a ((S ...) e)) static-double-response-agent))
  (check-not-false (redex-match aps-eval z static-response-spec))

  ;; (check-true (analyze (make-single-agent-config static-response-agent) static-response-spec))

  ;; all 3 of these fail; let's check double/single first
  ;; (check-false (analyze (make-single-agent-config static-response-agent) ignore-all-spec-instance))
  ;; (check-false (analyze (make-single-agent-config static-double-response-agent) static-response-spec))
  ;; (check-false (analyze ignore-all-config static-response-spec))

  ;; Pattern matching tests, without dynamic channels
  ;; TODO: uncomment and implement the stuff for these tests
  ;; (define pattern-match-spec
  ;;   '(((define-state (Matching r)
  ;;        ['a -> (with-outputs ([r 'a]) (goto Matching r))]
  ;;        [(list 'b *) -> (with-outputs ([r (list 'b *)]) (goto Matching r))]))
  ;;     (goto Matching (addr 2))
  ;;     (addr 1)))

  ;; (define pattern-matching-agent
  ;;   '((addr 1)
  ;;     (((define-state (Always r) (m)
  ;;         (match m
  ;;           ['a (begin (send r 'a) (goto Always r))]
  ;;           [(list 'b *) (begin (send r (list 'b *)) (goto Always r))]
  ;;           [_ (goto Always r)])))
  ;;      (rcv (m)
  ;;           (match m
  ;;           ['a (begin (send (addr 2) 'a) (goto Always (addr 2)))]
  ;;           [(list 'b *) (begin (send (addr 2) (list 'b *)) (goto Always (addr 2)))]
  ;;           [_ (goto Always (addr 2))])))))

  ;; (define reverse-pattern-matching-agent
  ;;   '((addr 1)
  ;;     (((define-state (Always r) (m)
  ;;         (match m
  ;;           ['a (begin (send r (list 'b *)) (goto Always r))]
  ;;           [(list 'b *) (begin (send r 'a) (goto Always r))]
  ;;           [_ (goto Always r)])))
  ;;      (rcv (m)
  ;;           (match m
  ;;           ['a (begin (send (addr 2) (list 'b *)) (goto Always (addr 2)))]
  ;;           [(list 'b *) (begin (send (addr 2) 'a) (goto Always (addr 2)))]
  ;;           [_ (goto Always (addr 2))])))))

  ;; (define partial-pattern-matching-agent
  ;;   '((addr 1)
  ;;     (((define-state (Always r) (m)
  ;;         (match m
  ;;           ['a (begin (send r 'a) (goto Always r))]
  ;;           [(list 'b *) (goto Always r)]
  ;;           [_ (goto Always r)])))
  ;;      (rcv (m)
  ;;           (match m
  ;;           ['a (begin (send (addr 2) 'a) (goto Always (addr 2)))]
  ;;           [(list 'b *) (goto Always (addr 2))]
  ;;           [_ (goto Always (addr 2))])))))
  ;;
  ;; (check-true (analyze (make-single-agent-config pattern-matching-agent) pattern-match-spec))
  ;; (check-false (analyze (make-single-agent-config partial-pattern-matching-agent) pattern-match-spec))
  ;; (check-false (analyze (make-single-agent-config reverse-pattern-matching-agent) pattern-match-spec))

  ;; TODO: make these *concrete* things, not abstracted ones
  (define request-response-spec
    '(((define-state (Always)
         [response-target -> (with-outputs ([response-target *]) (goto Always))]))
      (goto Always)
      SINGLE-ACTOR-ADDR))
  (define request-response-agent
    `(SINGLE-ACTOR-ADDR
      ((Addr Nat)
       ((define-state (Always) (response-target)
          (begin
            (send response-target (* Nat))
            (goto Always))))
       (goto Always))))
  (define respond-to-first-addr-agent
    `(SINGLE-ACTOR-ADDR
      ((Addr Nat)
       ((define-state (Init) (response-target)
          (begin
            (send response-target (* Nat))
            (goto HaveAddr response-target)))
        (define-state (HaveAddr response-target) (new-response-target)
          (begin
            (send response-target (* Nat))
            ;; TODO: also try the case where we save new-response-target instead
            (goto HaveAddr response-target))))
       (goto Always))))
  ;; (define static-double-response-agent
  ;;   `((addr 1)
  ;;     (((define-state (Always response-dest) (m)
  ;;         (begin
  ;;           (send response-dest 'ack)
  ;;           (send response-dest 'ack)
  ;;           (goto Always response-dest))))
  ;;      (rcv (m)
  ;;        (begin
  ;;          (send (addr 2) 'ack)
  ;;          (send (addr 2) 'ack)
  ;;          (goto Always (addr 2)))))))

  ;; (check-not-false (redex-match csa# (a# (τ (S# ...) e#)) ignore-all-agent))
  ;; (check-not-false (redex-match csa# K# ignore-all-config))
  (check-not-false (redex-match aps# z request-response-spec))
  (check-not-false (redex-match csa# α#n request-response-agent))
  (check-not-false (redex-match csa# α#n respond-to-first-addr-agent))

  (check-true (analyze (make-single-agent-config request-response-agent)
                       request-response-spec
                       (hash 'Always 'Always)))
  ;; TODO: uncomment this test
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent)
                        request-response-spec
                        (hash 'Init 'Always 'HaveAddr 'Always)))

  ;; TODO: write a test where the unobs input messages for pattern matching matter

  ;; TODO: test 2: program outputs on static observable channel, spec does not
  ;; TODO: test 3: spec outputs, program does not
  ;; TODO: test 4: program and spec output
  ;; TODO: test 5: spec requires an output to provided channel
  ;; TODO: test 6: stuck state in program (e.g. something that doesn't type-check)
  )

;; ---------------------------------------------------------------------------------------------------
;; Language evaluation forms

(module language-eval racket
  (require redex/reduction-semantics
           csa/model)
  (provide handle-message
           extract-external-sends)


  ;; Injects the given message into the config and runs the appropriate handler for it to completion,
  ;; returning all possible resulting configurationsn
  (define (handle-message prog-config address message)
    ;; TODO: check for all items matching their shape (make a contract and do a contract-out thing
    ;; TODO: check that the returned thing is in a goto/rcv state?
    ;; (printf "matching: ~s, ~s, ~s\n" (redex-match csa-eval K prog-config)
    ;;         (redex-match csa-eval a address)
    ;;         (redex-match csa-eval v message)
    ;;         )
    ;; (printf "config: ~s\n" prog-config)

    (apply-reduction-relation* handler-step (term (inject-message ,prog-config ,address ,message))))
  ;; TODO: use this version instead (from stash)
    ;; (apply-reduction-relation* handler-step# (term (inject-message ,prog-config ,address ,message))))

  ;; TODO: define this method
  ;;
  ;; Returns a 2-tuple of the list of address/value pairs for message packets destined for external
  ;; addresses, and the config with those message packets removed
  ;;
  ;; TODO: what if we don't know if the message is destined to be external or internal, or even
  ;; observable or not?
  (define (extract-external-sends config)
    ;; (printf "external config: ~s\n" config)
    (term (extract-external-sends/mf ,config)))

  (define-metafunction csa-eval
    extract-external-sends/mf : K -> ((m ...) K)
    [(extract-external-sends/mf (α μ ρ χ))
     (μ_external (α μ_internal ρ χ))
     (where μ_external ,(filter (curryr external-packet? (term χ)) (term μ)))
     (where μ_internal ,(filter (negate (curryr external-packet? (term χ))) (term μ)))])

  ;; TODO: write tests for exttract-external-sends

  ;; TODO: think about writing the nice Redex additions so that extract-external-sends isn't such a
  ;; pain

  (define (external-packet? packet externals)
    (term (external-packet?/mf ,packet ,externals)))

  ;; Returns true if the packet is destined for one of the external addresses; false otherwise
  (define-metafunction csa-eval
    external-packet?/mf : m χ -> boolean
    [(external-packet?/mf (a <= _) (_ ... a _ ...)) #t]
    [(external-packet?/mf _ _) #f])

  (module+ test
    (require rackunit)
    (check-false (external-packet? (term ((addr 1) <= 'a)) (term ())))
    (check-true  (external-packet? (term ((addr 1) <= 'a)) (term ((addr 1)))))
    (check-false (external-packet? (term ((addr 1) <= 'a)) (term ((addr 2)))))
    (check-true  (external-packet? (term ((addr 1) <= 'a)) (term ((addr 1) (addr 2)))))
    (check-false (external-packet? (term ((addr 1) <= 'a)) (term ((addr 3) (addr 2))))))

  ;; (define handler-step#
  ;;   (reduction-relation csa#
  ;;    #:domain K#
  ;;    (--> (in-hole A# (a# ((S# ...) (in-hole E (goto s v# ..._n)))))
  ;;         (in-hole A# (a# ((S# ...) (rcv (x_h) (subst-n e# (x_s v#) ...)))))
  ;;         (where (_ ... (define-state (s x_s ..._n) (x_h) e#) _ ...) (S# ...))
  ;;         Goto)
  ;;    ;; TODO: extend subst-n to work on the abstract language

  ;;    ;; TODO: goto with timeout

  ;;    ;; let, match, begin, send, goto
  ;;    (==> (begin v# e# e#_rest ...)
  ;;         (begin e# e#_rest ...)
  ;;         Begin1)
  ;;    (==> (begin v#)
  ;;         v#
  ;;         Begin2)

  ;;    ;; TODO: do the ρ/χ updates
  ;;    (--> ((any_a1 ... (a# ((S# ...) (in-hole E# (send a#_2 v#)))) any_a2 ...)
  ;;          (any_packets ...)
  ;;          ρ χ)
  ;;         ((any_a1 ... (a# ((S# ...) (in-hole E# v#)))            any_a2 ...)
  ;;          (any_packets ... (a#_2 <= v#)) ; TODO: figure out how to do send rule here...
  ;;          ρ χ)
  ;;         Send)

  ;;    ;; TODO: let
  ;;    ;; TODO: match

  ;;    with
  ;;    [(--> (in-hole A (a# ((S# ...) (in-hole E# e#_old))))
  ;;          (in-hole A (a# ((S# ...) (in-hole E# e#_new)))))
  ;;     (==> e#_old e#_new)]))
)

(require 'language-eval)

;; ---------------------------------------------------------------------------------------------------
;; Spec evaluation forms (maybe merge into previous section?

(module spec-eval racket

  (provide spec-input-pattern-groups
           matches-output-pattern?
           get-spec-commitments)

    (require redex/reduction-semantics
           csa/model)

  ;; Returns the transitions of the spec instance's current state with the state parameters
  ;; substituted in, grouped by input pattern
  (define (spec-input-pattern-groups instance)
    (term (spec-input-pattern-groups/mf ,instance)))

  (define-metafunction aps-eval
    spec-input-pattern-groups/mf : z -> ((p (e-hat ...)) ...)
    [(spec-input-pattern-groups/mf ((_ ... (define-state (s x ...) (ε -> e-hat) ...) _ ...) (goto s a ...) _))
     (spec-input-pattern-groups/acc ((ε -> (subst-n/aps e-hat (x a) ...)) ...) ())])

  ;; Inserts the given transitions (except the unobs ones) into the given pattern/expression grouping
  (define-metafunction aps-eval
    spec-input-pattern-groups/acc : ((ε -> e-hat) ...) ((p (e-hat ...)) ...) -> ((p (e-hat ...)) ...)
    [(spec-input-pattern-groups/acc () any_grouping) any_grouping]
    [(spec-input-pattern-groups/acc ((unobs -> e-hat) any_transitions ...) any_grouping)
     (spec-input-pattern-groups/acc (any_transitions ...) any_grouping)]
    ;; pattern with an existing group
    [(spec-input-pattern-groups/acc ((p -> e-hat) any_transitions ...) (any_group1 ... (p (any_e-hat ...)) any_group2 ...))
     (spec-input-pattern-groups/acc (any_transitions ...) (any_group1 ... (p (any_e-hat ... e-hat)) any_group2 ...))]
    ;; pattern without an existing group
    [(spec-input-pattern-groups/acc ((p -> e-hat) any_transitions ...) (any_group ...))
     (spec-input-pattern-groups/acc (any_transitions ...) (any_group ... (p (e-hat))))])

  ;; Returns a list of the distinct (i.e. no repeats) patterns specified in the spec-config's current
  ;; state
  (define (spec-input-patterns spec-config)
    (term (spec-input-patterns/mf ,spec-config)))

  (define-metafunction aps-eval
    spec-input-patterns/mf : z -> (p ...)
    [(spec-input-patterns/mf ((_ ... (define-state (s _ ...) [ε _ ...] ...) _ ...) (goto s _ ...) _))
     ,(set->list (list->set (term (p ...))))
     (where (p ...) (filter-patterns-from-events ε ...))])

  ;; Returns the list of all patterns (i.e. non-unobs triggers) in the given transitions, including
  ;; duplicates
  (define-metafunction aps-eval
    filter-patterns-from-events : ε ... -> (p ...)
    [(filter-patterns-from-events p any ...)
     (p p_rest ...)
     (where (p_rest ...) (filter-patterns-from-events any ...))]
    [(filter-patterns-from-events unobs any ...)
     (filter-patterns-from-events any ...)]
    [(filter-patterns-from-events) ()])

  ;; Returns the list of commitments generated by the given spec expression
  (define (get-spec-commitments e)
    (match (apply-reduction-relation* spec-step `(,e ()))
      [(list `((goto ,_ ...) ,commitments))
       commitments]))

  ;; TODO: deprecate this code
  ;; (module+ test
  ;;   (check-equal? (get-spec-commitments (term (goto S1))) null)
  ;;   (check-equal? (get-spec-commitments (term (with-outputs ([(addr 1) *] [(addr 2) 't]) (goto S1))))
  ;;                 (list (term [(addr 1) *]) (term [(addr 2) 't])))
  ;;   (check-equal? (get-spec-commitments
  ;;                  (term (with-outputs ([(addr 1) *] [(addr 2) 't])
  ;;                          (with-outputs ([(addr 3) *] [(addr 4) 't])
  ;;                            (goto S1)))))
  ;;                 (list (term [(addr 1) *])
  ;;                       (term [(addr 2) 't])
  ;;                       (term [(addr 3) *])
  ;;                       (term [(addr 4) 't]))))

  ;; TODO: deprecate this function; port the tests over
  (define (matches-output-pattern? value pattern)
    (term (matches-output-pattern?/mf ,value ,pattern)))

  (define-metafunction aps-eval
    matches-output-pattern?/mf : v po -> boolean
    [(matches-output-pattern?/mf _ *) #t]
    [(matches-output-pattern?/mf _ x) #t]
    ;; TODO: self
    [(matches-output-pattern?/mf t t) #t]
    [(matches-output-pattern?/mf (list v ..._n) (list po ..._n))
     ;; TODO: find a better way to normalize to boolean rather than not/not
     ,(andmap
       (lambda (v po) (term (matches-output-pattern?/mf ,v ,po)))
       (term (v ...))
       (term (po ...)))]
    [(matches-output-pattern?/mf _ _) #f])

  ;; TODO: deprecate this code, or something
  ;; (module+ test
  ;;   (check-true (matches-output-pattern? 42 '*))
  ;;   (check-true (matches-output-pattern? 42 'z))
  ;;   (check-true (matches-output-pattern? ''foo '*))
  ;;   (check-true (matches-output-pattern? ''foo 'foo))
  ;;   (check-false (matches-output-pattern? ''foo ''bar))
  ;;   (check-false (matches-output-pattern? 42 ''bar))
  ;;   (check-true (matches-output-pattern? '(list 42 'foo) '(list a *)))
  ;;   (check-false (matches-output-pattern? '(list 42 'foo) '(list 'bar *)))
  ;;   (check-false (matches-output-pattern? '(list 42 'foo) '(list * 'bar)))
  ;;   (check-false (matches-output-pattern? '(list 42 'foo) '(list 'a 'b))))

  (define spec-step
    (reduction-relation aps-eval
      #:domain (e-hat ((a po) ...))
      (--> ((with-outputs ([a po] ...) e-hat) (any_commits ...))
           (e-hat (any_commits ... [a po] ...)))))


  ;; TODO: deprecate this code, or something
  ;; (module+ test
  ;;   (require rackunit)

  ;;   ;; A check that succeeds if and only if each list does not contain duplicate members, and the two
  ;;   ;; lists have the same elements (possibly in different orders)
  ;;   (define-simple-check (check-same-distinct-members? l1 l2)
  ;;     (equal? (list->set l1) (list->set l2)))

  ;;   ;; no patterns
  ;;   ;; 2 distinct patterns
  ;;   ;; 2 similar patterns, 1 distinct
  ;;   ;; 2 different patterns, 2 other patterns in another state
  ;;   (check-same-distinct-members?
  ;;    (term (spec-input-patterns/mf
  ;;           (((define-state (S1))) (goto S1) null)))
  ;;    null)

  ;;   (check-same-distinct-members?
  ;;    (term (spec-input-patterns/mf
  ;;           (((define-state (S1)
  ;;               [(list 'a) -> (goto S1)]
  ;;               ['b -> (goto S1)]))
  ;;            (goto S1)
  ;;            null)))
  ;;    (list (term (list 'a)) (term 'b)))

  ;;   (check-same-distinct-members?
  ;;    (term (spec-input-patterns/mf
  ;;           (((define-state (S1)
  ;;               [(list 'a) -> (goto S1)]
  ;;               ['b -> (goto S1)]
  ;;               ['b -> (goto S2)]))
  ;;            (goto S1)
  ;;            null)))
  ;;    (list (term (list 'a)) (term 'b)))

  ;;   (check-same-distinct-members?
  ;;    (term (spec-input-patterns/mf
  ;;           (((define-state (S1)
  ;;               [(list 'a) -> (goto S1)]
  ;;               ['b -> (goto S1)])
  ;;             (define-state (S2)
  ;;               ['c -> (goto S1)] ['d -> (goto S1)]))
  ;;            (goto S1)
  ;;            null)))
  ;;    (list (term (list 'a)) (term 'b))))
  )

;; (require 'spec-eval)
