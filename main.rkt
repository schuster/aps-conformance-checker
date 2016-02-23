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
(define (analyze initial-prog-config initial-spec-instance state-matches)
  (let/cc return-early
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

  (match (csa#-match (csa#-transition-message prog-trans) (aps#-transition-pattern spec-trans))
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
  (and (equal? (csa#-output-address output) (aps#-commitment-address commitment))
       (aps#-matches-po? (csa#-output-message output) (aps#-commitment-pattern commitment))))

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
           "csa.rkt"

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
    ;; TODO: make these *concrete* things, not abstracted ones
  (define request-same-response-addr-spec
    '(((define-state (Init)
         [response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))])
       (define-state (HaveAddr response-target)
         [new-response-target -> (with-outputs ([response-target *]) (goto HaveAddr response-target))]))
      (goto Init)
      SINGLE-ACTOR-ADDR))
  (define request-response-agent/abstract
    `(SINGLE-ACTOR-ADDR
      ((Addr Nat)
       ((define-state (Always) (response-target)
          (begin
            (send response-target (* Nat))
            (goto Always))))
       (goto Always))))
  (define request-response-agent-concrete
    `(addr1234
      ((Addr Nat)
       ((define-state (Always i) (response-target)
          (begin
            (send response-target i)
            (goto Always (+ i 1)))))
       (goto Always))))
  (define respond-to-first-addr-agent/concrete
    `(addr4567
      ((Addr Nat)
       ((define-state (Init) (response-target)
          (begin
            (send response-target 0)
            (goto HaveAddr 1 response-target)))
        (define-state (HaveAddr i response-target) (new-response-target)
          (begin
            (send response-target i)
            ;; TODO: also try the case where we save new-response-target instead
            (goto HaveAddr (+ i 1) response-target))))
       (goto Init))))
    (define respond-to-first-addr-agent/abstract
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
       (goto Init))))
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
  (check-not-false (redex-match aps# z request-same-response-addr-spec))
  (check-not-false (redex-match csa# α#n request-response-agent/abstract))
  (check-not-false (redex-match csa# α#n respond-to-first-addr-agent/abstract))

  (check-true (analyze (make-single-agent-config request-response-agent/abstract)
                       request-response-spec
                       (hash 'Always 'Always)))
  (check-false (analyze (make-single-agent-config respond-to-first-addr-agent/abstract)
                        request-response-spec
                        (hash 'Init 'Always 'HaveAddr 'Always)))

  (check-false (analyze (make-single-agent-config request-response-agent/abstract)
                        request-same-response-addr-spec
                        (hash 'Always 'Init)))
  (check-true (analyze (make-single-agent-config respond-to-first-addr-agent/abstract)
                       request-same-response-addr-spec
                       (hash 'Init 'Init 'HaveAddr 'HaveAddr)))

  ;; TODO: write a test where the unobs input messages for pattern matching matter

  ;; TODO: test 2: program outputs on static observable channel, spec does not
  ;; TODO: test 3: spec outputs, program does not
  ;; TODO: test 4: program and spec output
  ;; TODO: test 5: spec requires an output to provided channel
  ;; TODO: test 6: stuck state in program (e.g. something that doesn't type-check)
  )
