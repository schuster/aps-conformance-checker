#lang racket

;; TODO: test 1: the actor that just loops on itself conforms to the spec that does the same thing
;; (all observable actions)

(struct spec-config (instances commitments))

;; TODO: probably avoid using these unofficial aliases
(define head car)
(define tail cdr)

;; TODO: make this handle full configs, not just a single spec instance and agent instance
;;
;; TODO: test this method separately, apart from the idea of visiting a transition (just check the BFS
;; implementation
(define (analyze initial-prog-config initial-spec-config)
  (let loop ([to-visit (list (cons initial-prog-config initial-spec-config))]
             [visited (set)])
    (cond
      [(empty? to-visit) #t]
      [(set-member? visited (head to-visit))
       (loop (tail to-visit) visited)]
      [else
       ;; TODO: rename this function. A better name will help me with the general terminology with
       ;; which I describe my technique
       (match-define (cons prog spec) (head to-visit))
       (match (check-immediate-transitions prog spec)
         [#f #f] ; if any state pair analysis fails, then the whole thing fails

         ;; TODO: figure out what it looks like here when we try all possible combinations of the
         ;; possible program/spec transition pairs. This currently assumes only one possible way to
         ;; match everything
         [(list new-pairs-to-visit ...)
          (loop (append new-pairs-to-visit (tail to-visit))
                (set-add visited (head to-visit)))])])))

(define pattern-group-pattern car)
(define pattern-group-exps cadr)

;; Returns #f if any of prog's immediate transitions violate conformance to spec (by sending/failing
;; to send some message); otherwise, it returns the list of program/specification configuration pairs
;; remaining to check to prove conformance for the given pair. This is the "visit" method for our
;; graph search algorithm.
;;
;; prog: program configuration
;; spec: specification configuration
(define (check-immediate-transitions prog spec)
  ;; Gather all possible inputs according to the spec (including non-specified ones) and run each one
  ;; abstractly through the handler. For each result, check if it satisfies a transition, and add the
  ;; next state to the to-visit queue if it's not there already (or add it anyway, I think...)

  ;; TODO: deal with commitments from previous transitions

  ;; TODO: figure out the actual source of input patterns here
  ;; TODO: also process the unobserved patterns
  (for/fold ([next-state-pairs null])
            ([input-pattern-group (spec-input-pattern-groups spec)]
             #:break (not next-state-pairs))
    ;; TODO: add in the real address and message here

    ;; TODO: replace 'sample-value with (pattern-group-pattern input-pattern-group), to use the
    ;; actual pattern (requires a new language in csa/model)
    (for/fold ([next-state-pairs null])
              ([result-config (handle-message prog '(addr 1) ''sample-value)]
               #:break (not next-state-pairs))
      ;; Check all of its outputs and see if it matches *some* transition

      ;; TODO: check that we're not in a stuck state (or maybe I just do this ahead of time with a
      ;; type-system-like thing

      ;; TODO: add primitive predicates to match patterns to check if something is an address, a
      ;; symbol, a number, or some other primitive

      ;; TODO: check each result to see if it matches a spec transition, and if so, add the next
      ;; state to the to-visit list

      ;; TODO: change this code to account for more than one possible transition
      ;;
      ;; TODO: change this code to allow for multiple possible ways to match the outputs against the
      ;; available commitments
      (match-define (list external-packets wiped-config) (extract-external-sends result-config))
      ;; TODO: deal with spec instance addresses communicated to the outside world

      ;; Returns the list of commitments still unsatisfied in the spec
      (define possible-transitions (pattern-group-exps input-pattern-group))
      (define match-results (match-sends-to-commitments external-packets possible-transitions))
      ;; TODO: remove this debug line and inline match-results definition
      (printf "match results: ~s\n" match-results)
      (match match-results
        [#f #f] ; if matching up the outputs failed, then the whole transition definitely fails
        [(list)
         ;; TODO: get the list of new state pairs that we've transitioned to and now want to check
         (list)]
        ;; TODO: find a way to check on the commitments that aren't immediately satisfied
        [_ #f]))))

;; Returns #f if any of the given message packets does not have a matching commitment in the given
;; transitions; otherwise, returns the list of remaining (unmatched) commitments.
(define (match-sends-to-commitments external-packets possible-transitions)
  (printf "external packets: ~s\n" external-packets)
  ;; TODO: make this handle more than 1 transition

  ;; TODO: make this handle all possible orderings of matches

  ;; TODO: make this work with abstract address values

  ;; TODO: make this allow for unobserved communication

  ;; TODO: also get the pre-existing commitments from the spec config

  (printf "commitments: ~s\n" (get-spec-commitments (car possible-transitions)))
  (define-values (conformance-violated? remaining-commitments)
    (for/fold ([conformance-violated? #f]
               [remaining-commitments (get-spec-commitments (car possible-transitions))])
        ([packet external-packets]
         #:break conformance-violated?)
      (match-define (cons packet-address packet-message) packet)
      (match (findf
              (lambda (commitment)
                (define commitment-address (car commitment))
                (define pattern (cdr commitment))

                ;; TODO: make pattern matching also do the variable-binding thing
                (and (equal? commitment-address packet-address)
                     (matches-output-pattern? packet-message pattern)))
              remaining-commitments)
        [#f (values #t remaining-commitments)]
        [pattern (values #f (remove pattern remaining-commitments))])))

  (if conformance-violated? #f remaining-commitments))

;; TODO: write tests for analyze-state-pair-transitions

(module+ test
  (require rackunit
           redex/reduction-semantics
           csa/model

           ;; also run the submodule tests here
           (submod ".." language-eval test)
           (submod ".." spec-eval test))

  (define (make-single-agent-config agent)
    `((,agent) () ((addr 1)) ((addr 2))))

  (define ignore-all-agent
    '((addr 1)
      (((define-state (Always) (m) (goto Always)))
       (rcv (m) (goto Always)))))
  (define ignore-all-config (make-single-agent-config ignore-all-agent))
  (define ignore-all-spec-instance
    '(((define-state (Always) [* -> (goto Always)]))
      (goto Always)
      (addr 1)))

  (check-not-false (redex-match csa-eval (a ((S ...) e)) ignore-all-agent))
  (check-not-false (redex-match csa-eval K ignore-all-config))
  (check-not-false (redex-match aps-eval z ignore-all-spec-instance))

  (check-true (analyze ignore-all-config ignore-all-spec-instance))

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

  (check-true (analyze (make-single-agent-config static-response-agent) static-response-spec))

  ;; all 3 of these fail; let's check double/single first
  (check-false (analyze (make-single-agent-config static-response-agent) ignore-all-spec-instance))
  (check-false (analyze (make-single-agent-config static-double-response-agent) static-response-spec))
  (check-false (analyze ignore-all-config static-response-spec))

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
    extract-external-sends/mf : K -> (((a v) ...) K)
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
    external-packet?/mf : (a v) χ -> boolean
    [(external-packet?/mf (a _) (_ ... a _ ...)) #t]
    [(external-packet?/mf _ _) #f])

  (module+ test
    (require rackunit)
    (check-false (external-packet? (term ((addr 1) 'a)) (term ())))
    (check-true  (external-packet? (term ((addr 1) 'a)) (term ((addr 1)))))
    (check-false (external-packet? (term ((addr 1) 'a)) (term ((addr 2)))))
    (check-true  (external-packet? (term ((addr 1) 'a)) (term ((addr 1) (addr 2)))))
    (check-false (external-packet? (term ((addr 1) 'a)) (term ((addr 3) (addr 2)))))))

;;      (match-define (list external-packets wiped-config) (extract-external-sends config))

(require 'language-eval)

;; ---------------------------------------------------------------------------------------------------
;; Spec evaluation forms (maybe merge into previous section?

(module spec-eval racket

  (provide spec-input-pattern-groups
           matches-output-pattern?
           get-spec-commitments)

    (require redex/reduction-semantics
           csa/model)


  ;; (provide spec-config-transitions)
  ;; ;; TODO: eventually this will depend on having an address for the instance, etc.
  ;; (define (spec-config-transitions config)

  ;;   )

  ;; TODO: implement this
  ;; Returns the transitions of the spec instance's current state, grouped by input pattern
  (define (spec-input-pattern-groups instance)
    (term (spec-input-pattern-groups/mf ,instance)))

  (define-metafunction aps-eval
    spec-input-pattern-groups/mf : z -> ((p (e-hat ...)) ...)
    [(spec-input-pattern-groups/mf ((_ ... (define-state (s _ ...) (ε -> e-hat) ...) _ ...) (goto s _ ...) _))
     (spec-input-pattern-groups/acc ((ε -> e-hat) ...) ())])

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
      [(list `(,_ ,commitments))
       commitments]))

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

  (module+ test
    (check-true (matches-output-pattern? 42 '*))
    (check-true (matches-output-pattern? 42 'z))
    (check-true (matches-output-pattern? ''foo '*))
    (check-true (matches-output-pattern? ''foo 'foo))
    (check-false (matches-output-pattern? ''foo ''bar))
    (check-false (matches-output-pattern? 42 ''bar))
    (check-true (matches-output-pattern? '(list 42 'foo) '(list a *)))
    (check-false (matches-output-pattern? '(list 42 'foo) '(list 'bar *)))
    (check-false (matches-output-pattern? '(list 42 'foo) '(list * 'bar)))
    (check-false (matches-output-pattern? '(list 42 'foo) '(list 'a 'b))))

  (define spec-step
    (reduction-relation aps-eval
      #:domain (e-hat ((a po) ...))
      (--> ((with-outputs ([a po] ...) e-hat) (any_commits ...))
           (e-hat (any_commits ... [a po] ...)))))


  (module+ test
    (require rackunit)

    ;; A check that succeeds if and only if each list does not contain duplicate members, and the two
    ;; lists have the same elements (possibly in different orders)
    (define-simple-check (check-same-distinct-members? l1 l2)
      (equal? (list->set l1) (list->set l2)))

    ;; no patterns
    ;; 2 distinct patterns
    ;; 2 similar patterns, 1 distinct
    ;; 2 different patterns, 2 other patterns in another state
    (check-same-distinct-members?
     (term (spec-input-patterns/mf
            (((define-state (S1))) (goto S1) null)))
     null)

    (check-same-distinct-members?
     (term (spec-input-patterns/mf
            (((define-state (S1)
                [(list 'a) -> (goto S1)]
                ['b -> (goto S1)]))
             (goto S1)
             null)))
     (list (term (list 'a)) (term 'b)))

    (check-same-distinct-members?
     (term (spec-input-patterns/mf
            (((define-state (S1)
                [(list 'a) -> (goto S1)]
                ['b -> (goto S1)]
                ['b -> (goto S2)]))
             (goto S1)
             null)))
     (list (term (list 'a)) (term 'b)))

    (check-same-distinct-members?
     (term (spec-input-patterns/mf
            (((define-state (S1)
                [(list 'a) -> (goto S1)]
                ['b -> (goto S1)])
              (define-state (S2)
                ['c -> (goto S1)] ['d -> (goto S1)]))
             (goto S1)
             null)))
     (list (term (list 'a)) (term 'b)))))

(require 'spec-eval)
