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
       (match (analyze-state-pair-transitions (head to-visit))
         [#f #f] ; if any state pair analysis fails, then the whole thing fails

         ;; TODO: figure out what it looks like here when we try all possible combinations of the
         ;; possible program/spec transition pairs. This currently assumes only one possible way to
         ;; match everything
         [(list new-pairs-to-visit ...)
          (loop (append new-pairs-to-visit (tail to-visit))
                (set-add visited (head to-visit)))])])))

;; TODO: make this purpose statement more precise. This is probably a function that will be described
;; in the paper

(define pattern-group-pattern car)
(define pattern-group-exps cdr)

;; Returns #f if conformance fails for this state pair, or returns a list of state pairs to check
;; otherwise
(define (analyze-state-pair-transitions current-pair)
  (define current-prog (car current-pair))
  (define current-spec-instance (cdr current-pair))

  ;; Gather all possible inputs according to the spec (including non-specified ones) and run each one
  ;; abstractly through the handler. For each result, check if it satisfies a transition, and add the
  ;; next state to the to-visit queue if it's not there already (or add it anyway, I think...)

  ;; TODO: deal with commitments from previous transitions

  ;; TODO: figure out the actual source of input patterns here
  ;; TODO: also process the unobserved patterns
  (for/fold ([next-state-pairs null])
            ([input-pattern-group (spec-input-pattern-groups current-spec-instance)]
             #:break (not next-state-pairs))
    ;; TODO: add in the real address and message here
    (define result-configs
      ;; TODO: replace 'sample-value with (pattern-group-pattern input-pattern-group), to use the
      ;; actual pattern (requires a new language in csa/model)
      (handle-message current-prog '(addr 1) ''sample-value))
    (for/fold ([next-state-pairs null])
              ([config result-configs]
               #:break (not next-state-pairs))
      ;; Check all of its outputs and see if it matches *some* transition

      ;; TODO: check that we're not in a stuck state

      ;; TODO: check each result to see if it matches a spec transition, and if so, add the next
      ;; state to the to-visit list

      ;; TODO: change this code to account for more than one possible transition
      ;;
      ;; TODO: change this code to allow for multiple possible ways to match the outputs against the
      ;; available commitments
      (match-define (list external-packets wiped-config) (extract-external-sends config))
      ;; TODO: deal with spec instance addresses communicated to the outside world

      ;; Returns the list of commitments still unsatisfied in the spec
      (define possible-transitions (pattern-group-exps input-pattern-group))
      (match (match-sends-to-commitments external-packets possible-transitions)
        [#f #f] ; if an output didn't match anything, then the whole transition definitely fails
        [(list)
         ;; TODO: get the list of new state pairs that we've transitioned to and now want to check
         (list)]
        ;; TODO: find a way to check on the commitments that aren't immediately satisfied
        [_ #f]))))

;; Returns the list of remaining commitments, or #f if some output does not match any commitment
(define (match-sends-to-commitments sends spec-instance)
  ;; TODO: implement this
  (list)
  )

;; TODO: write tests for analyze-state-pair-transitions

;; TODO: for right now the test just runs on instances, but we should really run it on full configs
;; instead, I think

(module+ test
  (require rackunit
           redex/reduction-semantics
           csa/model)

  (define ignore-all-agent
    '((addr 1)
      (((define-state (Always) (m) (goto Always)))
       (rcv (m) (goto Always)))))
  (define ignore-all-config
    `((,ignore-all-agent) () ((addr 1)) ()))
  (define ignore-all-spec-instance
    '(((define-state (Always) [* -> (goto Always)]))
      (goto Always)
      null))

  (check-not-false (redex-match csa-eval (a ((S ...) e)) ignore-all-agent))
  (check-not-false (redex-match csa-eval K ignore-all-config))
  (check-not-false (redex-match aps-eval z ignore-all-spec-instance))

  (check-true (analyze ignore-all-config ignore-all-spec-instance))

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

  ;; Runs the handler to completion for the message being sent to the given address and returns the
  ;; updated program config
  (define (handle-message prog-config address message)
    ;; TODO: check for all items matching their shape (make a contract and do a contract-out thing
    ;; TODO: check that the returned thing is in a goto/rcv state?
    (apply-reduction-relation* handler-step (term (inject-message ,prog-config ,address ,message))))

  ;; TODO: define this method
  ;;
  ;; Returns a 2-tuple of the list of address/value pairs for message packets destined for external
  ;; addresses, and the config with those message packets removed
  ;;
  ;; TODO: what if we don't know if the message is destined to be external or internal, or even
  ;; observable or not?
  (define (extract-external-sends config)
    (term (extract-external-sends ,config)))

  (define-metafunction csa-eval
    extract-external-sends/mf : K -> (((a v) ...) K)
    [(extract-external-sends/mf (α μ ρ χ))
     (μ_external (α μ_internal ρ χ))
     (where μ_external ,(filter (curryr external-packet? (term χ)) (term μ)))
     (where μ_internal ,(filter (negate (curryr external-packet? (term χ))) (term μ)))])

  ;; TODO: write tests for exttract-external-sends

  ;; TODO: think about writing the nice Redex additions so that extract-external-sends isn't such a
  ;; pain

  ;; Returns true if the packet is destined for one of the external addresses; false otherwise
  (define (external-packet? packet external-addresses)
    (member (car packet) (term external-addresses))))
    



;;      (match-define (list external-packets wiped-config) (extract-external-sends config))

(require 'language-eval)

;; ---------------------------------------------------------------------------------------------------
;; Spec evaluation forms (maybe merge into previous section?

(module spec-eval racket

  (provide spec-input-pattern-groups)

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

;;  ((goto Always) (define-state (Always) (* -> (goto Always))))

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

  (define-metafunction aps-eval
    filter-patterns-from-events : ε ... -> (p ...)
    [(filter-patterns-from-events p any ...)
     (p p_rest ...)
     (where (p_rest ...) (filter-patterns-from-events any ...))]
    [(filter-patterns-from-events unobs any ...)
     (filter-patterns-from-events any ...)])

  (module+ test
    (require rackunit)

    ;; Assumes the members can be sorted with sort
    (define-simple-check (check-same-members? l1 l2)
      (equal? (sort l1) (sort l2)))

    ;; no patterns
    ;; 2 distinct patterns
    ;; 2 similar patterns, 1 distinct
    ;; 2 different patterns, 2 other patterns in another state
    (check-same-members? (term (spec-input-patterns/mf (((define-state (S1))) (goto S1) null)))
                         null)
    (check-same-members? (term (spec-input-patterns/mf (((define-state (S1) [(list 'a) -> (goto S1)] ['b -> (goto S1)])) (goto S1) null)  ))
                         (list (term (list 'a)) (term 'b)))
    (check-same-members? (term (spec-input-patterns/mf (((define-state (S1) [(list 'a) -> (goto S1)] ['b -> (goto S1)] ['b -> (goto S2)])) (goto S1) null)))
                         (list (term (list 'a)) (term 'b)))
    (check-same-members? (term (spec-input-patterns/mf (((define-state (S1) [(list 'a) -> (goto S1)] ['b -> (goto S1)])
                                                         (define-state (S2) ['c -> (goto S1)] ['d -> (goto S1)]))
                                                        (goto S1)
                                                        null)))
                         (list (term (list 'a)) (term 'b)))))

(require 'spec-eval)
