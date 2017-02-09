#lang racket

;; Abstract standard semantic domains for CSA#, and associated functions

(provide
 ;; Required by conformance checker
 (struct-out csa#-transition)
 csa#-messages-of-type
 csa#-enabled-internal-actions
 csa#-action-enabled?
 csa#-make-external-trigger
 csa#-abstract-config
 csa#-blur-config
 necessary-action?
 csa#-address-type
 csa#-address-strip-type
 ;; required for widening
 csa#-transition-maybe-good-for-widen?
 (struct-out csa#-transition-effect)
 csa#-config<?
 csa#-eval-trigger
 csa#-apply-transition
 csa#-evictable-addresses

 ;; Required by conformance checker to select spawn-flag to blur; likely to change
 csa#-spawn-address?
 csa#-spawn-address-flag
 csa#-flags-that-know-externals

 ;; Required by APS#
 csa#-output-address
 csa#-output-message
 csa#-output-multiplicity
 csa#-blur-addresses ; needed for blurring in APS#
 internals-in
 externals-in
 csa#-sort-config-components
 csa#-evict-actor

 ;; Required by APS#; should go into a "common" language instead
 csa#
 csa#-abstract-address
 type-join
 type<=

 ;; Testing helpers
 make-single-actor-abstract-config

 ;; Debug helpers
 impl-config-without-state-defs
 impl-config-goto)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 (for-syntax syntax/parse)
 "csa.rkt"
 "list-helpers.rkt"
 "sexp-helpers.rkt")

;; Abstract-interpretation version of CSA
(define-extended-language csa# csa-eval
  (i# (α# β# μ#))
  (α# ((a#int-precise b#) ...))
  (β# ((a#int-collective (b# ...)) ...)) ; blurred actors, represented by a set of abstract behaviors
  (b# ((Q# ...) e#)) ; behavior
  ;; REFACTOR: make a general structure for abstract multisets: values with multiplicities attached
  (μ# ((a#int v# m) ...)) ; message packets
  (m single many) ; m for "multiplicity"
  (Q# (define-state (q [x τ] ...) (x) e#)
      (define-state (q [x τ] ...) (x) e# [(timeout e#) e#]))
  (v# τa#
      (variant t v# ...)
      (record [l v#] ...)
      (folded τ v#)
      (* τ)
      (list-val v# ...)
      (vector-val v# ...)
      (hash-val (v# ...) (v# ...)))
  (e# (spawn any_location τ e# Q# ...)
      (spawning a#int τ e# Q# ...)
      (goto q e# ...)
      (send e# e#)
      (begin e# ... e#)
      (let ([x e#] ...) e#)
      (case e# [(t x ...) e#] ...)
      (variant t e# ...)
      (record [l e#] ...)
      (: e# l)
      (! e# [l e#])
      (fold τ e#)
      (unfold τ e#)
      (primop e# ...)
      (printf string e# ...) ; for debugging only
      (list e# ...)
      (vector e# ...)
      (hash [e# e#] ...)
      (for/fold ([x e#]) ([x e#]) e#)
      (loop-context e#)
      (coerce e# τ)
      x
      v#)
  (a# a#int a#ext) ; internal and external addresses
  (a#int a#int-precise
         a#int-collective)
  (a#int-precise (init-addr natural)
                 (spawn-addr any_location spawn-flag))
  (a#int-collective (blurred-spawn-addr any_location))
  ;; OLD means it is a unique actor that existed before the current handler was run, NEW means it was
  ;; spawned in the current handler (should all be OLD between runs, after blur/canonicalize)
  (spawn-flag NEW OLD)
  (a#ext
   (* (Addr τ)) ; unobserved address
   (obs-ext natural))
  (τa# (τ a#int)
       (τ (obs-ext natural))
       (* (Addr τ)))
  ;; H# = handler machine state (exp + outputs + spawns so far)
  (H# (e# [([a# v# m] ...) ((a#int b#) ...)]))
  (E# hole
      (spawning a#int τ E# Q# ...)
      (goto q v# ... E# e# ...)
      (send E# e#)
      (send v# E#)
      (begin E# e# ...)
      (let ([x v#] ... [x E#] [x e#] ...) e#)
      (case E# [(t x ...) e#] ...)
      (variant t v# ... E# e# ...)
      (record [l v#] ... [l E#] [l e#] ...)
      (: E# l)
      (! E# [l e#])
      (! v# [l E#])
      (fold τ E#)
      (unfold τ E#)
      (primop v# ... E# e# ...)
      (printf string v# ... E# e# ...)
      (list v# ... E# e# ...)
      (vector v# ... E# e# ...)
      (hash [v# v#] ... [E# e#] [e# e#] ...)
      (hash [v# v#] ... [v# E#] [e# e#] ...)
      (for/fold ([x E#]) ([x e#]) e#)
      (for/fold ([x v#]) ([x E#]) e#)
      (loop-context E#)
      (coerce E# τ))
  (trigger# (timeout/empty-queue a#int)
            (timeout/non-empty-queue a#int)
            (internal-receive a#int v#)
            (external-receive a#int v#)))

;; ---------------------------------------------------------------------------------------------------
;; Test Data

(module+ test
  (define test-behavior1
    (term (((define-state (TestState1) (x) (goto TestState1)))
           (goto TestState1)))))

;; ---------------------------------------------------------------------------------------------------
;; Constants

;; The maximum number of times to unfold a recursive type while generating an exhaustive set of
;; abstract values for that type.
;;
;; This number is an arbitrary choice for now. Later it may make sense to base it off of the level of
;; detail in the spec or program.
(define MAX-RECURSION-DEPTH 1)

;; ---------------------------------------------------------------------------------------------------
;; Message generation

;; TODO: create a second type of "fresh" external address instead (one that gets converted into the
;; other one during canonicalization), so I don't have to worry about overlapping with existing
;; addresses
(define FIRST-GENERATED-ADDRESS 100)
(define next-generated-address FIRST-GENERATED-ADDRESS)

;; Returns an exhaustive list of abstract messages for the type of the given address
(define (csa#-messages-of-type type)
  ;; reset the generated address, so that we don't keep finding different numbers for different types
  ;; (or even the same type, if metafunction caching ever goes away here)
  (set! next-generated-address FIRST-GENERATED-ADDRESS)
  (term (messages-of-type/mf ,type ,MAX-RECURSION-DEPTH)))

;; Returns an exhaustive list of abstract messages for the given type with the natural argument
;; indicating the maximum number of times to unfold recursive types.
(define-metafunction csa#
  messages-of-type/mf : τ natural -> (v# ...)
  [(messages-of-type/mf Nat _) ((* Nat))]
  [(messages-of-type/mf String _) ((* String))]
  [(messages-of-type/mf (Union) _) ()]
  [(messages-of-type/mf (Union [t_1 τ_1 ...] [t_rest τ_rest ...] ...) natural_max-depth)
   (v#_1 ... v#_rest ...)
   (where (v#_1 ...) (generate-variants natural_max-depth t_1 τ_1 ...))
   (where (v#_rest ...)
          (messages-of-type/mf (Union [t_rest τ_rest ...] ...) natural_max-depth))]
  [(messages-of-type/mf (Union) _) ()]
  [(messages-of-type/mf (minfixpt X τ) 0)
   ((* (minfixpt X τ)))]
  [(messages-of-type/mf (minfixpt X τ) natural_max-depth)
   ((folded (minfixpt X τ) v#) ...)
   (where (v# ...)
          (messages-of-type/mf (type-subst τ X (minfixpt X τ)) ,(sub1 (term natural_max-depth))))]
  [(messages-of-type/mf (Record [l_1 τ_1] [l_rest τ_rest] ...) natural_max-depth)
   ,(for/fold ([records-so-far null])
              ([sub-record (term (messages-of-type/mf (Record [l_rest τ_rest] ...) natural_max-depth))])
      (append
       (for/list ([generated-v (term (messages-of-type/mf τ_1 natural_max-depth))])
         (redex-let csa# ([(record [l_other v#_other] ...) sub-record]
                          [v#_1 generated-v])
           (term (record [l_1 v#_1] [l_other v#_other] ...))))
       records-so-far))]
  [(messages-of-type/mf (Record) natural_max-depth)
   ((record))]
  [(messages-of-type/mf (Addr τ) _)
   ,(begin
      (set! next-generated-address (add1 next-generated-address))
      (term ((τ (obs-ext ,next-generated-address)))))]
  [(messages-of-type/mf (Listof τ) natural_max-depth)
   (,(normalize-collection (term (list-val v# ...))))
   (where (v# ...) (messages-of-type/mf τ natural_max-depth))]
  [(messages-of-type/mf (Vectorof τ) natural_max-depth)
   (,(normalize-collection (term (vector-val v# ...))))
   (where (v# ...) (messages-of-type/mf τ natural_max-depth))]
  [(messages-of-type/mf (Hash τ_1 τ_2) natural_max-depth)
   (,(normalize-collection (term (hash-val (v#_keys ...) (v#_vals ...)))))
   (where (v#_keys ...) (messages-of-type/mf τ_1 natural_max-depth))
   (where (v#_vals ...) (messages-of-type/mf τ_2 natural_max-depth))])

;; Generate an exhaustive list of variant values for the given tag and type, with the natural argument
;; acting as max-depth for the number of recursive type unfoldings
(define-metafunction csa#
  generate-variants : natural t τ ... -> ((variant t v# ...) ...)
  [(generate-variants _ t) ((variant t))]
  [(generate-variants natural_max-depth t τ_1 τ_rest ...)
   ,(for/fold ([variants-so-far null])
              ([sub-variant (term (generate-variants natural_max-depth t τ_rest ...))])
      (append
       (for/list ([generated-v (term (messages-of-type/mf τ_1 natural_max-depth))])
         (redex-let csa# ([(variant t v#_other ...) sub-variant]
                          [v#_1 generated-v])
           (term (variant t v#_1 v#_other ...))))
       variants-so-far))])

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt")

  (test-same-items?
   (term (messages-of-type/mf Nat 0))
   '((* Nat)))
  (test-same-items? (term (messages-of-type/mf (Union [Begin]) 0)) (list '(variant Begin)))
  (test-same-items?
   (term (messages-of-type/mf (Union [A] [B]) 0))
   '((variant A) (variant B)))
  (test-same-items? (term (messages-of-type/mf (Union) 0)) null)
  (test-same-items?
   (term (messages-of-type/mf (minfixpt Dummy Nat) 0))
   (list '(* (minfixpt Dummy Nat))))
  (test-same-items?
   (term (messages-of-type/mf (minfixpt Dummy Nat) 1))
   (list '(folded (minfixpt Dummy Nat) (* Nat))))
  (test-same-items?
   (term (messages-of-type/mf (Record [a Nat] [b Nat]) 0))
   (list '(record [a (* Nat)] [b (* Nat)])))
  (test-same-items?
   (term (messages-of-type/mf (Record [x (Union [A] [B])] [y (Union [C] [D])]) 0))
   (list '(record [x (variant A)] [y (variant C)])
         '(record [x (variant A)] [y (variant D)])
         '(record [x (variant B)] [y (variant C)])
         '(record [x (variant B)] [y (variant D)])))
  (define list-of-nat '(minfixpt NatList (Union [Null] [Cons Nat NatList])))
  (test-same-items?
   (term (messages-of-type/mf ,list-of-nat 0))
   (list `(* ,list-of-nat)))
  (test-same-items?
   (term (messages-of-type/mf ,list-of-nat 1))
   (list `(folded ,list-of-nat (variant Null))
         `(folded ,list-of-nat (variant Cons (* Nat) (* ,list-of-nat)))))
  (test-same-items?
   (term (messages-of-type/mf ,list-of-nat 2))
   (list `(folded ,list-of-nat (variant Null))
         `(folded ,list-of-nat (variant Cons (* Nat) (folded ,list-of-nat (variant Null))))
         `(folded ,list-of-nat (variant Cons (* Nat) (folded ,list-of-nat (variant Cons (* Nat) (* ,list-of-nat)))))))
  (test-same-items?
   (term (messages-of-type/mf (Union) 0))
   '())
  (test-same-items?
   (term (messages-of-type/mf (Union [A] [B String (Union [C] [D])]) 0))
   '((variant A)
     (variant B (* String) (variant C))
     (variant B (* String) (variant D))))
  (test-same-items?
   (term (messages-of-type/mf (Vectorof Nat) 0))
   (list `(vector-val (* Nat))))
  (test-same-items?
   (term (messages-of-type/mf (Listof Nat) 0))
   (list `(list-val (* Nat))))
  (test-same-items?
   (term (messages-of-type/mf (Hash Nat (Union [A] [B] [C])) 0))
   (list `(hash-val ((* Nat)) ((variant A) (variant B) [variant C]))))
  (test-case "Generated address number is re-used for each top-level generation"
    (check-equal? (second (first (csa#-messages-of-type `(Addr Nat))))
                  (second (first (csa#-messages-of-type `(Addr String)))))))

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; TODO: give these structs better names

;; Represents the effects of a single handler-level transition of an actor, before the results are
;; applied to the pre-handler configuration. Used for the widening optimization.
;;
;; sends is a list of abstract-addr/abstract-value/multiplicity 3-tuples. spawns is a list
;; of address/behavior 2-tuples (the address is a collective address for actors spawned inside loops)
(struct csa#-transition-effect (trigger behavior sends spawns) #:transparent)

;; Represents a single handler-level transition of an actor. Trigger is the event that caused the
;; handler to run, outputs is the list of outputs to the external world that happened during execution
;; (as formatted in csa#-transition-effect), and final-config is the resulting abstract configuration.
;;
;; This is the result of applying a csa#-transition-effect
(struct csa#-transition
  (trigger ; follows trigger# above
   outputs ; list of abstract-addr/abstract-message/multiplicity 3-tuples
   final-config) ; an abstract implementation configuration
  #:transparent)

;; impl-config -> (Listof trigger#)
(define (csa#-enabled-internal-actions config)
  (define internal-message-triggers
    (for/list ([packet-entry (csa#-config-message-packets config)])
      (define packet (csa#-packet-entry->packet packet-entry))
      (define address (csa#-message-packet-address packet))
      (define message (csa#-message-packet-value packet))
      (term (internal-receive ,address ,message))))
  (define atomic-actor-timeouts
    (for/fold ([timeout-triggers null])
              ([actor (csa#-config-actors config)])
      (define address (csa#-actor-address actor))
      (if (get-timeout-handler-exp (actor-behavior actor))
          (cons
           (if (any-messages-for? config address)
               (term (timeout/non-empty-queue ,address))
               (term (timeout/empty-queue ,address)))
           timeout-triggers)
          timeout-triggers)))
  (define collective-actor-timeouts
    (for/fold ([timeout-triggers null])
              ([blurred-actor (csa#-config-blurred-actors config)])
      (define address (csa#-blurred-actor-address blurred-actor))
      (if (ormap (lambda (behavior) (get-timeout-handler-exp behavior))
                 (csa#-blurred-actor-behaviors blurred-actor))
          (cons
           (if (any-messages-for? config address)
               (term (timeout/non-empty-queue ,address))
               (term (timeout/empty-queue ,address)))
           timeout-triggers)
          timeout-triggers)))
  (append internal-message-triggers atomic-actor-timeouts collective-actor-timeouts))

(define (csa#-make-external-trigger address message)
  (term (external-receive ,address ,message)))

(define trigger-eval-cache (make-hash))
(define trigger-eval-cache-lookup-count 0)
(define trigger-eval-cache-found-count 0)

;; i# trigger# -> (Listof csa#-transtion-effect)
(define (csa#-eval-trigger config trigger abort)
  (match trigger
    [`(timeout/empty-queue ,addr)
     (eval-timeout config addr trigger abort)]
    [`(timeout/non-empty-queue ,addr)
     (eval-timeout config addr trigger abort)]
    [`(internal-receive ,addr ,message)
     (eval-message config addr message trigger abort)]
    [`(external-receive ,addr ,message)
     (eval-message config addr message trigger abort)]))

(define (eval-timeout config addr trigger abort)
  (append*
   (for/list ([behavior (current-behaviors-for-address config addr)])
     (match (get-timeout-handler-exp behavior)
       [#f null]
       [handler-exp (eval-handler (inject/H# handler-exp)
                                  trigger
                                  (behavior-state-defs behavior)
                                  abort)]))))

(define (eval-message config addr message trigger abort)
  (append*
   (for/list ([behavior (current-behaviors-for-address config addr)])
     (define init-handler-machine (handler-machine-for-message behavior message))
     (eval-handler init-handler-machine trigger (behavior-state-defs behavior) abort))))

;; Returns a handler machine primed with the handler expression from the given behavior, with all
;; state arguments and the message substituted for the appropriate variables
(define (handler-machine-for-message behavior message)
  (match-define `(,state-defs (goto ,state-name ,state-args ...)) behavior)
  (match-define `(define-state (,_ [,state-arg-formals ,_] ...) (,message-formal) ,body ,_ ...)
    (state-def-by-name state-defs state-name))
  (define bindings (cons `[,message-formal ,message] (map list state-arg-formals state-args)))
  (inject/H# (csa#-subst-n body bindings)))

;; Abstractly removes the entry in i# corresponding to the packet (a# v#), which will actually remove
;; it if its multiplicity is single, else leave it there if its multiplicity is many (because removing
;; a message from an abstract list of 0 or more yields a list of 0 or more).
(define (config-remove-packet config addr-val-pair)
  (match-define `(,atomics ,collectives ,packets) config)
  (define new-packets
    ;; if the multiplicity is not single, it must be many, so we just return the original config
    ;; because nothing is actually removed
    (remove (append addr-val-pair `(single)) packets))
  `(,atomics ,collectives ,new-packets))

(module+ test
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1) (* Nat) single]
                                  [(init-addr 2) (* Nat) single]
                                  [(init-addr 1) (* String) single]))
                         `((init-addr 1) (* Nat)))
   `(() () ([(init-addr 2) (* Nat) single]
            [(init-addr 1) (* String) single])))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1) (* Nat) single]
                                  [(init-addr 2) (* Nat) single]
                                  [(init-addr 1) (* String) single]))
                         `((init-addr 2) (* Nat)))
   `(() () ([(init-addr 1) (* Nat) single]
            [(init-addr 1) (* String) single])))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1) (* Nat) single]
                                  [(init-addr 2) (* Nat) many]
                                  [(init-addr 1) (* String) single]))
                         `((init-addr 2) (* Nat)))
   `(() () ([(init-addr 1) (* Nat) single]
            [(init-addr 2) (* Nat) many]
            [(init-addr 1) (* String) single])))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1) (* Nat) single]
                                  [(init-addr 2) (* Nat) many]
                                  [(init-addr 1) (* String) single]))
                         `((init-addr 3) (* Nat)))
    `(() () ([(init-addr 1) (* Nat) single]
                                  [(init-addr 2) (* Nat) many]
                                  [(init-addr 1) (* String) single]))))

;; b# -> e# or #f
;;
;; Returns the behavior's current timeout handler expression with all state arguments substituted in
;; if the current state has a timeout clause, else #f
(define (get-timeout-handler-exp behavior)
  (define current-state-name (goto-state-name (behavior-exp behavior)))
  (match (state-def-by-name (behavior-state-defs behavior) current-state-name)
    [`(define-state (,_ [,formals ,_] ...) ,_ ,_ [(timeout ,_) ,timeout-body])
     (csa#-subst-n timeout-body (map list formals (goto-state-args (behavior-exp behavior))))]
    [_ #f]))

;; Returns #t if the configuration has any in-transit messages for the given internal address; #f
;; otherwise.
(define (any-messages-for? config address)
  (redex-let csa# ([(_ _ ((a#int _ _) ...)) config])
    ;; member does not return #t, so we normalize that result
    (if (member address (term (a#int ...))) #t #f)))

(module+ test
  (test-true "any-messages-for? 1"
    (any-messages-for? (term (() () ([(init-addr 1) (* Nat) 1]))) (term (init-addr 1))))
  (test-false "any-messages-for? 2"
    (any-messages-for? (term (() () ([(init-addr 2) (* Nat) 1]))) (term (init-addr 1))))
  (test-false "any-messages-for? 3"
    (any-messages-for? (term (() () ())) (term (init-addr 1)))))

;; Returns all behaviors currently available in the given config for the actor with the given address
;; (will only be a single behavior for precise addresses, one or more for blurred ones).
(define (current-behaviors-for-address config address)
  (cond
    [(precise-internal-address? address)
     (list (actor-behavior (csa#-config-actor-by-address config address)))]
    [else (blurred-actor-behaviors-by-address config address)]))

;; just like apply-reduction-relation*, but with debug messages
(define (apply-reduction-relation*/debug rel t)
  (define num-steps 0)
  (define num-loop-states-written 0)
  (let loop ([worklist (list t)]
             [processed-terms (set)]
             [irreducible-terms (set)])
    (match worklist
      ['() (set->list irreducible-terms)]
      [(list next-term rest-worklist ...)
       (cond [(set-member? processed-terms next-term)
              (loop rest-worklist processed-terms irreducible-terms)]
             [else
              (set! num-steps (add1 num-steps))
              (printf "Num steps: ~s\n" num-steps)
              (printf "Worklist size: ~s\n" (length worklist))
              ;; (printf "Reducing: ~s\n" next-term)
              (match (apply-reduction-relation/tag-with-names rel next-term)
                [(list)
                 (loop rest-worklist
                       (set-add processed-terms next-term)
                       (set-add irreducible-terms next-term))]
                [(list (list tags results) ...)
                 ;; (when (> (length results) 1)
                 ;;   (displayln tags))
                 (when (member "ForLoop1" tags)
                   (set! num-loop-states-written (add1 num-loop-states-written))
                   (printf "Found ~sth for loop step\n" num-loop-states-written)
                   ;; (call-with-output-file "loop-states.rktd"
                   ;;   (lambda (file)
                   ;;     (write next-term file)
                   ;;     (fprintf file "\n")
                   ;;     (close-output-port file))
                   ;;   #:exists 'append)
                   )
                 (loop (append rest-worklist results)
                       (set-add processed-terms next-term)
                       irreducible-terms)])])])))

;; A cache of handler evaluation results, represented as a hash table from (initial) handler machines
;; to a list of (final) handler machines
(define eval-cache (make-hash))

;; H# trigger# a#int impl-config (impl-config a#int e# -> impl-config) -> (Listof csa#-effect)
;;
;; Evaluates the given handler machine for the given trigger at the given actor address, returning for
;; each possible handler-level transition the final goto expression as well as all effects (outputs
;; and spawns). Calls the abort continuation instead if a transition leads to an unverifiable state.
(define (eval-handler handler-machine trigger state-defs abort)
  (parameterize ([abort-evaluation-param abort])
    (define final-machine-states
      (match (hash-ref eval-cache handler-machine #f)
        [#f
         ;; REFACTOR: have eval-machine just take the whole machine as input
         ;;
         ;; REFACTOR: don't return stuck states; just error if we run into them
         (match-define (list init-exp init-effects) handler-machine)
         (match-define (list maybe-duplicate-value-states stuck-states)
           (eval-machine init-exp
                         init-effects
                         (not (precise-internal-address? (trigger-address trigger)))))
         ;; OPTIMIZE: find out if there's a way to prevent the eval from generating duplicate states
         ;; in the first place (for loops probably make this hard). My hunch is there's no easy way to
         ;; do it.
         (define value-states (remove-duplicates maybe-duplicate-value-states))
         (unless (empty? stuck-states)
           (error 'eval-handler
                  "Abstract evaluation did not complete\nInitial state: ~s\nFinal stuck states:~s"
                  handler-machine
                  stuck-states))
         (hash-set! eval-cache handler-machine value-states)
         value-states]
        [cached-results cached-results]))

    (for/list ([machine-state final-machine-states])
      ;; TODO: rename outputs to something like "transmissions", because some of them stay internal
      ;; to the configuration
      (match-define (list final-exp (list outputs spawns)) machine-state)
      (redex-let csa# ([(in-hole E# (goto q v#_param ...)) final-exp])
        (csa#-transition-effect
         trigger
         (term (,state-defs (goto q v#_param ...)))
         outputs
         spawns)))))

(module+ test
  (test-equal? "Atomic actor spawns atomic actors"
    (eval-handler `((begin (spawn 1 Nat (goto S1)) (goto S2)) (() ()))
                  `(timeout/empty-queue (init-addr 1))
                  null
                  #f)
    (list (csa#-transition-effect `(timeout/empty-queue (init-addr 1))
                                  `(() (goto S2))
                                  null
                                  (list `[(spawn-addr 1 NEW) (() (goto S1))]))))

  (test-equal? "Collective actor spawns collective actors"
    (eval-handler `((begin (spawn 2 Nat (goto S1)) (goto S2)) (() ()))
                  `(timeout/empty-queue (blurred-spawn-addr 1))
                  null
                  #f)
    (list (csa#-transition-effect `(timeout/empty-queue (blurred-spawn-addr 1))
                                  `(() (goto S2))
                                  null
                                  (list `[(blurred-spawn-addr 2) (() (goto S1))])))))

;; ---------------------------------------------------------------------------------------------------
;; Interpreter

;; TODO: ideal thing would be a match-like macro that has special markers around the sub-terms to
;; eval, and each clause only deals with the *values* (stuck states are returned automatically). I
;; think that takes more macro-fu than I have time to learn right now, though (mostly because it
;; requires handling ellipses in patterns). If I did ever write it, though, it would probably be a
;; useful Racket package.
;;
;; Also, this should probably be written in a more canonical monad style (I think this is just a
;; combination of a state monad and some kind of non-determinism monad), but I don't know enough about
;; monads to do that right now.

;; TODO: type definitions and names

;; A MachineState is (Tuple Exp (Tuple Transmissions Spawns)), where Transmissions and Spawns are as
;; in H#
;;
;; A ValueState is a MachineState where the Exp is a Value
;;
;; A StuckState is a MachineState where the Exp is a stuck expression
;;
;; An EvalResult is (Tuple (Listof ValueState) (Listof StuckState))

(define in-loop-context? (make-parameter #f))
(define in-collective-handler? (make-parameter #f))
;; During evaluation, this is a hash table keyed by machine state (H#), and whose values are
;; eval-mahcine-results indicating all possible results of reducing that machine state.
(define loop-results (make-parameter #f))

;; MachineState -> (Tuple (Listof ValueState) (Listof StuckState))
;;
;; Reduces the given machine state into all reachable stuck states and value states
(define (eval-machine exp effects collective-actor?)
  (parameterize ([in-loop-context? #f]
                 [loop-results (make-hash)]
                 [in-collective-handler? collective-actor?])
    (eval-machine/internal exp effects)))

;; MachineState -> (Tuple (Listof ValueState) (Listof StuckState))
;;
;; Reduces the given machine state into all reachable stuck states and value states
(define (eval-machine/internal exp effects)
  (match exp
    ;; Begin
    [`(begin ,e1 ,e-rest ...)
     (eval-and-then* (cons e1 e-rest) effects
       (lambda (vs effects) (value-result (last vs) effects))
       (lambda (stucks) `(begin ,@stucks)))]
    ;; Case
    [`(case ,e-variant ,clauses ...)
     (eval-and-then e-variant effects
       (lambda (v effects)
         (match v
           [`(variant ,_ ...)
            ;; Find exactly one matching clause
            (let loop ([clauses clauses])
              (match clauses
                [(list) (one-stuck-result `(case ,v) effects)]
                [(list `(,pat ,body) other-clauses ...)
                 (match (match-case-pattern v pat)
                   [#f (loop other-clauses)]
                   [bindings (eval-machine/internal (csa#-subst-n body bindings) effects)])]))]
           [`(* (Union ,union-variants ...))
            ;; Use *all* matching patterns for wildcard values
            (define clause-results
              (for/fold ([result empty-eval-result])
                        ([union-variant union-variants])
                (match-define `(,tag ,sub-types ...) union-variant)
                (match (findf (lambda (clause) (equal? (first (case-clause-pattern clause)) tag))
                              clauses)
                  [#f result]
                  [clause
                   (define vals (for/list ([sub-type sub-types]) `(* ,sub-type)))
                   (define bindings (map list (cdr (case-clause-pattern clause)) vals))
                   (combine-eval-results
                    result
                    (eval-machine/internal (csa#-subst-n (case-clause-body clause) bindings) effects))])))
            (if (and (empty? (first clause-results)) (empty? (second clause-results)))
                (one-stuck-result `(case ,v ,@clauses))
                clause-results)]))
       (lambda (stuck) `(case ,stuck ,@clauses)))]
    ;; Let
    [`(let ([,vars ,exps] ...) ,body)
     (eval-and-then* exps effects
       (lambda (vs effects)
         (eval-machine/internal (csa#-subst-n body (map list vars vs)) effects))
       (lambda (stucks) `(let ,(map list vars stucks) ,body)))]
    ;; Records
    [`(record [,labels ,exps] ...)
     (eval-and-then* exps effects
       (lambda (vals effects) (value-result `(record ,@(map list labels vals)) effects))
       (lambda (stucks) `(record ,@(map list labels stucks))))]
    [`(: ,e ,l)
     (eval-and-then e effects
       (lambda (v effects)
         (match v
           [`(record ,fields ...)
            (match (findf (lambda (f) (equal? (first f) l)) fields)
              [#f (one-stuck-result `(: ,v ,l) effects)]
              [field (value-result (second field) effects)])]
           [`(* (Record ,fields ...))
            (match (findf (lambda (f) (equal? (first f) l)) fields)
              [#f (one-stuck-result `(: ,v ,l) effects)]
              [field (value-result `(* ,(second field)) effects)])]
           [_ (one-stuck-result `(: ,v ,l) effects)]))
       (lambda (stuck) `(: ,stuck l)))]
    [`(! ,rec [,l ,field-exp])
     (eval-and-then* (list rec field-exp) effects
       (lambda (vs effects)
         (match-define (list v-rec v-field) vs)
         (define (update-field f)
           (if (equal? (first f) l)
               `[,l ,v-field]
               f))
         (match v-rec
           [`(record ,fields ...)
            (match (findf (lambda (f) (equal? (first f) l)) fields)
              [#f (one-stuck-result `(! ,v-rec [,l ,v-field]) effects)]
              [field (value-result `(record ,@(map update-field fields)) effects)])]
           [`(* (Record ,field-types ...))
            (define fields
              (for/list ([field-type field-types])
                (match-define `[,name ,type] field-type)
                `[,name (* ,type)]))
            (value-result `(record ,@(map update-field fields)) effects)]
           [_ (one-stuck-result `(! ,v-rec [,l ,v-field]) effects)]))
       (lambda (stuck) `(! ,stuck l)))]
    ;; Recursive Types
    [`(fold ,type ,exp)
     (eval-and-then exp effects
       (lambda (v effects)
         (match v
           [`(* ,_) (value-result `(* ,type) effects)]
           [_
            (if (< (term (fold-depth/mf ,v)) MAX-RECURSION-DEPTH)
                (value-result `(folded ,type ,v) effects)
                (if (csa#-contains-address? v)
                    ((abort-evaluation-param))
                    (value-result `(* ,type) effects)))]))
       (lambda (stuck) `(fold ,type ,stuck)))]
    [`(unfold ,type ,e)
     (eval-and-then e effects
       (lambda (v effects)
         (match v
           [`(folded ,type ,val) (value-result val effects)]
           [`(* (minfixpt ,name ,type))
            (value-result (term (* (type-subst ,type ,name (minfixpt ,name ,type)))) effects)]
           [_ (error 'eval-machine/internal "Bad argument to unfold: ~s" v)]))
       (lambda (stuck) `(unfold ,type ,stuck)))]
    [`(folded ,_ ...) (value-result exp effects)]
    ;; Numeric/Boolean Operators
    [`(,(and op (or '< '<= '> '>=)) ,arg1 ,arg2)
     (eval-and-then* (list arg1 arg2) effects
       (lambda (vs effects)
         (match vs
           [`((* Nat) (* Nat)) (value-result `(variant True) `(variant False) effects)]
           [_ (error "Bad args to relative op: ~s\n" `(,op ,@vs))]))
       (lambda (stucks) `(,op ,@stucks)))]
    [`(,(and op (or '+ '- 'mult '/ 'arithmetic-shift)) ,arg1 ,arg2)
     (eval-and-then* (list arg1 arg2) effects
       (lambda (vs effects)
         (match vs
           [`((* Nat) (* Nat)) (value-result `(* Nat) effects)]
           [_ (error "Bad args to binary arithmetic op: ~s\n" `(,op ,@vs))]))
       (lambda (stucks) `(,op ,@stucks)))]
    [`(,(and op (or 'random 'ceiling)) ,arg)
     (eval-and-then arg effects
       (lambda (v effects)
         (match v
           [`(* Nat) (value-result `(* Nat) effects)]
           [_ (error "Bad args to unary arithmetic op: ~s\n" `(,op ,v))]))
       (lambda (stuck) `(,op ,stuck)))]
    [`(and ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (match-define (list v1 v2) vs)
         (value-result (term (csa#-and (canonicalize-boolean ,v1) (canonicalize-boolean ,v2)))
                       effects))
       (lambda (stucks) `(and ,@stucks)))]
    [`(or ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (match-define (list v1 v2) vs)
         (value-result (term (csa#-or (canonicalize-boolean ,v1) (canonicalize-boolean ,v2)))
                       effects))
       (lambda (stucks) `(or ,@stucks)))]
    [`(not ,e)
     (eval-and-then e effects
       (lambda (v effects)
         (value-result (term (csa#-not (canonicalize-boolean ,v))) effects))
       (lambda (stuck) `(not ,stuck)))]
    [`(= ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (value-result `(variant True) `(variant False) effects))
       (lambda (stucks) `(= ,@stucks)))]
    ;; Lists, Vectors, and Hashes
    [`(,(and op (or 'list 'cons 'list-as-variant 'list-ref 'remove 'length 'vector 'vector-ref 'vector-take 'vector-drop 'vector-length 'vector-copy 'vector-append 'hash-ref 'hash-keys 'hash-values 'hash-set 'hash-remove 'hash-has-key? 'hash-empty? 'sort-numbers-descending))
       ,args ...)
     (eval-and-then* args effects
       (lambda (vs effects)
         (match (cons op vs)
           [`(list ,vs ...) (value-result (normalize-collection `(list-val ,@vs)) effects)]
           [`(cons ,v ,rest)
            (define existing-list-vals
             (match rest
               [`(* (Listof ,type)) (list `(* ,type))]
               [`(list-val ,vs ...) vs]))
            (value-result (normalize-collection `(list-val ,@existing-list-vals ,v)) effects)]
           [`(list-as-variant ,l)
            (match l
              [`(* (Listof ,type)) (value-result `(variant Empty)
                                                 `(variant Cons (* ,type) (* (Listof ,type)))
                                                 effects)]
              [`(list-val ,items ...)
               (apply value-result
                      `(variant Empty)
                      (append (for/list ([item items]) `(variant Cons ,item ,l))
                              (list effects)))]
              [_ (error 'eval-machine/internal "Bad list for list-as-variant: ~s\n" l)])]
           [`(list-ref ,l ,_)
            (match l
              [`(* (Listof ,type)) (value-result `(* ,type) effects)]
              ;; NOTE: we can just return the empty list of results if there are no items in the list:
              ;; we assume that that won't happen, and that therefore we only reached this state
              ;; through over-abstraction
              [`(list-val ,items ...) (apply value-result (append items (list effects)))]
              [_ (error 'eval-machine/internal "Bad list for list-ref: ~s\n" l)])]
           [`(remove ,_ ,l) (value-result l effects)]
           [`(length ,_) (value-result `(* Nat) effects)]
           [`(vector ,vs ...) (value-result (normalize-collection `(vector-val ,@vs)) effects)]
           [`(vector-ref ,v ,_)
            (match v
              [`(* (Vectorof ,type)) (value-result `(* ,type) effects)]
              [`(vector-val ,items ...) (apply value-result (append items (list effects)))]
              [_ (error 'eval-machine/internal "Bad vector for vector-ref: ~s\n" v)])]
           [`(,(or 'vector-take 'vector-drop 'vector-copy) ,v ,_ ...)
            (value-result v effects)]
           [`(vector-length ,_) (value-result `(* Nat) effects)]
           ;; TODO: figure out if the type is ever *not* big enough to also cover the other vector
           [`(vector-append (* (Vectorof ,type)) (* (Vectorof ,type2)))
            (value-result `(* (Vectorof ,type)) effects)]
           ;; at least one of the vectors is precise, so convert the whole thing to a precise vector
           ;; (so that we don't lose a precise address)
           [`(vector-append ,v1 ,v2)
            (value-result
             (normalize-collection `(vector-val ,@(vector-values v1) ,@(vector-values v2)))
             effects)]
           [`(hash-ref ,h ,k)
            (match h
              [`(* (Hash ,key-type ,val-type))
               (value-result `(variant Nothing) `(variant Just (* ,val-type)) effects)]
              [`(hash-val ,_ ,vals)
               (apply value-result
                      `(variant Nothing)
                      (append (for/list ([val vals]) `(variant Just ,val))
                              (list effects)))])]
           [`(hash-keys ,h)
            (match h
              [`(* (Hash ,key-type ,_)) (value-result `(* (Listof ,key-type)) effects)]
              [`(hash-val ,keys ,_) (value-result `(list-val ,@keys) effects)])]
           [`(hash-values ,h)
            (match h
              [`(* (Hash ,_ ,value-type)) (value-result `(* (Listof ,value-type)) effects)]
              [`(hash-val ,_ ,values) (value-result `(list-val ,@values) effects)])]
           [`(hash-set ,h ,key ,val)
            (match h
              [`(* (Hash ,key-type ,value-type))
               (value-result
                (normalize-collection `(hash-val ((* ,key-type) ,key) ((* ,value-type) ,val)))
                effects)]
              [`(hash-val ,keys ,vals)
               (value-result
                (normalize-collection `(hash-val ,(cons key keys) ,(cons val vals)))
                effects)])]
           [`(hash-remove ,h ,k) (value-result h effects)]
           [`(hash-has-key? ,h ,k)
            (value-result `(variant True) `(variant False) effects)]
           [`(hash-empty? ,h)
            (value-result `(variant True) `(variant False) effects)]
           [`(sort-numbers-descending ,v) (value-result v effects)]
           [_ (error 'eval-machine/internal "Bad collection operation: ~s" `(,op ,@vs))]))
       (lambda (stucks) `(,op ,@stucks)))]
    [`(hash ,kvps ...)
     (eval-and-then* (append* (for/list ([kvp kvps]) (list (first kvp) (second kvp)))) effects
       (lambda (results effects)
         (match-define (list keys vals)
           (let loop ([results results]
                      [keys null]
                      [vals null])
             (match results
               [(list) (list keys vals)]
               [(list key val rest ...) (loop rest (cons key keys) (cons val vals))])))
         (value-result (normalize-collection `(hash-val ,keys ,vals)) effects))
       (lambda (stucks) (error 'eval-machine/internal "Stuck evaluating hash: ~s" `(hash ,@stucks))))]
    ;; Loops
    [`(for/fold ([,result-var ,result-exp])
                ([,item-var ,item-exp])
        ,body)
     ;; Without memoizing the results of evaluating for loops, we would enter an infinite loop in
     ;; which we unroll the loop body, evaluate it, unroll the body again, etc. forever. However, we
     ;; can't memoize the results until we finish evaluting an unrolling of the loop, so we have a
     ;; bootstrapping problem.
     ;;
     ;; Here's the solution: if we come across a loop we have *seen* but have not memoized the results
     ;; of yet, we must be nested inside that loop. This must be an instance of the same loop that
     ;; we're nested inside of (i.e. generated from the same syntactic location in the program),
     ;; because otherwise the current loop would have had to be in the original loop's body, and
     ;; therefore we would detect that this loop is different (because of the different
     ;; bodies). Because it is the same loop, the context is also the same: the only possibility is
     ;; that the body of the loop finished evaluating and now we're at the top of the loop
     ;; again. Because we encountered this exact state of the evaluation machine already (including
     ;; its context, which is not covered in the memoization check below), we know that all paths
     ;; through the loop are already being evaluated, so we can return the empty list of results and
     ;; be confident that all possible results are explored in the original iteration through the
     ;; loop.
     ;;
     ;; Of course, once we *have* memoized the results, we just return that result without
     ;; re-evaluating the loop.
     ;;
     ;; There's probably some math based on least-fixpoints that backs this up, but I haven't yet
     ;; formalized it.
     (match-define `(,final-value-states ,final-stuck-states)
      (eval-and-then* (list result-exp item-exp) effects
        (lambda (vs effects)
          (match-define (list result-val items-val) vs)
          (define this-loop (machine-state
                             `(for/fold ([,result-var ,result-val])
                                        ([,item-var ,items-val])
                                ,body)
                             effects))
          (match (hash-ref (loop-results) this-loop #f)
            [#f
             ;; Haven't seen this loop yet: return the result of skipping the loop as well as
             ;; iterating with every possible member of the collection.
             ;;
             ;; We set the empty-eval-result as the loop-result while evaluating the loop body: this is
             ;; what we expect to return if we reduce to this exact same state from here (the notes
             ;; above explain why). After evaluation complete, we set the loop-result to the full set
             ;; of resulting states.
             (hash-set! (loop-results) this-loop empty-eval-result)
             (define collection-members
               (match items-val
                 [`(,(or 'list-val 'vector-val) ,items ...) items]
                 [`(* (,(or 'Listof 'Vectorof) ,type)) (list `(* ,type))]))
             (define result-after-skipping (value-result result-val effects))
             ;; TODO: memoize the result
             (define final-results
               (for/fold ([full-result result-after-skipping])
                         ([member collection-members])
                 (define unrolled-body
                   (csa#-subst-n body (list `[,result-var ,result-val] `[,item-var ,member])))
                 (combine-eval-results
                  full-result
                  (parameterize ([in-loop-context? #t])
                    (eval-machine/internal `(for/fold ([,result-var ,unrolled-body])
                                                      ([,item-var ,items-val])
                                              ,body)
                                           effects)))))
             (hash-set! (loop-results) this-loop final-results)
             final-results]
            [memoized-result memoized-result]))
        (lambda (stucks)
          (match-define (list stuck-result stuck-items) stucks)
          `(for/fold ([,result-var ,stuck-result])
                     ([,item-var ,stuck-items])
             ,body))))
     `(,(remove-duplicates final-value-states) ,final-stuck-states)]
    ;; Coercion
    [`(coerce ,e ,type)
     (eval-and-then e effects
       (lambda (v effects)
         (value-result (term (coerce/mf ,v ,type)) effects))
       (lambda (stuck) `(coerce ,stuck ,type)))]
    ;; Communication
    [`(send ,e-addr ,e-message)
     (eval-and-then* (list e-addr e-message) effects
       (lambda (vs effects)
         (match-define (list v-addr v-message) vs)
         (define addr-type (term (address-type/mf ,v-addr)))
         (define addr (term (address-strip-type/mf ,v-addr)))
         (define quantity (if (in-loop-context?) 'many 'single))
         (match-define `(,sends ,spawns) effects)
         (value-result v-message
                       `(,(add-output sends (term [,addr (coerce/mf ,v-message ,addr-type) ,quantity]))
                         ,spawns)))
       (lambda (stucks) `(send ,@stucks)))]
    ;; Spawns
    [`(spawn ,loc ,type ,init-exp ,raw-state-defs ...)
     (define address
       (if (or (in-collective-handler?) (in-loop-context?))
           `(blurred-spawn-addr ,loc)
           `(spawn-addr ,loc NEW)))
     (define address-value `(,type ,address))
     (define state-defs
       (for/list ([def raw-state-defs])
         (csa#-subst-n/Q# def (list `[self ,address-value]))))
     (eval-and-then (csa#-subst-n init-exp (list `[self ,address-value])) effects
       (lambda (goto-val effects)
         (match-define (list sends spawns) effects)
         (value-result address-value
                       (list sends
                             (add-spawn spawns `[,address (,state-defs ,goto-val)]))))
       (lambda (stuck) `(spawn ,loc ,type ,stuck ,@raw-state-defs)))]
    ;; Goto
    [`(goto ,state-name ,args ...)
     (eval-and-then* args effects
       (lambda (arg-vals effects) (value-result `(goto ,state-name ,@arg-vals) effects))
       (lambda (stucks) `(goto ,state-name ,@stucks)))]
    [`(,(or 'list-val 'vector-val 'hash-val) ,_ ...) (value-result exp effects)]
    ;; Debugging
    [`(printf ,template ,args ...)
     (eval-and-then* args effects
       (lambda (vs effects)
         (apply printf template vs)
         (value-result `(* Nat) effects))
       (lambda (stucks) `(printf ,@stucks)))]
    ;; TODO: add print-len back in for lists and vectors
    ;; Misc. Values
    [`(variant ,tag ,exps ...)
     (eval-and-then* exps effects
       (lambda (vs effects) (value-result `(variant ,tag ,@vs) effects))
       (lambda (stucks) `(variant ,tag ,@stucks)))]
    [`(* ,type) (value-result exp effects)]
    [`(,_
       ,(or `(init-addr ,_)
            `(spawn-addr ,_ ,_)
            `(blurred-spawn-addr ,_)
            `(obs-ext ,_)))
     (value-result exp effects)]
    ;; TODO: need clauses for value forms
    [_ (error 'eval-machine/internal "Don't know how to evaluate ~s\n" exp)]))

;; (Listof Exp)
;; Effects
;; ((Listof ValueExp) Effects -> (Tuple (Listof ValueState) (Listof StuckState)))
;; ((Listof MaybeStuckExp) -> Exp)
;; -> (Tuple (Listof ValueState) (Listof StuckState))
;;
;; Reduces all of the exps in order, accumulating stuck states as they happen. This is essentially a
;; fold over eval-and-then.
;;
;; Note: the value-kont and stuck-kont should each expect an exp-list whose length is equal to the
;; number of exps
(define (eval-and-then* exps effects value-kont stuck-kont)
  (match exps
    [(list) (value-kont (list) effects)]
    [(list exp exps ...)
     (eval-and-then
      exp
      effects
      (lambda (v effects)
        (eval-and-then* exps effects
                        (lambda (other-vs effects) (value-kont (cons v other-vs) effects))
                        (lambda (other-stucks) (stuck-kont (cons v other-stucks)))))
      (lambda (stuck) (stuck-kont (cons stuck exps))))]))

(module+ test
  (test-equal? "Eval-and-then* returns proper stuck state result for first value"
    (eval-and-then* (list `(case (variant A))) empty-effects
        (lambda (vs fx) (error "shouldn't do this"))
        (lambda (stucks) `(variant B ,@stucks)))
    (eval-machine-result null
                         (list (machine-state `(variant B (case (variant A))) empty-effects))))

  (test-equal? "Eval-and-then* returns proper stuck state result for later value"
    (eval-and-then* (list `(* Nat) `(case (variant A))) empty-effects
        (lambda (vs fx) (error "shouldn't do this"))
        (lambda (stucks) `(variant B ,@stucks)))
    (eval-machine-result
     null
     (list (machine-state `(variant B (* Nat) (case (variant A))) empty-effects)))))

;; Exp
;; Effects
;; ValueExp Effects -> (Tuple (Listof ValueState) (Listof StuckState))
;; Exp -> Exp
;; -> (Tuple (Listof ValueState) (Listof StuckState))
;;
;; Reduces the expression to all possible reachable states. When a branch of the reduction leads to a
;; value, a result is computed by calling value-kont on that value. If a branch leads to a stuck
;; state, the stuck-kont is called on that expression and the effects up to that point to build the
;; expected stuck state. All reachable values are combined and returned.
(define (eval-and-then exp effects value-kont stuck-kont)
  (match-define (list value-states stuck-states) (eval-machine/internal exp effects))
  (define value-result
   ;; results from value states
   (for/fold ([results empty-eval-result])
             ([value-state value-states])
     (match-define `(,value ,effects) value-state)
     (combine-eval-results results (value-kont value effects))))
  (eval-result-add-stuck-states value-result
                                (map (curryr add-context-to-stuck-state stuck-kont) stuck-states)))

(module+ test
  (test-equal? "Eval-and-then returns proper stuck state result"
    (eval-and-then `(case (variant A)) empty-effects
        (lambda (v fx) (error "shouldn't do this"))
        (lambda (stuck) `(variant B ,stuck)))
    (eval-machine-result null
                         (list (machine-state `(variant B (case (variant A))) empty-effects)))))

(define empty-eval-result `(() ()))

(define empty-effects `(() ()))

;; Combines two eval results into one by appending their lists together
(define (combine-eval-results r1 r2)
  (match-define `(,values1 ,stucks1) r1)
  (match-define `(,values2 ,stucks2) r2)
  `(,(append values1 values2) ,(append stucks1 stucks2)))

(define (add-context-to-stuck-state state add-context)
  (match-define `(,exp ,effects) state)
  `(,(add-context exp) ,effects))

(define (eval-result-add-stuck-states result stuck-states)
  (match-define `(,value-states ,old-stucks) result)
  `(,value-states ,(append old-stucks stuck-states)))

(define (one-stuck-result exp effects)
  (eval-machine-result null (list (machine-state exp effects))))

(define (value-result . args)
  (match-define (list exps ... effects) args)
  (eval-machine-result (map (curryr machine-state effects) exps) null))

(define (machine-state exp fx)
  (list exp fx))

(define (inject/H# exp)
  (machine-state exp empty-effects))

(define (eval-machine-result values stucks)
  (list values stucks))

;; Attempt to matche the given abstract variant against its pattern from a case clause, returning the
;; list of bindings if it succeeds and #f if not
(define (match-case-pattern variant-val pat)
  (match-define `(variant ,val-tag ,vals ...) variant-val)
  (match-define `(,pat-tag ,vars ...) pat)
  (if (and (equal? val-tag pat-tag) (equal? (length vals) (length vars)))
      (map list vars vals)
      #f))

(define abort-evaluation-param (make-parameter #f))

(module+ test
  (define (exp-reduce* e)
    (match-define `(,value-states ,stuck-states) (eval-machine e empty-effects #f))
    (match-define (list `(,final-exps ,_) ...) (append value-states stuck-states))
    final-exps)

  ;; TODO: rename this to something like check-exp-reduces*-to, since it reduces all the way to either
  ;; a stuck state or a value
  (define-check (check-exp-steps-to? e1 e2)
    (define terminal-exps (exp-reduce* e1))
    (unless (equal? terminal-exps (list e2))
      (fail-check (format "There were ~s final exps: ~s" (length terminal-exps) terminal-exps))))

  (define-check (check-exp-steps-to-all? exp expected-exp-results)
    (define terminal-exps (exp-reduce* exp))
    (unless (equal? (list->set terminal-exps) (list->set expected-exp-results))
      (fail-check (format "Actual next steps were ~s, expected ~s"
                          terminal-exps
                          expected-exp-results))))

  (check-exp-steps-to? `(variant B) `(variant B))
  (check-exp-steps-to? `(begin (variant A) (variant B)) `(variant B))
  (check-exp-steps-to? `(case (variant A (* Nat))
                         [(A x) x]
                         [(B) (variant X)]
                         [(C) (variant Y)])
                      `(* Nat))
  (check-exp-steps-to-all? `(case (* (Union [A Nat] [B] [D]))
                              [(A x) x]
                              [(B) (variant X)]
                              [(C) (variant Y)])
                           (list `(* Nat) `(variant X)))
  (check-exp-steps-to? `(let ([x (variant X)]
                              [y (variant Y)])
                          (variant A x y y))
                       `(variant A (variant X) (variant Y) (variant Y)))
  (check-exp-steps-to? `(record [a (let () (variant A))] [b (* Nat)])
                       `(record [a (variant A)] [b (* Nat)]))
  (check-exp-steps-to? `(record [a (let () (variant A))]
                                [b (case (variant A) [(B) (* Nat)])]
                                [c (let () (* Nat))])
                       `(record [a (variant A)] [b (case (variant A))] [c (let () (* Nat))]))
  (check-exp-steps-to? `(: (record [a (variant A)] [b (variant B)]) b)
                       `(variant B))
  (check-exp-steps-to? `(: (* (Record [a (Union [A])] [b (Union [B])])) b)
                       `(* (Union [B])))
  (check-exp-steps-to? `(: (record [a (variant A)] [b (variant B)]) c)
                       `(: (record [a (variant A)] [b (variant B)]) c))
  (check-exp-steps-to? `(! (record [a (variant A)] [b (variant B)]) [b (variant C)])
                       `(record [a (variant A)] [b (variant C)]))
  (check-exp-steps-to? (term (! (* (Record [a Nat] [b (Union [A] [B] [C])] [c String]))
                                [b (variant C)]))
                       (term (record [a (* Nat)] [b (variant C)] [c (* String)])))
  (check-exp-steps-to? (term (fold   (Union [A]) (variant A)))
                       (term (folded (Union [A]) (variant A))))
  (define nat-list-type (term (minfixpt NatList (Union (Null) (Cons Nat NatList)))))
  (check-exp-steps-to? (term (fold   ,nat-list-type (variant Null)))
                       (term (folded ,nat-list-type (variant Null))))
  (check-exp-steps-to? (term (fold   ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type))))
                       (term (folded ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type)))))
  (check-exp-steps-to? (term (fold ,nat-list-type (variant Cons (* Nat)
                               (fold ,nat-list-type (variant Cons (* Nat)
                                 (fold ,nat-list-type (variant Null)))))))
                       (term (folded ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type)))))
  (check-exp-steps-to? `(unfold (minfixpt NatAddrList (Union [Nil] [ConsIt (Addr Nat) NatAddrList]))
                                (* (minfixpt NatAddrList (Union [Nil] [ConsIt (Addr Nat) NatAddrList]))))
                       `(* (Union [Nil]
                                  [ConsIt (Addr Nat) (minfixpt NatAddrList (Union [Nil] [ConsIt (Addr Nat) NatAddrList]))])))
  (check-exp-steps-to-all? `(< (* Nat) (let () (* Nat)))
                           (list `(variant True) `(variant False)))
  (check-exp-steps-to? `(+ (* Nat) (let () (* Nat)))
                       `(* Nat))
  (check-exp-steps-to? `(random (* Nat))
                       `(* Nat))
  (check-exp-steps-to? `(or (variant True) (variant False))
                       `(variant True))
  (check-exp-steps-to? `(or (* (Union [True] [False])) (variant False))
                       `(* (Union [True] [False])))
  (check-exp-steps-to? `(and (variant True) (variant False))
                       `(variant False))
  (check-exp-steps-to? `(not (variant True))
                       `(variant False))
  (check-exp-steps-to? `(not (* (Union [True] [False])))
                       `(* (Union [True] [False])))
  (check-exp-steps-to? `(coerce ((Union [A] [B] [C]) (init-addr 1)) (Addr (Union [B])))
                       `((Union [B]) (init-addr 1)))
  ;; Equality checks
  (check-exp-steps-to-all? (term (= (* String) (* String)))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all? (term (= (* Nat) (* Nat)))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all? (term (= (* (Addr Nat)) (Nat (obs-ext 1))))
                          (list (term (variant True)) (term (variant False))))

  ;; Tests for sorting when adding to lists, vectors, and hashes
  ;; list
  (check-exp-steps-to?
   (term (list (variant C) (variant B)))
   (term (list-val (variant B) (variant C))))
  (check-exp-steps-to?
   (term (list))
   (term (list-val)))
  (check-exp-steps-to?
   (term (cons (variant A) (list-val (variant B) (variant C))))
   (term (list-val (variant A) (variant B) (variant C))))
  (check-exp-steps-to?
   (term (cons (variant A) (list-val)))
   (term (list-val (variant A))))
  (check-exp-steps-to?
   (term (cons (variant D) (list-val (variant B) (variant C))))
   (term (list-val (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
   (term (cons (variant B) (list-val (variant B) (variant C))))
   (term (list-val (variant B) (variant C))))
  (check-exp-steps-to?
   (term (cons (variant A) (* (Listof (Union [A] [B] [C])))))
   (term (list-val (* (Union [A] [B] [C])) (variant A))))
  (check-exp-steps-to?
   (term (remove (variant A) (list-val (variant A) (variant B))))
   (term (list-val (variant A) (variant B))))
  (check-exp-steps-to?
   (term (remove (variant A) (* (Listof (Union [A] [B])))))
   (term (* (Listof (Union [A] [B])))))
  (check-exp-steps-to-all?
   `(list-ref (list-val) (* Nat))
   null)
  (check-exp-steps-to?
   (term (list-ref (* (Listof Nat)) (* Nat)))
   (term (* Nat)))
  ;; vector
  (check-exp-steps-to?
   (term (vector (variant C) (variant B)))
   (term (vector-val (variant B) (variant C))))
  (check-exp-steps-to?
   (term (vector))
   (term (vector-val)))
  (check-exp-steps-to?
   (term (vector-append (vector-val (variant A) (variant B))
                        (vector-val (variant C) (variant D))))
   (term (vector-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
   (term (vector-append (vector-val (variant A) (variant B))
                        (vector-val (variant C) (variant B))))
   (term (vector-val (variant A) (variant B) (variant C))))
  (check-exp-steps-to?
   (term (vector-append (vector-val (variant C) (variant D))
                        (vector-val (variant A) (variant B))))
   (term (vector-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
  (term (vector-append (vector-val (variant C) (variant D))
                       (vector-val (variant B) (variant A))))
  (term (vector-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to? (term (vector-append (vector-val) (vector-val))) (term (vector-val)))
  (check-exp-steps-to?
   (term (vector-append (vector-val (variant A)) (vector-val)))
   (term (vector-val (variant A))))
  (check-exp-steps-to?
   (term (vector-append (vector-val) (vector-val (variant A))))
   (term (vector-val (variant A))))
  (check-exp-steps-to-all?
   `(vector-ref (vector-val) (* Nat))
   null)
  (check-exp-steps-to? `(vector-copy (vector-val (* Nat)) (* Nat) (* Nat))
                       `(vector-val (* Nat)))
  (check-exp-steps-to? `(vector-take (vector-val (* Nat)) (* Nat))
                       `(vector-val (* Nat)))
  (check-exp-steps-to?
   (term (vector-take (* (Vectorof (Union [A]))) (* Nat)))
   (term (* (Vectorof (Union [A])))))
  (check-exp-steps-to?
   (term (vector-append (vector-val (variant A) (variant B))
                        (* (Vectorof (Union [A] [B] [C])))))
   (term (vector-val (* (Union [A] [B] [C])) (variant A) (variant B))))
  (check-exp-steps-to?
   (term (vector-append (* (Vectorof (Union [A] [B] [C])))
                        (vector-val (variant A) (variant B))))
   (term (vector-val (* (Union [A] [B] [C])) (variant A) (variant B))))

  ;; hash
  (check-exp-steps-to?
   (term (hash [(* Nat) (variant B)] [(* Nat) (variant A)]))
   (term (hash-val ((* Nat)) ((variant A) (variant B)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val ((* Nat)) ((variant B) (variant C))) (* Nat) (variant A)))
   (term (hash-val ((* Nat)) ((variant A) (variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val ((* Nat)) ((variant C) (variant B))) (* Nat) (variant A)))
   (term (hash-val ((* Nat)) ((variant A) (variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val () ()) (* Nat) (variant A)))
   (term (hash-val ((* Nat)) ((variant A)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val ((* Nat)) ((variant B) (variant C))) (* Nat) (variant D)))
   (term (hash-val ((* Nat)) ((variant B) (variant C) (variant D)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val ((* Nat)) ((variant B) (variant C))) (* Nat) (variant B)))
   (term (hash-val ((* Nat)) ((variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-set (* (Hash Nat (Union [A] [B] [C]))) (* Nat) (variant B)))
   (term (hash-val ((* Nat)) ((* (Union [A] [B] [C])) (variant B)))))
  (check-exp-steps-to?
   (term (hash-remove (hash-val ((* Nat)) ((variant B) (variant C))) (variant B)))
   (term (hash-val ((* Nat)) ((variant B) (variant C)))))
  (check-exp-steps-to-all? (term (hash-ref (* (Hash Nat Nat)) (* Nat)))
                           (list '(variant Nothing)
                                 '(variant Just (* Nat))))
  (check-exp-steps-to-all? (term (hash-ref (* (Hash Nat Nat)) (* Nat)))
                           (list (term (variant Nothing))
                                 (term (variant Just (* Nat)))))
  (check-exp-steps-to? (term (hash-ref (hash-val () ()) (* Nat)))
                       '(variant Nothing))
  (check-exp-steps-to? (term (hash-remove (* (Hash Nat Nat)) (* Nat)))
                       (term (* (Hash Nat Nat))))
  (check-exp-steps-to-all? (term (hash-empty? (hash-val ((* Nat)) ((variant A) (variant B)))))
                           (list (term (variant True))
                                 (term (variant False))))
  (check-exp-steps-to-all? (term (hash-empty? (* (Hash Nat Nat))))
                           (list (term (variant True))
                                 (term (variant False))))
  (check-exp-steps-to-all? (term (list-as-variant (list-val (variant A) (variant B))))
                           (list (term (variant Empty))
                                 (term (variant Cons (variant A) (list-val (variant A) (variant B))))
                                 (term (variant Cons (variant B) (list-val (variant A) (variant B))))))
  (check-exp-steps-to-all? (term (list-as-variant (* (Listof Nat))))
                           (list (term (variant Empty))
                                 (term (variant Cons (* Nat) (* (Listof Nat))))))
  (check-exp-steps-to? (term (hash-keys (hash-val ((variant A) (variant B)) ((* Nat)))))
                       (term (list-val (variant A) (variant B))))
  (check-exp-steps-to? (term (hash-keys (* (Hash Nat (Union [A] [B])))))
                       (term (* (Listof Nat))))
  (check-exp-steps-to? (term (hash-values (hash-val ((* Nat)) ((variant A) (variant B)))))
                       (term (list-val (variant A) (variant B))))
  (check-exp-steps-to? (term (hash-values (* (Hash Nat (Union [A] [B])))))
                       (term (* (Listof (Union [A] [B])))))
  (check-exp-steps-to? (term (sort-numbers-descending (list-val (* Nat))))
                       (term (list-val (* Nat))))
  (check-exp-steps-to-all? `(for/fold ([result (variant X)])
                                      ([item (list (variant A) (variant B) (variant C))])
                              (case (* (Union [True] [False]))
                                [(True) item]
                                [(False) result]))
                           (list `(variant X) `(variant A) `(variant B)`(variant C)))
  (check-exp-steps-to-all? `(for/fold ([result (variant X)])
                                      ([item (list (* Nat))])
                              (variant Y))
                           (list `(variant X) `(variant Y)))
  (test-case "Seeing the same loop twice in different contexts returns all results"
    (check-exp-steps-to-all?
     `(let ([a (case (* (Union [A] [B])) [(A) (variant A)] [(B) (variant B)])])
        (begin
          (for/fold ([dummy (* Nat)])
                    ([item (list-val (* Nat))])
            item)
          a))
     (list '(variant A) '(variant B))))

  (test-case "Loops do not return duplicate values"
    (define terminal-exps (exp-reduce* `(for/fold ([result (variant X)])
                                                  ([item (list (variant A) (variant B) (variant C))])
                                          (case (* (Union [True] [False]))
                                            [(True) item]
                                            [(False) result]))))
    (check-equal? (length terminal-exps) (length (remove-duplicates terminal-exps))))

  (check-equal? (eval-machine
                 `(spawn loc Nat
                         (goto Foo self)
                         (define-state (Foo) (m) (goto Foo)))
                 empty-effects
                 #f)
                (value-result `(Nat (spawn-addr loc NEW))
                              `(() ([(spawn-addr loc NEW)
                                     (((define-state (Foo) (m) (goto Foo)))
                                      (goto Foo (Nat (spawn-addr loc NEW))))]))))

  (test-case "Spawn in loop is a collective actor"
    (check-same-items?
     (first
      (eval-machine
       `(for/fold ([dummy (* Nat)])
                  ([item (* (Listof Nat))])
          (begin
            (spawn loc Nat (goto Foo (variant A)))
            (* Nat)))
       empty-effects
       #f))
     (list
      (machine-state `(* Nat) `(() ()))
      (machine-state `(* Nat) `(() ([(blurred-spawn-addr loc) (() (goto Foo (variant A)))]))))))

  (check-exp-steps-to? `(goto S (begin (variant A)) (begin (variant B) (variant C)))
                       `(goto S (variant A) (variant C)))

  (check-equal?
   (eval-machine
    `(begin (send (Nat (init-addr 1)) (* Nat)) (variant X))
    empty-effects
    #f)
   (eval-machine-result (list (machine-state `(variant X) `(([(init-addr 1) (* Nat) single]) ())))
                        null))

  (test-case "Send in loop is a many-of message"
    (check-same-items?
     (first
      (eval-machine
       `(for/fold ([dummy (* Nat)])
                  ([item (* (Listof Nat))])
          (send (Nat (init-addr 1)) item))
       empty-effects
       #f))
     (list
      (machine-state `(* Nat) `(() ()))
      (machine-state `(* Nat) `(([(init-addr 1) (* Nat) many]) ())))))

  ;; NOTE: these are the old tests for checking sorting of loop-sent messages, which I don't do
  ;; anymore. Keeping them around in case I change my mind
  ;;
  ;; Check for sorting of loop sends
  ;; (check-equal?
  ;;  (apply-reduction-relation handler-step#
  ;;                            (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant A)))
  ;;                                   ()
  ;;                                   ([(obs-ext 1) (variant B)])
  ;;                                   ())))
  ;;  (list (term ((loop-context (variant A))
  ;;               ()
  ;;               ([(obs-ext 1) (variant A)]
  ;;                [(obs-ext 1) (variant B)])
  ;;               ()))))
  ;; (check-equal?
  ;;  (apply-reduction-relation handler-step#
  ;;                            (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
  ;;                                   ()
  ;;                                   ([(obs-ext 1) (variant A)])
  ;;                                   ())))
  ;;  (list (term ((loop-context (variant B))
  ;;               ()
  ;;               ([(obs-ext 1) (variant A)]
  ;;                [(obs-ext 1) (variant B)])
  ;;               ()))))
  ;; (check-equal?
  ;;  (apply-reduction-relation handler-step#
  ;;                            (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
  ;;                                   ()
  ;;                                   ([(obs-ext 1) (variant A)]
  ;;                                    [(obs-ext 1) (variant B)])
  ;;                                   ())))
  ;;  (list (term ((loop-context (variant B))
  ;;               ()
  ;;               ([(obs-ext 1) (variant A)]
  ;;                [(obs-ext 1) (variant B)])
  ;;               ()))))
  ;; (check-equal?
  ;;  (apply-reduction-relation handler-step#
  ;;                            (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
  ;;                                   ()
  ;;                                   ()
  ;;                                   ())))
  ;;  (list (term ((loop-context (variant B))
  ;;               ()
  ;;               ([(obs-ext 1) (variant B)])
  ;;               ()))))

  ;; Check that internal addresses in the transmissions do not change the evaluation (had a problem
  ;; with this before)
  ;; TODO: rewrite these tests
  ;; (check-equal?
  ;;  (apply-reduction-relation* handler-step# (inject/H# (term (begin (send (Nat (init-addr 1)) (* Nat)) (goto A)))))
  ;;  (list (term ((begin (goto A)) (((init-addr 1) (* Nat) single)) ()))))

  ;; (check-equal?
  ;;  (apply-reduction-relation* handler-step#
  ;;    (inject/H# (term (begin (spawn L Nat (goto A) (define-state (A) (x) (goto A))) (goto B)))))
  ;;  (list (term ((begin (goto B)) () ([(spawn-addr L NEW) [((define-state (A) (x) (goto A))) (goto A)]])))))

  ;; ;; loop spawn test
  ;; (check-equal?
  ;;  (list->set
  ;;   (apply-reduction-relation* handler-step#
  ;;                              (inject/H#
  ;;                               (term
  ;;                                (begin
  ;;                                  (for/fold ([x (* Nat)])
  ;;                                            ([y (list-val (* Nat))])
  ;;                                    (spawn L Nat (goto A) (define-state (A) (x) (goto A))))
  ;;                                  (goto B))))))
  ;;  (set (term ((begin (goto B)) () ()))
  ;;       (term ((begin (goto B)) () ([(blurred-spawn-addr L) [((define-state (A) (x) (goto A))) (goto A)]])))))
  )

(define (vector-values v)
  (match v
    [`(vector-val ,vs ...) vs]
    [`(* (Vectorof ,type)) (list `(* ,type))]))

;; Puts the given abstract collection value (a list, vector, or hash) and puts it into a canonical
;; form
(define (normalize-collection v)
  (match v
    [`(list-val ,vs ...)
     `(list-val ,@(sort (remove-duplicates vs) sexp<?))]
    [`(vector-val ,vs ...)
     `(vector-val ,@(sort (remove-duplicates vs) sexp<?))]
    [`(hash-val ,keys ,vals)
     `(hash-val ,(sort (remove-duplicates keys) sexp<?)
                ,(sort (remove-duplicates vals) sexp<?))]))

(define (add-output existing-packets new-packet)
  (match-define `[,new-addr ,new-val ,new-mult] new-packet)
  (let loop ([reversed-checked-packets null]
             [packets-to-check existing-packets])
    (match packets-to-check
      [(list) (reverse (cons new-packet reversed-checked-packets))]
      [(list old-packet packets-to-check ...)
       (if (and (equal? (csa#-message-packet-address old-packet) new-addr)
                (equal? (csa#-message-packet-value old-packet) new-val))
           (append (reverse reversed-checked-packets)
                   (list `[,new-addr ,new-val many])
                   packets-to-check)
           (loop (cons old-packet reversed-checked-packets) packets-to-check))])))

(module+ test
  (test-equal? "Basic add-output test 1: already exists"
    (add-output (list `[(init-addr 1) (* Nat) single]
                      `[(init-addr 2) (* Nat) single]
                      `[(init-addr 3) (* Nat) single])
                `[(init-addr 2) (* Nat) single])
    (list `[(init-addr 1) (* Nat) single]
          `[(init-addr 2) (* Nat) many]
          `[(init-addr 3) (* Nat) single]))
  (test-equal? "Basic add-output test 2: does not exist"
    (add-output (list `[(init-addr 1) (* Nat) single]
                      `[(init-addr 2) (* Nat) single]
                      `[(init-addr 3) (* Nat) single])
                `[(init-addr 4) (* Nat) single])
    (list `[(init-addr 1) (* Nat) single]
          `[(init-addr 2) (* Nat) single]
          `[(init-addr 3) (* Nat) single]
          `[(init-addr 4) (* Nat) single]))
  (test-equal? "Must include wildcard outputs for the purpose of escaped addresses"
    (add-output `() `[(* (Addr (Addr Nat))) ((Addr Nat) (init-addr 2)) single])
    `([(* (Addr (Addr Nat))) ((Addr Nat) (init-addr 2)) single])))

(define (add-spawn existing-spawns new-spawn)
  (if (member new-spawn existing-spawns)
      existing-spawns
      (sort (cons new-spawn existing-spawns) sexp<?)))

;; i# csa#-transition-effect -> csa#-transition
(define (csa#-apply-transition config transition-effect)
  (define trigger (csa#-transition-effect-trigger transition-effect))
  (define addr (trigger-address trigger))
  ;; 1. If the handler was triggered by an internal message, remove the message
  (define with-trigger-message-removed
    (match trigger
      [`(internal-receive ,_ ,message) (config-remove-packet config (list addr message))]
      [_ config]))
  ;; 2. update the behavior
  (define new-behavior (csa#-transition-effect-behavior transition-effect))
  (define with-updated-behavior
    (if (precise-internal-address? addr)
        (update-behavior/precise with-trigger-message-removed addr new-behavior)
        (config-add-blurred-behaviors with-trigger-message-removed (list `[,addr ,new-behavior]))))
  ;; 3. add spawned actors
  (define with-spawns (merge-new-actors with-updated-behavior (csa#-transition-effect-spawns transition-effect)))
  ;; 4. add sent messages
  (define-values (internal-sends external-sends)
    (partition internal-output? (csa#-transition-effect-sends transition-effect)))
  (csa#-transition trigger
                   external-sends
                   (merge-messages-into-config with-spawns internal-sends)))

;; Sets the behavior for the actor with the given precise address to the given expression
(define (update-behavior/precise config address behavior)
  (match-define `(,first-actors ,_ ,later-actors)
    (config-actor-and-rest-by-address config address))
  `((,@first-actors (,address ,behavior) ,@later-actors)
    ,(csa#-config-blurred-actors config)
    ,(csa#-config-message-packets config)))

;; Abstractly adds the set of new packets to the packet set in the given config.
(define (merge-messages-into-config config new-message-list)
  (redex-let csa# ([(any_actors any_blurred any_packets) config])
    (term (any_actors
           any_blurred
           ,(merge-messages-into-packet-set (term any_packets) new-message-list)))))

;; Abstractly adds the set of new packets to the given set.
(define (merge-messages-into-packet-set packet-set new-message-list)
  (deduplicate-packets (append packet-set new-message-list)))

(module+ test
  (check-equal?
   (merge-messages-into-config (term (() () ())) (list (term ((init-addr 0) (* Nat) single))))
   (term (() () (((init-addr 0) (* Nat) single)))))

  (check-equal?
   (merge-messages-into-config (term (() () ())) (list (term ((init-addr 0) (* Nat) many))))
   (term (() () (((init-addr 0) (* Nat) many)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0) (* Nat) single))))
                       (list (term ((init-addr 0) (* Nat) single))))
   (term (() () (((init-addr 0) (* Nat) many)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0) (* Nat) single))))
                       (list (term ((init-addr 0) (* Nat) many))))
   (term (() () (((init-addr 0) (* Nat) many)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0) (* Nat) single))))
                               (list (term ((init-addr 1) (* Nat) many))))
   (term (() () (((init-addr 0) (* Nat) single) ((init-addr 1) (* Nat) many)))))

  (check-equal?
   (merge-messages-into-config (term (()
                                      ()
                                      (((init-addr 1) (* (Addr Nat)) single)
                                       ((init-addr 1) (Nat (obs-ext 0)) single))))
                               (term (((init-addr 1) (* (Addr Nat)) single))))
   (term (()
          ()
          (((init-addr 1) (* (Addr Nat)) many)
           ((init-addr 1) (Nat (obs-ext 0)) single))))))

(define (merge-new-actors config new-actors)
  (for/fold ([config config])
            ([actor new-actors])
    (match-define (list atomic-actors collective-actors messages) config)
    (match-define (list new-addr new-behavior) actor)
    (if (precise-internal-address? new-addr)
        (list (append atomic-actors (list (list new-addr new-behavior))) collective-actors messages)
        (list atomic-actors
              (add-blurred-behaviors collective-actors (list `[,new-addr ,new-behavior]))
              messages))))

(module+ test
  (define new-spawn1
    (term ((spawn-addr foo NEW) (((define-state (A) (x) (goto A))) (goto A)))))
  (define new-spawn2
    (term ((blurred-spawn-addr foo) (((define-state (A) (x) (goto A))) (goto A)))))
  (define init-actor1
    (term ((init-addr 0) (((define-state (B) (x) (goto B))) (goto B)))))
  (test-equal? "merge-new-actors test"
               (merge-new-actors
                (make-single-actor-abstract-config init-actor1)
                (list new-spawn1 new-spawn2))
               (term ((,init-actor1 ,new-spawn1)
                      (((blurred-spawn-addr foo)
                        ((((define-state (A) (x) (goto A))) (goto A)))))
                      ()))))

;; Returns a natural number indicating the maximum number of folds that may be crossed in a path from
;; the root of the given AST to a leaf
(define-metafunction csa#
  fold-depth/mf : any -> natural
  [(fold-depth/mf (folded _ any)) ,(add1 (term (fold-depth/mf any)))]
  [(fold-depth/mf (* _)) 0]
  [(fold-depth/mf (any ...))
   ,(apply max 0 (term (natural_result ...)))
   (where (natural_result ...) ((fold-depth/mf any) ...))]
  [(fold-depth/mf any) 0])

(module+ test
  (test-equal? "fold-depth 1" (term (fold-depth/mf (* Nat))) 0)
  (test-equal? "fold-depth 2"
    (term (fold-depth/mf (folded Nat (variant A (folded Nat (variant B))))))
    2)
  (test-equal? "fold-depth 3"
    (term
     (fold-depth/mf (folded Nat (variant A
                                         (folded Nat (variant B))
                                         (folded Nat (variant A (folded Nat (variant B))))))))
    3))

;; Returns true if the given expression contains *any* address
(define (csa#-contains-address? e)
  (not (empty? (csa#-contained-addresses e))))

;; Returns the list of all addresses in the given term (possibly with duplicates)
(define (csa#-contained-addresses t)
  (match t
    [(or `(init-addr ,_)
         `(spawn-addr ,_ ,_)
         `(blurred-spawn-addr ,_)
         `(* (Addr ,_))
         `(obs-ext ,_))
     (list t)]
    [(list subterms ...) (append* (map csa#-contained-addresses subterms))]
    [_ null]))

(module+ test
  (test-equal? "csa#-contained-addresses"
    (csa#-contained-addresses (term ((Nat (init-addr 1)) (Nat (obs-ext 2)))))
    (list `(init-addr 1) `(obs-ext 2)))

  (test-equal? "csa#-contained-addresses"
    (csa#-contained-addresses (term ((abc 1 Nat) (def 2 Nat))))
    null)

  (test-equal? "csa#-contained-address?"
    (csa#-contained-addresses (term (((abc) (Nat (spawn-addr 3 OLD))) ())))
    (list `(spawn-addr 3 OLD))))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define (binding var val) `[,var ,val])
(define (binding-var binding) (first binding))
(define (binding-val binding) (second binding))
(define (remove-bindings bindings vars-to-remove)
  (filter (lambda (binding) (not (memq (binding-var binding) vars-to-remove))) bindings))

;; e# (listof [x v#]) -> e#
(define (csa#-subst-n exp bindings)
  ;; NOTE: substitution written in Racket rather than Redex for performance. We also do all bindings
  ;; at once, rather than one at a time, to reduce the number of times we traverse the full AST
  (define (do-subst other-exp) (csa#-subst-n other-exp bindings))
  (define (shadow vars) (remove-bindings bindings vars))
  (match exp
    [(? symbol?)
     (match (findf (lambda (binding) (eq? (binding-var binding) exp)) bindings)
       [#f exp]
       [binding (binding-val binding)])]
    [`(* ,type) exp]
    [(? typed-address?) exp]
    [`(spawn ,loc ,type ,init ,states ...)
     (define non-self-bindings (shadow (list 'self)))
     (if (empty? non-self-bindings)
         exp
         `(spawn ,loc
                 ,type
                 ,(csa#-subst-n init non-self-bindings)
                 ,@(map (lambda (s) (csa#-subst-n/Q# s non-self-bindings)) states)))]
    [`(goto ,s ,args ...) `(goto ,s ,@(map do-subst args))]
    [`(printf ,str ,args ...) `(printf ,str ,@(map do-subst args))]
    [(list (and kw (or 'send 'begin (? primop?) 'list 'list-val 'vector 'vector-val 'loop-context)) args ...)
     `(,kw ,@(map do-subst args))]
    [`(hash-val ,args1 ,args2)
     `(hash-val ,(map do-subst args1) ,(map do-subst args2))]
    [`(let ([,new-vars ,new-vals] ...) ,body)
     (define new-let-bindings (map binding new-vars (map do-subst new-vals)))
     `(let ,new-let-bindings ,(csa#-subst-n body (shadow new-vars)))]
    [`(case ,body ,clauses ...)
     `(case ,(do-subst body) ,@(map (curryr csa#-subst-n/case-clause bindings) clauses))]
    [`(variant ,tag ,args ...) `(variant ,tag ,@(map do-subst args))]
    [`(record [,labels ,fields] ...)
     `(record ,@(map (lambda (l f) `(,l ,(do-subst f))) labels fields))]
    [`(: ,e ,l) `(: ,(do-subst e) ,l)]
    [`(! ,e [,l ,e2]) `(! ,(do-subst e) [,l ,(do-subst e2)])]
    [(list (and kw (or 'fold 'unfold 'folded)) type args ...)
     `(,kw ,type ,@(map do-subst args))]
    [`(hash [,keys ,vals] ...)
     `(hash ,@(map (lambda (k v) `[,(do-subst k) ,(do-subst v)]) keys vals))]
    [`(for/fold ([,x1 ,e1]) ([,x2 ,e2]) ,body)
     `(for/fold ([,x1 ,(do-subst e1)])
                ([,x2 ,(do-subst e2)])
        ,(csa#-subst-n body (shadow (list x1 x2))))]
    [`(coerce ,e ,type) `(coerce ,(do-subst e) ,type)]))

;; OPTIMIZE: perhaps this should use non-Redex match instead?
(define (typed-address? exp)
  (match exp
    [`(* (Addr ,_)) #t]
    [`(,_ (,(or 'init-addr 'spawn-addr 'blurred-spawn-addr 'obs-ext) ,_ ...)) #t]
    [_ #f]))

(module+ test
  (check-true (typed-address? '(* (Addr Nat))))
  (check-false (typed-address? '(* (Union [A (Addr Nat)]))))
  (check-true (typed-address? '((Union [A] [B]) (obs-ext 1))))
  (check-true (typed-address? '((Union [A] [B]) (init-addr 1))))
  (check-true (typed-address? '((Union [A] [B]) (spawn-addr 1 OLD))))
  (check-true (typed-address? '((Union [A] [B]) (blurred-spawn-addr 1))))
  (check-false (typed-address? '((Union [A] [B]) (record))))
  (check-false (typed-address? '(obs-ext 1)))
  (check-false (typed-address? '(init-addr 1)))
  (check-false (typed-address? '(spawn-addr 1 OLD)))
  (check-false (typed-address? '(blurred-spawn-addr 1)))
  (check-not-false (typed-address? '(Nat (obs-ext 1))))
  (check-equal? (typed-address? '(foobar)) #f))

(define primop? (redex-match csa# primop))

(define (csa#-subst-n/case-clause clause bindings)
  (match-define `[(,tag ,vars ...) ,body] clause)
  `[(,tag ,@vars) ,(csa#-subst-n body (remove-bindings bindings vars))])

(define (csa#-subst-n/Q# Q bindings)
  (match Q
    ;; No timeout
    [`(define-state (,q ,(and full-args `[,state-args ,arg-types]) ...) (,message-arg) ,body)
     `(define-state (,q ,@full-args) (,message-arg)
        ,(csa#-subst-n body (remove-bindings bindings (cons message-arg state-args))))]
    ;; Has timeout
    [`(define-state (,q ,(and full-args `[,state-args ,arg-types]) ...) (,message-arg)
        ,body
        [(timeout ,timeout-exp) ,timeout-body])
     `(define-state (,q ,@full-args) (,message-arg)
        ,(csa#-subst-n body (remove-bindings bindings (cons message-arg state-args)))
        [(timeout ,(csa#-subst-n timeout-exp (remove-bindings bindings state-args)))
         ,(csa#-subst-n timeout-body (remove-bindings bindings state-args))])]))

(module+ test
  (check-equal? (csa#-subst-n '(begin x) (list `[x (* Nat)])) '(begin (* Nat)))
  (check-equal? (csa#-subst-n '(send x y) (list `[y (* Nat)])) '(send x (* Nat)))
  (check-equal? (csa#-subst-n '(Nat (obs-ext 1)) (list `[x (* Nat)])) '(Nat (obs-ext 1)))
  (check-equal? (csa#-subst-n '(= x y) (list `[x (* Nat)])) '(= (* Nat) y))
  (check-equal? (csa#-subst-n '(! (record [a x]) [a (* Nat)]) (list `[x (* Nat)]))
                '(! (record [a (* Nat)]) [a (* Nat)]))
  (check-equal? (csa#-subst-n/case-clause `[(Cons p) (begin p x)] (list `[p (* Nat)]))
                (term [(Cons p) (begin p x)]))
  (check-equal? (csa#-subst-n/case-clause `[(Cons p) (begin p x)] (list `[x (* Nat)]))
                (term [(Cons p) (begin p (* Nat))]))
  (check-equal? (csa#-subst-n `(list (* Nat) x) (list `[x (* Nat)]))
                (term (list (* Nat) (* Nat))))
  (check-equal? (csa#-subst-n `(vector (* Nat) x) (list `[x (* Nat)]))
                (term (vector (* Nat) (* Nat))))
  (check-equal? (csa#-subst-n `(variant Foo (* Nat)) (list `[a (* Nat)]))
                (term (variant Foo (* Nat))))
  (check-equal? (csa#-subst-n `((Union [A] [B]) (init-addr 1)) (list `[x (* Nat)]))
                `((Union [A] [B]) (init-addr 1)))
  (check-equal? (csa#-subst-n `(coerce x (Addr (Union [B])))
                              (list `[x ((Union [A] [B]) (init-addr 1))]))
                `(coerce ((Union [A] [B]) (init-addr 1)) (Addr (Union [B]))))
  (test-equal? "spawn subst 1"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self (* Nat))
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[self (Nat (init-addr 2))]))
    (term (spawn loc
                 Nat
                 (goto A self (* Nat))
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 2"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self (* Nat))
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[x (Nat (init-addr 2))]))
    (term (spawn loc
                 Nat
                 (goto A self (* Nat))
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 3"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self (* Nat))
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[y (Nat (init-addr 2))]))
    (term (spawn loc
                 Nat
                 (goto A self (* Nat))
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x (Nat (init-addr 2)) self)))))

  (test-equal? "shadowing works as expected"
    (csa#-subst-n `(begin (let ([x (* Nat)]) x) x) (list (binding 'x '(* String))))
    `(begin (let ([x (* Nat)]) x) (* String)))

    (test-equal? "let-binding test"
      (csa#-subst-n `(let ([x (* Nat)] [y (* Nat)]) (begin a x y z))
                    (list (binding 'x '(* String))
                          (binding 'z '(* String))))
      `(let ([x (* Nat)] [y (* Nat)]) (begin a x y (* String))))

  (test-equal? "state-def subst 1"
    (csa#-subst-n/Q# `(define-state (A [x Nat] [y String]) (m) (begin x y z (goto A x y)))
                     (list `[z (* Nat)]))
    `(define-state (A [x Nat] [y String]) (m) (begin x y (* Nat) (goto A x y))))

    (test-equal? "state-def subst with timeout"
      (csa#-subst-n/Q# `(define-state (A [x Nat] [y String]) (m)
                          (begin x y z (goto A x y))
                          [(timeout z) (begin z (goto A x y))])
                     (list `[z (* Nat)]))
      `(define-state (A [x Nat] [y String]) (m)
         (begin x y (* Nat) (goto A x y))
         [(timeout (* Nat)) (begin (* Nat) (goto A x y))])))

;; Substitutes the second type for X in the first type
(define-metafunction csa#
  type-subst : τ X τ -> τ
  [(type-subst Nat _ _) Nat]
  [(type-subst String _ _) String]
  [(type-subst (minfixpt X τ_1) X τ_2)
   (minfixpt X τ_1)]
  [(type-subst (minfixpt X_1 τ_1) X_2 τ_2)
   (minfixpt X_fresh (type-subst (type-subst τ_1 X_1 X_fresh) X_2 τ_2))
   (where X_fresh ,(variable-not-in (term ((minfixpt X_1 τ_1) X_2 τ_2)) (term X_1)))]
  [(type-subst X X τ) τ]
  [(type-subst X_1 X_2 τ) X_1]
  [(type-subst (Union [t τ ...] ...) X τ_2)
   (Union [t (type-subst τ X τ_2) ...] ...)]
  [(type-subst (Record [l τ_l] ...) X τ)
   (Record [l (type-subst τ_l X τ)] ...)]
  [(type-subst (Addr τ) X τ_2)
   (Addr (type-subst τ X τ_2))]
  [(type-subst (Listof τ_e) X τ) (Listof (type-subst τ_e X τ))]
  [(type-subst (Vectorof τ_e) X τ) (Vectorof (type-subst τ_e X τ))]
  [(type-subst (Hash τ_k τ_v) X τ) (Hash (type-subst τ_k X τ) (type-subst τ_v X τ))])

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; Abstracts the given CSA configuration, with a maximum recursion depth for values. Returns #f if
;; abstraction was not possible for some reason (e.g. an address was under a folded past the max fold
;; depth).
;;
;; NOTE: currently supports only no-messages, no-externals configs
(define (csa#-abstract-config concrete-config internal-addresses)
  (let/cc result-kont
   (parameterize ([abstract-config-result-continuation result-kont])
     (term (abstract-config/mf ,concrete-config ,internal-addresses ,MAX-RECURSION-DEPTH)))))

(define abstract-config-result-continuation (make-parameter #f))
(define (cancel-abstraction)
  ((abstract-config-result-continuation) #f))

(define-metafunction csa#
  abstract-config/mf : i (a_internal ...) natural_recursion-depth -> i#
  [(abstract-config/mf (((a b) ...) ; actors
                 () ; messages-in-transit
                 _ ; receptionists (ignored because the spec config manages these)
                 _ ; externals (ignored because the spec config manages these)
                 )
                (a_internal ...)
                natural_depth)
   (([a# b#] ...) () ())
   (where ([a# b#] ...) ((abstract-actor (a b) (a_internal ...) natural_depth) ...))])

(define-metafunction csa#
  abstract-actor : (a b) (a_internals ...) natural_depth -> [a# b#]
  [(abstract-actor (a_this ((Q ...) e)) (a ...) natural_depth)
   ((abstract-address a_this (a ...))
    (((abstract-Q Q (a ...) natural_depth) ...)
     (abstract-e e (a ...) natural_depth)))])

(define-metafunction csa#
  abstract-Q : Q (a_internals ...) natural_depth -> Q#
  [(abstract-Q (define-state (q [x τ] ...) (x_m) e) (a ...) natural_depth)
   (define-state (q [x τ] ...) (x_m) (abstract-e e (a ...) natural_depth))]
  [(abstract-Q (define-state (q [x τ] ...) (x_m) e [(timeout e_timeout) e_t-handler])
               (a ...)
               natural_depth)
   (define-state (q [x τ] ...) (x_m)
     (abstract-e e (a ...) natural_depth)
     [(timeout (abstract-e e_timeout (a ...) natural_depth))
      (abstract-e e_t-handler (a ...) natural_depth)])])

(module+ test
  (check-equal? (term (abstract-Q (define-state (S) (m) (goto S) [(timeout 5) (goto S)]) () 1))
                (term (define-state (S) (m) (goto S) [(timeout (* Nat)) (goto S)])))
  (check-equal? (term (abstract-Q (define-state (S) (m) (goto S)
                                    [(timeout (case x [(A) 1] [(B) 2])) (goto S)]) () 1))
                (term (define-state (S) (m) (goto S)
                        [(timeout (case x [(A) (* Nat)] [(B) (* Nat)])) (goto S)]))))

;; Abstracts the given expression to the given depth, with the given address list indicating the set
;; of internal addresses
(define-metafunction csa#
  abstract-e : e (a ...) natural_depth -> e#
  [(abstract-e natural _ _) (* Nat)]
  [(abstract-e string _ _) (* String)]
  [(abstract-e x _ _) x]
  [(abstract-e (τ a) (a_int ...) _) (τ (abstract-address a (a_int ...)))]
  [(abstract-e (goto q e ...) (a ...) natural_depth)
   (goto q (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (begin e ...) (a ...) natural_depth) (begin (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (send e_1 e_2) (a ...) natural_depth)
   (send (abstract-e e_1 (a ...) natural_depth) (abstract-e e_2 (a ...) natural_depth))]
  [(abstract-e (spawn any_location τ e Q ...) (a ...) natural_depth)
   (spawn any_location
          τ
          (abstract-e e (a ...) natural_depth)
          (abstract-Q Q (a ...) natural_depth) ...)]
  [(abstract-e (let ([x e_binding] ...) e_body) (a ...) natural)
   (let ([x (abstract-e e_binding (a ...) natural)] ...) (abstract-e e_body (a ...) natural))]
  [(abstract-e (case e_val [(t x ...) e_clause] ...) (a ...) natural_depth)
   (case (abstract-e e_val (a ...) natural_depth)
     [(t x ...) (abstract-e e_clause (a ...) natural_depth)] ...)]
  [(abstract-e (printf string e ...) (a ...) natural_depth)
   (printf string (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (primop e ...) (a ...) natural_depth)
   (primop (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (variant t e ...) (a ...) natural_depth)
   (variant t (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (record [l e] ...) (a ...) natural_depth)
   (record [l (abstract-e e (a ...) natural_depth)] ...)]
  [(abstract-e (: e l) (a ...) natural_depth) (: (abstract-e e (a ...) natural_depth) l)]
  [(abstract-e (! e_1 [l e_2]) (a ...) natural_depth)
   (! (abstract-e e_1 (a ...) natural_depth) [l (abstract-e e_2 (a ...) natural_depth)])]
  [(abstract-e (folded τ e) (a ...) 0)
   (* τ)
   ;; We're currently not able to give any addresses in a "folded" past our maximum fold-depth a sound
   ;; abstraction if the address is an internal address or an external address observed by the spec,
   ;; so we take the easy way out here and just bail out if the expression contains *any* address
   (side-condition (when (csa-contains-address? (term e)) (cancel-abstraction)))]
  [(abstract-e (folded τ e) (a ...) natural_depth)
   (folded τ (abstract-e e (a ...) ,(sub1 (term natural_depth))))]
  [(abstract-e (fold τ e) (a ...) natural_depth)
   (fold τ (abstract-e e (a ...) natural_depth))]
  [(abstract-e (unfold τ e) (a ...) natural_depth)
   (unfold τ (abstract-e e (a ...) natural_depth))]
  [(abstract-e (list v ...) (a ...) natural_depth)
   ,(normalize-collection (term (list-val (abstract-e v (a ...) natural_depth) ...)))]
  [(abstract-e (list e ...) (a ...) natural_depth)
   (list (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (vector v ...) (a ...) natural_depth)
   ,(normalize-collection (term (vector-val (abstract-e v (a ...) natural_depth) ...)))]
  [(abstract-e (vector e ...) (a ...) natural_depth)
   (vector (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (hash [v_key v_val] ...) (a ...) natural_depth)
   ,(normalize-collection (term (hash-val ((abstract-e v_key (a ...) natural_depth) ...)
                                          ((abstract-e v_val (a ...) natural_depth) ...))))]
  [(abstract-e (hash [e_key e_val] ...) (a ...) natural_depth)
   (hash [(abstract-e e_key (a ...) natural_depth) (abstract-e e_val (a ...) natural_depth)] ...)]
  [(abstract-e (for/fold ([x_1 e_1]) ([x_2 e_2]) e) (a ...) natural)
   (for/fold ([x_1 (abstract-e e_1 (a ...) natural)])
             ([x_2 (abstract-e e_2 (a ...) natural)])
     (abstract-e e (a ...) natural))]
  [(abstract-e (coerce e τ) (a ...) natural) (coerce (abstract-e e (a ...) natural) τ)])

;; Abstracts the address a, where internal-addresses is the list of all addresses belonging to actors
;; in a's implementation configuration.
(define (csa#-abstract-address a internal-addresses)
  (term (abstract-address ,a ,internal-addresses)))

(define-metafunction csa#
  abstract-address : a (a ...) -> a#
  [(abstract-address (addr natural) (_ ... (addr natural) _ ...)) (init-addr natural)]
  [(abstract-address (addr natural) _) (obs-ext natural)])

(module+ test
  (check-equal? (term (abstract-e (record [f1 1] [f2 2]) () 1))
                (term (record [f1 (* Nat)] [f2 (* Nat)])))
  (check-not-false
   (redex-match? csa#
                 (variant Foo (Nat (init-addr 1)) (Nat (obs-ext 2)))
                 (term (abstract-e (variant Foo (Nat (addr 1)) (Nat (addr 2))) ((addr 1)) 10))))
  (check-equal? (term (abstract-e (list 1 2) () 10))
                (term (list-val (* Nat))))
  (check-equal? (term (abstract-e (list 1 (let () 1)) () 10))
                (term (list (* Nat) (let () (* Nat)))))
  (check-equal? (term (abstract-e (vector 1 2) () 10))
                (term (vector-val (* Nat))))
  (check-equal? (term (abstract-e (vector 1 (let () 1)) () 10))
                (term (vector (* Nat) (let () (* Nat)))))
  (check-equal? (term (abstract-e (list (variant B) (variant A)) () 10))
                (term (list-val (variant A) (variant B))))
  (check-equal? (term (abstract-e (vector (variant B) (variant A)) () 10))
                (term (vector-val (variant A) (variant B))))
  (check-equal? (term (abstract-e (hash [1 (variant B)] [2 (variant A)]) () 10))
                (term (hash-val ((* Nat)) ((variant A) (variant B)))))
  (check-equal? (term (abstract-e (hash [1 2] [3 4]) () 10))
                (term (hash-val ((* Nat)) ((* Nat)))))
  (check-equal? (term (abstract-e (hash) () 10))
                (term (hash-val () ())))
  (check-equal? (term (abstract-e (hash [1 (let ([x 1]) x)] [3 4]) () 10))
                (term (hash [(* Nat) (let ([x (* Nat)]) x)] [(* Nat) (* Nat)])))
  (check-equal? (term (abstract-e (coerce ((Union [A] [B]) (addr 1)) (Addr (Union [B])))
                                  ((addr 1))
                                  10))
                (term (coerce ((Union [A] [B]) (init-addr 1)) (Addr (Union [B])))))
  (test-equal? "Abstraction on non-matching addresses"
               (term (abstract-e ((Union [A]) (addr 1)) ((addr 1)) 0))
               (term ((Union [A]) (init-addr 1))))
  (test-equal? "Abstraction on non-matching addresses"
               (term (abstract-e ((Union [A]) (addr 2)) ((addr 1)) 0))
               (term ((Union [A]) (obs-ext 2))))
  (test-case "Unable to abstract addresses past max fold depth"
    (define nat-addr-list-type `(minfixpt NatAddrList (Union [Nil] [Cons (Addr Nat) NatAddrList])))
    (check-false
     (csa#-abstract-config
      `((((addr 1)
          (() (folded ,nat-addr-list-type
                      (variant Cons (Nat (addr 1))
                               (folded ,nat-addr-list-type
                                       (variant Cons (Nat (addr 2))
                                                (folded ,nat-addr-list-type
                                                        (variant Nil)))))))))
        () () ())
      null))))

;; ---------------------------------------------------------------------------------------------------
;; Selecting the spawn flag to blur

(define (csa#-spawn-address? a)
  (redex-match? csa# (spawn-addr _ _) a))

(module+ test
  (test-case "New-span-addr? check"
    (define a (term (spawn-addr 5 NEW)))
    (define b (term (spawn-addr 6 OLD)))
    (define c (term (init-addr 7)))
    (check-not-false (redex-match csa# a#int a))
    (check-not-false (redex-match csa# a#int b))
    (check-not-false (redex-match csa# a#int c))
    (check-true (csa#-spawn-address? a))
    (check-true (csa#-spawn-address? b))
    (check-false (csa#-spawn-address? c))))

(define (csa#-spawn-address-flag a)
  (redex-let csa# ([(spawn-addr _ spawn-flag) a])
    (term spawn-flag)))

;; impl-config (Listof a#ext) -> (Listof spawn-flag)
;;
;; Returns the list of all spawn-flags such that at least one actor in the config whose address has
;; one of those spawn flags "knows" (i.e. syntactically contains in its behavior) at least one of the
;; addresses in the relevant-externals list
(define (csa#-flags-that-know-externals config relevant-externals)
  (define all-spawns
    (filter (lambda (actor) (csa#-spawn-address? (csa#-actor-address actor)))
            (csa#-config-actors config)))
  (define-values (old-spawns new-spawns)
    (partition
     (lambda (actor)
       (equal? (csa#-spawn-address-flag (csa#-actor-address actor)) 'OLD))
     all-spawns))
  (append
   (if (contains-relevant-externals? old-spawns relevant-externals) (list 'OLD) null)
   (if (contains-relevant-externals? new-spawns relevant-externals) (list 'NEW) null)))

;; Returns true if the given list of actors contains in their behaviors at least one of the given
;; external addresses
(define (contains-relevant-externals? actors externals)
  (not
   (set-empty?
    (set-intersect (list->set externals) (list->set (externals-in actors))))))

;; ---------------------------------------------------------------------------------------------------
;; Blurring

;; impl-config spawn-flag (a#ext ...) -> (List impl-config (Listof a#int))
;;
;; Blurs all actors in the configuration with the given spawn flag, and blurs any external address not
;; in relevant-externals. Returns the blurred impl-config as well as the list of internal addresses
;; that were blurred. See the discussion of blurring in main.rkt for more details.
(define (csa#-blur-config config spawn-flag-to-blur relevant-externals)
  ;; 1. Remove all blurred addresses and their messages
  (match-define (list remaining-config removed-actors)
    (remove-actors-by-flag config spawn-flag-to-blur))
  ;; 2. Do the actual rename/blur for both internals and externals (in remaining config, removed
  ;; actors, and removed messages)
  (define removed-actor-addresses (map csa#-actor-address removed-actors))
  (match-define (list renamed-config renamed-removed-actors)
    (csa#-blur-addresses (list remaining-config removed-actors)
                         removed-actor-addresses
                         relevant-externals))
  ;; 3. Deduplicate message packets in the packet set that now have the same content (the renaming
  ;; might have caused messages with differing content or address to now be the same)
  (define deduped-packets (deduplicate-packets (csa#-config-message-packets renamed-config)))
  ;; 4. Merge blurred behaviors in and subsume others as necessary
  (define existing-addr-behavior-pairs
    (append*
     (for/list ([collective (csa#-config-blurred-actors renamed-config)])
       (map (curry list (csa#-blurred-actor-address collective))
            (csa#-blurred-actor-behaviors collective)))))
  (define updated-blurred-actors
    (add-blurred-behaviors null (append existing-addr-behavior-pairs renamed-removed-actors)))
  (list
   (term (,(csa#-config-actors renamed-config)
          ,updated-blurred-actors
          ,deduped-packets))
   removed-actor-addresses))

(module+ test
  (test-equal? "check that messages with blurred addresses get merged together"
    (csa#-blur-config
     (term (()
            ()
            (((init-addr 2) (Nat (obs-ext 1)) single)
             ((init-addr 2) (Nat (obs-ext 2)) single)
             ((init-addr 2) (Nat (obs-ext 3)) single))))
     'NEW
     (list '(obs-ext 3)))
    (list
     (term (()
            ()
            (((init-addr 2) (* (Addr Nat)) many)
             ((init-addr 2) (Nat (obs-ext 3)) single))))
     null))

  (test-equal? "Will remove actors by spawn flag"
    (csa#-blur-config
     (term (([(spawn-addr 1 OLD) (() (goto A))]
             [(spawn-addr 1 NEW) (() (goto A))])
            ()
            ()))
     'OLD
     null)
    (list
     (term (([(spawn-addr 1 NEW) (() (goto A))])
            ([(blurred-spawn-addr 1) ((() (goto A)))])
            ()))
     (list '(spawn-addr 1 OLD))))

  (test-equal? "Merge collective behaviors when they become the same"
    (csa#-blur-config
     (term (()
            ([(blurred-spawn-addr 1)
              ((() (goto A (Nat (obs-ext 1))))
               (() (goto A (* (Addr Nat)))))])
            ()))
     'OLD
     null)
    (list
     (term (()
            ([(blurred-spawn-addr 1) ((() (goto A (* (Addr Nat)))))])
            ()))
     (list))))

;; impl-config spawn-flag -> impl-config ((a# b#) ...)
;;
;; Removes from the configuration all actors that have the given spawn flag in their address, along
;; with any in-transit message packets sent to them. Returns the resulting config, and the list of
;; removed actors.
(define (remove-actors-by-flag config flag)
  (define (should-be-removed? actor)
    ;; should be removed if it's a spawn address with the given spawn flag AND the same address with
    ;; the opposite flag exists
    (define addr (csa#-actor-address actor))
    (and (has-spawn-flag? addr flag)
         (csa#-config-actor-by-address config (switch-spawn-flag addr))))
  (define-values (removed-actors remaining-actors)
    (partition should-be-removed? (csa#-config-actors config)))
  (list (term (,remaining-actors
               ,(csa#-config-blurred-actors config)
               ,(csa#-config-message-packets config)))
        removed-actors))

(define (switch-spawn-flag address)
  (match address
    [`(spawn-addr ,any-loc NEW) `(spawn-addr ,any-loc OLD)]
    [`(spawn-addr ,any-loc OLD) `(spawn-addr ,any-loc NEW)]))

(module+ test
  (test-equal? "remove-actors test"
    (remove-actors-by-flag
     (term
      ((((spawn-addr 1 OLD) ,test-behavior1)
        ((spawn-addr 1 NEW) ,test-behavior1)
        ((spawn-addr 2 OLD) ,test-behavior1)
        ((spawn-addr 3 NEW) ,test-behavior1))
       ()
       ()))
     'NEW)
    (list
     (term
      ((((spawn-addr 1 OLD) ,test-behavior1)
        ((spawn-addr 2 OLD) ,test-behavior1)
        ((spawn-addr 3 NEW) ,test-behavior1))
       ()
       ()))
     (list (term ((spawn-addr 1 NEW) ,test-behavior1))))))

;; term (a#int-without-type ...) (a#ext-without-type ...) -> term
;;
;; Renames internal addresses in internals-to-blur and external addresses *not* in
;; relevant-externals to their respective imprecise forms
;;
;; NOTE: any updates to this function may also need to be added to pseudo-blur
(define (csa#-blur-addresses some-term internals-to-blur relevant-externals)
  (match some-term
    [(and addr `(spawn-addr ,loc ,_))
     (if (member addr internals-to-blur)
         (term (blurred-spawn-addr ,loc))
         addr)]
    [`(,type ,(and addr `(obs-ext ,_)))
     (if (member addr relevant-externals)
         some-term
         (term (* (Addr ,type))))]
    [(list (and keyword (or `vector-val 'list-val 'hash-val)) terms ...)
     (define blurred-args (map (curryr csa#-blur-addresses internals-to-blur relevant-externals) terms))
     (normalize-collection `(,keyword ,@blurred-args))]
    [`(hash-val ,keys ,vals)
     (define blurred-keys (map (curryr csa#-blur-addresses internals-to-blur relevant-externals) keys))
     (define blurred-vals (map (curryr csa#-blur-addresses internals-to-blur relevant-externals) vals))
     (normalize-collection `(hash-val ,blurred-keys ,blurred-vals))]
    [(list terms ...)
     (map (curryr csa#-blur-addresses internals-to-blur relevant-externals) terms)]
    [_ some-term]))

(module+ test
  (test-equal? "blur test"
    (csa#-blur-addresses
     (term (((Nat (spawn-addr foo OLD)) (Nat (spawn-addr foo NEW)))
            (Nat (spawn-addr bar NEW))
            (Nat (obs-ext 1))
            (Nat (obs-ext 2))
            (Nat (spawn-addr bar OLD))
            (Nat (spawn-addr baz OLD))
            (Nat (spawn-addr quux NEW))))
     (list (term (spawn-addr foo NEW)) (term (spawn-addr bar NEW)))
     (list '(obs-ext 2)))
    (term (((Nat (spawn-addr foo OLD)) (Nat (blurred-spawn-addr foo)))
           (Nat (blurred-spawn-addr bar))
           (* (Addr Nat))
           (Nat (obs-ext 2))
           (Nat (spawn-addr bar OLD))
           (Nat (spawn-addr baz OLD))
           (Nat (spawn-addr quux NEW)))))

  (test-equal? "blur test 2"
    (csa#-blur-addresses
     (redex-let* csa#
                 ([(a# b#)
                   (term
                       ((init-addr 0)
                        (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                            (begin
                              (send (Nat (obs-ext 1)) (* Nat))
                              (send (Nat (obs-ext 2)) (* Nat))
                              (goto A x y z))))
                         (goto A (Nat (obs-ext 2)) (Nat (obs-ext 3)) (Nat (obs-ext 4))))))]
                  [i# (term (([a# b#]) () ()))])
                 (term i#))
     null
     (term ((obs-ext 1) (obs-ext 3))))
    (redex-let* csa#
                ([(a# b#)
                  (term
                         ((init-addr 0)
                          (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                              (begin
                                (send (Nat (obs-ext 1)) (* Nat))
                                (send (* (Addr Nat)) (* Nat))
                                (goto A x y z))))
                           (goto A (* (Addr Nat)) (Nat (obs-ext 3)) (* (Addr Nat))))))]
                 [i# (term (([a# b#]) () ()))])
                (term i#)))

  ;; Make sure duplicates are removed from vectors, lists, and hashes
  (test-equal? "blur test 3"
   (csa#-blur-addresses
    (redex-let csa#
        ([e# (term (hash-val ((* Nat))
                             ((Nat (obs-ext 1))
                              (Nat (obs-ext 2))
                              (Nat (obs-ext 3))
                              (Nat (obs-ext 4)))))])
      (term e#))
    null
    '((obs-ext 1) (obs-ext 3)))
   ;; Some reordering happens as a result of normalize-collection
   (term (hash-val ((* Nat)) ((* (Addr Nat)) (Nat (obs-ext 1)) (Nat (obs-ext 3))))))

  (test-equal? "blur test 4"
   (csa#-blur-addresses
    (redex-let csa#
        ([e# (term (list-val (Nat (obs-ext 1))
                             (Nat (obs-ext 2))
                             (Nat (obs-ext 3))
                             (Nat (obs-ext 4))))])
      (term e#))
    null
    null)
   (term (list-val (* (Addr Nat)))))

  (test-equal? "blur test 5"
   (csa#-blur-addresses
    (redex-let csa#
        ([e# (term (vector-val (Nat (obs-ext 1))
                               (Nat (obs-ext 2))
                               (Nat (obs-ext 3))
                               (Nat (obs-ext 4))))])
      (term e#))
    null
    `((obs-ext 1) (obs-ext 2) (obs-ext 3) (obs-ext 4)))
   (term (vector-val (Nat (obs-ext 1)) (Nat (obs-ext 2)) (Nat (obs-ext 3)) (Nat (obs-ext 4)))))

  (test-equal? "Blur for addresses with differing types"
    (csa#-blur-addresses `(vector-val ((Union [A] [B]) (obs-ext 3))
                                      ((Union [A] [B]) (obs-ext 4))
                                      ((Union [A] [B]) (spawn-addr 1 OLD))
                                      ((Union [A] [B]) (spawn-addr 2 OLD))
                                      ((Union [A]) (obs-ext 3))
                                      ((Union [A]) (obs-ext 4))
                                      ((Union [A]) (spawn-addr 1 OLD))
                                      ((Union [A]) (spawn-addr 2 OLD)))
                         `((spawn-addr 1 OLD))
                         `((obs-ext 3)))
    ;; Some reordering happens as a result of normalize-collection
    `(vector-val (* (Addr (Union [A])))
                 (* (Addr (Union [A] [B])))
                 ((Union [A]) (blurred-spawn-addr 1))
                 ((Union [A]) (obs-ext 3))
                 ((Union [A]) (spawn-addr 2 OLD))
                 ((Union [A] [B]) (blurred-spawn-addr 1))
                 ((Union [A] [B]) (obs-ext 3))
                 ((Union [A] [B]) (spawn-addr 2 OLD)))))

;; Returns #t if the address is of the form (spawn-addr _ flag _), #f otherwise.
(define (has-spawn-flag? addr flag)
  (match addr
    [`(spawn-addr ,_ ,addr-flag)
     (equal? addr-flag flag)]
    [_ #f]))

;; i# (Listof (List a#int b#)) -> i#
(define (config-add-blurred-behaviors config new-addr-behavior-pairs)
  (match-define `(,atomics ,collectives ,messages) config)
  `(,atomics ,(add-blurred-behaviors collectives new-addr-behavior-pairs) ,messages))

;; β# (Listof (List a#int b#)) -> β#
;;
;; Adds each address/behavior pair in behaviors-to-add as possible behaviors in blurred-actors.
(define (add-blurred-behaviors blurred-actors new-addr-behavior-pairs)
  (for/fold ([blurred-actors blurred-actors])
            ([new-addr-behavior-pair new-addr-behavior-pairs])
    (match-define `(,target-address ,new-behavior) new-addr-behavior-pair)
    (match (find-with-rest (lambda (actor) (equal? (csa#-blurred-actor-address actor) target-address))
                           blurred-actors)
      [(list before `(,_ ,found-behaviors) after)
       ;; check if any existing behavior subsumes this one, and remove any behaviors that this one
       ;; subsumes
       (define updated-behaviors
         (let loop ([behaviors-to-check found-behaviors]
                    [checked-behaviors null])
           (match behaviors-to-check
             [(list) (append checked-behaviors (list new-behavior))]
             [(list current-behavior behaviors-to-check ...)
              (match (compare-behavior new-behavior current-behavior #t)
                [(or 'eq 'lt) (append checked-behaviors (list current-behavior) behaviors-to-check)]
                ['gt (loop behaviors-to-check checked-behaviors)]
                ['not-gteq
                 (loop behaviors-to-check (append checked-behaviors (list current-behavior)))])])))
       (append before (list `(,target-address ,updated-behaviors)) after)]
      [#f (append blurred-actors (list `(,target-address (,new-behavior))))])))

(module+ test
  (define behavior1
    (term (((define-state (A) (x) (goto A))) (goto A))))
  (define behavior2
    (term (((define-state (B) (r) (begin (send r (* Nat)) (goto B)))) (goto B))))
  (define behavior3
    (term (((define-state (C [x (Listof Nat)]) (r) (begin (send r (* Nat)) (goto C x))))
           (goto C (list-val)))))
  (define behavior3-greater
    (term (((define-state (C [x (Listof Nat)]) (r) (begin (send r (* Nat)) (goto C x))))
           (goto C (list-val (* Nat))))))

  (test-begin
    (check-true (redex-match? csa# b# behavior1))
    (check-true (redex-match? csa# b# behavior2))
    (check-true (redex-match? csa# b# behavior3)))

  (test-equal? "config-add-blurred-behaviors same behavior"
    (config-add-blurred-behaviors (term (() (((blurred-spawn-addr 1) (,behavior1))) ()))
                                  (list (term ((blurred-spawn-addr 1) ,behavior1))))
    (term (() (((blurred-spawn-addr 1) (,behavior1))) ())))

  (test-equal? "add-blurred-behaviors"
    (add-blurred-behaviors (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2))
                                  ((blurred-spawn-addr 2) (,behavior3))))
                           (list (term ((blurred-spawn-addr 1) ,behavior3))
                                 (term ((blurred-spawn-addr 3) ,behavior3))
                                 (term ((blurred-spawn-addr 1) ,behavior1))))
    (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3))
           ((blurred-spawn-addr 2) (,behavior3))
           ((blurred-spawn-addr 3) (,behavior3)))))

  (test-equal? "add-blurred-behaviors greater behavior"
    (add-blurred-behaviors (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3))))
                           (list (term ((blurred-spawn-addr 1) ,behavior3-greater))))
    (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3-greater)))))

  (test-equal? "add-blurred-behaviors lesser behavior"
    (add-blurred-behaviors
     (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3-greater))))
     (list (term ((blurred-spawn-addr 1) ,behavior3))))
    (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3-greater)))))

  (test-equal? "add-blurred-behaviors same behavior"
    (add-blurred-behaviors (term (((blurred-spawn-addr 1) (,behavior1))))
                           (list (term ((blurred-spawn-addr 1) ,behavior1))))
    (term (((blurred-spawn-addr 1) (,behavior1))))))

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization (the sorting of config components)

;; Sorts the components of an impl configuration as follows:
;; * atomic actors by address
;; * collective actors by address
;; * behaviors of a collective actor by the entire behavior
;; * message packets by the entire packet
(define (csa#-sort-config-components config)
  (match-define `(,atomic-actors ,collective-actors ,packets) config)
  (define (actor<? a b)
    (sexp<? (csa#-actor-address a) (csa#-actor-address b)))
  (define sorted-atomic-actors (sort atomic-actors actor<?))
  (define sorted-collective-actors
    (sort (map sort-collective-actor-behaviors collective-actors) actor<?))
  (define sorted-packets (sort packets sexp<?))
  `(,sorted-atomic-actors ,sorted-collective-actors ,sorted-packets))

(define (sort-collective-actor-behaviors actor)
  (match-define `(,addr ,behaviors) actor)
  `(,addr ,(sort behaviors sexp<?)))

(module+ test
  (define sort-components-test-config
    `(;; atomic actors
      ([(init-addr 2) (() (goto A))]
       [(init-addr 1) (() (goto Z))])
      ;; collective actors
      ([(blurred-spawn-addr Q) ((() (goto Z))
                                (() (goto M))
                                (() (goto A)))]
       [(blurred-spawn-addr B) ((() (goto Z))
                                (() (goto M))
                                (() (goto A)))])
      ;; messages
      ([(init-addr 2) (* Nat) single]
       [(init-addr 1) (* Nat) single])))
  (check-true (redex-match? csa# i# sort-components-test-config))
  (check-equal?
   (csa#-sort-config-components sort-components-test-config)
   `(;; atomic actors
     ([(init-addr 1) (() (goto Z))]
      [(init-addr 2) (() (goto A))])
      ;; collective actors
     ([(blurred-spawn-addr B) ((() (goto A))
                               (() (goto M))
                               (() (goto Z)))]
      [(blurred-spawn-addr Q) ((() (goto A))
                               (() (goto M))
                               (() (goto Z)))])
      ;; messages
     ([(init-addr 1) (* Nat) single]
      [(init-addr 2) (* Nat) single]))))

;; ---------------------------------------------------------------------------------------------------
;; Duplicate message merging

;; Merges all message packet entries in the given μ# that have the same address and content into a
;; single entry with the many-of multiplicity. These kinds of duplicate messages may arise, for
;; example, during blurring.
;;
;; TODO: Do some kind of ordering on the messages to avoid symmetry issues
(define (deduplicate-packets message-list)
  (let loop ([processed-messages null]
             [remaining-messages message-list])
    (match remaining-messages
      [(list) processed-messages]
      [(list message remaining-messages ...)
       (define remaining-without-duplicates (remove* (list message) remaining-messages same-message?))
       (define new-message
         ;; message stays same if nothing was duplicated, else have to change multiplicity
         (if (equal? remaining-without-duplicates remaining-messages)
             message
             (match-let ([`[,addr ,value ,_] message]) `(,addr ,value many))))
       (loop (append processed-messages (list new-message))
             remaining-without-duplicates)])))

(module+ test
  (test-equal? "Deduplicate-packets test"
    (deduplicate-packets (list `[(init-addr 1) (* Nat) single]
                               `[(init-addr 2) (* Nat) single]
                               `[(init-addr 1) (* Nat) single]
                               `[(init-addr 2) (* String) many]))
    (list `[(init-addr 1) (* Nat) many]
          `[(init-addr 2) (* Nat) single]
          `[(init-addr 2) (* String) many])))

;; For two "messages" (the things inside the message queue in a config), returns true if they have the
;; same address and value
(define (same-message? m1 m2)
  (redex-let csa# ([(a#_1 v#_1 _) m1]
                   [(a#_2 v#_2 _) m2])
    (equal? (term (a#_1 v#_1)) (term (a#_2 v#_2)))))

(module+ test
  (check-equal?
   (deduplicate-packets
    (term (((obs-ext 1) (* Nat) single)
           ((obs-ext 1) (* Nat) single))))
   (term (((obs-ext 1) (* Nat) many))))

    (check-equal?
   (deduplicate-packets
    (term (((obs-ext 1) (* Nat) single)
           ((obs-ext 1) (* Nat) single)
           ((obs-ext 1) (* Nat) single))))
   (term (((obs-ext 1) (* Nat) many))))

  (check-equal?
   (deduplicate-packets
    (term (((obs-ext 1) (* Nat) single)
           ((obs-ext 2) (* Nat) single)
           ((obs-ext 3) (* Nat) many)
           ((* (Addr Nat)) (* Nat) many)
           ((obs-ext 1) (* Nat) single)
           ((* (Addr Nat)) (* Nat) single))))
   (term (((obs-ext 1) (* Nat) many)
          ((obs-ext 2) (* Nat) single)
          ((obs-ext 3) (* Nat) many)
          ((* (Addr Nat)) (* Nat) many)))))

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (make-single-actor-abstract-config actor)
  (term (make-single-actor-abstract-config/mf ,actor)))

(define-metafunction csa#
  make-single-actor-abstract-config/mf : (a# b#) -> i#
  [(make-single-actor-abstract-config/mf (a# b#))
   (([a# b#]) () ())])

;; ---------------------------------------------------------------------------------------------------
;; Selectors

;; Returns a list of actors ([a# b#] tuples)
(define (csa#-config-actors config)
  (first config))

;; Returns the list of blurred actors in the config
(define (csa#-config-blurred-actors config)
  (second config))

;; Returns the configuration's set of in-flight message packets
(define (csa#-config-message-packets config)
  (third config))

(define (config-actor-and-rest-by-address config addr)
  (find-with-rest (lambda (actor) (equal? (csa#-actor-address actor) addr))
                  (csa#-config-actors config)))

(define (config-collective-actor-and-rest-by-address config addr)
  (find-with-rest (lambda (actor) (equal? (csa#-blurred-actor-address actor) addr))
                  (csa#-config-blurred-actors config)))

;; Returns the given precise actor with the given address, or #f if it's not in the given config
(define (csa#-config-actor-by-address config addr)
  (findf (lambda (actor) (equal? (csa#-actor-address actor) addr))
         (csa#-config-actors config)))

;; Returns the collective actor with the given address, or #f if it doesn't exist
(define (csa#-config-collective-actor-by-address config addr)
  (findf (lambda (a) (equal? (csa#-blurred-actor-address a) addr))
         (csa#-config-blurred-actors config)))

;; τa# -> τ
;;
;; Returns the type for the given typed address
(define (csa#-address-type ta)
  (term (address-type/mf ,ta)))

(define-metafunction csa#
  address-type/mf : τa# -> τ
  [(address-type/mf (* (Addr τ))) τ]
  [(address-type/mf (τ _)) τ])

;; Returns the address portion of an abstract typed address
(define (csa#-address-strip-type a)
  (term (address-strip-type/mf ,a)))

(define-metafunction csa#
  address-strip-type/mf : τa# -> any
  [(address-strip-type/mf (* (Addr τ))) (* (Addr τ))]
  [(address-strip-type/mf (_ a#)) a#])

(define (csa#-actor-address a)
  (first a))

(define (csa#-blurred-actor-address a)
  (first a))

(define (csa#-blurred-actor-behaviors a)
  (second a))

;; (a#int v# multiplicity) -> (a#int v#)
(define (csa#-packet-entry->packet entry)
  (redex-let csa# ([(a#int v# _) entry])
    (term (a#int v#))))

(define (csa#-message-packet-address packet)
  (first packet))

(define (csa#-message-packet-value packet)
  (second packet))

(define (csa#-message-packet-multiplicity packet)
  (third packet))

(define csa#-output-address car)

(define csa#-output-message cadr)

(define csa#-output-multiplicity caddr)

;; (a# b#) -> b#
(define (actor-behavior actor)
  (second actor))

;; Returns the behaviors of the actor for the indicated collective OR atomic address (or #f if the
;; actor does not exist)
(define (csa#-behaviors-of config addr)
  (if (precise-internal-address? addr)
      (match (csa#-config-actor-by-address config addr)
        [#f #f]
        [actor (list (actor-behavior actor))])
      (match (csa#-config-collective-actor-by-address config addr)
        [#f #f]
        [actor (csa#-blurred-actor-behaviors actor)])))

(module+ test
  (define behavior-test-config
    (term (([(init-addr 1) (() (goto A))])
           ([(blurred-spawn-addr 2)
             ((() (goto B))
              (() (goto C)))])
           ())))
  (test-equal? "csa#-behaviors-of atomic"
    (csa#-behaviors-of behavior-test-config `(init-addr 1))
    (list '(() (goto A))))
  (test-equal? "csa#-behaviors-of collective"
    (csa#-behaviors-of behavior-test-config `(blurred-spawn-addr 2))
    (list '(() (goto B)) '(() (goto C)))))

;; Returns all behaviors assigned to the blurred actor with the given address in the given config
(define (blurred-actor-behaviors-by-address config address)
  (csa#-blurred-actor-behaviors (csa#-config-collective-actor-by-address config address)))

(module+ test
  (test-case "Blurred actor behaviors by address"
    (redex-let csa# ([i# (term (()
                                (((blurred-spawn-addr 1) ())
                                 ((blurred-spawn-addr 2) ((() (goto A)))))
                                ()))])
      (check-equal? (blurred-actor-behaviors-by-address (term i#) `(blurred-spawn-addr 2))
                    (list (term (() (goto A))))))))

;; Returns the state definitions of the given behavior
(define (behavior-state-defs behavior)
  (first behavior))

(define (behavior-exp behavior)
  (second behavior))

(define (goto-state-name goto-exp) (second goto-exp))
(define (goto-state-args goto-exp) (cddr goto-exp))

(define (case-clause-pattern clause) (first clause))
(define (case-clause-body clause) (second clause))

(define (state-def-by-name state-defs state-name)
  (findf (lambda (state-def) (equal? state-name (first (second state-def)))) state-defs))

;; ---------------------------------------------------------------------------------------------------
;; Boolean Logic

(define-metafunction csa#
  canonicalize-boolean : v# -> v#
  [(canonicalize-boolean (variant True)) (variant True)]
  [(canonicalize-boolean (variant False)) (variant False)]
  [(canonicalize-boolean (* (Union (True) (False)))) (* (Union (True) (False)))]
  [(canonicalize-boolean (* (Union (False) (True)))) (* (Union (True) (False)))]
  [(canonicalize-boolean (* (Union (True)))) (variant True)]
  [(canonicalize-boolean (* (Union (False)))) (variant False)])

(define-metafunction csa#
  csa#-and : v# v# -> v#
  [(csa#-and (variant False) _) (variant False)]
  [(csa#-and _ (variant False)) (variant False)]
  [(csa#-and (variant True) (variant True)) (variant True)]
  [(csa#-and _ _) (* (Union (True) (False)))])

(define-metafunction csa#
  csa#-or : v# v# -> v#
  [(csa#-or (variant True) _) (variant True)]
  [(csa#-or _ (variant True)) (variant True)]
  [(csa#-or (variant False) (variant False)) (variant False)]
  [(csa#-or _ _) (* (Union (True) (False)))])

(define-metafunction csa#
  csa#-not : v# -> v#
  [(csa#-not (variant True)) (variant False)]
  [(csa#-not (variant False)) (variant True)]
  [(csa#-not (* (Union (True) (False)))) (* (Union (True) (False)))])

(module+ test
  (define boolean-maybe (term (* (Union (True) (False)))))
  (check-equal? (term (csa#-and (variant False) ,boolean-maybe)) (term (variant False)))
  (check-equal? (term (csa#-and (variant True) ,boolean-maybe)) boolean-maybe)
  (check-equal? (term (csa#-and (variant True) (variant True))) (term (variant True)))
  (check-equal? (term (csa#-and (variant False) (variant False))) (term (variant False)))

  (check-equal? (term (csa#-or (variant False) ,boolean-maybe)) boolean-maybe)
  (check-equal? (term (csa#-or (variant True) ,boolean-maybe)) (term (variant True)))
  (check-equal? (term (csa#-or (variant True) (variant True))) (term (variant True)))
  (check-equal? (term (csa#-or (variant False) (variant False))) (term (variant False)))

  (check-equal? (term (csa#-not (variant False))) (term (variant True)))
  (check-equal? (term (csa#-not (variant True))) (term (variant False)))
  (check-equal? (term (csa#-not (canonicalize-boolean (* (Union (False) (True))))))
                (term (* (Union (True) (False))))))

(define (trigger-address trigger)
  (term (trigger-address/mf ,trigger)))

(define-metafunction csa#
  trigger-address/mf : trigger# -> a#int
  [(trigger-address/mf (timeout/empty-queue a#int)) a#int]
  [(trigger-address/mf (timeout/non-empty-queue a#int)) a#int]
  [(trigger-address/mf (internal-receive a#int _)) a#int]
  [(trigger-address/mf (external-receive a#int _)) a#int])

;; ---------------------------------------------------------------------------------------------------
;; Predicates

;; Returns true if the output is to an internal address, false otherwise
(define (internal-output? output)
  (redex-match? csa# (a#int _ _) output))

(module+ test
  (check-true (internal-output? (term ((init-addr 1) (* Nat) single))))
  (check-false (internal-output? (term ((obs-ext 2) (* Nat) single)))))

;; Returns #t if the address is a precise internal address (meaning it represents a single concrete
;; address in the concretized configuration), #f otherwise
(define (precise-internal-address? addr)
  (redex-match? csa# a#int-precise addr))

(define (necessary-action? trigger)
  (judgment-holds (necessary-action?/j ,trigger)))

(define-judgment-form csa#
  #:mode (necessary-action?/j I)
  #:contract (necessary-action?/j trigger#)

  [-----------------------------------------------------
   (necessary-action?/j (timeout/empty-queue a#int))]

  [-----------------------------------------------------
   (necessary-action?/j (internal-receive a#int v#))])

(module+ test
  (test-true "necessary-action? 1"
    (necessary-action? (term (timeout/empty-queue (init-addr 1)))))
  (test-false "necessary-action? 2"
    (necessary-action? (term (timeout/non-empty-queue (init-addr 1)))))
  (test-true "necessary-action? 3"
    (necessary-action? (term (internal-receive (init-addr 1) (* Nat)))))
  (test-false "necessary-action? 4"
    (necessary-action? (term (external-receive (init-addr 1) (* Nat))))))

;; ---------------------------------------------------------------------------------------------------
;; Types

(define-metafunction csa#
  type-join : τ τ -> τ
  [(type-join (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))
   (Union [t_3 τ_3 ...] ...)
   (where ([t_3 τ_3 ...] ...)
          ,(sort (remove-duplicates (term ([t_1 τ_1 ...] ... [t_2 τ_2 ...] ...))) sexp<?))]
  ;; TODO: allow for more sophisticated joins that look at the inner types of records, variants,
  ;; etc. and go recur into Union fields
  [(type-join τ τ) τ])

(module+ test
  (test-equal? "type-join 1" (term (type-join Nat Nat)) 'Nat)
  (test-equal? "type-join 2"
               (term (type-join (Union [A]) (Union [B])))
               '(Union [A] [B]))
  (test-equal? "type-join 2, other direction"
               (term (type-join (Union [B]) (Union [A])))
               '(Union [A] [B]))
  (test-equal? "type-join 3"
               (term (type-join (Union [A] [B]) (Union [B])))
               '(Union [A] [B])))

;; Coerces the abstract value v# according to the type τ (just change the types of addresses in
;; v). The type system should always make this sound
(define-metafunction csa#
  coerce/mf : v# τ -> v#
  ;; wildcard
  [(coerce/mf (* _) τ) (* τ)]
  ;; addresses
  [(coerce/mf (_ (init-addr natural)) (Addr τ))
   (τ (init-addr natural))]
  [(coerce/mf (_ (spawn-addr any_loc spawn-flag)) (Addr τ))
   (τ (spawn-addr any_loc spawn-flag))]
  [(coerce/mf (_ (blurred-spawn-addr any_loc)) (Addr τ))
   (τ (blurred-spawn-addr any_loc))]
  [(coerce/mf (_ (obs-ext natural)) (Addr τ))
   (τ (obs-ext natural))]
  ;; variants and records
  [(coerce/mf (variant t v# ..._n) (Union _ ... [t τ ..._n] _ ...))
   (variant t (coerce/mf v# τ) ...)]
  [(coerce/mf (record [l v#] ..._n) (Record [l τ] ..._n))
   (record [l (coerce/mf v# τ)] ...)]
  ;; fold
  [(coerce/mf (folded _ v#) (minfixpt X τ))
   (folded (minfixpt X τ) (coerce/mf v# (type-subst τ X (minfixpt X τ))))]
  ;; lists, vectors, and hashes
  [(coerce/mf (list-val v# ...) (Listof τ))
   ,(normalize-collection (term (list-val (coerce/mf v# τ) ...)))]
  [(coerce/mf (vector-val v# ...) (Vectorof τ))
   ,(normalize-collection (term (vector-val (coerce/mf v# τ) ...)))]
  [(coerce/mf (hash-val (v#_keys ...) (v#_vals ...)) (Hash τ_key τ_val))
   ,(normalize-collection
     (term (hash-val ((coerce/mf v#_keys τ_key) ...) ((coerce/mf v#_vals τ_val) ...))))])

(module+ test
  (test-equal? "coerce/mf wildcard 1" (term (coerce/mf (* Nat) Nat)) (term (* Nat)))
  (test-equal? "coerce/mf wildcard 2"
    (term (coerce/mf (* (Addr (Union [A] [B]))) (Addr (Union [A]))))
    (term (* (Addr (Union [A])))))
  (test-equal? "coerce/mf init-addr"
    (term (coerce/mf ((Union [A] [B]) (init-addr 1)) (Addr (Union [A]))))
    (term ((Union [A]) (init-addr 1))))
  (test-equal? "coerce/mf spawn-addr"
    (term (coerce/mf ((Union [A] [B]) (spawn-addr 1 OLD)) (Addr (Union [A]))))
    (term ((Union [A]) (spawn-addr 1 OLD))))
  (test-equal? "coerce/mf blurred-spawn-addr"
    (term (coerce/mf ((Union [A] [B]) (blurred-spawn-addr 1)) (Addr (Union [A]))))
    (term ((Union [A]) (blurred-spawn-addr 1))))
  (test-equal? "coerce/mf obs-ext"
    (term (coerce/mf ((Union [A] [B]) (obs-ext 1)) (Addr (Union [A]))))
    (term ((Union [A]) (obs-ext 1))))
  (test-equal? "coerce/mf variant"
    (term (coerce/mf (variant Z (* (Addr (Union [A] [B])))) (Union [Z (Addr (Union [A]))])))
    (term (variant Z (* (Addr (Union [A]))))))
  (test-equal? "coerce/mf record"
    (term (coerce/mf (record [foo (* (Addr (Union [A] [B])))]) (Record [foo (Addr (Union [A]))])))
    (term (record [foo (* (Addr (Union [A])))])))
  (test-equal? "coerce/mf fold"
    (term (coerce/mf (folded (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A] [B])) AddrList]))
                          (* (Union [Empty]
                                    [Cons (Addr (Union [A] [B]))
                                          (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A] [B])) AddrList]))])))
                  (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))))
    (term (folded (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))
                  (* (Union [Empty]
                            [Cons (Addr (Union [A]))
                                  (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))])))))
  (test-equal? "coerce/mf list"
    (term (coerce/mf (list-val (* (Addr (Union [A] [B]))) (* (Addr (Union [A]))))
                  (Listof (Addr (Union [A])))))
    (term (list-val (* (Addr (Union [A]))))))
  (test-equal? "coerce/mf vector"
    (term (coerce/mf (vector-val (* (Addr (Union [A] [B]))) (* (Addr (Union [A]))))
                  (Vectorof (Addr (Union [A])))))
    (term (vector-val (* (Addr (Union [A]))))))
  (test-equal? "coerce/mf hash"
    (term (coerce/mf (hash-val ((* Nat)) ((* (Addr (Union [A] [B]))) (* (Addr (Union [A])))))
                  (Hash Nat (Addr (Union [A])))))
    (term (hash-val ((* Nat)) ((* (Addr (Union [A]))))))))

;; NOTE: this is really a conservative approximation of <= for types. For instance, we don't rename
;; variables in recursive types to check for alpha-equivalent recursive types
(define (type<= type1 type2)
  (judgment-holds (type<=/j ,type1 ,type2)))

(define-judgment-form csa#
  #:mode (type<=/j I I)
  #:contract (type<=/j τ τ)

  [-------------------
   (type<=/j Nat Nat)]

  [-------------------
   (type<=/j String String)]

  ;; TODO: think abut whether recursive types screw with subtyping in a weird way
  [--------------
   (type<=/j X X)]

  [(type<=/j τ_1 τ_2)
   --------------------------------------------
   (type<=/j (minfixpt X τ_1) (minfixpt X τ_2))]

  [;; every variant in type 1 must have >= type in type 2
   (union-variant<=/j [t_1 τ_1 ...] (Union [t_2 τ_2 ...] ...)) ...
   ---------------------------------------------------------------
   (type<=/j (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))]

  [(type<=/j τ_1 τ_2) ...
   ---------------------------------------------------
   (type<=/j (Record [l τ_1] ...) (Record [l τ_2] ...))]

  [;; Address types are contravariant (they're "sinks")
   (type<=/j τ_2 τ_1)
   ---------------------------------
   (type<=/j (Addr τ_1) (Addr τ_2))]

  [(type<=/j τ_1 τ_2)
   ---------------------------------
   (type<=/j (Listof τ_1) (Listof τ_2))]

  [(type<=/j τ_1 τ_2)
   ---------------------------------
   (type<=/j (Vectorof τ_1) (Vectorof τ_2))]

  [(type<=/j τ_k1 τ_k2)
   (type<=/j τ_v1 τ_v2)
   -------------------------------------------
   (type<=/j (Hash τ_k1 τ_v1) (Hash τ_k2 τ_v2))])

(module+ test
  (test-true "type<= same type" (type<= 'Nat 'Nat))
  (test-true "type<= expanded union" (type<= '(Union [A]) '(Union [A] [B])))
  (test-false "type<= reduced union" (type<= '(Union [A] [B]) '(Union [A])))
  (test-false "type<= record 1" (type<= '(Record [a (Union [A] [B])]) '(Record [a (Union [A])])))
  (test-true "type<= record 2" (type<= '(Record [a (Union [A])]) '(Record [a (Union [A] [B])])))
  (test-true "type<= address 1" (type<= '(Addr (Union [A] [B])) '(Addr (Union [A]))))
  (test-false "type<= address 2" (type<= '(Addr (Union [A])) '(Addr (Union [A] [B]))))
  (define union-a '(Union [A]))
  (define union-ab '(Union [A] [B]))
  (test-true "type<= list 1" (type<= `(Listof ,union-a) `(Listof ,union-ab)))
  (test-false "type<= list 2" (type<= `(Listof ,union-ab) `(Listof ,union-a)))
  (test-true "type<= vector 1" (type<= `(Vectorof ,union-a) `(Vectorof ,union-ab)))
  (test-false "type<= vector 2" (type<= `(Vectorof ,union-ab) `(Vectorof ,union-a)))
  (test-true "type<= hash 1" (type<= `(Hash ,union-a ,union-a) `(Hash ,union-ab ,union-ab)))
  (test-false "type<= hash 2" (type<= `(Hash ,union-ab ,union-ab)  `(Hash ,union-a ,union-a))))

;; Holds if the variant [t_1 τ_1 ...] has a >= variant in the given union type
(define-judgment-form csa#
  #:mode (union-variant<=/j I I)
  #:contract (union-variant<=/j [t_1 τ_1 ...] (Union [t_2 τ_2 ...] ...))

  [(type<=/j τ_1 τ_2) ...
   ------------------------------------------------------------------------
   (union-variant<=/j [t_1 τ_1 ..._n] (Union _ ... [t_1 τ_2 ..._n] _ ...))])

(module+ test
  (test-true "union-variant<= for union with that variant"
    (judgment-holds (union-variant<=/j [A] (Union [A]))))
  (test-true "union-variant<= for bigger union"
    (judgment-holds (union-variant<=/j [A] (Union [A] [B]))))
  (test-false "union-variant<= for union without variant"
    (judgment-holds (union-variant<=/j [A] (Union [B]))))
  (test-true "union-variant<= for union with bigger type"
    (judgment-holds (union-variant<=/j [A (Union [C])]
                                     (Union [A (Union [C] [D])] [B]))))
  (test-false "union-variant<= for union with smaller type"
    (judgment-holds (union-variant<=/j [A (Union [C] [D])]
                                     (Union [A (Union [C])] [B])))))

;; ---------------------------------------------------------------------------------------------------
;; Address containment

;; Returns the list of all (precise) external addresses in the given term
(define (externals-in the-term)
  (remove-duplicates (externals-in/internal the-term)))

(define (externals-in/internal the-term)
  (match the-term
    [`(obs-ext ,_) (list the-term)]
    [(list terms ...) (append* (map externals-in/internal the-term))]
    [_ null]))

(module+ test
  (check-same-items?
   (externals-in (term ((Nat (obs-ext 1))
                        (Nat (obs-ext 2))
                        (Nat (obs-ext 2))
                        (* (Addr Nat))
                      (foo bar (baz (Nat (init-addr 2)) (Nat (obs-ext 3)))))))
   (term ((obs-ext 1) (obs-ext 2) (obs-ext 3)))))

;; Returns the list of all internal (typed) addresses in the given term
(define (internals-in the-term)
  (remove-duplicates (term (internals-in/mf ,the-term))))

(define-metafunction csa#
  internals-in/mf : any -> (τa# ...)
  [(internals-in/mf (τ a#int)) ((τ a#int))]
  [(internals-in/mf (any ...))
   (any_addr ... ...)
   (where ((any_addr ...) ...) ((internals-in/mf any) ...))]
  [(internals-in/mf _) ()])

(module+ test
  (check-same-items?
   (internals-in (term ((Nat (init-addr 1))
                        (Nat (init-addr 1))
                        (Nat (obs-ext 2))
                        (Nat (spawn-addr 3 NEW))
                      (foo bar (baz (Nat (init-addr 2)) (Nat (obs-ext 3)))))))
   (term ((Nat (init-addr 1)) (Nat (spawn-addr 3 NEW)) (Nat (init-addr 2))))))

;; ---------------------------------------------------------------------------------------------------
;; Eviction (see the Eviction section of aps-abstract.rkt for more info)

;; Returns (list a#)
(define (csa#-evictable-addresses i)
  (append
   (filter evictable? (map csa#-actor-address (csa#-config-actors i)))
   (filter evictable? (map csa#-blurred-actor-address (csa#-config-blurred-actors i)))))

(module+ test
  (check-equal?
   (csa#-evictable-addresses  `[([(init-addr 1) (() (goto A))]
                                 [(spawn-addr EVICT NEW) (() (goto B))]
                                 [(spawn-addr 2-EVICT NEW) (() (goto C))]
                                 [(spawn-addr 3 NEW) (() (goto D))])
                                ()
                                ()])
   (list `(spawn-addr EVICT NEW) `(spawn-addr 2-EVICT NEW))))

(define (evictable? address)
  (match address
    [`(spawn-addr ,loc ,_) (evictable-location? loc)]
    [`(blurred-spawn-addr ,loc) (evictable-location? loc)]
    [_ #f]))

(define (evictable-location? loc)
  (regexp-match? #rx"EVICT$" (location->string loc)))

(define (location->string loc)
  (match loc
    [(? number?) (number->string loc)]
    [(? symbol?) (symbol->string loc)]
    [_ (error 'location->string "Don't know how to convert ~s into a string" loc)]))

(module+ test
  (check-false (evictable? `(init-addr 1)))
  (check-true (evictable? `(spawn-addr L-EVICT NEW)))
  (check-false (evictable? `(spawn-addr L NEW)))
  (check-false (evictable? `(blurred-spawn-addr L)))
  (check-true (evictable? `(blurred-spawn-addr L-EVICT)))
  (check-false (evictable? `(blurred-spawn-addr EVICT-NOT))))

;; Returns (tuple i# (list τa#)), where the list of typed addresses is those internal addresses
;; contained by the evicted actor or its incoming messages
(define (csa#-evict-actor i address)
  (define-values (packets-to-evict remaining-packets)
    (partition
     (lambda (packet) (equal? address (csa#-message-packet-address packet)))
     (csa#-config-message-packets i)))
  (match-define-values (removed-atomics remaining-atomics)
   (partition (lambda (a) (equal? (csa#-actor-address a) address))
              (csa#-config-actors i)))
  (match-define-values (removed-collectives remaining-collectives)
   (partition (lambda (a) (equal? (csa#-blurred-actor-address a) address))
              (csa#-config-blurred-actors i)))

  ;; conservative approximation of relevant addresses so that we don't have to do the
  ;; relevancy computation
  (when (not (null? (externals-in (list removed-atomics removed-collectives packets-to-evict))))
    (error 'evict "Cannot evict actor ~s with incoming packets ~s"
           (list removed-atomics removed-collectives) packets-to-evict))

  (list
   (evict-rename
    `[,remaining-atomics
      ,remaining-collectives
      ,remaining-packets]
    address)
   (internals-in (list  removed-atomics removed-collectives packets-to-evict))))

;; REFACTOR: consider merging my various address-rename functions together and just using a hash table
;; of old address->new address mappings
(define (evict-rename some-term addr)
  (match addr
    [`(spawn-addr ,loc ,_) (evict-rename/atomic some-term loc)]
    [`(blurred-spawn-addr ,loc) (evict-rename/collective some-term loc)]))

(define (evict-rename/atomic some-term loc)
  (match some-term
    [`[,type (spawn-addr ,(== loc) ,_)]
     `(* (Addr ,type))]
    [(list terms ...)
     (map (curryr evict-rename/atomic loc) terms)]
    [_ some-term]))

(define (evict-rename/collective some-term loc)
  (match some-term
    [`[,type (blurred-spawn-addr ,(== loc))]
     `(* (Addr ,type))]
    [(list terms ...)
     (map (curryr evict-rename/collective loc) terms)]
    [_ some-term]))

(module+ test
  (check-equal? (evict-rename `((Nat (spawn-addr 1 NEW))
                                (String (spawn-addr 2-EVICT OLD)))
                              `(spawn-addr 2-EVICT OLD))
                 `((Nat (spawn-addr 1 NEW))
                   (* (Addr String))))

  (check-equal? (evict-rename `((Nat (spawn-addr 1 NEW))
                                (String (blurred-spawn-addr 2-EVICT)))
                              `(blurred-spawn-addr 2-EVICT))
                `((Nat (spawn-addr 1 NEW))
                  (* (Addr String)))))

;; ---------------------------------------------------------------------------------------------------
;; Pre-sbc maybe-widen check

;; i# transition-effect -> #t or #f
;;
;; Returns #t if the transition satisfies some basic, quick-to-check tests that indicate it's a
;; possible candidate to use for widening of original-i; #f otherwise
(define (csa#-transition-maybe-good-for-widen? original-i transition-result)
  (define this-actor-address (trigger-address (csa#-transition-effect-trigger transition-result)))
  (define new-behavior (csa#-transition-effect-behavior transition-result))
  (define comp-result
    (comp-result-and
     ;; 1. Are there any spawns?
     (if (not (empty? (csa#-transition-effect-spawns transition-result))) 'gt 'eq)
     ;; 2. Do all atomic spawns have have a corresponding existing actor with that spawn location, and
     ;; have the same state name?
     ;;
     ;; REFACTOR: should probably just compare behaviors without state defs for spawns instead of
     ;; looking at the state name
     (for/and ([spawn (csa#-transition-effect-spawns transition-result)])
       (match-define `[,addr ,behavior] spawn)
       (cond
         [(precise-internal-address? addr)
          (match-define `(spawn-addr ,loc ,_) addr)
          (if (atomic-state-name-by-address original-i `(spawn-addr ,loc OLD)) 'eq 'not-gteq)]
         [else 'eq]))
     (let ([after-pseudo-blur (pseudo-blur-transition-result transition-result)])
       (comp-result-and
        ;; 3. Is the current behavior a valid behavior to add/keep for this configuration pair? Is it
        ;; new?
        (compare-pseudo-behavior original-i
                                 this-actor-address
                                 (csa#-transition-effect-behavior after-pseudo-blur))
        ;; 4. Are there any new messages/a message that only exists as a one-of?
        (if (for/or ([send (filter internal-output?
                                   (csa#-transition-effect-sends after-pseudo-blur))])
              (new-pseudo-send? original-i send))
            'gt
            'eq)))))
  (eq? comp-result 'gt))

;; Returns the name of the current state for the actor with the given address in config if it exists,
;; #f if the actor does not exist
(define (atomic-state-name-by-address config address)
  (match (csa#-config-actor-by-address config address)
    [#f #f]
    [actor (goto-state-name (behavior-exp (actor-behavior actor)))]))

(module+ test
  (check-equal?
   (atomic-state-name-by-address
    `[([(init-addr 1) (() (goto A))]
       [(init-addr 2) (() (goto B (* Nat)))])
      ()
      ()]
    `(init-addr 2))
   'B))

;; Rename addresses in everything but the state definitions of the transition so that any
;; obs-ext > 100 is blurred, and any NEW spawn address is converted to a blurred-spawn-addr.
(define (pseudo-blur-transition-result transition-result)
  (match-define (csa#-transition-effect trigger `(,state-defs ,goto-exp) sends spawns)
    transition-result)
  (define new-sends
    (for/list ([send sends])
      (match-define `[,target ,message ,mult] send)
      `[,(pseudo-blur target) ,(pseudo-blur message) ,mult]))
  (define new-spawns
    (for/list ([spawn spawns])
      (match-define `[,addr [,spawn-state-defs ,spawn-goto]] spawn)
      `[,(pseudo-blur addr) [,(pseudo-blur spawn-state-defs) ,(pseudo-blur spawn-goto)]]))
  (csa#-transition-effect trigger `(,state-defs ,(pseudo-blur goto-exp)) new-sends new-spawns))

(define (pseudo-blur some-term)
  (match some-term
    [`(spawn-addr ,loc NEW)
     `(blurred-spawn-addr ,loc)]
    [`(,type ,(and addr `(obs-ext ,num)))
     (if (< num FIRST-GENERATED-ADDRESS)
         some-term
         (term (* (Addr ,type))))]
    [(list (and keyword (or `vector-val 'list-val 'hash-val)) terms ...)
     (define blurred-args (map pseudo-blur terms))
     (normalize-collection `(,keyword ,@blurred-args))]
    [`(hash-val ,keys ,vals)
     (define blurred-keys (map pseudo-blur keys))
     (define blurred-vals (map pseudo-blur vals))
     `(normalize-collection `(hash-val ,blurred-keys ,blurred-vals))]
    [(list terms ...) (map pseudo-blur terms)]
    [_ some-term]))

(module+ test
  (check-equal? (pseudo-blur `(Nat (obs-ext 2))) `(Nat (obs-ext 2)))
  (check-equal? (pseudo-blur `(Nat (obs-ext 102))) `(* (Addr Nat)))
  (check-equal? (pseudo-blur `(spawn-addr 1 OLD)) `(spawn-addr 1 OLD))
  (check-equal? (pseudo-blur `(spawn-addr 1 NEW)) `(blurred-spawn-addr 1))
  (check-equal? (pseudo-blur `(Nat (init-addr 1))) `(Nat (init-addr 1))))

(define (new-pseudo-send? config send)
  (match-define `[,addr ,message ,_] send)
  (not (member `[,addr ,message many] (csa#-config-message-packets config))))

(module+ test
  (check-not-false
   (new-pseudo-send? `[() () ([(init-addr 1) (* Nat) single])]
                     `[(init-addr 1) (* Nat) single]))
  (check-false
   (new-pseudo-send? `[() () ([(init-addr 1) (* Nat) many])]
                     `[(init-addr 1) (* Nat) single]))
  (check-not-false
   (new-pseudo-send? `[() () ([(init-addr 1) (* Nat) many])]
                     `[(init-addr 1) (* String) single]))
  (check-not-false
   (new-pseudo-send? `[() () ([(init-addr 1) (* Nat) many])]
                     `[(init-addr 2) (* Nat) single])))

;; Is the behavior better than all existing ones for this address if we ignore state definitions?
(define (compare-pseudo-behavior config addr behavior)
  (match (csa#-behaviors-of config addr)
    [#f 'gt]
    [old-behaviors
     (if (precise-internal-address? addr)
         (compare-behavior behavior (first old-behaviors) #f)
         (let loop ([behaviors-to-check old-behaviors])
           (match behaviors-to-check
             [(list old-behavior behaviors-to-check ...)
              (match (compare-behavior behavior old-behavior #f)
                ['not-gteq (loop behaviors-to-check)]
                ['eq
                 (if (equal? (behavior-state-defs behavior)
                             (behavior-state-defs old-behavior))
                     'eq
                     (loop behaviors-to-check))]
                [result result])]
             [(list) 'gt])))]))

(module+ test
  (check-equal?
   (compare-pseudo-behavior `[([(init-addr 1) (() (goto A))])
                              ()
                              ()]
                            `(init-addr 1)
                            `(() (goto B)))
   'not-gteq)
  (check-equal?
   (compare-pseudo-behavior `[([(init-addr 1) (() (goto A))])
                              ()
                              ()]
                            `(init-addr 1)
                            `(() (goto A)))
   'eq)
  (check-equal?
   (compare-pseudo-behavior `[([(init-addr 1) (() (goto A (list-val)))])
                              ()
                              ()]
                            `(init-addr 1)
                            `(() (goto A (list-val (* Nat)))))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[([(init-addr 1) (() (goto A))])
                              ()
                              ()]
                            `(init-addr 2)
                            `(() (goto A)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(blurred-spawn-addr 2)
                            `(() (goto A)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(blurred-spawn-addr 1)
                            `(() (goto A)))
   'eq)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(blurred-spawn-addr 1)
                            `(() (goto C)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([() (goto A (list-val))]
                                 [() (goto B)])])
                              ()]
                            `(blurred-spawn-addr 1)
                            `(() (goto A (list-val (* Nat)))))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([() (goto A (list-val (* Nat)))]
                                 [() (goto B)])])
                              ()]
                            `(blurred-spawn-addr 1)
                            `(() (goto A (list-val))))
   'lt)
  (test-equal? "Blurred actor with different state defs (faking different constructor args)"
   (compare-pseudo-behavior `[()
                              ([(blurred-spawn-addr 1)
                                ([((define-state (A))) (goto A)])])
                              ()]
                            `(blurred-spawn-addr 1)
                            `(() (goto A)))
   'gt))

;; ---------------------------------------------------------------------------------------------------
;; Tests for use during widening

;; NOTE: for various comparisons here, I need to record if a transition takes the config to a new
;; configuration that is greater than the old one (in terms of the abstract interpretation), the same
;; as the old one, or neither of those. I represent those results with 'gt, 'eq, and 'not-gteq,
;; respectively, and call them "comp-results"

;; i# csa#-transition-effect -> Boolean
;;
;; Returns #t if multiple applications of this transition effect would result in a configuration
;; strictly larger than the given one
(define (csa#-config<? i1 i2)
  ;; NOTE: I removed the check for non-existent internal addresses in the effect: now that I'm only
  ;; checking against fully transitioned and sbc'ed configurations rather than transition effects,
  ;; that should no longer be possible.

  (define atomics-comp (config-compare-atomics i2 i1))
  (define collectives-comp (config-compare-collectives i2 i1))
  (define messages-comp (config-compare-messages i2 i1))

  (match (comp-result-and atomics-comp collectives-comp messages-comp)
    ['gt #t]
    [_ #f]))

;; Returns:
;;
;; * 'gt if i1 contains no atomic actors not in i2 and at least one of its behaviors subsumes the
;; corresponding behavior in i2
;;
;; * 'eq if the atomics are all exactly the same
;;
;; * 'not-gteq otherwise
(define (config-compare-atomics i1 i2)
  (let loop ([comp-result 'eq]
             [i1-actors (csa#-config-actors i1)])
    (match i1-actors
      [(list) comp-result]
      [(list i1-actor i1-actors ...)
       (match (csa#-config-actor-by-address i2 (csa#-actor-address i1-actor))
         [#f 'not-gteq]
         [i2-actor
          (define i1-behavior (actor-behavior i1-actor))
          (define i2-behavior (actor-behavior i2-actor))
          (cond
            [(equal? (behavior-state-defs i1-behavior) (behavior-state-defs i2-behavior))
             (match (compare-behavior i1-behavior i2-behavior #t)
               ['not-gteq 'not-gteq]
               [this-result (loop (comp-result-and comp-result this-result) i1-actors)])]
            [else 'not-gteq])])])))

(module+ test
  ;; TODO: update these tests
  (define spawn-behavior-change-test-config
    (redex-let csa# ([i#
                      (term
                       (([(spawn-addr the-loc OLD)
                          (() (goto A))]
                         [(spawn-addr second-loc OLD)
                          (() (goto A))]
                         [(spawn-addr third-loc OLD)
                          (() (goto A))])
                        ([(blurred-spawn-addr the-loc)
                          ((() (goto A)))]
                         [(blurred-spawn-addr second-loc)
                          ((() (goto B)))])
                        ()))])
      (term i#)))

  ;; (test-equal? "effect matches existing spawn behavior, no blurred version"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           (list '((spawn-addr third-loc NEW) (() (goto A)))))
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto B)))]
  ;;      [(spawn-addr third-loc)
  ;;       (() (goto A))])
  ;;     ())))
  ;;  'gt)
  ;; (test-equal? "effect matches existing spawn behavior, blurred behavior also exists"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           (list '((spawn-addr the-loc NEW) (() (goto A)))))
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'eq)
  ;; (test-equal? "effect matches existing spawn behavior, blurred actor with other behavior exists"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           (list '((spawn-addr second-loc NEW) (() (goto A)))))
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto A)) (() (goto B)))])
  ;;     ())))
  ;;  'gt)
  ;; (test-equal? "effect changes existing spawn behavior"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           (list '((spawn-addr the-loc NEW) (() (goto C)))))
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto C))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'not-gteq)
  ;; (test-equal? "config has no actor for corresponding spawn"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           (list '((spawn-addr other-loc NEW) (() (goto C)))))
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr other-loc OLD)
  ;;       (() (goto C))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'not-gteq)
  ;; (test-equal? "effect has no spawns"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
  ;;                           '(() (goto B))
  ;;                           null
  ;;                           null)
  ;;   spawn-behavior-change-test-config
  ;;   (term
  ;;    (([(spawn-addr the-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr second-loc OLD)
  ;;       (() (goto A))]
  ;;      [(spawn-addr third-loc OLD)
  ;;       (() (goto A))])
  ;;     ([(blurred-spawn-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(blurred-spawn-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'eq)
  )

;; (module+ test
;;   (test-equal? "actor-compare-behavior: new atomic behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout/empty-queue (init-addr 1)) '(() (goto D)) null null)
;;      (term (([(init-addr 1) (() (goto D))])
;;            ([(blurred-spawn-addr 2)
;;              ((() (goto B))
;;               (() (goto C)))])
;;            ())))
;;     'not-gteq)
;;   (test-equal? "actor-compare-behavior: old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout/empty-queue (init-addr 1)) '(() (goto A)) null null)
;;      behavior-test-config)
;;     'eq)
;;   (test-equal? "actor-compare-behavior: adding to vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(init-addr 1) (() (goto A (vector-val (variant A))))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout/empty-queue (init-addr 1)) '(() (goto A (vector-val (variant B) (variant A)) )) null null)
;;      (term (([(init-addr 1) (() (goto A (vector-val (variant B) (variant A))))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'gt)
;;   (test-equal? "actor-compare-behavior: same vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(init-addr 1) (() (goto A (vector-val (variant A))))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout/empty-queue (init-addr 1)) '(() (goto A (vector-val (variant A)))) null null)
;;      (term (([(init-addr 1) (() (goto A (vector-val (variant A))))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'eq)
;;   (test-equal? "actor-compare-behavior: smaller vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(init-addr 1) (() (goto A (vector-val (variant A))))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout/empty-queue (init-addr 1)) '(() (goto A (vector-val))) null null)
;;      (term (([(init-addr 1) (() (goto A (vector-val)))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'not-gteq)
;;   (test-equal? "actor-compare-behavior: new collective behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout/empty-queue (blurred-spawn-addr 2)) '(() (goto D)) null null)
;;      (term (([(init-addr 1) (() (goto A))])
;;             ([(blurred-spawn-addr 2)
;;               ((() (goto B))
;;                (() (goto C))
;;                (() (goto D)))])
;;             ())))
;;     'gt)
;;   (test-equal? "actor-compare-behavior: old collective behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout/empty-queue (blurred-spawn-addr 2)) '(() (goto B)) null null)
;;      behavior-test-config)
;;     'eq))

;; TODO: test this

;; Returns:
;;
;; * 'gt if i1 has at least one collective actor with a behavior different than the one in i1, or a
;; collective actor not in i1 at all
;;
;; * 'eq if the collective actors of i1 and i2 are exactly the same
;;
;; NOTE: this function assumes that i1 was reached by some number of transitions from i2, so any
;; behavior that was present in i2 *must* still be present (or subsumed) in i1
(define (config-compare-collectives i1 i2)
  (let loop ([i1-collectives (csa#-config-blurred-actors i1)])
    (match i1-collectives
      [(list) 'eq]
      [(list i1-collective i1-collectives ...)
       (match (csa#-config-collective-actor-by-address i2 (csa#-blurred-actor-address i1-collective))
         [#f 'gt]
         [i2-collective
          (if (equal? (csa#-blurred-actor-behaviors i1-collective)
                      (csa#-blurred-actor-behaviors i2-collective))
              (loop i1-collectives)
              'gt)])])))

;; TODO: test this

;; Returns:
;;
;; * 'gt if i1 has the same or greater multiplicity for every message from i2 plus a "many"
;; multiplicity for any new messages
;;
;; * 'eq if the in-transit message sets are the same
;;
;; * 'not-gteq otherwise
(define (config-compare-messages i1 i2)
  (define (get-multiplicity addr message config)
    (match (findf (lambda (pkt)
                    (and (equal? (csa#-message-packet-address pkt) addr)
                         (equal? (csa#-message-packet-value pkt) message)))
                  (csa#-config-message-packets config))
      [#f 'none]
      [found-packet (csa#-message-packet-multiplicity found-packet)]))

  (define old-message-comp
   (for/fold ([comp-result 'eq])
             ([packet (csa#-config-message-packets i2)])
     (comp-result-and
      comp-result
      (match (list (csa#-message-packet-multiplicity packet)
                   (get-multiplicity (csa#-message-packet-address packet)
                                     (csa#-message-packet-value packet)
                                     i1))
        [`(single none)   'not-gteq]
        [`(single single) 'eq]
        [`(single many)   'gt]
        [`(many   none)   'not-gteq]
        [`(many   single) 'not-gteq]
        [`(many   many)   'eq]))))

  (match old-message-comp
    ['not-gteq 'not-gteq]
    [_
     ;; Step 2: check multiplicity on new messages
     (for/fold ([comp-result old-message-comp])
               ([packet (csa#-config-message-packets i1)])
       (comp-result-and
        comp-result
        (match (list (csa#-message-packet-multiplicity packet)
                     (get-multiplicity (csa#-message-packet-address packet)
                                       (csa#-message-packet-value packet)
                                       i2))
          [`(single single) 'eq]
          [`(single ,_)     'not-gteq]
          [`(many   many)   'eq]
          [`(many   ,_)      'gt])))]))

;; TODO: for real, write some tests
;; TODO: test the new message rule

;; (module+ test

;;   (define new-message-test-config
;;     (term (([(spawn-addr 0 OLD) (() (goto A))]
;;             [(spawn-addr 1 OLD) (() (goto A))]
;;             [(spawn-addr 2 OLD) (() (goto A))])
;;            ()
;;            ([(spawn-addr 1 OLD) (* Nat) single]
;;             [(spawn-addr 2 OLD) (* Nat) many]))))

;;   (test-equal? "Ensure that only internal messages are compared"
;;     (csa#-compare-new-messages
;;      new-message-test-config
;;      (csa#-transition-effect #f #f (list `[(obs-ext 1) (* Nat) single]) null)
;;      new-message-test-config)
;;     'eq)

;;   ;; (define (compare-one-message m)
;;   ;;   (csa#-compare-new-messages
;;   ;;    new-message-test-config
;;   ;;    (csa#-transition-effect #f #f (list m) null)))

;;   ;; (test-equal? "single message to init-addr"
;;   ;;   (compare-one-message `((init-addr 3) (* Nat) single))
;;   ;;   'gt)
;;   ;; (test-equal? "single message to OLD spawn-addr"
;;   ;;   (compare-one-message `((spawn-addr 1 OLD) (* Nat) single))
;;   ;;   'gt)
;;   ;; (test-equal? "single message to collective address"
;;   ;;   (compare-one-message `((blurred-spawn-addr 3) (* Nat) single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send one"
;;   ;;   (compare-one-message `((spawn-addr 0 NEW) (* Nat) single))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: OLD doesn't exist, send one"
;;   ;;   (compare-one-message `((spawn-addr 4 NEW) (* Nat) single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send many"
;;   ;;   (compare-one-message `((spawn-addr 0 NEW) (* Nat) many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had one, send one"
;;   ;;   (compare-one-message `((spawn-addr 1 NEW) (* Nat) single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had one, send many"
;;   ;;   (compare-one-message `((spawn-addr 1 NEW) (* Nat) many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had many, send one"
;;   ;;   (compare-one-message `((spawn-addr 2 NEW) (* Nat) single))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: had many, send many"
;;   ;;   (compare-one-message `((spawn-addr 2 NEW) (* Nat) many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ()))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 0 NEW) (() (goto A))))))
;;   ;;   'eq)
;;   ;; (test-equal? "to NEW: had one, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 1 OLD) (* Nat) single])))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 1 NEW) (() (goto A))))))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: had many, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 2 OLD) (* Nat) many])))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 2 NEW) (() (goto A))))))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "had 1, NEW does not exist"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 1 OLD) (* Nat) single])))
;;   ;;    (csa#-transition-effect #f #f null null))
;;   ;;   'eq)
;;   ;; (test-equal? "had many, NEW does not exist"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 2 OLD) (* Nat) many])))
;;   ;;    (csa#-transition-effect #f #f null null))
;;   ;;   'eq)
;;   )


;; b# b# -> ('eq or 'gt or 'lt or 'not-gteq)
;;
;; To be comparable, behaviors b1 and b2 must have the same current state name and state
;; definitions. The comparison is doing point-wise on the state argument values.
(define (compare-behavior behavior1 behavior2 check-state-defs?)
  (match-define `(,state-defs1 (goto ,state1 ,state-args1 ...)) behavior1)
  (match-define `(,state-defs2 (goto ,state2 ,state-args2 ...)) behavior2)

  (comp-result-and
   ;; state names
   (if (equal? state1 state2) 'eq 'not-gteq)
   ;; state arguments
   (for/fold ([comp-result 'eq])
             ([arg1 state-args1]
              [arg2 state-args2])
     (comp-result-and comp-result (compare-value arg1 arg2)))
   ;; state definitions
   (if (or (not check-state-defs?) (equal? state-defs1 state-defs2)) 'eq 'not-gteq)))

(module+ test
  (check-equal? (compare-behavior (term (() (goto A))) (term (() (goto B))) #t)
                'not-gteq)
  (check-equal? (compare-behavior (term (() (goto A (variant B)))) (term (() (goto A (variant B)))) #t)
                'eq)
  (check-equal? (compare-behavior (term (() (goto A (vector-val (variant A) (variant B)))))
                                  (term (() (goto A (vector-val (variant B)))))
                                  #t)
                'gt)
  (check-equal?
   (compare-behavior
    (term (((define-state (A) (m) (goto A)))         (goto A (vector-val (variant B)))))
    (term (((define-state (A) (m) (goto A (* Nat)))) (goto A (vector-val (variant B)))))
    #t)
   'not-gteq)
  (check-equal?
   (compare-behavior
    (term (((define-state (A) (m) (goto A)))         (goto A (vector-val (variant B)))))
    (term (((define-state (A) (m) (goto A (* Nat)))) (goto A (vector-val (variant B)))))
    #f)
   'eq))

(define (compare-value v1 v2)
  (match (list v1 v2)
    [(list (list 'variant tag1 fields1 ...)
           (list 'variant tag2 fields2 ...))
     (if (equal? tag1 tag2)
         (for/fold ([comp-result 'eq])
                   ([field1 fields1]
                    [field2 fields2])
           (comp-result-and comp-result (compare-value field1 field2)))
         'not-gteq)]
    [(list (list 'record `[,ls1 ,vs1] ...) (list 'record `[,ls2 ,vs2] ...))
     (for/fold ([comp-result 'eq])
               ([l1 ls1]
                [l2 ls2]
                [v1 vs1]
                [v2 vs2])
       (comp-result-and
        comp-result
        (if (equal? l1 l2)
            (compare-value v1 v2)
            'not-gteq)))]
    [(list `(folded ,t1 ,v1) `(folded ,t2 ,v2))
     (if (equal? t1 t2)
         (compare-value v1 v2)
         'not-gteq)]
    [(list (list 'list-val args1 ...) (list 'list-val args2 ...))
     (compare-value-sets args1 args2)]
    [(list (list 'vector-val args1 ...) (list 'vector-val args2 ...))
     (compare-value-sets args1 args2)]
    [(list (list 'hash-val (list keys1 ...) (list vals1 ...))
           (list 'hash-val (list keys2 ...) (list vals2 ...)))
     (comp-result-and (compare-value-sets keys1 keys2)
                      (compare-value-sets vals1 vals2))]
    [_ (if (equal? v1 v2) 'eq 'not-gteq)]))

(module+ test
  (check-equal?
   (compare-value (term (variant A (* Nat)))
                  (term (variant B (* Nat))))
   'not-gteq))

(define (compare-value-sets vals1 vals2)
     (define val-set1 (list->set vals1))
     (define val-set2 (list->set vals2))
     (cond
       [(subset? val-set1 val-set2)
        (cond
          [(subset? val-set2 val-set1) 'eq]
          [else 'lt])]
       [(subset? val-set2 val-set1) 'gt]
       [else 'not-gteq]))

(module+ test
  (test-equal? "compare-value record 1"
    (compare-value `(record [a (vector-val (* Nat))] [b (* Nat)])
                   `(record [a (vector-val)]         [b (* Nat)]))
    'gt)
  (test-equal? "compare-value record 2"
    (compare-value `(record [a (vector-val (* Nat))] [b (* Nat)])
                   `(record [a (vector-val (* Nat))] [b (* Nat)]))
    'eq)
  (test-equal? "compare-value record 3"
    (compare-value `(record [a (vector-val (variant A))] [b (* Nat)])
                   `(record [a (vector-val (variant B))] [b (* Nat)]))
    'not-gteq)

  (test-equal? "compare-value variant 1"
    (compare-value `(variant A (vector-val (* Nat)) (* Nat))
                   `(variant A (vector-val) (* Nat)))
    'gt)
  (test-equal? "compare-value variant 2"
    (compare-value `(variant A (vector-val (* Nat)) (* Nat))
                   `(variant A (vector-val (* Nat)) (* Nat)))
    'eq)
  (test-equal? "compare-value variant 3"
    (compare-value `(variant A (vector-val) (* Nat))
                   `(variant A (vector-val (* Nat)) (* Nat)))
    'lt)

  (test-equal? "compare-value vector-val 1"
    (compare-value '(vector-val (* Nat))
                   '(vector-val))
    'gt)
  (test-equal? "compare-value vector-val 2"
    (compare-value '(vector-val (* Nat))
                   '(vector-val (* Nat)))
    'eq)
  (test-equal? "compare-value vector-val 3"
    (compare-value '(vector-val)
                   '(vector-val (* Nat)))
    'lt)
  (test-equal? "compare-value vector-val 4"
    (compare-value '(vector-val (variant A))
                   '(vector-val (variant B)))
    'not-gteq)

  (test-equal? "compare-value hash-val 1"
    (compare-value '(hash-val () ())
                   '(hash-val () ()))
    'eq)
  (test-equal? "compare-value hash-val 2"
    (compare-value '(hash-val ((* Nat)) ((variant A)))
                   '(hash-val () ()))
    'gt)
  (test-equal? "compare-value hash-val 3"
    (compare-value '(hash-val ((* Nat)) ((variant A) (variant B)))
                   '(hash-val ((* Nat)) ((variant A))))
    'gt)
  (test-equal? "compare-value hash-val 4"
    (compare-value '(hash-val ((variant A) (variant B)) ((* Nat)))
                   '(hash-val ((variant A)) ((* Nat))))
    'gt)
  (test-equal? "compare-value hash-val 5"
    (compare-value '(hash-val ((* Nat)) ((variant A)))
                   '(hash-val ((* Nat)) ((variant A) (variant B))))
    'lt)
  (test-equal? "compare-value hash-val 6"
    (compare-value '(hash-val ((variant A)) ((* Nat)))
                   '(hash-val ((variant A) (variant B)) ((* Nat))))
    'lt)
  (test-equal? "compare-value hash-val 7"
    (compare-value '(hash-val ((variant A)) ((* Nat)))
                   '(hash-val ((variant B)) ((* Nat))))
    'not-gteq)

  (test-equal? "compare-value addresses 1"
    (compare-value `((* Nat) (init-addr 1))
                   `((* Nat) (init-addr 2)))
    'not-gteq)
  (test-equal? "compare-value addresses 2"
    (compare-value `((* String) (init-addr 1))
                   `((* Nat) (init-addr 1)))
    'not-gteq)
  (test-equal? "compare-value addresses 3"
    (compare-value `((* Nat) (init-addr 1))
                   `((* Nat) (init-addr 1)))
    'eq))

;; comparison-result comparison-result -> comparison-result
(define-syntax (comp-result-and stx)
  (syntax-parse stx
    [(_) #''eq]
    [(_ exp1 exp2 ...)
     #`(let ([result1 exp1])
         (if (eq? result1 'not-gteq)
             'not-gteq
             (comp-result-and/internal result1 (comp-result-and exp2 ...))))]))

(define (comp-result-and/internal c1 c2)
  (cond
    [(or (eq? c1 'not-gteq) (eq? c2 'not-gteq))
     'not-gteq]
    [(or (and (eq? c1 'lt) (eq? c2 'gt))
         (and (eq? c1 'gt) (eq? c2 'lt)))
     'not-gteq]
    [(or (eq? c1 'gt) (eq? c2 'gt))
     'gt]
    [(or (eq? c1 'lt) (eq? c2 'lt))
     'lt]
    [else 'eq]))

(module+ test
  (test-equal? "comp-result-and gt eq" (comp-result-and 'gt 'eq) 'gt)
  (test-equal? "comp-result-and not-gteq eq" (comp-result-and 'not-gteq 'eq) 'not-gteq)
  (test-equal? "comp-result-and not-gteq gt" (comp-result-and 'not-gteq 'gt) 'not-gteq)
  (test-equal? "comp-result-and gt eq 2" (comp-result-and 'eq 'gt) 'gt)
  (test-equal? "comp-result-and not-gteq eq 2" (comp-result-and 'eq 'not-gteq) 'not-gteq)
  (test-equal? "comp-result-and not-gteq gt 2" (comp-result-and 'gt 'not-gteq) 'not-gteq)
  (test-equal? "comp-result-and short-circuits" (comp-result-and 'not-gteq (error "foo")) 'not-gteq)
  (test-equal? "comp-result-and with no args" (comp-result-and) 'eq)
  (test-equal? "comp-result-and takes many args" (comp-result-and 'eq 'eq 'gt 'eq) 'gt)
  (test-equal? "comp-result-and lt/gt" (comp-result-and 'lt 'gt) 'not-gteq)
  (test-equal? "comp-result-and lt/gt" (comp-result-and 'lt 'gt) 'not-gteq)
  (test-equal? "comp-result-and lt/eq" (comp-result-and 'lt 'eq) 'lt)
  (test-equal? "comp-result-and lt/not-gteq" (comp-result-and 'lt 'not-gteq) 'not-gteq))

;; Returns a true value (i.e. non-#f) if the action represented by the given trigger is enabled in the
;; given configuration; #f otherwise
(define (csa#-action-enabled? config trigger)
  ;; if it's not an internal messsage, or the received message will be available in the new config
  (match trigger
    [`(internal-receive ,addr ,message)
     (findf (lambda (packet)
              (and (equal? (csa#-message-packet-address packet) addr)
                   (equal? (csa#-message-packet-value packet) message)))
            (csa#-config-message-packets config))]
    [_ #t]))

;; TODO: redo these tests

;; (module+ test
;;   ;; timeout, internal receive repeatable (in effects), internal repeatable (many-of in config),
;;   ;; internal not repeatable
;;   (define repeatable-action-test-config
;;     (redex-let csa# ([i# `(() () ([(init-addr 0) (* Nat) many] [(init-addr 1) (* Nat) single]))])
;;       (term i#)))
;;   (define (make-trigger-only-effect trigger)
;;     (csa#-transition-effect trigger '(() (goto A)) null null))
;;   (test-false "Not repeatable action"
;;     (csa#-repeatable-action? repeatable-action-test-config
;;                              (make-trigger-only-effect '(internal-receive (init-addr 1) (* Nat)))))
;;   (test-not-false "Repeatable timeout"
;;     (csa#-repeatable-action? repeatable-action-test-config
;;                              (make-trigger-only-effect '(timeout/empty-queue (init-addr 1)))))
;;   (test-not-false "Repeatable internal receive (many-of message)"
;;     (csa#-repeatable-action? repeatable-action-test-config
;;                              (make-trigger-only-effect '(internal-receive (init-addr 0) (* Nat)))))
;;   (test-not-false "Repeatable internal receive (from effect)"
;;     (csa#-repeatable-action? repeatable-action-test-config
;;                              (csa#-transition-effect '(internal-receive (init-addr 1) (* Nat))
;;                                                      '(() (goto A))
;;                                                      (list `((init-addr 1) (* Nat) single))
;;                                                      null))))

;; ---------------------------------------------------------------------------------------------------
;; Debug helpers

(define (impl-config-without-state-defs config)
  (redex-let csa# ([(((any_addr (_ any_exp)) ...) ((any_addr-b ((_ any_exp-b) ...)) ...) any_msg)
                    config])
    (term (((any_addr any_exp) ...) ((any_addr-b (any_exp-b ...)) ...) any_msg))))

(define (impl-config-goto config)
  ;; NOTE: only suports single-actor impls for now
  (redex-let csa# ([(((a#int (_ e#))) any_blurred μ#) config])
             (term e#)))
