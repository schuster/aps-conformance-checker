#lang racket

;; Abstract standard semantic domains for CSA#, and associated functions

(provide
 ;; Required by conformance checker
 (struct-out csa#-transition)
 csa#-transition-spawn-locs
 csa#-messages-of-type
 csa#-config-receptionists
 csa#-config-receptionist-addr-by-marker
 csa#-enabled-internal-actions
 csa#-action-enabled?
 csa#-make-external-trigger
 csa#-abstract-config
 csa#-blur-config
 csa#-age-addresses
 csa#-rename-markers
 internal-atomic-action?
 trigger-address
 internal-single-receive?
 ;; required for widening
 csa#-transition-maybe-good-for-widen?
 (struct-out csa#-transition-effect)
 csa#-config<?
 csa#-trigger-updated-by-step?
 csa#-eval-trigger
 csa#-apply-transition

 ;; Required by conformance checker to select spawn-flag to blur; likely to change
 csa#-actor-with-opposite-id-exists?
 csa#-address-id
 csa#-atomic-address?
 csa#-ids-that-know-markers

 ;; Required by APS#
 csa#-internal-address?
 csa#-output-address
 csa#-output-markers
 csa#-output-type
 csa#-output-message
 csa#-output-multiplicity
 ;; internal-addr-types
 markers-in
 csa#-sort-config-components
 csa#-addrs-to-evict
 csa#-evict
 ;; merge-receptionists
 csa#-contains-marker?

 ;; Required by APS#; should go into a "common" language instead
 csa#
 csa#-abstract-address
 type-subst
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
 "optimization-parameters.rkt"
 "sexp-helpers.rkt"
 "statistics.rkt")

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt"))

;; Abstract-interpretation version of CSA
(define-extended-language csa# csa-eval
  ;; NOTE: can leave the marker set out here as an optimization: we assume for the sake of this
  ;; checker it never goes over 100 (can easily adjust those constants)
  (i# (α# β# μ# ρ#))
  (α# ((a#-atomic b#) ...))
  (β# ((a#-collective (b# ...)) ...)) ; collective actors, represented by a set of abstract behaviors
  (b# ((Q# ...) e#)) ; behavior
  ;; REFACTOR: make a general structure for abstract multisets: values with multiplicities attached
  (μ# ((a# v# m) ...)) ; message packets
  (m single many) ; m for "multiplicity"
  (ρ# ([τ (marked a# mk ...)] ...))
  (Q# (define-state (q [x τ] ...) (x) e#)
      (define-state (q [x τ] ...) (x) e# [(timeout e#) e#]))
  (v# (marked a# mk ...)
      (variant t v# ...)
      (record [l v#] ...)
      (folded τ v#)
      abs-nat
      abs-string
      (list-val v# ...)
      (hash-val (v# ...) (v# ...)))
  (e# (spawn any_location τ e# Q# ...)
      (spawning a# τ e# Q# ...)
      (goto q e# ...)
      (send e# e#)
      (begin e# ... e#)
      (let ([x e#] ...) e#)
      (case e# [(t x ...) e#] ...)
      (variant t e# ...)
      (record [l e#] ...)
      (: e# l)
      (fold τ e#)
      (unfold τ e#)
      (primop e# ...)
      (printf string e# ...) ; for debugging only
      (list e# ...)
      (hash [e# e#] ...)
      (for/fold ([x e#]) ([x e#]) e#)
      (loop-context e#)
      x
      v#)
  (a# a#-atomic
      a#-collective)
  ;; if natural = 0 for internal address, the actor was spanwed before the current handler was run or
  ;; there was no current handler before the current handler was run
  (a#-atomic (addr loc natural))
  (a#-collective (collective-addr loc))
  ;; H# = handler machine state (exp + outputs + spawns so far + least unused marker)
  (H# (e# [([(marked a# mk ...) v# m] ...) ((a# b#) ...) mk]))
  (E# hole
      (spawning a# τ E# Q# ...)
      (goto q v# ... E# e# ...)
      (send E# e#)
      (send v# E#)
      (begin E# e# ...)
      (let ([x v#] ... [x E#] [x e#] ...) e#)
      (case E# [(t x ...) e#] ...)
      (variant t v# ... E# e# ...)
      (record [l v#] ... [l E#] [l e#] ...)
      (: E# l)
      (fold τ E#)
      (unfold τ E#)
      (primop v# ... E# e# ...)
      (printf string v# ... E# e# ...)
      (list v# ... E# e# ...)
      (hash [v# v#] ... [E# e#] [e# e#] ...)
      (hash [v# v#] ... [v# E#] [e# e#] ...)
      (for/fold ([x E#]) ([x e#]) e#)
      (for/fold ([x v#]) ([x E#]) e#)
      (loop-context E#))
  (trigger# (timeout a#)
            (internal-receive         a#     v# m)
            (external-receive (marked a# mk ...) v#)))

;; ---------------------------------------------------------------------------------------------------
;; Test Data

(module+ test
  (define test-behavior1
    (term (((define-state (TestState1) (x) (goto TestState1)))
           (goto TestState1)))))

;; ---------------------------------------------------------------------------------------------------
;; Message generation

;; NOTE: using a really big marker for the intiial "unused" (100), so the marker in the message
;; doesn't depend on what markers are currently in the configuration. This should avoid
;; unnecessary duplicate configs
(define INIT-MESSAGE-MARKER 100)

;; Returns the exhaustive list of externals-only message representatives for the given type and unused
;; marker
(define (csa#-messages-of-type type)
  ;; reset the generated address, so that we don't keep finding different numbers for different types
  ;; (or even the same type, if metafunction caching ever goes away here)
  ;;
  ;; TODO: can I get re-enable caching now that I don't use a global for the generated addresses?
  (parameterize ([caching-enabled? #f])
    (map (lambda (v) (first (mark v INIT-MESSAGE-MARKER))) (term (messages-of-type/mf ,type)))))

;; Generates all *unmarked* messages of the given type
(define-metafunction csa#
  messages-of-type/mf : τ -> (v# ...)
  [(messages-of-type/mf Nat) (abs-nat)]
  [(messages-of-type/mf String) (abs-string)]
  [(messages-of-type/mf (Union)) ()]
  [(messages-of-type/mf (Union [t_1 τ_1 ...] [t_rest τ_rest ...] ...))
   (v#_1 ... v#_rest ...)
   (where (v#_1  ...) (generate-variants t_1 τ_1 ...))
   (where (v#_rest ...)
          (messages-of-type/mf (Union [t_rest τ_rest ...] ...)))]
  [(messages-of-type/mf (minfixpt X τ))
   ((folded (minfixpt X τ) v#) ...)
   (where (v# ...)
          (messages-of-type/mf (type-subst τ X (minfixpt X τ))))]
  [(messages-of-type/mf (Record [l_rest τ_rest] ... [l_1 τ_1]))
   ,(for/fold ([records-so-far null])
              ([sub-record (term (messages-of-type/mf (Record [l_rest τ_rest] ...)))])
      (append
       (for/list ([generated-v (term (messages-of-type/mf τ_1))])
         (redex-let csa# ([(record [l_other v#_other] ...) sub-record]
                          [v#_1 generated-v])
           (term (record [l_other v#_other] ... [l_1 v#_1]))))
       records-so-far))]
  [(messages-of-type/mf (Record))
   ((record))]
  [(messages-of-type/mf (Addr τ))
   ((marked (collective-addr (env τ))))]
  [(messages-of-type/mf (List τ))
   (,(normalize-collection (term (list-val v# ...))))
   (where (v# ...) (messages-of-type/mf τ))]
  [(messages-of-type/mf (Hash τ_1 τ_2))
   (,(normalize-collection (term (hash-val (v#_keys ...) (v#_vals ...)))))
   (where (v#_keys ...) (messages-of-type/mf τ_1))
   (where (v#_vals ...) (messages-of-type/mf τ_2))])

;; Generate an exhaustive list of variant values for the given tag and type, with the natural argument
;; acting as max-depth for the number of recursive type unfoldings
(define-metafunction csa#
  generate-variants : t τ ... -> ((variant t v# ...) ...)
  [(generate-variants t) ((variant t))]
  [(generate-variants t τ_rest ... τ_1)
   ,(for/fold ([variants-so-far null])
              ([sub-variant (term (generate-variants t τ_rest ...))])
      (append
       (for/list ([generated-v (term (messages-of-type/mf τ_1))])
         (redex-let csa# ([(variant t v#_other ...) sub-variant]
                          [v#_1 generated-v])
           (term (variant t v#_other ... v#_1))))
       variants-so-far))])

(module+ test
  (test-same-items? "messages-of-type 1"
   (term (messages-of-type/mf Nat))
   '(abs-nat))
  (test-same-items? "messages-of-type 2"
    (term (messages-of-type/mf (Union [Begin]))) (list '(variant Begin)))
  (test-same-items? "messages-of-type 3"
   (term (messages-of-type/mf (Union [A] [B])))
   '((variant A) (variant B)))
  (test-same-items? "messages-of-type 4"
    (term (messages-of-type/mf (Union))) null)
  (test-same-items? "messages-of-type 5"
   (term (messages-of-type/mf (Record [a Nat] [b Nat])))
   (list '(record [a abs-nat] [b abs-nat])))
  (test-same-items? "messages-of-type 6"
   (csa#-messages-of-type `(Record [a (Addr Nat)] [b (Addr Nat)]))
   (list `(record [a (marked (collective-addr (env Nat)) ,INIT-MESSAGE-MARKER)]
                  [b (marked (collective-addr (env Nat)) ,(add1 INIT-MESSAGE-MARKER))])))
  (test-same-items? "messages-of-type 7"
   (term (messages-of-type/mf (Record [x (Union [A] [B])] [y (Union [C] [D])])))
   (list '(record [x (variant A)] [y (variant C)])
         '(record [x (variant A)] [y (variant D)])
         '(record [x (variant B)] [y (variant C)])
         '(record [x (variant B)] [y (variant D)])))
  (define recursive-record-address-type
    `(minfixpt RecTypeAddr (Addr (Record [a RecTypeAddr]))))
  (define recursive-record-type
    `(Record [a ,recursive-record-address-type]))
  (test-same-items? "messages-of-type 8"
   (csa#-messages-of-type recursive-record-type)
   (list `(record [a (folded ,recursive-record-address-type
                             (marked (collective-addr (env ,recursive-record-type))
                                     ,INIT-MESSAGE-MARKER))])))
  (test-same-items? "messages-of-type 9"
   (term (messages-of-type/mf (Union)))
   '())
  (test-same-items? "messages-of-type 10"
   (term (messages-of-type/mf (Union [A] [B String (Union [C] [D])])))
   '((variant A)
     (variant B abs-string (variant C))
     (variant B abs-string (variant D))))
  (test-same-items? "messages-of-type 11"
   (term (messages-of-type/mf (List Nat)))
   (list `(list-val abs-nat)))
  (test-same-items? "messages-of-type 12"
   (term (messages-of-type/mf (Hash Nat (Union [A] [B] [C]))))
   (list `(hash-val (abs-nat) ((variant A) (variant B) [variant C])))))

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; REFACTOR: give these structs better names

;; Represents the effects of a single handler-level transition of an actor, before the results are
;; applied to the pre-handler configuration. Used for the widening optimization.
;;
;; trigger: trigger#
;;
;; behavior: b#
;;
;; sends: (Listof [(marked a# mk...) v# m])
;;
;; spawns: (Listof [a# b#])
;;
;; unused-marker: mk ; TODO: remove this?
(struct csa#-transition-effect (trigger behavior sends spawns unused-marker) #:transparent)

(define (csa#-transition-spawn-locs transition)
  (map address-location (map first (csa#-transition-effect-spawns transition))))

;; Represents a single handler-level transition of an actor. Trigger is the event that caused the
;; handler to run, outputs is the list of outputs to the external world that happened during execution
;; (as formatted in csa#-transition-effect), and final-config is the resulting abstract configuration.
;;
;; This is the result of applying a csa#-transition-effect
(struct csa#-transition
  (trigger ; follows trigger# above
   outputs ; list of marked-abstract-addr/abstract-message/multiplicity 3-tuples
   final-config) ; an abstract implementation configuration
  #:transparent)

;; impl-config -> (Listof trigger#)
(define (csa#-enabled-internal-actions config)
  (define internal-message-triggers
    (for/list ([packet-entry (csa#-config-message-packets config)])
      (match-define `[,address ,message ,multiplicity] packet-entry)
      (term (internal-receive ,address ,message ,multiplicity))))
  (define atomic-actor-timeouts
    (for/fold ([timeout-triggers null])
              ([actor (csa#-config-actors config)])
      (define address (csa#-actor-address actor))
      (if (get-timeout-handler-exp (actor-behavior actor))
          (cons (term (timeout ,address)) timeout-triggers)
          timeout-triggers)))
  (define collective-actor-timeouts
    (for/fold ([timeout-triggers null])
              ([blurred-actor (csa#-config-blurred-actors config)])
      (define address (csa#-blurred-actor-address blurred-actor))
      (if (ormap (lambda (behavior) (get-timeout-handler-exp behavior))
                 (csa#-blurred-actor-behaviors blurred-actor))
          (cons (term (timeout ,address)) timeout-triggers)
          timeout-triggers)))
  (append internal-message-triggers atomic-actor-timeouts collective-actor-timeouts))

(define (csa#-make-external-trigger marked-address message)
  (term (external-receive ,marked-address ,message)))

(define trigger-eval-cache (make-hash))
(define trigger-eval-cache-lookup-count 0)
(define trigger-eval-cache-found-count 0)

;; i# trigger# -> (Listof csa#-transtion-effect)
(define (csa#-eval-trigger config trigger abort)
  (match trigger
    [`(timeout ,addr)
     (eval-timeout config addr trigger abort)]
    [`(internal-receive ,addr ,message ,mult)
     (eval-message config addr message trigger abort)]
    [`(external-receive (marked ,addr ,_ ...) ,message)
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
  (match-define `(,atomics ,collectives ,packets ,recs) config)
  (define new-packets
    ;; if the multiplicity is not single, it must be many, so we just return the original config
    ;; because nothing is actually removed
    (remove (append addr-val-pair `(single)) packets))
  `(,atomics ,collectives ,new-packets ,recs))

(module+ test
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1 0) abs-nat single]
                                  [(init-addr 2 0) abs-nat single]
                                  [(init-addr 1 0) abs-string single])
                              ())
                         `((init-addr 1 0) abs-nat))
   `(() () ([(init-addr 2 0) abs-nat single]
            [(init-addr 1 0) abs-string single])
        ()))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1 0) abs-nat single]
                                  [(init-addr 2 0) abs-nat single]
                                  [(init-addr 1 0) abs-string single])
                              ())
                         `((init-addr 2 0) abs-nat))
   `(() () ([(init-addr 1 0) abs-nat single]
            [(init-addr 1 0) abs-string single])
        ()))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1 0) abs-nat single]
                                  [(init-addr 2 0) abs-nat many]
                                  [(init-addr 1 0) abs-string single])
                              ())
                         `((init-addr 2 0) abs-nat))
   `(() () ([(init-addr 1 0) abs-nat single]
            [(init-addr 2 0) abs-nat many]
            [(init-addr 1 0) abs-string single])
        ()))
  (check-equal?
   (config-remove-packet `(() () ([(init-addr 1 0) abs-nat single]
                                  [(init-addr 2 0) abs-nat many]
                                  [(init-addr 1 0) abs-string single])
                              ())
                         `((init-addr 3 0) abs-nat))
   `(() () ([(init-addr 1 0) abs-nat single]
            [(init-addr 2 0) abs-nat many]
            [(init-addr 1 0) abs-string single])
        ())))

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

;; Returns all behaviors currently available in the given config for the actor with the given address
;; (will only be a single behavior for precise addresses, one or more for blurred ones).
(define (current-behaviors-for-address config address)
  (cond
    [(csa#-atomic-address? address)
     (list (actor-behavior (csa#-config-actor-by-address/fail config address)))]
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

;; H# trigger# a#int impl-config (impl-config a#int e# -> impl-config) -> (Listof csa#-transition-effect)
;;
;; Evaluates the given handler machine for the given trigger at the given actor address, returning for
;; each possible handler-level transition the final goto expression as well as all effects (outputs
;; and spawns). Calls the abort continuation instead if a transition leads to an unverifiable state.
(define (eval-handler handler-machine trigger state-defs abort)
  (parameterize ([abort-evaluation-param abort])
    (stat-set! STAT-num-eval-handler-calls (add1 (stat-value STAT-num-eval-handler-calls)))
    (define final-machine-states
      (match (and (MEMOIZE-EVAL-HANDLER?) (hash-ref eval-cache handler-machine #f))
        [#f
         ;; REFACTOR: have eval-machine just take the whole machine as input
         ;;
         ;; REFACTOR: don't return stuck states; just error if we run into them
         (match-define (list init-exp init-effects) handler-machine)
         (match-define (list maybe-duplicate-value-states stuck-states)
           (eval-machine init-exp
                         init-effects
                         (not (csa#-atomic-address? (trigger-address trigger)))))
         ;; OPTIMIZE: find out if there's a way to prevent the eval from generating duplicate states
         ;; in the first place (for loops probably make this hard). My hunch is there's no easy way to
         ;; do it.
         (define value-states (remove-duplicates maybe-duplicate-value-states))
         (unless (empty? stuck-states)
           (error 'eval-handler
                  "Abstract evaluation did not complete\nInitial state: ~s\nFinal stuck states:~s"
                  handler-machine
                  stuck-states))
         (when (MEMOIZE-EVAL-HANDLER?)
           (hash-set! eval-cache handler-machine value-states))
         value-states]
        [cached-results
         (stat-set! STAT-num-eval-handler-cache-hits
                    (add1 (stat-value STAT-num-eval-handler-cache-hits)))
         cached-results]))

    (for/list ([machine-state final-machine-states])
      ;; REFACTOR: rename outputs to something like "transmissions", because some of them stay
      ;; internal to the configuration
      (match-define (list final-exp (list outputs spawns unused-marker)) machine-state)
      (redex-let csa# ([(in-hole E# (goto q v#_param ...)) final-exp])
        (csa#-transition-effect
         trigger
         (term (,state-defs (goto q v#_param ...)))
         outputs
         spawns
         unused-marker)))))

(module+ test
  (test-equal? "Atomic actor spawns atomic actors"
    (eval-handler `((begin (spawn 1 Nat (goto S1)) (goto S2)) (() () ,INIT-HANDLER-MARKER))
                  `(timeout (addr 1 0))
                  null
                  #f)
    (list (csa#-transition-effect `(timeout (addr 1 0))
                                  `(() (goto S2))
                                  null
                                  (list `[(addr 1 1) (() (goto S1))])
                                  INIT-HANDLER-MARKER)))

  (test-equal? "Collective actor spawns collective actors"
    (eval-handler `((begin (spawn 2 Nat (goto S1)) (goto S2)) (() () ,INIT-HANDLER-MARKER))
                  `(timeout (collective-addr 1))
                  null
                  #f)
    (list (csa#-transition-effect `(timeout (collective-addr 1))
                                  `(() (goto S2))
                                  null
                                  (list `[(collective-addr 2) (() (goto S1))])
                                  INIT-HANDLER-MARKER))))

;; ---------------------------------------------------------------------------------------------------
;; Interpreter

;; REFACTOR: ideal thing would be a match-like macro that has special markers around the sub-terms to
;; eval, and each clause only deals with the *values* (stuck states are returned automatically). I
;; think that takes more macro-fu than I have time to learn right now, though (mostly because it
;; requires handling ellipses in patterns). If I did ever write it, though, it would probably be a
;; useful Racket package.
;;
;; Also, this should probably be written in a more canonical monad style (I think this is just a
;; combination of a state monad and some kind of non-determinism monad), but I don't know enough about
;; monads to do that right now.

;; A MachineState is (Tuple Exp (Tuple Transmissions Spawns Marker)), where Transmissions, Spawns, and
;; Marker are as in H#
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
         ;; Find exactly one matching clause
         (let loop ([clauses clauses])
           (match clauses
             [(list) (one-stuck-result `(case ,v) effects)]
             [(list `(,pat ,body) other-clauses ...)
              (match (match-case-pattern v pat)
                [#f (loop other-clauses)]
                [bindings (eval-machine/internal (csa#-subst-n body bindings) effects)])])))
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
           [_ (one-stuck-result `(: ,v ,l) effects)]))
       (lambda (stuck) `(: ,stuck l)))]
    ;; Recursive Types
    [`(fold ,type ,exp)
     (eval-and-then exp effects
       (lambda (v effects)
         (value-result `(folded ,type ,v) effects))
       (lambda (stuck) `(fold ,type ,stuck)))]
    [`(unfold ,type ,e)
     (eval-and-then e effects
       (lambda (v effects)
         (match v
           [`(folded ,type ,val) (value-result val effects)]
           [_ (error 'eval-machine/internal "Bad argument to unfold: ~s" v)]))
       (lambda (stuck) `(unfold ,type ,stuck)))]
    [`(folded ,_ ...) (value-result exp effects)]
    ;; Numeric/Boolean Operators
    [`(,(and op (or '< '<= '> '>=)) ,arg1 ,arg2)
     (eval-and-then* (list arg1 arg2) effects
       (lambda (vs effects)
         (match vs
           [`(abs-nat abs-nat) (value-result `(variant True) `(variant False) effects)]
           [_ (error "Bad args to relative op: ~s\n" `(,op ,@vs))]))
       (lambda (stucks) `(,op ,@stucks)))]
    [`(,(and op (or '+ '- 'mult '/ 'arithmetic-shift)) ,arg1 ,arg2)
     (eval-and-then* (list arg1 arg2) effects
       (lambda (vs effects)
         (match vs
           [`(abs-nat abs-nat) (value-result `abs-nat effects)]
           [_ (error "Bad args to binary arithmetic op: ~s\n" `(,op ,@vs))]))
       (lambda (stucks) `(,op ,@stucks)))]
    [`(,(and op (or 'random)) ,arg)
     (eval-and-then arg effects
       (lambda (v effects)
         (match v
           [`abs-nat (value-result `abs-nat effects)]
           [_ (error "Bad args to unary arithmetic op: ~s\n" `(,op ,v))]))
       (lambda (stuck) `(,op ,stuck)))]
    [`(and ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (match-define (list v1 v2) vs)
         (value-result (term (csa#-and ,v1 ,v2)) effects))
       (lambda (stucks) `(and ,@stucks)))]
    [`(or ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (match-define (list v1 v2) vs)
         (value-result (term (csa#-or ,v1 ,v2)) effects))
       (lambda (stucks) `(or ,@stucks)))]
    [`(not ,e)
     (eval-and-then e effects
       (lambda (v effects)
         (value-result (term (csa#-not ,v)) effects))
       (lambda (stuck) `(not ,stuck)))]
    [`(= ,e1 ,e2)
     (eval-and-then* (list e1 e2) effects
       (lambda (vs effects)
         (value-result `(variant True) `(variant False) effects))
       (lambda (stucks) `(= ,@stucks)))]
    ;; Lists and Hashes
    [`(,(and op (or 'list 'cons 'list-as-variant 'list-ref 'remove 'length 'append 'list-copy 'take 'drop 'hash-ref 'hash-keys 'hash-values 'hash-set 'hash-remove 'hash-has-key? 'hash-empty?))
       ,args ...)
     (eval-and-then* args effects
       (lambda (vs effects)
         (match (cons op vs)
           [`(list ,vs ...) (value-result (normalize-collection `(list-val ,@vs)) effects)]
           [`(cons ,v (list-val ,existing-list-vals ...))
            (value-result (normalize-collection `(list-val ,@existing-list-vals ,v)) effects)]
           [`(list-as-variant ,l)
            (match l
              [`(list-val ,items ...)
               (apply value-result
                      `(variant Empty)
                      (append (for/list ([item items]) `(variant Cons ,item ,l))
                              (list effects)))]
              [_ (error 'eval-machine/internal "Bad list for list-as-variant: ~s\n" l)])]
           [`(list-ref ,l ,_)
            (match l
              ;; NOTE: we can just return the empty list of results if there are no items in the list:
              ;; we assume that that won't happen, and that therefore we only reached this state
              ;; through over-abstraction
              [`(list-val ,items ...) (apply value-result (append items (list effects)))]
              [_ (error 'eval-machine/internal "Bad list for list-ref: ~s\n" l)])]
           [`(remove ,_ ,l) (value-result l effects)]
           [`(length ,_) (value-result `abs-nat effects)]

           [`(,(or 'take 'drop 'list-copy) ,v ,_ ...)
            (value-result v effects)]
           ;; at least one of the lists is precise, so convert the whole thing to a precise list
           ;; (so that we don't lose a precise address)
           [`(append ,v1 ,v2)
            (value-result
             (normalize-collection `(list-val ,@(list-values v1) ,@(list-values v2)))
             effects)]
           [`(hash-ref (hash-val ,_ ,vals) ,k)
            (apply value-result
                   `(variant Nothing)
                   (append (for/list ([val vals]) `(variant Just ,val))
                           (list effects)))]
           [`(hash-keys (hash-val ,keys ,_))
            (value-result `(list-val ,@keys) effects)]
           [`(hash-values (hash-val ,_ ,values))
            (value-result `(list-val ,@values) effects)]
           [`(hash-set (hash-val ,keys ,vals) ,key ,val)
            (value-result
             (normalize-collection `(hash-val ,(cons key keys) ,(cons val vals)))
             effects)]
           [`(hash-remove ,h ,k) (value-result h effects)]
           [`(hash-has-key? ,h ,k)
            (value-result `(variant True) `(variant False) effects)]
           [`(hash-empty? ,h)
            (value-result `(variant True) `(variant False) effects)]
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
             ;; We set the empty-eval-result as the loop-result while evaluating the loop body: this
             ;; is what we expect to return if we reduce to this exact same state from here (the notes
             ;; above explain why). After evaluation complete, we set the loop-result to the full set
             ;; of resulting states.
             (hash-set! (loop-results) this-loop empty-eval-result)
             (match-define `(list-val ,collection-members ...) items-val)
             (define result-after-skipping (value-result result-val effects))
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
    ;; Communication
    [`(send ,e-addr ,e-message)
     (eval-and-then* (list e-addr e-message) effects
       (lambda (vs effects)
         (match-define (list v-addr v-message) vs)
         (define quantity (if (in-loop-context?) 'many 'single))
         (match-define `(,sends ,spawns ,unused-marker) effects)
         (match-define `[,maybe-marked-message ,new-unused-marker]
           (if (internal-output? `[,v-addr ,v-message ,quantity])
               `[,v-message ,unused-marker]
               (mark v-message unused-marker)))
         (value-result maybe-marked-message
                       `(,(add-output sends (term [,v-addr ,maybe-marked-message ,quantity]))
                         ,spawns
                         ,new-unused-marker)))
       (lambda (stucks) `(send ,@stucks)))]
    ;; Spawns
    [`(spawn ,loc ,type ,init-exp ,raw-state-defs ...)
     (define address
       (if (or (in-collective-handler?) (in-loop-context?))
           `(collective-addr ,loc)
           `(addr ,loc 1)))
     (define marked-address `(marked ,address))
     (define state-defs
       (for/list ([def raw-state-defs])
         (csa#-subst-n/Q# def (list `[self ,marked-address]))))
     (eval-and-then (csa#-subst-n init-exp (list `[self ,marked-address])) effects
       (lambda (goto-val effects)
         (match-define (list sends spawns marker) effects)
         (value-result marked-address
                       (list sends
                             (add-spawn spawns `[,address (,state-defs ,goto-val)])
                             marker)))
       (lambda (stuck) `(spawn ,loc ,type ,stuck ,@raw-state-defs)))]
    ;; Goto
    [`(goto ,state-name ,args ...)
     (eval-and-then* args effects
       (lambda (arg-vals effects) (value-result `(goto ,state-name ,@arg-vals) effects))
       (lambda (stucks) `(goto ,state-name ,@stucks)))]
    [`(,(or 'list-val 'hash-val) ,_ ...) (value-result exp effects)]
    ;; Debugging
    [`(printf ,template ,args ...)
     (eval-and-then* args effects
       (lambda (vs effects)
         (apply printf template vs)
         (flush-output)
         (value-result `abs-nat effects))
       (lambda (stucks) `(printf ,@stucks)))]
    ;; Misc. Values
    [`(variant ,tag ,exps ...)
     (eval-and-then* exps effects
       (lambda (vs effects) (value-result `(variant ,tag ,@vs) effects))
       (lambda (stucks) `(variant ,tag ,@stucks)))]
    [`abs-nat (value-result `abs-nat effects)]
    [`abs-string (value-result `abs-string effects)]
    [`(marked ,_ ,_ ...) (value-result exp effects)]
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
    (eval-and-then* (list `abs-nat `(case (variant A))) empty-effects
        (lambda (vs fx) (error "shouldn't do this"))
        (lambda (stucks) `(variant B ,@stucks)))
    (eval-machine-result
     null
     (list (machine-state `(variant B abs-nat (case (variant A))) empty-effects)))))

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

;; NOTE: using 200 as the initial unused marker, which should be large enough to account for all
;; markers on config and any received message (after assimilation and canonicalization)
(define INIT-HANDLER-MARKER 200)
(define empty-effects `(() () ,INIT-HANDLER-MARKER))

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

  ;; REFACTOR: rename this to something like check-exp-reduces*-to, since it reduces all the way to
  ;; either a stuck state or a value
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

  (define-syntax (test-exp-steps-to? stx)
    (syntax-parse stx
      [(_ name actual expected)
       #`(test-case name #,(syntax/loc stx (check-exp-steps-to? actual expected)))]))

  (test-exp-steps-to? "exp-steps-to variant 1" `(variant B) `(variant B))
  (test-exp-steps-to? "exp-steps-to begin" `(begin (variant A) (variant B)) `(variant B))
  (test-exp-steps-to? "exp-steps-to case"
                      `(case (variant A abs-nat)
                         [(A x) x]
                         [(B) (variant X)]
                         [(C) (variant Y)])
                      `abs-nat)
  (test-exp-steps-to? "exp-steps-to let"
                      `(let ([x (variant X)]
                             [y (variant Y)])
                         (variant A x y y))
                      `(variant A (variant X) (variant Y) (variant Y)))
  (test-exp-steps-to? "exp-steps-to record"
                      `(record [a (let () (variant A))] [b abs-nat])
                      `(record [a (variant A)] [b abs-nat]))
  (test-exp-steps-to? "exp-steps-to other record"
                      `(record [a (let () (variant A))]
                               [b (case (variant A) [(B) abs-nat])]
                               [c (let () abs-nat)])
                      `(record [a (variant A)] [b (case (variant A))] [c (let () abs-nat)]))
  (test-exp-steps-to? "exp-steps-to record field"
                      `(: (record [a (variant A)] [b (variant B)]) b)
                      `(variant B))
  (test-exp-steps-to? "exp-steps-to other record field"
                      `(: (record [a (variant A)] [b (variant B)]) c)
                      `(: (record [a (variant A)] [b (variant B)]) c))
  (test-exp-steps-to? "exp-steps-to marked address"
                      `(marked (addr 1 1))
                      `(marked (addr 1 1)))
  (test-exp-steps-to? "exp-steps-to fold"
                      (term (fold   (Union [A]) (variant A)))
                      (term (folded (Union [A]) (variant A))))
  (test-exp-steps-to? "exp-steps-to record fold"
                      (term (record [a (fold   ,recursive-record-address-type (marked (addr (env ,recursive-record-type) 1)))]))
                      (term (record [a (folded ,recursive-record-address-type (marked (addr (env ,recursive-record-type) 1)))])))
  (test-exp-steps-to? "exp-steps-to another record fold"
                      `(record [a (unfold ,recursive-record-address-type (folded ,recursive-record-address-type (marked (addr (env ,recursive-record-type) 1))))])
                      `(record [a (marked (addr (env ,recursive-record-type) 1))]))
  (check-exp-steps-to-all? `(< abs-nat (let () abs-nat))
                           (list `(variant True) `(variant False)))
  (test-exp-steps-to? "exp-steps-to plus"
                      `(+ abs-nat (let () abs-nat))
                      `abs-nat)
  (test-exp-steps-to? "exp-steps-to random"
                      `(random abs-nat)
                      `abs-nat)
  (test-exp-steps-to? "exp-steps-to or"
                      `(or (variant True) (variant False))
                      `(variant True))
  (test-exp-steps-to? "exp-steps-to and"
                      `(and (variant True) (variant False))
                      `(variant False))
  (test-exp-steps-to? "exp-steps-to not"
                       `(not (variant True))
                       `(variant False))
  ;; Equality checks
  (check-exp-steps-to-all? (term (= abs-string abs-string))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all? (term (= abs-nat abs-nat))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all? (term (= (marked (collective-addr (env 1))) (marked (addr (env 1) 0))))
                          (list (term (variant True)) (term (variant False))))

  ;; Tests for sorting when adding to lists and hashes
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
   (term (remove (variant A) (list-val (variant A) (variant B))))
   (term (list-val (variant A) (variant B))))
  (check-exp-steps-to-all?
   `(list-ref (list-val) abs-nat)
   null)
  (check-exp-steps-to?
   (term (append (list-val (variant A) (variant B))
                        (list-val (variant C) (variant D))))
   (term (list-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
   (term (append (list-val (variant A) (variant B))
                        (list-val (variant C) (variant B))))
   (term (list-val (variant A) (variant B) (variant C))))
  (check-exp-steps-to?
   (term (append (list-val (variant C) (variant D))
                        (list-val (variant A) (variant B))))
   (term (list-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
  (term (append (list-val (variant C) (variant D))
                       (list-val (variant B) (variant A))))
  (term (list-val (variant A) (variant B) (variant C) (variant D))))
  (check-exp-steps-to? (term (append (list-val) (list-val))) (term (list-val)))
  (check-exp-steps-to?
   (term (append (list-val (variant A)) (list-val)))
   (term (list-val (variant A))))
  (check-exp-steps-to?
   (term (append (list-val) (list-val (variant A))))
   (term (list-val (variant A))))
  (check-exp-steps-to-all?
   `(list-ref (list-val) abs-nat)
   null)
  (check-exp-steps-to? `(list-copy (list-val abs-nat) abs-nat abs-nat)
                       `(list-val abs-nat))
  (check-exp-steps-to? `(take (list-val abs-nat) abs-nat)
                       `(list-val abs-nat))
  (check-exp-steps-to? `(drop (list-val abs-nat) abs-nat)
                       `(list-val abs-nat))

  ;; hash
  (check-exp-steps-to?
   (term (hash [abs-nat (variant B)] [abs-nat (variant A)]))
   (term (hash-val (abs-nat) ((variant A) (variant B)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (abs-nat) ((variant B) (variant C))) abs-nat (variant A)))
   (term (hash-val (abs-nat) ((variant A) (variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (abs-nat) ((variant C) (variant B))) abs-nat (variant A)))
   (term (hash-val (abs-nat) ((variant A) (variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val () ()) abs-nat (variant A)))
   (term (hash-val (abs-nat) ((variant A)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (abs-nat) ((variant B) (variant C))) abs-nat (variant D)))
   (term (hash-val (abs-nat) ((variant B) (variant C) (variant D)))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (abs-nat) ((variant B) (variant C))) abs-nat (variant B)))
   (term (hash-val (abs-nat) ((variant B) (variant C)))))
  (check-exp-steps-to?
   (term (hash-remove (hash-val (abs-nat) ((variant B) (variant C))) (variant B)))
   (term (hash-val (abs-nat) ((variant B) (variant C)))))
  (check-exp-steps-to? (term (hash-ref (hash-val () ()) abs-nat))
                       '(variant Nothing))
  (check-exp-steps-to-all? (term (hash-empty? (hash-val (abs-nat) ((variant A) (variant B)))))
                           (list (term (variant True))
                                 (term (variant False))))
  (check-exp-steps-to-all? (term (list-as-variant (list-val (variant A) (variant B))))
                           (list (term (variant Empty))
                                 (term (variant Cons (variant A) (list-val (variant A) (variant B))))
                                 (term (variant Cons (variant B) (list-val (variant A) (variant B))))))
  (check-exp-steps-to? (term (hash-keys (hash-val ((variant A) (variant B)) (abs-nat))))
                       (term (list-val (variant A) (variant B))))
  (check-exp-steps-to? (term (hash-values (hash-val (abs-nat) ((variant A) (variant B)))))
                       (term (list-val (variant A) (variant B))))
  (check-exp-steps-to-all? `(for/fold ([result (variant X)])
                                      ([item (list abs-nat)])
                              (variant Y))
                           (list `(variant X) `(variant Y)))
  (test-case "Seeing the same loop twice in different contexts returns all results"
    (check-exp-steps-to-all?
     `(let ([a (list-ref (list-val (variant A) (variant B)) abs-nat)])
        (begin
          (for/fold ([dummy abs-nat])
                    ([item (list-val abs-nat)])
            item)
          a))
     (list '(variant A) '(variant B))))

  (test-case "Loops do not return duplicate values"
    (define terminal-exps
      (exp-reduce* `(for/fold ([result (variant X)])
                              ([item (list (variant A) (variant B) (variant C))])
                      (case (list-ref (list-val (variant True) (variant False)) abs-nat)
                        [(True) item]
                        [(False) result]))))
    (check-equal? (length terminal-exps) (length (remove-duplicates terminal-exps))))

  (test-equal? "eval-machine test"
    (eval-machine
     `(spawn loc Nat
             (goto Foo self)
             (define-state (Foo) (m) (goto Foo)))
     empty-effects
     #f)
    (value-result `(marked (addr loc 1))
                  `(()
                    ([(addr loc 1)
                      (((define-state (Foo) (m) (goto Foo)))
                       (goto Foo (marked (addr loc 1))))])
                    ,INIT-HANDLER-MARKER)))

  (test-case "Spawn in loop is a collective actor"
    (check-same-items?
     (first
      (eval-machine
       `(for/fold ([dummy abs-nat])
                  ([item (list-val abs-nat)])
          (begin
            (spawn loc Nat (goto Foo (variant A)))
            abs-nat))
       empty-effects
       #f))
     (list
      (machine-state `abs-nat `(() () ,INIT-HANDLER-MARKER))
      (machine-state
       `abs-nat
       `(() ([(collective-addr loc) (() (goto Foo (variant A)))]) ,INIT-HANDLER-MARKER)))))

  (test-case "eval-machine test 2"
   (check-exp-steps-to? `(goto S (begin (variant A)) (begin (variant B) (variant C)))
                        `(goto S (variant A) (variant C))))

  (test-case "eval-machine test 3"
   (check-equal?
    (eval-machine
     `(begin (send (marked (addr 1 0)) abs-nat) (variant X))
     empty-effects
     #f)
    (eval-machine-result
     (list (machine-state `(variant X) `(([(marked (addr 1 0)) abs-nat single]) () ,INIT-HANDLER-MARKER)))
     null)))

  (test-case "Send in loop is a many-of message"
    (check-same-items?
     (first
      (eval-machine
       `(for/fold ([dummy abs-nat])
                  ([item (list-val abs-nat)])
          (send (marked (addr 1 0)) item))
       empty-effects
       #f))
     (list
      (machine-state `abs-nat `(() () ,INIT-HANDLER-MARKER))
      (machine-state `abs-nat `(([(marked (addr 1 0)) abs-nat many]) () ,INIT-HANDLER-MARKER)))))

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

  ;; testing this because I had a problem with it before
  (test-equal? "Internal addresses in the transmissions do not change the evaluation"
    (eval-machine `(begin (send (marked (addr 1 0)) abs-nat) (goto A)) empty-effects #f)
    (value-result `(goto A)
                  `((((marked (addr 1 0)) abs-nat single)) () ,INIT-HANDLER-MARKER))))

(define (list-values v)
  (match v
    [`(list-val ,vs ...) vs]))

;; Puts the given abstract collection value (a list or hash) and puts it into a canonical
;; form
(define (normalize-collection v)
  (match v
    [`(list-val ,vs ...)
     `(list-val ,@(sort (remove-duplicates vs) sexp<?))]
    [`(hash-val ,keys ,vals)
     `(hash-val ,(sort (remove-duplicates keys) sexp<?)
                ,(sort (remove-duplicates vals) sexp<?))]))

;; Adds a new output to an existing list of outputs, in sexp<? order, merging with existing outputs
;; and updating the multiplicity if needed
(define (add-output existing-outputs new-output)
  (match-define `[,new-addr ,new-val ,new-mult] new-output)
  (match existing-outputs
    [(list) (list new-output)]
    [(list old-output existing-outputs ...)
     (define new-output-without-mult `[,new-addr ,new-val])
     (define old-output-without-mult
       `[,(csa#-output-address old-output) ,(csa#-output-message old-output)])
     (cond
       [(equal? old-output-without-mult new-output-without-mult)
        (cons `[,new-addr ,new-val many] existing-outputs)]
       [(sexp<? new-output-without-mult old-output-without-mult)
        (cons new-output (cons old-output existing-outputs))]
       [else (cons old-output (add-output existing-outputs new-output))])]))

(module+ test
  (test-equal? "Basic add-output test 1: already exists"
    (add-output (list `[(marked (addr 1 0)) abs-nat single]
                      `[(marked (addr 2 0)) abs-nat single]
                      `[(marked (addr 3 0)) abs-nat single])
                `[(marked (addr 2 0)) abs-nat single])
    (list `[(marked (addr 1 0)) abs-nat single]
          `[(marked (addr 2 0)) abs-nat many]
          `[(marked (addr 3 0)) abs-nat single]))
  (test-equal? "Basic add-output test 2: does not exist"
    (add-output (list `[(marked (addr 1 0)) abs-nat single]
                      `[(marked (addr 2 0)) abs-nat single]
                      `[(marked (addr 3 0)) abs-nat single])
                `[(marked (addr 4 0)) abs-nat single])
    (list `[(marked (addr 1 0)) abs-nat single]
          `[(marked (addr 2 0)) abs-nat single]
          `[(marked (addr 3 0)) abs-nat single]
          `[(marked (addr 4 0)) abs-nat single]))
  (test-equal? "Must include collective-address outputs for the purpose of escaped addresses"
    (add-output `() `[(marked (collective-addr (env (Addr Nat)))) (marked (addr 2 0)) single])
    `([(marked (collective-addr (env (Addr Nat)))) (marked (addr 2 0)) single])))

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
      [`(internal-receive ,_ ,message ,_) (config-remove-packet config (list addr message))]
      [_ config]))
  ;; 2. update the behavior
  (define new-behavior (csa#-transition-effect-behavior transition-effect))
  (define with-updated-behavior
    (if (csa#-atomic-address? addr)
        (update-behavior/precise with-trigger-message-removed addr new-behavior)
        (config-add-blurred-behaviors with-trigger-message-removed (list `[,addr ,new-behavior]))))
  ;; 3. add spawned actors
  (define with-spawns (merge-new-actors with-updated-behavior (csa#-transition-effect-spawns transition-effect)))
  ;; 4. add sent messages
  (define-values (internal-sends external-sends)
    (partition internal-output? (csa#-transition-effect-sends transition-effect)))
  (define config-with-messages
    (merge-messages-into-config with-spawns (map output->packet internal-sends)))
  ;; 5. add new receptionists
  (define new-receptionists
    ;; NOTE: merge-receptionists will remove duplicates
    (append*
     (for/list ([output external-sends])
       (internal-addr-types (csa#-output-message output) (csa#-output-type output)))))
  (csa#-transition trigger
                   external-sends
                   (make-config (csa#-config-actors config-with-messages)
                                (csa#-config-blurred-actors config-with-messages)
                                (csa#-config-message-packets config-with-messages)
                                (merge-receptionists (csa#-config-receptionists config-with-messages)
                                                     new-receptionists))))

(module+ test
  (test-equal? "Applying transition merges in new receptionists"
    (csa#-apply-transition
     (make-config (list `[(addr 1 1) (() (goto A))]) null null null)
     (csa#-transition-effect `(timeout (addr 1 1))
                             `(() (goto A))
                             (list `[(marked (collective-addr (env (Addr String))))
                                     (marked (addr 1 1) 1)
                                     single])
                             null
                             2))
    (csa#-transition `(timeout (addr 1 1))
                     (list `[(marked (collective-addr (env (Addr String))))
                             (marked (addr 1 1) 1)
                             single])
                     (make-config (list `[(addr 1 1) (() (goto A))])
                                  null
                                  null
                                  (list `[String (marked (addr 1 1) 1)])))))

;; Sets the behavior for the actor with the given precise address to the given expression
(define (update-behavior/precise config address behavior)
  (match-define `(,first-actors ,_ ,later-actors)
    (config-actor-and-rest-by-address config address))
  (make-config
   `(,@first-actors (,address ,behavior) ,@later-actors)
   (csa#-config-blurred-actors config)
   (csa#-config-message-packets config)
   (csa#-config-receptionists config)))

(module+ test
  (test-equal? "update-behavior/precise"
    (redex-let csa# ([i# (make-config (list `[(addr 1 1) (() (goto A))]) null null null)])
      (update-behavior/precise (term i#) `(addr 1 1) `(() (goto B))))
    (make-config (list `[(addr 1 1) (() (goto B))]) null null null)))

;; converts an output (which includes the marker on an address) to a packet (which does not)
(define (output->packet output)
  `[,(unmark-addr (csa#-output-address output))
    ,(csa#-output-message output)
    ,(csa#-output-multiplicity output)])

;; Abstractly adds the set of new packets to the packet set in the given config.
(define (merge-messages-into-config config new-packets)
  (redex-let csa# ([(any_actors any_blurred any_packets any_recs) config])
    (term (any_actors
           any_blurred
           ,(merge-messages-into-packet-set (term any_packets) new-packets)
           any_recs))))

;; Abstractly adds the set of new packets to the given set.
(define (merge-messages-into-packet-set packet-set new-message-list)
  (deduplicate-packets (append packet-set new-message-list)))

(module+ test
  (test-equal? "merge-messages-into-config 1"
    (merge-messages-into-config (term (() () () ())) (list (term ((addr 0 0) abs-nat single))))
    (term (() () (((addr 0 0) abs-nat single)) ())))

  (test-equal? "merge-messages-into-config 2"
    (merge-messages-into-config (term (() () () ())) (list (term ((addr 0 0) abs-nat many))))
    (term (() () (((addr 0 0) abs-nat many)) ())))

  (test-equal? "merge-messages-into-config 3"
    (merge-messages-into-config (term (() () (((addr 0 0) abs-nat single)) ()))
                                (list (term ((addr 0 0) abs-nat single))))
    (term (() () (((addr 0 0) abs-nat many)) ())))

  (test-equal? "merge-messages-into-config 4"
    (merge-messages-into-config (term (() () (((addr 0 0) abs-nat single)) ()))
                                (list (term ((addr 0 0) abs-nat many))))
    (term (() () (((addr 0 0) abs-nat many)) ())))

  (test-equal? "merge-messages-into-config 5"
    (merge-messages-into-config (term (() () (((addr 0 0) abs-nat single)) ()))
                                (list (term ((addr 1 0) abs-nat many))))
    (term (() () (((addr 0 0) abs-nat single) ((addr 1 0) abs-nat many)) ())))

  (test-equal? "merge-messages-into-config 6"
    (merge-messages-into-config (term (()
                                       ()
                                       (((addr 1 0) (marked (collective-addr (env Nat))) single)
                                        ((addr 1 0) (marked (addr (env Nat) 0)) single))
                                       ()))
                                (term (((addr 1 0) (marked (collective-addr (env Nat))) single))))
    (term (()
           ()
           (((addr 1 0) (marked (collective-addr (env Nat))) many)
            ((addr 1 0) (marked (addr (env Nat) 0)) single))
           ()))))

(define (merge-new-actors config new-actors)
  (for/fold ([config config])
            ([actor new-actors])
    (match-define (list atomic-actors collective-actors messages recs) config)
    (match-define (list new-addr new-behavior) actor)
    (if (csa#-atomic-address? new-addr)
        (make-config (append atomic-actors (list (list new-addr new-behavior)))
                     collective-actors
                     messages
                     recs)
        (make-config  atomic-actors
                      (add-blurred-behaviors collective-actors (list `[,new-addr ,new-behavior]))
                      messages
                      recs))))

(module+ test
  (define new-spawn1
    (term ((addr foo 0) (((define-state (A) (x) (goto A))) (goto A)))))
  (define new-spawn2
    (term ((collective-addr foo) (((define-state (A) (x) (goto A))) (goto A)))))
  (define init-actor1
    (term ((addr 0 0) (((define-state (B) (x) (goto B))) (goto B)))))
  (test-equal? "merge-new-actors test"
               (merge-new-actors
                (make-single-actor-abstract-config init-actor1 null)
                (list new-spawn1 new-spawn2))
               (term ((,init-actor1 ,new-spawn1)
                      (((collective-addr foo)
                        ((((define-state (A) (x) (goto A))) (goto A)))))
                      ()
                      ()))))

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
    [`abs-nat `abs-nat]
    [`abs-string `abs-string]
    [`(marked (addr ,_ ,_) ,_ ...) exp]
    [`(marked (collective-addr ,_) ,_ ...) exp]
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
    [(list (and kw (or 'send 'begin (? primop?) 'list 'list-val 'loop-context)) args ...)
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
    [(list (and kw (or 'fold 'unfold 'folded)) type args ...)
     `(,kw ,type ,@(map do-subst args))]
    [`(hash [,keys ,vals] ...)
     `(hash ,@(map (lambda (k v) `[,(do-subst k) ,(do-subst v)]) keys vals))]
    [`(for/fold ([,x1 ,e1]) ([,x2 ,e2]) ,body)
     `(for/fold ([,x1 ,(do-subst e1)])
                ([,x2 ,(do-subst e2)])
        ,(csa#-subst-n body (shadow (list x1 x2))))]))

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
  (check-equal? (csa#-subst-n '(begin x) (list `[x abs-nat])) '(begin abs-nat))
  (check-equal? (csa#-subst-n '(send x y) (list `[y abs-nat])) '(send x abs-nat))
  (check-equal? (csa#-subst-n '(marked (addr (env Nat) 1)) (list `[x abs-nat])) '(marked (addr (env Nat) 1)))
  (check-equal? (csa#-subst-n '(= x y) (list `[x abs-nat])) '(= abs-nat y))
  (check-equal? (csa#-subst-n/case-clause `[(Cons p) (begin p x)] (list `[p abs-nat]))
                (term [(Cons p) (begin p x)]))
  (check-equal? (csa#-subst-n/case-clause `[(Cons p) (begin p x)] (list `[x abs-nat]))
                (term [(Cons p) (begin p abs-nat)]))
  (check-equal? (csa#-subst-n `(list abs-nat x) (list `[x abs-nat]))
                (term (list abs-nat abs-nat)))
  (check-equal? (csa#-subst-n `(variant Foo abs-nat) (list `[a abs-nat]))
                (term (variant Foo abs-nat)))
  (check-equal? (csa#-subst-n `(marked (addr 1 0)) (list `[x abs-nat]))
                `(marked (addr 1 0)))
  (test-equal? "try subst into marked collective address"
    (csa#-subst-n `(marked (collective-addr (env Nat)) 2) (list `[x abs-nat]))
    `(marked (collective-addr (env Nat)) 2))
  (test-equal? "spawn subst 1"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self abs-nat)
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[self (marked (addr 2 0))]))
    (term (spawn loc
                 Nat
                 (goto A self abs-nat)
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 2"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self abs-nat)
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[x (marked (addr 2 0))]))
    (term (spawn loc
                 Nat
                 (goto A self abs-nat)
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 3"
    (csa#-subst-n `(spawn loc
                          Nat
                          (goto A self abs-nat)
                          (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                  (list `[y (marked (addr 2 0))]))
    (term (spawn loc
                 Nat
                 (goto A self abs-nat)
                 (define-state (A [s Nat] [a Nat]) (x) (goto A x (marked (addr 2 0)) self)))))

  (test-equal? "shadowing works as expected"
    (csa#-subst-n `(begin (let ([x abs-nat]) x) x) (list (binding 'x 'abs-string)))
    `(begin (let ([x abs-nat]) x) abs-string))

    (test-equal? "let-binding test"
      (csa#-subst-n `(let ([x abs-nat] [y abs-nat]) (begin a x y z))
                    (list (binding 'x 'abs-string)
                          (binding 'z 'abs-string)))
      `(let ([x abs-nat] [y abs-nat]) (begin a x y abs-string)))

  (test-equal? "state-def subst 1"
    (csa#-subst-n/Q# `(define-state (A [x Nat] [y String]) (m) (begin x y z (goto A x y)))
                     (list `[z abs-nat]))
    `(define-state (A [x Nat] [y String]) (m) (begin x y abs-nat (goto A x y))))

    (test-equal? "state-def subst with timeout"
      (csa#-subst-n/Q# `(define-state (A [x Nat] [y String]) (m)
                          (begin x y z (goto A x y))
                          [(timeout z) (begin z (goto A x y))])
                     (list `[z abs-nat]))
      `(define-state (A [x Nat] [y String]) (m)
         (begin x y abs-nat (goto A x y))
         [(timeout abs-nat) (begin abs-nat (goto A x y))])))

;; Substitutes the second type for X in the first type
(define-metafunction csa#
  type-subst : τ X τ -> τ
  [(type-subst τ_1 X τ_2) (type-subst/internal τ_1 X τ_2)])

(define-metafunction csa#
  type-subst/internal : τ X any -> any
  [(type-subst/internal Nat _ _) Nat]
  [(type-subst/internal String _ _) String]
  [(type-subst/internal (minfixpt X any_1) X τ_2)
   (minfixpt X any_1)]
  [(type-subst/internal (minfixpt X_1 τ_1) X_2 any)
   (minfixpt X_fresh (type-subst/internal (type-subst/internal τ_1 X_1 X_fresh) X_2 any))
   (where X_fresh ,(variable-not-in (term ((minfixpt X_1 τ_1) X_2 any)) (term X_1)))]
  [(type-subst/internal X X any) any]
  [(type-subst/internal X_1 X_2 any) X_1]
  [(type-subst/internal (Union [t τ ...] ...) X any)
   (Union [t (type-subst/internal τ X any) ...] ...)]
  [(type-subst/internal (Record [l τ_l] ...) X any)
   (Record [l (type-subst/internal τ_l X any)] ...)]
  [(type-subst/internal (Addr τ) X any)
   (Addr (type-subst/internal τ X any))]
  [(type-subst/internal (List τ_e) X any) (List (type-subst/internal τ_e X any))]
  [(type-subst/internal (Hash τ_k τ_v) X any)
   (Hash (type-subst/internal τ_k X any) (type-subst/internal τ_v X any))])

(module+ test
  (test-equal? "type-subst on non-matching minfixpt"
    (term (type-subst (minfixpt SomeType (Addr (Record [a AnotherType] [b SomeType])))
                      AnotherType
                      Nat))
    (term (minfixpt SomeType1 (Addr (Record (a Nat) (b SomeType1)))))))

;; ---------------------------------------------------------------------------------------------------
;; Marking

;; any mk -> [any mk]
;;
;; Marks given AST with fresh markers, given that mk is the least unused marker. Additionally returns
;; the new unused least marker.
(define (mark ast unused-marker)
  (match ast
    [(list 'marked addr markers ...)
     `[(marked ,addr ,@markers ,unused-marker)
       ,(add1 unused-marker)]]
    [`(,ast1 ,ast-others ...)
     (match-define `[,m-ast1 ,mk1] (mark ast1 unused-marker))
     (match-define `[,m-rest ,mk-final] (mark ast-others mk1))
     `[(,m-ast1 ,@m-rest) ,mk-final]]
    [`() `[() ,unused-marker]]
    [_ `[,ast ,unused-marker]]))

(module+ test
  (test-equal? "mark 1"
    (mark (term ((marked (collective-addr (env Nat)) 0)
                 (marked (addr (env Nat) 1) 1)
                 abs-nat
                 (begin abs-string (marked (addr (env Nat) 1)))))
          2)
    (term [((marked (collective-addr (env Nat)) 0 2)
            (marked (addr (env Nat) 1) 1 3)
            abs-nat
            (begin abs-string (marked (addr (env Nat) 1) 4)))
           5])))

(define (unmark-addr marked)
  (match marked
    [`(marked ,a ,_ ...) a]))

(module+ test
  (test-equal? "unmark-addr"
    (unmark-addr `(marked (addr (env Nat) 1) 2 3))
    `(addr (env Nat) 1)))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; Abstracts the given CSA configuration, with a maximum recursion depth for values. Returns #f if
;; abstraction was not possible for some reason (e.g. an address was under a folded past the max fold
;; depth).
;;
;; NOTE: I think I've removed all code that would ever return #f (because max recursion depth is no
;; longer a thing), but I haven't taken the time to confirm that
;;
;; NOTE: currently supports only no-messages, no-externals configs
(define (csa#-abstract-config concrete-config)
  (term (abstract-config/mf ,concrete-config ())))

(define-metafunction csa#
  ;; NOTE: a_internal no longer used; keeping it here for now in case we ever need to thread it back
  ;; through
  abstract-config/mf : i (a_internal ...) -> i#
  [(abstract-config/mf (((a b) ...) ; actors
                        () ; messages-in-transit
                        ρ ; receptionists
                        _ ; externals (ignored)
                        )
                       (a_internal ...))
   (([a# b#] ...) () () ρ)
   (where ([a# b#] ...) ((abstract-actor (a b) (a_internal ...)) ...))])

(define-metafunction csa#
  abstract-actor : (a b) (a_internals ...) -> [a# b#]
  [(abstract-actor (a_this ((Q ...) e)) (a ...))
   (a_this ; used to be: (abstract-e a_this (a ...))
    (((abstract-Q Q (a ...)) ...)
     (abstract-e e (a ...))))])

(module+ test
  (test-equal? "abstract-actor"
    (term (abstract-actor [(addr 0 0) [((define-state (A) (m) (goto A))) (goto A)]] ()))
    (term [(addr 0 0) [((define-state (A) (m) (goto A))) (goto A)]])))

(define-metafunction csa#
  abstract-Q : Q (a_internals ...) -> Q#
  [(abstract-Q (define-state (q [x τ] ...) (x_m) e) (a ...))
   (define-state (q [x τ] ...) (x_m) (abstract-e e (a ...)))]
  [(abstract-Q (define-state (q [x τ] ...) (x_m) e [(timeout e_timeout) e_t-handler])
               (a ...))
   (define-state (q [x τ] ...) (x_m)
     (abstract-e e (a ...))
     [(timeout (abstract-e e_timeout (a ...)))
      (abstract-e e_t-handler (a ...))])])

(module+ test
  (check-equal? (term (abstract-Q (define-state (S) (m) (goto S) [(timeout 5) (goto S)]) ()))
                (term (define-state (S) (m) (goto S) [(timeout abs-nat) (goto S)])))
  (check-equal? (term (abstract-Q (define-state (S) (m) (goto S)
                                    [(timeout (case x [(A) 1] [(B) 2])) (goto S)]) ()))
                (term (define-state (S) (m) (goto S)
                        [(timeout (case x [(A) abs-nat] [(B) abs-nat])) (goto S)]))))

;; Abstracts the given expression to the given depth. The given address list is currently unused; may
;; be used for choosing collective addresses in the future.
(define-metafunction csa#
  abstract-e : e (a ...) -> e#
  [(abstract-e natural _) abs-nat]
  [(abstract-e string _) abs-string]
  [(abstract-e x _) x]
  [(abstract-e (marked a mk ...) _) (marked ,(csa#-abstract-address (term a)) mk ...)]
  [(abstract-e (goto q e ...) (a ...))
   (goto q (abstract-e e (a ...)) ...)]
  [(abstract-e (begin e ...) (a ...)) (begin (abstract-e e (a ...)) ...)]
  [(abstract-e (send e_1 e_2) (a ...))
   (send (abstract-e e_1 (a ...)) (abstract-e e_2 (a ...)))]
  [(abstract-e (spawn any_location τ e Q ...) (a ...))
   (spawn any_location
          τ
          (abstract-e e (a ...))
          (abstract-Q Q (a ...)) ...)]
  [(abstract-e (let ([x e_binding] ...) e_body) (a ...))
   (let ([x (abstract-e e_binding (a ...))] ...) (abstract-e e_body (a ...)))]
  [(abstract-e (case e_val [(t x ...) e_clause] ...) (a ...))
   (case (abstract-e e_val (a ...))
     [(t x ...) (abstract-e e_clause (a ...))] ...)]
  [(abstract-e (printf string e ...) (a ...))
   (printf string (abstract-e e (a ...)) ...)]
  [(abstract-e (primop e ...) (a ...))
   (primop (abstract-e e (a ...)) ...)]
  [(abstract-e (variant t e ...) (a ...))
   (variant t (abstract-e e (a ...)) ...)]
  [(abstract-e (record [l e] ...) (a ...))
   (record [l (abstract-e e (a ...))] ...)]
  [(abstract-e (: e l) (a ...)) (: (abstract-e e (a ...)) l)]
  [(abstract-e (folded τ e) (a ...))
   (folded τ (abstract-e e (a ...)))]
  [(abstract-e (fold τ e) (a ...))
   (fold τ (abstract-e e (a ...)))]
  [(abstract-e (unfold τ e) (a ...))
   (unfold τ (abstract-e e (a ...)))]
  [(abstract-e (list v ...) (a ...))
   ,(normalize-collection (term (list-val (abstract-e v (a ...)) ...)))]
  [(abstract-e (list e ...) (a ...))
   (list (abstract-e e (a ...)) ...)]
  [(abstract-e (hash [v_key v_val] ...) (a ...))
   ,(normalize-collection (term (hash-val ((abstract-e v_key (a ...)) ...)
                                          ((abstract-e v_val (a ...)) ...))))]
  [(abstract-e (hash [e_key e_val] ...) (a ...))
   (hash [(abstract-e e_key (a ...)) (abstract-e e_val (a ...))] ...)]
  [(abstract-e (for/fold ([x_1 e_1]) ([x_2 e_2]) e) (a ...))
   (for/fold ([x_1 (abstract-e e_1 (a ...))])
             ([x_2 (abstract-e e_2 (a ...))])
     (abstract-e e (a ...)))])

;; Abstracts the address a, where internal-addresses is the list of all addresses belonging to actors
;; in a's implementation configuration.
(define (csa#-abstract-address a)
  a)

(module+ test
  (test-equal? "abstract-e 1"
    (term (abstract-e (record [f1 1] [f2 2]) ()))
    (term (record [f1 abs-nat] [f2 abs-nat])))
  (test-not-false "abstract-e 2"
    (redex-match? csa#
                  (variant Foo (marked (addr 1 0)) (marked (addr (env Nat) 2) 3))
                  (term (abstract-e (variant Foo (marked (addr 1 0)) (marked (addr (env Nat) 2) 3)) ()))))
  (test-equal? "abstract-e 3" (term (abstract-e (list 1 2) ()))
               (term (list-val abs-nat)))
  (test-equal? "abstract-e 4"
    (term (abstract-e (list 1 (let () 1)) ()))
    (term (list abs-nat (let () abs-nat))))
  (test-equal? "abstract-e 5"
    (term (abstract-e (list (variant B) (variant A)) ()))
    (term (list-val (variant A) (variant B))))
  (test-equal? "abstract-e 6"
    (term (abstract-e (hash [1 (variant B)] [2 (variant A)]) ()))
    (term (hash-val (abs-nat) ((variant A) (variant B)))))
  (test-equal? "abstract-e 7"
    (term (abstract-e (hash [1 2] [3 4]) ()))
    (term (hash-val (abs-nat) (abs-nat))))
  (test-equal? "abstract-e 8"
    (term (abstract-e (hash) ()))
    (term (hash-val () ())))
  (test-equal? "abstract-e 9"
    (term (abstract-e (hash [1 (let ([x 1]) x)] [3 4]) ()))
    (term (hash [abs-nat (let ([x abs-nat]) x)] [abs-nat abs-nat])))
  (test-equal? "Abstraction okay on folded"
    (term (abstract-e (folded ,recursive-record-address-type (marked (addr 1 0))) ()))
    `(folded ,recursive-record-address-type (marked (addr 1 0)))))

;; ---------------------------------------------------------------------------------------------------
;; Selecting the spawn id to blur

(define (csa#-address-id a)
  (redex-let csa# ([(addr _ any_id) a])
    (term any_id)))

(define (csa#-address-with-opposite-id a)
  `(addr ,(address-location a) ,(if (= (csa#-address-id a) 0) 1 0)))

(define (csa#-actor-with-opposite-id-exists? config address)
  (csa#-config-actor-by-address config (csa#-address-with-opposite-id address)))

;; impl-config (Listof mk) -> (Listof spawn-id)
;;
;; Returns the list of all actor-address-ids such that at least one actor in the config whose address
;; has one of those ids (and such that an actor with the opposite id exists) "knows"
;; (i.e. syntactically contains in its behavior) an address with at least one of the markers in the
;; relevant-markers list
(define (csa#-ids-that-know-markers config relevant-markers)
  (define all-atomics-with-opposite-id-exists
    (filter
     (lambda (actor)
       (csa#-config-actor-by-address config (csa#-address-with-opposite-id (csa#-actor-address actor))))
     (csa#-config-actors config)))
  (define-values (old-spawns new-spawns)
    (partition
     (lambda (actor)
       (equal? (csa#-address-id (csa#-actor-address actor)) 0))
     all-atomics-with-opposite-id-exists))
  (append
   (if (contains-addr-with-markers? old-spawns relevant-markers) (list 0) null)
   (if (contains-addr-with-markers? new-spawns relevant-markers) (list 1) null)))

;; Returns true if the given list of actors contains in their behaviors an address marked with at
;; least one of the given markers
(define (contains-addr-with-markers? actors markers)
  (not
   (set-empty?
    (set-intersect (list->set markers) (list->set (markers-in actors))))))

;; ---------------------------------------------------------------------------------------------------
;; Blurring

;; impl-config nat (a#ext ...) -> impl-config
;;
;; Blurs all actors in the configuration with the given spawn flag, and removes any markers not in
;; monitored-markers. See the discussion of blurring in main.rkt for more details.
(define (csa#-blur-config config id-to-blur monitored-markers)
  ;; 1. Remove all blurred addresses and their messages
  (match-define (list remaining-config actors-to-assimilate)
    (remove-actors-by-id config id-to-blur))
  ;; 2. Do the renaming/marker removal throughout the remaining config for both internals and externals (in remaining config, removed
  ;; actors, and removed messages)
  (define addrs-to-assimilate (map csa#-actor-address actors-to-assimilate))
  (define renamed-config
    (make-config
     (rename-for-assimilation (csa#-config-actors remaining-config)
                              addrs-to-assimilate
                              monitored-markers)
     (rename-for-assimilation (csa#-config-blurred-actors remaining-config)
                              addrs-to-assimilate
                              monitored-markers)
     (rename-packets-for-assimilation (csa#-config-message-packets remaining-config)
                                      addrs-to-assimilate
                                      monitored-markers)
     (rename-for-assimilation (csa#-config-receptionists remaining-config)
                              addrs-to-assimilate
                              monitored-markers)))
  ;; 3. Deduplicate message packets, collective actor behaviors, and receptionists that might be
  ;; identical after the rename (the renaming might have caused terms with differing content to now be
  ;; the same)
  (define deduped-config
    (make-config (csa#-config-actors renamed-config)
                 (deduplicate-collectives (csa#-config-blurred-actors renamed-config))
                 (deduplicate-packets (csa#-config-message-packets renamed-config))
                 (deduplicate-receptionists (csa#-config-receptionists renamed-config))))
  ;; 4. Do the renaming/removal throughout the actors to assimilate, then add them back into the
  ;; config
  (define renamed-actors-to-assimilate
    (for/list ([actor actors-to-assimilate])
      (define renamed (rename-for-assimilation actor addrs-to-assimilate monitored-markers))
      `[,(rename-addr-for-assimilation (csa#-actor-address renamed) addrs-to-assimilate)
        ,(actor-behavior renamed)]))
  (make-config (csa#-config-actors deduped-config)
               (add-blurred-behaviors (csa#-config-blurred-actors deduped-config)
                                      renamed-actors-to-assimilate)
               (csa#-config-message-packets deduped-config)
               (csa#-config-receptionists deduped-config)))

(module+ test
  (test-equal? "check that messages with removed markers get merged together"
    (csa#-blur-config
     (term (()
            ()
            (((addr 2 0) (marked (collective-addr (env Nat)) 1) single)
             ((addr 2 0) (marked (collective-addr (env Nat)) 2) single)
             ((addr 2 0) (marked (collective-addr (env Nat)) 3) single))
            ()))
     1
     (list 3))
    (term (()
           ()
           (((addr 2 0) (marked (collective-addr (env Nat))) many)
            ((addr 2 0) (marked (collective-addr (env Nat)) 3) single))
           ())))

  (test-equal? "Will assimilate actors by id"
    (csa#-blur-config
     (term (([(addr 1 0) (() (goto A))]
             [(addr 1 1) (() (goto A))])
            ()
            ()
            ()))
     0
     null)
    (term (([(addr 1 1) (() (goto A))])
           ([(collective-addr 1) ((() (goto A)))])
           ()
           ())))

  (test-equal? "Merge collective behaviors when they become the same"
    (csa#-blur-config
     (term (()
            ([(collective-addr 1)
              ((() (goto A (marked (collective-addr (env Nat)) 1)))
               (() (goto A (marked (collective-addr (env Nat))))))])
            ()
            ()))
     0
     null)
    (term (()
           ([(collective-addr 1) ((() (goto A (marked (collective-addr (env Nat))))))])
           ()
           ())))

  (test-equal? "Markers are assimilated on receptionists"
    (csa#-blur-config
     (term (() () () ([Nat (marked (addr 1 1) 2 3 4)])))
     0
     (list 2))
    (term (() () () ([Nat (marked (addr 1 1) 2)]))))

  (test-equal? "Markers are assimilated on assimilated receptionists"
    (csa#-blur-config
     (term (([(addr 1 1) [() (goto A)]]
             [(addr 1 0) [() (goto A)]])
            ()
            ()
            ([Nat (marked (addr 1 1) 2 3 4)])))
     1
     (list 2))
    (term (([(addr 1 0) [() (goto A)]])
           ([(collective-addr 1) ([() (goto A)])])
           ()
           ([Nat (marked (collective-addr 1) 2)]))))

  (test-equal? "Markers in atomic actor behaviors are assimilated"
    (csa#-blur-config
     (term (([(addr 1 1) [((define-state (A) (m) (goto A (marked (addr 2 1) 2 3))))
                          (goto A (marked (addr 2 1) 2 3))]])
            ()
            ()
            ()))
     0
     (list 3))
    (term (([(addr 1 1) [((define-state (A) (m) (goto A (marked (addr 2 1) 3))))
                          (goto A (marked (addr 2 1) 3))]])
            ()
            ()
            ())))

  (test-equal? "Markers in collective actor behaviors are assimilated"
    (csa#-blur-config
     (term (()
            ([(collective-addr 1) ([((define-state (A) (m) (goto A (marked (addr 2 1) 2 3))))
                                    (goto A (marked (addr 2 1) 2 3))])])
            ()
            ()))
     0
     (list 3))
    (term (()
           ([(collective-addr 1) ([((define-state (A) (m) (goto A (marked (addr 2 1) 3))))
                                   (goto A (marked (addr 2 1) 3))])])
           ()
           ()))))

;; impl-config nat -> impl-config ((a# b#) ...)
;;
;; Removes from the configuration all actors that have the given id in their address, along with any
;; in-transit message packets sent to them. Returns the resulting config, and the list of removed
;; actors.
(define (remove-actors-by-id config id)
  (define (should-be-removed? actor)
    ;; should be removed if it's a spawn address with the given id AND the same address with the
    ;; opposite id exists
    (define addr (csa#-actor-address actor))
    (and (has-addr-id? addr id)
         (csa#-config-actor-by-address config (csa#-address-with-opposite-id addr))))
  (define-values (removed-actors remaining-actors)
    (partition should-be-removed? (csa#-config-actors config)))
  (list (make-config remaining-actors
                     (csa#-config-blurred-actors config)
                     (csa#-config-message-packets config)
                     (csa#-config-receptionists config))
        removed-actors))

(define (switch-spawn-flag address)
  (match address
    [`(addr ,any-loc 1) `(addr ,any-loc 0)]
    [`(addr ,any-loc 0) `(addr ,any-loc 1)]))

(module+ test
  (test-equal? "remove-actors test"
    (remove-actors-by-id
     (term
      ((((addr 1 0) ,test-behavior1)
        ((addr 1 1) ,test-behavior1)
        ((addr 2 0) ,test-behavior1)
        ((addr 3 1) ,test-behavior1))
       ()
       ()
       ()))
     1)
    (list
     (term
      ((((addr 1 0) ,test-behavior1)
        ((addr 2 0) ,test-behavior1)
        ((addr 3 1) ,test-behavior1))
       ()
       ()
       ()))
     (list (term ((addr 1 1) ,test-behavior1))))))

(define (rename-packets-for-assimilation packets addrs-to-assimilate monitored-markers)
  (for/list ([packet packets])
    (make-packet (rename-addr-for-assimilation (csa#-message-packet-address packet)
                                               addrs-to-assimilate)
                 (rename-for-assimilation (csa#-message-packet-value packet)
                                          addrs-to-assimilate
                                          monitored-markers)
                 (csa#-message-packet-multiplicity packet))))

(module+ test
  (test-equal? "rename-packets-for-assimilation"
    (rename-packets-for-assimilation `([(addr 1 1) (marked (addr 2 1) 3) single])
                                     (list `(addr 1 1))
                                     null)
    `([(collective-addr 1) (marked (addr 2 1)) single])))

;; term (a#int ...) (mk ...) -> term
;;
;; Transforms internal addresses in addrs-to-assimilate to collective addresses and removes markers
;; *not* in monitored-markers. Also performs the deduplication for hash and list values
;;
;; NOTE: any updates to this function may also need to be added to pseudo-blur
(define (rename-for-assimilation some-term addrs-to-assimilate monitored-markers)
  (match some-term
    [`(marked ,addr ,markers ...)
     (define new-markers (filter (lambda (m) (member m monitored-markers)) markers))
     `(marked ,(rename-addr-for-assimilation addr addrs-to-assimilate) ,@new-markers)]
    [(list (and keyword (or 'list-val 'hash-val)) terms ...)
     (define blurred-args
       (map (curryr rename-for-assimilation addrs-to-assimilate monitored-markers) terms))
     (normalize-collection `(,keyword ,@blurred-args))]
    [`(hash-val ,keys ,vals)
     (define blurred-keys
       (map (curryr rename-for-assimilation addrs-to-assimilate monitored-markers) keys))
     (define blurred-vals
       (map (curryr rename-for-assimilation addrs-to-assimilate monitored-markers) vals))
     (normalize-collection `(hash-val ,blurred-keys ,blurred-vals))]
    [(list terms ...)
     (map (curryr rename-for-assimilation addrs-to-assimilate monitored-markers) terms)]
    [_ some-term]))

(module+ test
  (test-equal? "blur test"
    (rename-for-assimilation
     (term (((marked (addr foo 0)) (marked (addr foo 1)))
            (marked (addr bar 1))
            (marked (collective-addr (env Nat)) 1)
            (marked (collective-addr (env Nat)) 2)
            (marked (addr bar 0))
            (marked (addr baz 0))
            (marked (addr quux 1))))
     (list (term (addr foo 1)) (term (addr bar 1)))
     (list 2))
    (term (((marked (addr foo 0)) (marked (collective-addr foo)))
           (marked (collective-addr bar))
           (marked (collective-addr (env Nat)))
           (marked (collective-addr (env Nat)) 2)
           (marked (addr bar 0))
           (marked (addr baz 0))
           (marked (addr quux 1)))))

  (test-equal? "blur test 2"
    (rename-for-assimilation
     (redex-let* csa#
                 ([(a# b#)
                   (term
                       ((addr 0 0)
                        (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                            (begin
                              (send (marked (collective-addr (env Nat)) 1) abs-nat)
                              (send (marked (collective-addr (env Nat)) 2) abs-nat)
                              (goto A x y z))))
                         (goto A
                               (marked (collective-addr (env Nat)) 2)
                               (marked (collective-addr (env Nat)) 3)
                               (marked (collective-addr (env Nat)) 4)))))]
                  [i# (make-config (term ([a# b#])) null null null)])
                 (term i#))
     null
     (list 1 3))
    (redex-let* csa#
                ([(a# b#)
                  (term
                         ((addr 0 0)
                          (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                              (begin
                                (send (marked (collective-addr (env Nat)) 1) abs-nat)
                                (send (marked (collective-addr (env Nat))) abs-nat)
                                (goto A x y z))))
                           (goto A
                                 (marked (collective-addr (env Nat)))
                                 (marked (collective-addr (env Nat)) 3)
                                 (marked (collective-addr (env Nat)))))))]
                 [i# (make-config (term ([a# b#])) null null null)])
                (term i#)))

  ;; Make sure duplicates are removed from lists and hashes
  (test-equal? "blur test 3"
   (rename-for-assimilation
    (redex-let csa#
        ([e# (term (hash-val (abs-nat)
                             ((marked (collective-addr (env Nat)) 1)
                              (marked (collective-addr (env Nat)) 2)
                              (marked (collective-addr (env Nat)) 3)
                              (marked (collective-addr (env Nat)) 4))))])
      (term e#))
    null
    '(1 3))
   ;; Some reordering happens as a result of normalize-collection
   (term (hash-val (abs-nat)
                   ((marked (collective-addr (env Nat)))
                    (marked (collective-addr (env Nat)) 1)
                    (marked (collective-addr (env Nat)) 3)))))

  (test-equal? "blur test 4"
   (rename-for-assimilation
    (redex-let csa#
        ([e# (term (list-val (marked (collective-addr (env Nat)) 1)
                             (marked (collective-addr (env Nat)) 2)
                             (marked (collective-addr (env Nat)) 3)
                             (marked (collective-addr (env Nat)) 4)))])
      (term e#))
    null
    null)
   (term (list-val (marked (collective-addr (env Nat))))))

  (test-equal? "blur test 5"
   (rename-for-assimilation
    (redex-let csa#
        ([e# (term (list-val (marked (collective-addr (env Nat)) 1)
                             (marked (collective-addr (env Nat)) 2)
                             (marked (collective-addr (env Nat)) 3)
                             (marked (collective-addr (env Nat)) 4)))])
      (term e#))
    null
    `(1 2 3 4))
   (term (list-val (marked (collective-addr (env Nat)) 1)
                   (marked (collective-addr (env Nat)) 2)
                   (marked (collective-addr (env Nat)) 3)
                   (marked (collective-addr (env Nat)) 4)))))

(define (rename-addr-for-assimilation addr addrs-to-assimilate)
  (if (member addr addrs-to-assimilate)
      (match-let ([`(addr ,loc ,_) addr]) `(collective-addr ,loc))
      addr))

(module+ test
  (test-equal? "Rename addr for assimilation"
    (rename-addr-for-assimilation `(addr 1 1) (list `(addr 1 1)))
    `(collective-addr 1))
  (test-equal? "Don't rename addrs not supposed to be assimilated"
    (rename-addr-for-assimilation `(addr 1 0) (list `(addr 1 1)))
    `(addr 1 0)))

;; Returns #t if the address is of the form (addr _ id), #f otherwise.
(define (has-addr-id? addr id)
  (match addr
    [`(addr ,_ ,addr-id)
     (equal? addr-id id)]
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
    (term (((define-state (B) (r) (begin (send r abs-nat) (goto B)))) (goto B))))
  (define behavior3
    (term (((define-state (C [x (List Nat)]) (r) (begin (send r abs-nat) (goto C x))))
           (goto C (list-val)))))
  (define behavior3-greater
    (term (((define-state (C [x (List Nat)]) (r) (begin (send r abs-nat) (goto C x))))
           (goto C (list-val abs-nat)))))

  (test-begin
    (check-true (redex-match? csa# b# behavior1))
    (check-true (redex-match? csa# b# behavior2))
    (check-true (redex-match? csa# b# behavior3)))

  (test-equal? "config-add-blurred-behaviors same behavior"
    (config-add-blurred-behaviors (term (() (((collective-addr 1) (,behavior1))) ()))
                                  (list (term ((collective-addr 1) ,behavior1))))
    (term (() (((collective-addr 1) (,behavior1))) ())))

  (test-equal? "add-blurred-behaviors"
    (add-blurred-behaviors (term (((collective-addr 1) (,behavior1 ,behavior2))
                                  ((collective-addr 2) (,behavior3))))
                           (list (term ((collective-addr 1) ,behavior3))
                                 (term ((collective-addr 3) ,behavior3))
                                 (term ((collective-addr 1) ,behavior1))))
    (term (((collective-addr 1) (,behavior1 ,behavior2 ,behavior3))
           ((collective-addr 2) (,behavior3))
           ((collective-addr 3) (,behavior3)))))

  (test-equal? "add-blurred-behaviors greater behavior"
    (add-blurred-behaviors (term (((collective-addr 1) (,behavior1 ,behavior2 ,behavior3))))
                           (list (term ((collective-addr 1) ,behavior3-greater))))
    (term (((collective-addr 1) (,behavior1 ,behavior2 ,behavior3-greater)))))

  (test-equal? "add-blurred-behaviors lesser behavior"
    (add-blurred-behaviors
     (term (((collective-addr 1) (,behavior1 ,behavior2 ,behavior3-greater))))
     (list (term ((collective-addr 1) ,behavior3))))
    (term (((collective-addr 1) (,behavior1 ,behavior2 ,behavior3-greater)))))

  (test-equal? "add-blurred-behaviors same behavior"
    (add-blurred-behaviors (term (((collective-addr 1) (,behavior1))))
                           (list (term ((collective-addr 1) ,behavior1))))
    (term (((collective-addr 1) (,behavior1))))))

(define (config-deduplicate-collectives config)
  (match-define `[,atomics ,collectives ,packets] config)
  `[,atomics ,(deduplicate-collectives collectives) ,packets])

(define (deduplicate-collectives collectives)
  ;; deduplication just takes the behaviors out and adds them back in, one by one, which does the
  ;; merging as part of the addition process
  (add-blurred-behaviors
   null
   (append*
    (for/list ([collective collectives])
      (map (curry list (csa#-blurred-actor-address collective))
           (csa#-blurred-actor-behaviors collective))))))

;; Leaving this as a separate function just in case I want to define it differently later
(define (deduplicate-receptionists recs)
  (remove-duplicates recs))

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization (the sorting of config components)

;; Converts all address identifiers to 0, and returns the appropriate address substitution map
(define (csa#-age-addresses config)
  ;; TODO: return addr subst, too
  (list (do-aging config)
        (map
         (lambda (actor)
           (define addr (csa#-actor-address actor))
           `[,addr ,(do-aging addr)])
         (csa#-config-actors config))))

(module+ test
  (test-equal? "Age addresses test"
    (redex-let csa# ([i# `[([(addr 1 1) (() (goto A (marked (addr 1 1))))]
                            [(addr 2 0) (() (goto B (marked (addr 1 1))))]
                            [(addr 3 2) (() (goto C
                                                  (marked (addr (env Nat) 0))
                                                  (marked (addr (env String) 0))
                                                  (list)))])
                           ()
                           ()
                           ()]])
      (csa#-age-addresses (term i#)))
    (list `[([(addr 1 0) (() (goto A (marked (addr 1 0))))]
                            [(addr 2 0) (() (goto B (marked (addr 1 0))))]
                            [(addr 3 0) (() (goto C
                                                  (marked (addr (env Nat) 0))
                                                  (marked (addr (env String) 0))
                                                  (list)))])
                           ()
                           ()
                           ()]
          `([(addr 1 1) (addr 1 0)]
            [(addr 2 0) (addr 2 0)]
            [(addr 3 2) (addr 3 0)]))))

;; Given a term, changes all spawn addresses of the form (addr _ 1 _) to (addr _ 0 _),
;; to ensure that spawned addresses in the next handler are fresh.
(define (do-aging some-term)
  (match some-term
    [`(addr ,loc ,id) (term (addr ,loc 0))]
    [(list terms ...) (map do-aging terms)]
    [_ some-term]))

(define (csa#-rename-markers some-term subst)
  (match some-term
    [`(marked ,addr ,marker)
     `(marked ,addr ,(second (assoc marker subst)))]
    [(list terms ...) (map (curryr csa#-rename-markers subst) terms)]
    [_ some-term]))

(module+ test
  (test-equal? "csa#-rename-markers"
    (csa#-rename-markers `(list (marked (addr 1 0) 2)
                                (marked (addr 3 0)))
                         `([0 1]
                           [1 2]
                           [2 3]))
     `(list (marked (addr 1 0) 3)
            (marked (addr 3 0)))))

;; Sorts the components of an impl configuration as follows:
;; * atomic actors by address
;; * collective actors by address
;; * behaviors of a collective actor by the entire behavior
;; * message packets by the entire packet
;; * receptionists by the entire receptionist
(define (csa#-sort-config-components config)
  (match-define `(,atomic-actors ,collective-actors ,packets ,receptionists) config)
  (define (actor<? a b)
    (sexp<? (csa#-actor-address a) (csa#-actor-address b)))
  (define sorted-atomic-actors (sort atomic-actors actor<?))
  (define sorted-collective-actors
    (sort (map sort-collective-actor-behaviors collective-actors) actor<?))
  (define sorted-packets (sort packets sexp<?))
  (define sorted-receptionists (sort receptionists sexp<?))
  (make-config sorted-atomic-actors sorted-collective-actors sorted-packets sorted-receptionists))

(define (sort-collective-actor-behaviors actor)
  (match-define `(,addr ,behaviors) actor)
  `(,addr ,(sort behaviors sexp<?)))

(module+ test
  (define sort-components-test-config
    (make-config
     ;; atomic actors
     `([(addr 2 0) (() (goto A))]
       [(addr 1 0) (() (goto Z))])
     ;; collective actors
     `([(collective-addr Q) ((() (goto Z))
                             (() (goto M))
                             (() (goto A)))]
       [(collective-addr B) ((() (goto Z))
                             (() (goto M))
                             (() (goto A)))])
     ;; messages
     `([(addr 2 0) abs-nat single]
       [(addr 1 0) abs-nat single])
     ;; receptionists
     `([Nat (marked (addr 2 0) 2)]
       [Nat (marked (addr 2 0) 1)]
       [Nat (marked (addr 1 0) 3)])))
  (test-case "sort-config-components"
    (check-true  (redex-match? csa# i# sort-components-test-config))
    (check-equal?
     (csa#-sort-config-components sort-components-test-config)
     (make-config
      ;; atomic actors
      `([(addr 1 0) (() (goto Z))]
        [(addr 2 0) (() (goto A))])
      ;; collective actors
      `([(collective-addr B) ((() (goto A))
                              (() (goto M))
                              (() (goto Z)))]
        [(collective-addr Q) ((() (goto A))
                              (() (goto M))
                              (() (goto Z)))])
      ;; messages
      `([(addr 1 0) abs-nat single]
        [(addr 2 0) abs-nat single])
      ;; receptionists
      `([Nat (marked (addr 1 0) 3)]
        [Nat (marked (addr 2 0) 1)]
        [Nat (marked (addr 2 0) 2)])))))

;; ---------------------------------------------------------------------------------------------------
;; Duplicate message merging

;; Merges all message packet entries in the given μ# that have the same address and content into a
;; single entry with the many-of multiplicity. These kinds of duplicate messages may arise, for
;; example, during blurring.
;;
;; OPTIMIZE: Do some kind of ordering on the messages to avoid symmetry issues
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
    (deduplicate-packets (list `[(addr 1 0) abs-nat single]
                               `[(addr 2 0) abs-nat single]
                               `[(addr 1 0) abs-nat single]
                               `[(addr 2 0) abs-string many]))
    (list `[(addr 1 0) abs-nat many]
          `[(addr 2 0) abs-nat single]
          `[(addr 2 0) abs-string many])))

(define (config-deduplicate-packets config)
  (match-define `[,atomics ,collectives ,packets] config)
  `[,atomics ,collectives ,(deduplicate-packets packets)])

;; For two "messages" (the things inside the message queue in a config), returns true if they have the
;; same address and value
(define (same-message? m1 m2)
  (redex-let csa# ([(a#_1 v#_1 _) m1]
                   [(a#_2 v#_2 _) m2])
    (equal? (term (a#_1 v#_1)) (term (a#_2 v#_2)))))

(module+ test
  (test-equal? "deduplicate-packets 1"
   (deduplicate-packets
    (term (((addr 5 1) abs-nat single)
           ((addr 5 1) abs-nat single))))
   (term (((addr 5 1) abs-nat many))))

  (test-equal? "deduplicate-packets 2"
   (deduplicate-packets
    (term (((addr 5 1) abs-nat single)
           ((addr 5 1) abs-nat single)
           ((addr 5 1) abs-nat single))))
   (term (((addr 5 1) abs-nat many))))

  (test-equal? "deduplicate-packets 3"
   (deduplicate-packets
    (term (((addr 5 1) abs-nat single)
           ((addr 5 2) abs-nat single)
           ((addr 5 3) abs-nat many)
           ((collective-addr 5) abs-nat many)
           ((addr 5 1) abs-nat single)
           ((collective-addr 5) abs-nat single))))
   (term (((addr 5 1) abs-nat many)
          ((addr 5 2) abs-nat single)
          ((addr 5 3) abs-nat many)
          ((collective-addr 5) abs-nat many)))))

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (make-config atomics collectives messages receptionists)
  (list atomics collectives messages receptionists))

(module+ test
  (test-true "make-config creates valid abstract program config"
    (redex-match? csa#
                  i#
                  (redex-let csa#
                      ([α# (list `[(addr 1 1) [() (goto A)]])]
                       [β# (list `[(collective-addr 1) ([() (goto A)])])]
                       [μ# (list `[(addr 1 1) abs-nat single])]
                       [ρ# (list `[Nat (marked (addr 1 1) 2)])])
                    (make-config (term α#) (term β#) (term μ#) (term ρ#))))))

(define (make-single-actor-abstract-config actor recs)
  (term (make-single-actor-abstract-config/mf ,actor ,recs)))

(define-metafunction csa#
  make-single-actor-abstract-config/mf : (a# b#) ρ# -> i#
  [(make-single-actor-abstract-config/mf (a# b#) ρ#)
   (([a# b#]) () () ρ#)])

(module+ test
  (test-true "make-single-actor-abstract-config returns valid config"
    (redex-match? csa#
                  i#
                  (make-single-actor-abstract-config `[(addr 0 0) [() (goto A)]] `()))))

(define (make-packet addr message quant)
  (list addr message quant))

(module+ test
  (test-true "make-packet creates valid packets"
    (redex-match? csa# μ# (list (make-packet `(addr 1 1) `abs-nat `single)))))

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

;; Returns the configuration's receptionists
(define (csa#-config-receptionists config)
  (fourth config))

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

(define (csa#-config-actor-by-address/fail config addr)
  (match (csa#-config-actor-by-address config addr)
    [#f (error 'csa#-config-actor-by-address/fail "Configuration ~s does not have an atomic actor with address ~s" config addr)]
    [actor actor]))

;; Returns the collective actor with the given address, or #f if it doesn't exist
(define (csa#-config-collective-actor-by-address config addr)
  (findf (lambda (a) (equal? (csa#-blurred-actor-address a) addr))
         (csa#-config-blurred-actors config)))

(define (csa#-config-collective-actor-by-address/fail config addr)
  (match (csa#-config-collective-actor-by-address config addr)
    [#f (error 'csa#-config-collective-actor-by-address/fail "Configuration ~s does not have a collective actor with address ~s" config addr)]
    [actor actor]))

(define (csa#-config-receptionist-addr-by-marker config marker)
  (unmark-addr
   (findf
    (lambda (a)
      (match a
        [`(marked ,_ ,mk) (equal? mk marker)]
        [_ #f]))
    (map receptionist-marked-address (csa#-config-receptionists config)))))

(module+ test
  (test-equal? "csa#-config-receptionist-addr-by-marker"
    (csa#-config-receptionist-addr-by-marker
     `[() () () ([Nat (marked (addr 0 0) 0)]
                 [String (marked (addr 0 1) 1)]
                 [String (marked (addr 0 1) 2)])]
     2)
    `(addr 0 1)))

(define (csa#-actor-address a)
  (first a))

(define (csa#-blurred-actor-address a)
  (first a))

(define (csa#-blurred-actor-behaviors a)
  (second a))

(define (csa#-message-packet-address packet)
  (first packet))

(define (csa#-message-packet-value packet)
  (second packet))

(define (csa#-message-packet-multiplicity packet)
  (third packet))

(define csa#-output-address car)

(define (csa#-output-markers o)
  (match-define `(marked ,_ ,markers ...) (csa#-output-address o))
  markers)

(module+ test
  (test-equal? "csa#-output-markers"
    (csa#-output-markers `[(marked (addr (env Nat) 0) 1) Nat abs-nat single])
    (list 1))

  (test-equal? "csa#-output-markers 2"
    (csa#-output-markers `[(marked (addr (env Nat) 0)) Nat abs-nat single])
    null)

  (test-equal? "csa#-output-markers 3"
    (csa#-output-markers `[(marked (addr (env Nat) 0) 1 2 3) Nat abs-nat single])
    (list 1 2 3)))

(define (csa#-output-type o)
  (match (address-location (unmark-addr (csa#-output-address o)))
    [`(env ,type) type]))

(define csa#-output-message cadr)

(define csa#-output-multiplicity caddr)

;; (a# b#) -> b#
(define (actor-behavior actor)
  (second actor))

;; Returns the behaviors of the actor for the indicated collective OR atomic address (or #f if the
;; actor does not exist)
(define (csa#-behaviors-of config addr)
  (if (csa#-atomic-address? addr)
      (match (csa#-config-actor-by-address config addr)
        [#f #f]
        [actor (list (actor-behavior actor))])
      (match (csa#-config-collective-actor-by-address config addr)
        [#f #f]
        [actor (csa#-blurred-actor-behaviors actor)])))

(module+ test
  (define behavior-test-config
    (term (([(addr 1 0) (() (goto A))])
           ([(collective-addr 2)
             ((() (goto B))
              (() (goto C)))])
           ())))
  (test-equal? "csa#-behaviors-of atomic"
    (csa#-behaviors-of behavior-test-config `(addr 1 0))
    (list '(() (goto A))))
  (test-equal? "csa#-behaviors-of collective"
    (csa#-behaviors-of behavior-test-config `(collective-addr 2))
    (list '(() (goto B)) '(() (goto C)))))

;; Returns all behaviors assigned to the blurred actor with the given address in the given config
(define (blurred-actor-behaviors-by-address config address)
  (csa#-blurred-actor-behaviors (csa#-config-collective-actor-by-address/fail config address)))

(module+ test
  (test-case "Blurred actor behaviors by address"
    (redex-let csa# ([i# (term (()
                                (((collective-addr 1) ())
                                 ((collective-addr 2) ((() (goto A)))))
                                ()
                                ()))])
      (check-equal? (blurred-actor-behaviors-by-address (term i#) `(collective-addr 2))
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

(define (address-location addr)
  (match addr
    [`(addr ,loc ,_) loc]
    [`(collective-addr ,loc) loc]))

(define (receptionist-marked-address r)
  (second r))

(define (marked-address-markers ma)
  (match ma
    [`(marked ,_ ,mks ...) mks]))

;; ---------------------------------------------------------------------------------------------------
;; Boolean Logic

(define-metafunction csa#
  csa#-and : v# v# -> v#
  [(csa#-and (variant True) (variant True)) (variant True)]
  [(csa#-and _ _) (variant False)])

(define-metafunction csa#
  csa#-or : v# v# -> v#
  [(csa#-or (variant False) (variant False)) (variant False)]
  [(csa#-or _ _) (variant True)])

(define-metafunction csa#
  csa#-not : v# -> v#
  [(csa#-not (variant True)) (variant False)]
  [(csa#-not (variant False)) (variant True)])

(module+ test
  (check-equal? (term (csa#-and (variant True) (variant True))) (term (variant True)))
  (check-equal? (term (csa#-and (variant False) (variant False))) (term (variant False)))

  (check-equal? (term (csa#-or (variant True) (variant True))) (term (variant True)))
  (check-equal? (term (csa#-or (variant False) (variant False))) (term (variant False)))

  (check-equal? (term (csa#-not (variant False))) (term (variant True)))
  (check-equal? (term (csa#-not (variant True))) (term (variant False))))

(define (trigger-address trigger)
  (term (trigger-address/mf ,trigger)))

(define-metafunction csa#
  trigger-address/mf : trigger# -> a#
  [(trigger-address/mf (timeout a#)) a#]
  [(trigger-address/mf (internal-receive a# _ _)) a#]
  [(trigger-address/mf (external-receive (marked a# _ ...) _)) a#])

(module+ test
  (test-equal? "Trigger address of timeout" (trigger-address `(timeout (addr 1 1))) `(addr 1 1))
  (test-equal? "Trigger address of internal-receive"
    (trigger-address `(internal-receive (addr 1 1) abs-nat single))
    `(addr 1 1))
  (test-equal? "Trigger address of external-receive"
    (trigger-address `(external-receive (marked (addr 1 1) 0) abs-nat))
    `(addr 1 1)))

;; ---------------------------------------------------------------------------------------------------
;; Predicates

;; Returns true if the output is to an internal address, false otherwise
(define (internal-output? output)
  (match-let ([`((marked ,addr ,_ ...) ,_ ,_) output])
    (csa#-internal-address? addr)))

(module+ test
  (test-true "internal-output? 1" (internal-output? (term ((marked (addr 1 0)) abs-nat single))))
  (test-false "internal-output? 2"
    (internal-output? (term ((marked (collective-addr (env Nat)) 2) abs-nat single)))))

(define (csa#-atomic-address? addr)
  (match addr
    [`(addr ,loc ,_) #t]
    [_ #f]))

(define (csa#-internal-address? addr)
  (match (address-location addr)
    [`(env ,_) #f]
    [_ #t]))

(module+ test
  (test-true "csa#-internal-address? true" (csa#-internal-address? `(addr foo 1)))
  (test-false "csa#-internal-address? false" (csa#-internal-address? `(addr (env Nat) 2))))

(define (internal-atomic-action? trigger)
  (match trigger
    [`(external-receive ,_ ,_) #f]
    [`(internal-receive ,_ ,_ many) #f]
    [_ (csa#-atomic-address? (trigger-address trigger))]))

(module+ test
  (test-true "internal-atomic-action? 1"
    (internal-atomic-action? (term (timeout (addr 1 0)))))
  (test-false "internal-atomic-action? collective actor timeout"
    (internal-atomic-action? (term (timeout (collective-addr 1)))))
  (test-true "internal-atomic-action? atomic actor, single message"
    (internal-atomic-action? (term (internal-receive (addr 1 0) abs-nat single))))
  (test-false "internal-atomic-action? atomic actor, many-of message"
    (internal-atomic-action? (term (internal-receive (addr 1 0) abs-nat many))))
  (test-false "internal-atomic-action? collective actor, single message"
    (internal-atomic-action? (term (internal-receive (collective-addr 1) abs-nat single))))
  (test-false "internal-atomic-action? collecive actor, many-of message"
    (internal-atomic-action? (term (internal-receive (collective-addr 1) abs-nat many))))
  (test-false "internal-atomic-action? external receive"
    (internal-atomic-action? (term (external-receive (marked (addr 1 0) 0) abs-nat)))))

(define (internal-single-receive? trigger)
  (match trigger
    [`(internal-receive ,_ ,_ single) #t]
    [_ #f]))

(module+ test
  (test-true "internal-single-receive? atomic/single"
    (internal-single-receive? `(internal-receive (addr 1 0) abs-nat single)))
  (test-false "internal-single-receive? atomic/many"
    (internal-single-receive? `(internal-receive (addr 1 0) abs-nat many)))
  (test-true "internal-single-receive? collective/single"
    (internal-single-receive? `(internal-receive (collective-addr 1 NEW) abs-nat single)))
  (test-false "internal-single-receive? collective/many"
    (internal-single-receive? `(internal-receive (collective-addr 1 NEW) abs-nat many)))
  (test-false "internal-single-receive? external-receive"
    (internal-single-receive? `(external-receive (marked (addr 1 0) 0) abs-nat)))
  (test-false "internal-single-receive? timeout)"
    (internal-single-receive? `(timeout (addr 1 0)))))

;; Returns true iff the given value contains any of the given markers
(define (csa#-contains-marker? val target-markers)
  (match val
    [`(marked ,_ ,found-markers ...)
     (ormap (curryr member found-markers) target-markers)]
    [`(variant ,_ ,vals ...)
     (ormap (curryr csa#-contains-marker? target-markers) vals)]
    [`(record [,_ ,vals] ...)
     (ormap (curryr csa#-contains-marker? target-markers) vals)]
    [`(folded ,_ ,val)
     (csa#-contains-marker? val target-markers)]
    [`(list-val ,vals ...)
     (ormap (curryr csa#-contains-marker? target-markers) vals)]
    [`(hash-val ,keys ,vals)
     (or (ormap (curryr csa#-contains-marker? target-markers) keys)
         (ormap (curryr csa#-contains-marker? target-markers) vals))]
    [_ #f]))

(module+ test
  (test-false "basic value does not contain given markers"
    (csa#-contains-marker? `(record [a abs-nat]) (list 1)))
  (test-false "record with internal address does not contain given markers"
    (csa#-contains-marker? `(record [b (marked (addr 0 0) 1)]) (list 2)))
  (test-not-false "record with external address contains any of given markers"
    (csa#-contains-marker? `(record [b (marked (addr (env Nat) 0) 1)]) (list 1))))

;; ---------------------------------------------------------------------------------------------------
;; Types

;; ;; NOTE: non-equality-based join for lists and hashes is not implemented
;; (define-metafunction csa#
;;   type-join : τ τ -> τ
;;   [(type-join (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))
;;    (Union [t_3 τ_3 ...] ...)
;;    (where ([t_3 τ_3 ...] ...)
;;           ,(let ()
;;              (define branches1 (term ([t_1 τ_1 ...] ...)))
;;              (define branches2 (term ([t_2 τ_2 ...] ...)))
;;              (define type1-branches
;;               (for/list ([branch1 branches1])
;;                 (define tag (first branch1))
;;                 (match (findf (lambda (branch2) (equal? (first branch2) tag)) branches2)
;;                   [#f branch1]
;;                   [branch2
;;                    (define (join-components type1 type2)
;;                      (term (type-join ,type1 ,type2)))
;;                    ;; NOTE: assumes that the branches have the same number of components
;;                    `[,tag ,@(map join-components (rest branch1) (rest branch2))]])))
;;              (define remaining-branch2-branches
;;                (filter (lambda (b2)
;;                          (not (findf (lambda (b1) (equal? (first b1) (first b2))) branches1)))
;;                        branches2))
;;              (define all-new-branches (append type1-branches remaining-branch2-branches))
;;              ;; NOTE: We sort here to get the types into a canonical form and avoid repeated states,
;;              ;; but only when the number of branches is different from the original number in each
;;              ;; list (as a conservative heuristic to detect when the types might be the
;;              ;; possibly-out-order types from the original program)
;;              (if (and (= (length all-new-branches) (length branches1))
;;                       (= (length all-new-branches) (length branches2)))
;;                  all-new-branches
;;                  (sort all-new-branches sexp<?))))]
;;   [(type-join (Record [l_1 τ_1] ...) (Record [l_2 τ_2] ...))
;;    (Record [l_1 (type-join τ_1 τ_2)] ...)]
;;   ;; If names for minfixpt are the same, don't rename them
;;   [(type-join (minfixpt X τ_1) (minfixpt X τ_2))
;;    (minfixpt X (type-join τ_1 τ_2))]
;;   [(type-join (minfixpt X_1 τ_1) (minfixpt X_2 τ_2))
;;    (minfixpt X_fresh (type-join τ_1subst τ_2subst))
;;    (where X_fresh
;;           ,(variable-not-in (term ((minfixpt X_1 τ_1) (minfixpt X_2 τ_2))) (term X_1)))
;;    (where τ_1subst (type-subst τ_1 X_1 X_fresh))
;;    (where τ_2subst (type-subst τ_2 X_2 X_fresh))]
;;   [(type-join X X) X]
;;   [(type-join (Addr τ_1) (Addr τ_2))
;;    ;; addresses are contravariant, so have to do the meet instead
;;    (Addr (type-meet τ_1 τ_2))]
;;   [(type-join τ τ) τ])

;; (module+ test
;;   (test-equal? "type-join 1" (term (type-join Nat Nat)) 'Nat)
;;   (test-equal? "type-join 2"
;;                (term (type-join (Union [A]) (Union [B])))
;;                '(Union [A] [B]))
;;   (test-equal? "type-join 2, other direction"
;;                (term (type-join (Union [B]) (Union [A])))
;;                '(Union [A] [B]))
;;   (test-equal? "type-join 3"
;;                (term (type-join (Union [A] [B]) (Union [B])))
;;                '(Union [A] [B]))

;;   (test-equal? "type-join for records"
;;     (term (type-join (Record [a (Union [A])]) (Record [a (Union [B])])))
;;     (term (Record [a (Union [A] [B])])))

;;   (test-equal? "type-join on addresses"
;;     (term (type-join (Addr (Union [A])) (Addr (Union [B]))))
;;     (term (Addr (Union))))

;;   (test-equal? "type-join on minfixpts with the same names"
;;     (term (type-join (minfixpt A (Addr (Union [M A])))
;;                      (minfixpt A (Addr (Union [N A])))))
;;     (term (minfixpt A (Addr (Union)))))

;;   (test-equal? "type-join on minfixpts with different names"
;;     (term (type-join (minfixpt A (Addr (Union [M A])))
;;                      (minfixpt B (Addr (Union [N B])))))
;;     ;; TODO: I think this test is wrong
;;     (term (minfixpt A1 (Addr (Union)))))

;;   (test-exn "type-join on minfixpts with different numbers of 'unfoldings'"
;;     (lambda (exn) #t)
;;     (lambda () (term (type-join (minfixpt A (Addr (Union [M (minfixpt A (Addr (Union [M A])))])))
;;                                 (minfixpt A (Addr (Union [M A])))))))

;;   (test-equal? "type-join on one more minfixpt example"
;;     (term (type-join (minfixpt B (Addr (Addr (Union     [Y B]))))
;;                      (minfixpt A (Addr (Addr (Union [X] [Y A]))))))
;;     `(minfixpt B1 (Addr (Addr (Union [X] [Y B1])))))

;;   (test-equal? "No sorting when we have same number of branches in result and original inputs"
;;     (term (type-join (Union [B] [A]) (Union [B] [A])))
;;     (term (Union [B] [A]))))

;; (define-metafunction csa#
;;   type-meet : τ τ -> τ
;;   [(type-meet (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))
;;    (Union [t_3 τ_3 ...] ...)
;;    (where ([t_3 τ_3 ...] ...)
;;           ,(let ()
;;              (define branches1 (term ([t_1 τ_1 ...] ...)))
;;              (define branches2 (term ([t_2 τ_2 ...] ...)))
;;              (define all-new-branches
;;               (for/fold ([result-branches null])
;;                         ([branch1 branches1])
;;                 (define tag (first branch1))
;;                 (match (findf (lambda (branch2) (equal? (first branch2) tag)) branches2)
;;                   [#f result-branches]
;;                   [branch2
;;                    (define (meet-components type1 type2)
;;                      (term (type-meet ,type1 ,type2)))
;;                    ;; NOTE: assumes that the branches have the same number of components
;;                    (append result-branches
;;                            (list `[,tag ,@(map meet-components (rest branch1) (rest branch2))]))])))
;;              ;; NOTE: We sort here to get the types into a canonical form and avoid repeated states,
;;              ;; but only when the number of branches is different from the original number in each
;;              ;; list (as a conservative heuristic to detect when the types might be the
;;              ;; possibly-out-order types from the original program)
;;              (if (and (= (length all-new-branches) (length branches1))
;;                       (= (length all-new-branches) (length branches2)))
;;                  all-new-branches
;;                  (sort all-new-branches sexp<?))))]
;;   [(type-meet (Record [l_1 τ_1] ...) (Record [l_2 τ_2] ...))
;;    (Record [l_1 (type-meet τ_1 τ_2)] ...)]
;;   ;; If names for minfixpt are the same, don't rename them
;;   [(type-meet (minfixpt X τ_1) (minfixpt X τ_2))
;;    (minfixpt X (type-meet τ_1 τ_2))]
;;   [(type-meet (minfixpt X_1 τ_1) (minfixpt X_2 τ_2))
;;    (minfixpt X_fresh (type-meet τ_1subst τ_2subst))
;;    (where X_fresh
;;           ,(variable-not-in (term ((minfixpt X_1 τ_1) (minfixpt X_2 τ_2))) (term X_1)))
;;    (where τ_1subst (type-subst τ_1 X_1 X_fresh))
;;    (where τ_2subst (type-subst τ_2 X_2 X_fresh))]
;;   [(type-meet X X) X]
;;   [(type-meet (Addr τ_1) (Addr τ_2))
;;    (Addr (type-join τ_1 τ_2))]
;;   [(type-meet τ τ) τ])

;; (module+ test
;;   (test-equal? "type-meet 1" (term (type-meet Nat Nat)) 'Nat)
;;   (test-equal? "type-meet 2"
;;                (term (type-meet (Union [A]) (Union [B])))
;;                '(Union))
;;   (test-equal? "type-meet 2, other direction"
;;                (term (type-meet (Union [B]) (Union [A])))
;;                '(Union))
;;   (test-equal? "type-meet 3"
;;                (term (type-meet (Union [A] [B]) (Union [B])))
;;                '(Union [B]))

;;   (test-equal? "type-meet for records"
;;     (term (type-meet (Record [a (Union [A])]) (Record [a (Union [B])])))
;;     (term (Record [a (Union)])))

;;   (test-equal? "type-meet on addresses"
;;     (term (type-meet (Addr (Union [A])) (Addr (Union [B]))))
;;     (term (Addr (Union [A] [B]))))

;;   (test-equal? "type-meet on minfixpts with the same names"
;;     (term (type-meet (minfixpt A (Addr (Union [M A])))
;;                      (minfixpt A (Addr (Union [N A])))))
;;     (term (minfixpt A (Addr (Union [M A] [N A])))))

;;   (test-equal? "type-meet on minfixpts with different names"
;;     (term (type-meet (minfixpt A (Addr (Union [M A])))
;;                      (minfixpt B (Addr (Union [N B])))))
;;     (term (minfixpt A1 (Addr (Union [M A1] [N A1])))))

;;   (test-exn "type-meet on minfixpts with different numbers of 'unfoldings'"
;;     (lambda (exn) #t)
;;     (lambda () (term (type-meet (minfixpt A (Addr (Union [M (minfixpt A (Addr (Union [M A])))])))
;;                                 (minfixpt A (Addr (Union [M A])))))))

;;   (test-equal? "No sorting when we have same number of branches in result and original inputs"
;;     (term (type-meet (Union [B] [A]) (Union [B] [A])))
;;     (term (Union [B] [A]))))

;; NOTE: this is really a conservative approximation of <= for types. For instance, we don't rename
;; variables in recursive types to check for alpha-equivalent recursive types
(define (type<= type1 type2)
  (judgment-holds (type<=/j () ,type1 ,type2)))

(define-judgment-form csa#
  #:mode (type<=/j I I I)
  #:contract (type<=/j ([X X] ...) τ τ) ; first part is the (X_1 <: X_2) assumptions

  [-------------------
   (type<=/j _ Nat Nat)]

  [-------------------
   (type<=/j _ String String)]

  [--------------
   (type<=/j (_ ... (X_1 X_2) _ ...) X_1 X_2)]

  ;; implements the Amber rule
  [(type<=/j (any ... (X_1 X_2)) τ_1 τ_2)
   ;; TODO: shouldn't these constraints override previous ones, e.g. if one recursive type shadows
   ;; another?
   ----------------------------------------------------------
   (type<=/j (any ...) (minfixpt X_1 τ_1) (minfixpt X_2 τ_2))]

  [;; every variant in type 1 must have >= type in type 2
   ;; (side-condition ,(printf "Union: ~s\n"  (term (any (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...)))))
   (union-variant<=/j any [t_1 τ_1 ...] (Union [t_2 τ_2 ...] ...)) ...
   ---------------------------------------------------------------
   (type<=/j any (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))]

  [(type<=/j any τ_1 τ_2) ...
   ---------------------------------------------------
   (type<=/j any (Record [l τ_1] ...) (Record [l τ_2] ...))]

  [;; Address types are contravariant (they're "sinks")
   ;; (side-condition ,(printf "~s\n" (term (any (Addr τ_1) (Addr τ_2)))))
   (type<=/j any τ_2 τ_1)
   ---------------------------------
   (type<=/j any (Addr τ_1) (Addr τ_2))]

  [(type<=/j any τ_1 τ_2)
   ---------------------------------
   (type<=/j any (List τ_1) (List τ_2))]

  [(type<=/j any τ_k1 τ_k2)
   (type<=/j any τ_v1 τ_v2)
   -------------------------------------------
   (type<=/j any (Hash τ_k1 τ_v1) (Hash τ_k2 τ_v2))])

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
  (test-true "type<= list 1" (type<= `(List ,union-a) `(List ,union-ab)))
  (test-false "type<= list 2" (type<= `(List ,union-ab) `(List ,union-a)))
  (test-true "type<= hash 1" (type<= `(Hash ,union-a ,union-a) `(Hash ,union-ab ,union-ab)))
  (test-false "type<= hash 2" (type<= `(Hash ,union-ab ,union-ab)  `(Hash ,union-a ,union-a)))
  (test-true "type<= alpha-equiv minfixpts"
    (type<= `(minfixpt A (Addr (Addr A)))
            `(minfixpt B (Addr (Addr B)))))
  (test-true "type<= minfixpts with no recursive use"
    (type<= `(minfixpt A (Addr (Union [X] [Y])))
            `(minfixpt B (Addr (Union [X])))))
  (test-true "type<= minfixpt 1"
    (type<= `(minfixpt B (Addr (Addr (Union     [Y B]))))
            `(minfixpt A (Addr (Addr (Union [X] [Y A]))))))
  (test-false "type<= minfixpt 2"
    (type<= `(minfixpt A (Addr (Addr (Union [X] [Y A]))))
            `(minfixpt B (Addr (Addr (Union     [Y B])))))))

;; Holds if the variant [t_1 τ_1 ...] has a >= variant in the given union type
(define-judgment-form csa#
  #:mode (union-variant<=/j I I I)
  #:contract (union-variant<=/j ([X X] ...) [t_1 τ_1 ...] (Union [t_2 τ_2 ...] ...))

  [(type<=/j any τ_1 τ_2) ...
   ------------------------------------------------------------------------
   (union-variant<=/j any [t_1 τ_1 ..._n] (Union _ ... [t_1 τ_2 ..._n] _ ...))])

(module+ test
  (test-true "union-variant<= for union with that variant"
    (judgment-holds (union-variant<=/j ()
                                       [A]
                                       (Union [A]))))
  (test-true "union-variant<= for bigger union"
    (judgment-holds (union-variant<=/j ()
                                       [A]
                                       (Union [A] [B]))))
  (test-false "union-variant<= for union without variant"
    (judgment-holds (union-variant<=/j ()
                                       [A]
                                       (Union [B]))))
  (test-true "union-variant<= for union with bigger type"
    (judgment-holds (union-variant<=/j ()
                                       [A (Union [C])]
                                       (Union [A (Union [C] [D])] [B]))))
  (test-false "union-variant<= for union with smaller type"
    (judgment-holds (union-variant<=/j ()
                                       [A (Union [C] [D])]
                                       (Union [A (Union [C])] [B])))))

;; v# τ -> ([τ (marked a# mk ...)] ...)
;;
;; Returns the marked-address environment inferred by type-checking v# as τ
(define (internal-addr-types v type)
  (filter
   (lambda (entry)
     (match-define (list type marked-addr) entry)
     (csa#-internal-address? (unmark-addr marked-addr)))
   (addr-types v type)))

(module+ test
  (test-equal? "internal-addr-types: simple test"
    (internal-addr-types `(marked (addr 1 0)) `(Addr Nat))
    (list `(Nat (marked (addr 1 0)))))
  (test-equal? "internal-addr-types: same address at multiple types"
    (internal-addr-types `(record [a (marked (addr 1 0))]
                                  [b (marked (addr 1 0))])
                         `(Record [a (Addr (Union [A]))] [b (Addr (Union [B]))]))
    (list `((Union [A]) (marked (addr 1 0)))
          `((Union [B]) (marked (addr 1 0)))))
  (test-equal? "internal-addr-types: natural"
    (internal-addr-types `abs-nat `Nat)
    null)
  (test-equal? "internal-addr-types 4: string"
    (internal-addr-types `abs-string `String)
    null)
  (test-equal? "internal-addr-types 5: recursive"
    (internal-addr-types `(folded (minfixpt X (Addr (Union [A X])))
                                  (marked (addr 1 0)))
                         `(minfixpt X (Addr (Union [A X]))))
    (list `[(Union [A (minfixpt X (Addr (Union [A X])))]) (marked (addr 1 0))]))
  (test-case "internal-addr-types: internals and externals"
    (check-same-items?
     (internal-addr-types (term (record [a (marked (addr 1 0) 1)]
                                        [b (marked (collective-addr (env Nat)) 2)]
                                        [c (marked (addr 3 1) 3)]
                                        [d (list-val (marked (addr 2 0))
                                                     (marked (collective-addr (env Nat)) 3))]))
                          (term (Record [a (Addr Nat)]
                                        [b (Addr String)]
                                        [c (Addr String)]
                                        [d (List (Addr Nat))])))
     (term ((Nat (marked (addr 1 0) 1))
            (String (marked (addr 3 1) 3))
            (Nat (marked (addr 2 0))))))))

;; v# τ -> ρ#
;;
;; Returns the type/address pairs for all address in the given value when the value is typechecked as
;; the given type
(define (addr-types v type)
  (define (get-types-and-merge-all v-type-pairs)
    (for/fold ([results null])
              ([vtp v-type-pairs])
      (match-define (list v type) vtp)
      (merge-receptionists results (addr-types v type))))

  (match (list v type)
    [(list `(marked ,(? (lambda (v) (redex-match? csa# a# v))) ,_ ...) `(Addr ,type))
     (list `[,type ,v])]
    [(list `(folded ,type ,v) `(minfixpt ,X ,fold-type))
     (addr-types v (term (type-subst ,fold-type ,X (minfixpt ,X ,fold-type))))]
    [(list `(variant ,tag ,vs ...) `(Union ,cases ...))
     (match-define `(,_ ,case-arg-types ...)
       (first (filter (lambda (case) (equal? (first case) tag)) cases)))
     (get-types-and-merge-all (map list vs case-arg-types))]
    [(list `(record ,rec-fields ...) `(Record ,rec-field-types ...))
     (get-types-and-merge-all (map list (map second rec-fields) (map second rec-field-types)))]
    [(list `(list-val ,vs ...) `(List ,type))
     (get-types-and-merge-all (map (lambda (v) (list v type)) vs))]
    [(list `(hash-val ,vs1 ,vs2) `(Hash ,type1 ,type2))
     (merge-receptionists
      (get-types-and-merge-all (map (lambda (v) (list v type1)) vs1))
      (get-types-and-merge-all (map (lambda (v) (list v type2)) vs2)))]
    [(list `abs-nat 'Nat) null]
    [(list `abs-string 'String) null]
    [_ (error 'addr-types "Unknown val/type combo ~s ~s" v type)]))

(module+ test
  (test-equal? "addr-types: simple addr"
    (addr-types `(marked (addr 1 1)) `(Addr Nat))
    (term ([Nat (marked (addr 1 1))])))
  (test-equal? "addr-types: simple collective addr"
    (addr-types `(marked (collective-addr 1)) `(Addr Nat))
    (term ([Nat (marked (collective-addr 1))])))
  (test-equal? "addr-types: variant"
    (addr-types `(variant A abs-nat (marked (addr 2 2))) `(Union [B] [A Nat (Addr String)]))
    (term ([String (marked (addr 2 2))])))
  (test-equal? "addr-types: record"
    (addr-types `(record [a (marked (addr 1 2))] [b abs-string]) `(Record [a (Addr String)] [b String]))
    (term ([String (marked (addr 1 2))])))
  (test-equal? "addr-types: same address at multiple types"
    (addr-types `(record [a (marked (addr 2 2))] [b (marked (addr 2 2))])
                `(Record [a (Addr (Union [A]))]  [b (Addr (Union [B]))]))
    (term ([(Union [A]) (marked (addr 2 2))]
           [(Union [B]) (marked (addr 2 2))])))
  (test-case "addr-types: fold"
    (define type `(minfixpt SelfAddr (Addr (Union [A SelfAddr]))))
    (check-equal?
     (addr-types `(folded ,type (marked (addr 1 1))) type)
     (term ([(Union [A ,type]) (marked (addr 1 1))]))))
  (test-equal? "addr-types: list"
    (addr-types `(list-val (marked (addr 1 1)) (marked (addr 2 2))) `(List (Addr (Record))))
    (term ([(Record) (marked (addr 1 1))] [(Record) (marked (addr 2 2))])))
  (test-equal? "addr-types: hash"
    (addr-types `(hash-val ((marked (addr 0 0))) ((marked (addr 1 1)) (marked (addr 2 2))))
                `(Hash (Addr String) (Addr (Record))))
    (term ([String (marked (addr 0 0))]
           [(Record) (marked (addr 1 1))]
           [(Record) (marked (addr 2 2))]))))

;; ρ# ρ# -> ρ#
;;
;; Merges the list of new receptionists into the old one,
(define (merge-receptionists old-recs new-recs)
  (remove-duplicates (append old-recs new-recs)))

(module+ test
  (test-equal? "merge-receptionists adds new items"
    (merge-receptionists
     `([Nat (marked (addr 1 1) 1)])
     `([Nat (marked (addr 2 2) 2)]))
    `([Nat (marked (addr 1 1) 1)]
      [Nat (marked (addr 2 2) 2)]))

  (test-equal? "merge-receptionists removes duplicates"
    (merge-receptionists
     `([Nat (marked (addr 1 1))])
     `([Nat (marked (addr 1 1))]))
    `([Nat (marked (addr 1 1))]))

  (test-equal? "merge-receptionists handles lists with multiple items"
    (merge-receptionists
     `(((Union [A]) (marked (addr 1 1) 1))
       ((Union [B]) (marked (addr 2 2) 2)))
     `(((Union [A]) (marked (addr 1 1) 1))
       ((Union [C]) (marked (addr 3 3) 3))))
    `(((Union [A]) (marked (addr 1 1) 1))
      ((Union [B]) (marked (addr 2 2) 2))
      ((Union [C]) (marked (addr 3 3) 3)))))

;; ---------------------------------------------------------------------------------------------------
;; Address containment

;; Returns the list of all markers in the given term
(define (markers-in the-term)
  (remove-duplicates (markers-in/internal the-term)))

(define (markers-in/internal the-term)
  (match the-term
    [`(marked ,_ ,markers ...) markers]
    [(list terms ...) (append* (map markers-in/internal the-term))]
    [_ null]))

;; ---------------------------------------------------------------------------------------------------
;; Eviction (see the Eviction section of aps-abstract.rkt for more info)

;; Eviction is motivated by the phenomenon of actors causing lots of state explosion even though their
;; precise state and communication does not affect conformance for the overall program. The idea of
;; eviction is that when we're about to spawn a specially marked "evictable" actor, we instead create
;; an external address with that type and send a message to the environment that contains all internal
;; addresses that would be contained in the spawned actor's behavior (as long as the behavior does not
;; itself contain precise external addresses). This allows potentially more messages to come from
;; those actors than would be generated otherwise, but it avoids the state explosion from precisely
;; modeling

(define (csa#-addrs-to-evict i)
  (filter (curryr evictable? i)
          (append (map csa#-actor-address (csa#-config-actors i))
                  (map csa#-blurred-actor-address (csa#-config-blurred-actors i)))))

(module+ test
  (define non-evictable1-addr `(addr 1 1))
  (define non-evictable1 `[,non-evictable1-addr (() (goto S))])
  (define evictable-addr1
    `(addr (2-EVICT (Addr Nat)
                          ([(0 3 1) (Addr String)]
                           [(0 4 1 1) (Record [a (Addr String)])]))
                 1))
    (define collective-evictable-addr1
      `(collective-addr (2-EVICT (Addr Nat)
                                    ([(0 3 1) (Addr String)]
                                     [(0 4 1 1) (Record [a (Addr String)])]))))
  (define evictable1
    `[,evictable-addr1
      (((define-state (A [x (Union [Foo (Addr Nat)])]) (m)
          (send (marked (addr 2 0)) "foobar")
          (send (: (record [a (marked (addr 3 0))]) a) "foo")
          (goto A x)))
       (goto A (variant Foo (marked (addr 1 0)))))])
  (define collective-evictable1
    `[,collective-evictable-addr1
      ([((define-state (A [x (Union [Foo (Addr Nat)])]) (m)
           (send (marked (addr 2 0)) "foobar")
           (send (: (record [a (marked (addr 3 0))]) a) "foo")
           (goto A x)))
        (goto A (variant Foo (marked (addr 1 0))))])])
  (define non-evictable2-addr `(addr (3-EVICT Nat ()) 0))
  (define non-evictable2
    `[,non-evictable2-addr
      [((define-state (B) (m)
          (begin (marked ,evictable-addr1)
                 (marked (collective-addr (env Nat)) 1)
                 (goto B))))
       (goto B)]])
  (define non-evictable-has-mon-ext-message-addr `(addr (4-EVICT (Addr Nat) ()) 0))
  (define non-evictable-has-mon-ext-message
    `[,non-evictable-has-mon-ext-message-addr
      [((define-state (A) (m) (goto A))) (goto A)]])

  (define evict-test-config
    `((,non-evictable1 ,evictable1 ,non-evictable2 ,non-evictable-has-mon-ext-message)
      ;; β#
      (,collective-evictable1)
      ;; μ#
      ([,evictable-addr1 (marked (addr 4 0)) single]
       [(addr (4-EVICT (Addr Nat) ()) 0) (marked (collective-addr (env Nat)) 3) single]
       [,non-evictable2-addr (marked ,collective-evictable-addr1) many])
      ;; ρ#
      ([Nat (marked ,non-evictable1-addr 1)])))

  (define expected-precise-evicted-config
    `(([(addr 1 1) (() (goto S))]
       [(addr (3-EVICT Nat ()) 0)
        [((define-state (B) (m)
            (begin (marked (collective-addr (env (Addr Nat))))
                   (marked (collective-addr (env Nat)) 1)
                   (goto B))))
         (goto B)]]
       ,non-evictable-has-mon-ext-message)
      ;; β#
      (,collective-evictable1)
      ;; μ#
      ([(addr (4-EVICT (Addr Nat) ()) 0) (marked (collective-addr (env Nat)) 3) single]
       [,non-evictable2-addr (marked ,collective-evictable-addr1) many])
      ;; ρ#
      ([Nat (marked ,non-evictable1-addr 1)]
       [String (marked (addr 2 0))]
       [String (marked (addr 3 0))]
       [Nat (marked (addr 1 0))]
       [Nat (marked (addr 4 0))])))

    (define expected-blurred-evicted-config
      `((,non-evictable1
         ,evictable1
         ,non-evictable2
         ,non-evictable-has-mon-ext-message)
        ;; β#
        ()
        ;; μ#
        ([,evictable-addr1 (marked (addr 4 0)) single]
         [(addr (4-EVICT (Addr Nat) ()) 0) (marked (collective-addr (env Nat)) 3) single]
         [,non-evictable2-addr (marked (collective-addr (env (Addr Nat)))) many])
        ;; ρ#
        ([Nat (marked ,non-evictable1-addr 1)]
         [String (marked (addr 2 0))]
         [String (marked (addr 3 0))]
         [Nat (marked (addr 1 0))])))

  (test-equal? "Addresses to evict"
    (csa#-addrs-to-evict evict-test-config)
    (list evictable-addr1 collective-evictable-addr1)))

(define (evictable? addr i)
  (define behaviors (csa#-behaviors-of i addr))
  (and (evictable-addr? addr)
       ;; more behaviors would technically be okay, but my proof in the dissertation is only for
       ;; single behaviors
       (= 1 (length behaviors))
       (let ([packets-to-this-actor
              (filter (lambda (packet) (equal? (csa#-message-packet-address packet) addr))
                      (csa#-config-message-packets i))])
         (null? (markers-in (list behaviors packets-to-this-actor))))))

(module+ test
  (test-false "non-evictable actor 1" (evictable? non-evictable1-addr evict-test-config))
  (test-true "evictable actor 1" (evictable? evictable-addr1 evict-test-config))
  (test-false "non-evictable actor 2" (evictable? non-evictable2-addr evict-test-config))
  (test-false "non-evictable b/c external in message"
    (evictable? non-evictable-has-mon-ext-message-addr evict-test-config)))

(define (evictable-addr? address)
  (evictable-location? (address-location address)))

(module+ test
  (test-true "evictable address 1" (evictable-addr? evictable-addr1))
  (test-false "evictable address 2" (evictable-addr? `(addr 1 0)))
  (test-false "evictable address 3" (evictable-addr? `(collective-addr 1))))

(define (evictable-location? loc)
  (match loc
    [(list (? (lambda (kw) (and (symbol? kw) (regexp-match? #rx"EVICT$" (symbol->string kw))))) _ _)
     #t]
    [_ #f]))

(module+ test
  (check-false (evictable-addr? `(addr 1 0)))
  (check-true (evictable-addr? `(addr (L-EVICT Nat ()) 1)))
  (check-false (evictable-addr? `(addr (L Nat ()) 1)))
  (check-false (evictable-addr? `(collective-addr (L Nat ()))))
  (check-true (evictable-addr? `(collective-addr (L-EVICT Nat ()))))
  (check-false (evictable-addr? `(collective-addr (EVICT-NOT Nat ())))))

;; i# a# -> (list i# ρ#) Evicts the given address from the given config, returning the new
;; configuration and receptionists added
;;
;; REFACTOR: I don't think I need to return the receptionists anymore
(define (csa#-evict i addr)
  (match-define (list remaining-actors remaining-blurred-actors evicted-behavior)
    (cond
      [(csa#-atomic-address? addr)
       (match-define (list first-actors to-evict later-actors)
         (config-actor-and-rest-by-address i addr))
       (list (append first-actors later-actors)
             (csa#-config-blurred-actors i)
             (actor-behavior to-evict))]
      [else
       (match-define (list first-actors to-evict later-actors)
         (config-collective-actor-and-rest-by-address i addr))
       (list (csa#-config-actors i)
             (append first-actors later-actors)
             (first (csa#-blurred-actor-behaviors to-evict)))]))
  (match-define `(,state-defs (goto ,state-name ,state-args ...)) evicted-behavior)
  (match-define `(,_ ,evicted-type ,state-defs-type-env) (address-location addr))
  (define state-def-captured-receptionists
    (for/fold ([receptionists null])
              ([env-binding state-defs-type-env])
      (match-define `(,path ,type) env-binding)
      (merge-receptionists receptionists
                           (internal-addr-types (sexp-by-path state-defs path) type))))
  (match-define `(define-state ,(list _ [list _ arg-types] ...) ,_ ...)
    (state-def-by-name state-defs state-name))
  (define state-arg-captured-receptionists
    (for/fold ([receptionists null])
              ([arg state-args]
               [type arg-types])
      (merge-receptionists receptionists (internal-addr-types arg type))))
  (define-values (evicted-packets non-evicted-packets)
    (partition (lambda (packet) (equal? addr (csa#-message-packet-address packet)))
               (csa#-config-message-packets i)))
  (define message-captured-receptionists
    (for/fold ([receptionists null])
              ([packet evicted-packets])
      (merge-receptionists receptionists
                           (internal-addr-types (csa#-message-packet-value packet) evicted-type))))
  (define all-new-receptionists
    (merge-receptionists
     (merge-receptionists state-def-captured-receptionists state-arg-captured-receptionists)
     message-captured-receptionists))
  (define updated-receptionists
    (merge-receptionists
     (remove-receptionist (csa#-config-receptionists i) addr)
     all-new-receptionists))
  (list (rename-address `(,remaining-actors
                          ,remaining-blurred-actors
                          ,non-evicted-packets
                          ,updated-receptionists)
                        addr
                        `(collective-addr (env ,evicted-type)))
        all-new-receptionists))

(module+ test
  (test-equal? "csa#-evict atomic address"
    (csa#-evict evict-test-config evictable-addr1)
    (list expected-precise-evicted-config
          `([String (marked (addr 2 0))]
            [String (marked (addr 3 0))]
            [Nat (marked (addr 1 0))]
            [Nat (marked (addr 4 0))])))

  (test-equal? "csa#-evict collective address"
    (csa#-evict evict-test-config collective-evictable-addr1)
    (list expected-blurred-evicted-config
          `([String (marked (addr 2 0))]
            [String (marked (addr 3 0))]
            [Nat (marked (addr 1 0))]))))

(define (remove-receptionist receptionists addr-to-remove)
  (filter (lambda (rec) (not (equal? (unmark-addr (second rec)) addr-to-remove)))
          receptionists))

(define (sexp-by-path sexp path)
  (match path
    [(list) sexp]
    [(list index path-rest ...) (sexp-by-path (list-ref sexp index) path-rest)]))

(module+ test
  (test-equal? "sexp-by-path 1" (sexp-by-path `(foo (bar) baz) null) `(foo (bar) baz))
  (test-equal? "sexp-by-path 2" (sexp-by-path `(foo (bar (quux 2)) baz) (list 1 1 0)) `quux))

(define (rename-address exp old new)
  (match exp
    [(or `(addr ,_ ,_) `(collective-addr ,_))
     (if (equal? exp old)
         new
         (map (lambda (e) (rename-address e old new)) exp))]
    [(list exps ...)
     (map (lambda (e) (rename-address e old new)) exps)]
    [_ exp]))

(module+ test
  (test-equal? "rename-address 1"
    (rename-address 'foo `(addr 1 2) `(collective-addr (env Nat)))
    'foo)
  (test-equal? "rename-address 2"
    (rename-address `(begin (addr 1 2)
                            (addr 5 6))
                    `(addr 1 2)
                    `(collective-addr (env Nat)))
    `(begin (collective-addr (env Nat)) (addr 5 6)))
  (test-equal? "rename-address 2"
    (rename-address `(begin (collective-addr 2)
                            (addr 5 6))
                    `(collective-addr 2)
                    `(collective-addr (env Nat)))
    `(begin (collective-addr (env Nat)) (addr 5 6))))

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
     ;; 2. Do all atomic spawns either come from an evictable location or have have a corresponding
     ;; existing actor with that spawn location, and have the same state name?
     ;;
     ;; REFACTOR: should probably just compare behaviors without state defs for spawns instead of
     ;; looking at the state name
     (for/and ([spawn (csa#-transition-effect-spawns transition-result)])
       (match-define `[,addr ,behavior] spawn)
       (cond
         [(csa#-atomic-address? addr)
          (define loc (address-location addr))
          (if (or (evictable-location? loc)
                  (atomic-state-name-by-address original-i `(addr ,loc 0)))
              'eq
              'not-gteq)]
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
    `[([(addr 1 0) (() (goto A))]
       [(addr 2 0) (() (goto B abs-nat))])
      ()
      ()]
    `(addr 2 0))
   'B))

;; Rename addresses in everything but the state definitions of the transition so that any marker >
;; INIT-MESSAGE-MARKER is removed, and any NEW spawn address is converted to a collective-addr.
(define (pseudo-blur-transition-result transition-result)
  (match-define (csa#-transition-effect trigger `(,state-defs ,goto-exp) sends spawns unused-marker)
    transition-result)
  (define new-sends
    (for/list ([send sends])
      (match-define `[,target ,message ,mult] send)
      `[,(pseudo-blur target) ,(pseudo-blur message) ,mult]))
  (define new-spawns
    (for/list ([spawn spawns])
      (match-define `[,addr [,spawn-state-defs ,spawn-goto]] spawn)
      `[,(pseudo-blur addr) [,(pseudo-blur spawn-state-defs) ,(pseudo-blur spawn-goto)]]))
  (csa#-transition-effect trigger `(,state-defs ,(pseudo-blur goto-exp)) new-sends new-spawns unused-marker))

;; Does the marker-removal/assimilation mentioned in comments for pseudo-blur-transition-result, on an
;; arbitrary expression/term
(define (pseudo-blur some-term)
  (match some-term
    [`(marked ,address ,markers ...)
     `(marked ,(pseudo-blur-address address) ,@(filter (curryr < INIT-MESSAGE-MARKER) markers))]
    [(list (and keyword (or 'list-val 'hash-val)) terms ...)
     (define blurred-args (map pseudo-blur terms))
     (normalize-collection `(,keyword ,@blurred-args))]
    [`(hash-val ,keys ,vals)
     (define blurred-keys (map pseudo-blur keys))
     (define blurred-vals (map pseudo-blur vals))
     `(normalize-collection `(hash-val ,blurred-keys ,blurred-vals))]
    [(list terms ...) (map pseudo-blur terms)]
    [_ some-term]))

(module+ test
  (test-equal? "pseudo-blur on old external"
    (pseudo-blur `(marked (collective-addr (env Nat)) 2))
    `(marked (collective-addr (env Nat)) 2))
  (test-equal? "pseudo-blur on new external"
    (pseudo-blur `(marked (collective-addr (env Nat)) 102))
    `(marked (collective-addr (env Nat))))
  (test-equal? "pseudo-blur on marked old internal"
    (pseudo-blur `(marked (addr 1 0)))
    `(marked (addr 1 0)))
  (test-equal? "pseudo-blur on marked new internal"
    (pseudo-blur `(marked (addr 1 1)))
    `(marked (collective-addr 1)))
  (test-equal? "pseudo-blur on old internal"
    (pseudo-blur `(marked (addr 1 0)))
    `(marked (addr 1 0)))
  (test-equal? "pseudo-blur on marked new internal"
    (pseudo-blur `(marked (addr 1 1)))
    `(marked (collective-addr 1))))

(define (pseudo-blur-address a)
  (match a
    [`(addr ,loc ,id)
     (cond
       [(csa#-internal-address? a)
        (if (= id 1) `(collective-addr ,loc) a)]
       [else
        ;; externals are already collective, so can just return the address
        a])]
    [_ ;; don't need to do anything for collectives
     a]))

;; returns true if the given packet appears with a "many" quantity in the given config
(define (new-pseudo-send? config send)
  (match-define `[,addr ,message ,_] send)
  (not (member `[,addr ,message many] (csa#-config-message-packets config))))

(module+ test
  (check-not-false
   (new-pseudo-send? `[() () ([(addr 1 0) abs-nat single])]
                     `[(addr 1 0) abs-nat single]))
  (check-false
   (new-pseudo-send? `[() () ([(addr 1 0) abs-nat many])]
                     `[(addr 1 0) abs-nat single]))
  (check-not-false
   (new-pseudo-send? `[() () ([(addr 1 0) abs-nat many])]
                     `[(addr 1 0) abs-string single]))
  (check-not-false
   (new-pseudo-send? `[() () ([(addr 1 0) abs-nat many])]
                     `[(addr 2 0) abs-nat single])))

;; Is the behavior better than all existing ones for this address if we ignore state definitions?
(define (compare-pseudo-behavior config addr behavior)
  (match (csa#-behaviors-of config addr)
    [#f 'gt]
    [old-behaviors
     (if (csa#-atomic-address? addr)
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
   (compare-pseudo-behavior `[([(addr 1 0) (() (goto A))])
                              ()
                              ()]
                            `(addr 1 0)
                            `(() (goto B)))
   'not-gteq)
  (check-equal?
   (compare-pseudo-behavior `[([(addr 1 0) (() (goto A))])
                              ()
                              ()]
                            `(addr 1 0)
                            `(() (goto A)))
   'eq)
  (check-equal?
   (compare-pseudo-behavior `[([(addr 1 0) (() (goto A (list-val)))])
                              ()
                              ()]
                            `(addr 1 0)
                            `(() (goto A (list-val abs-nat))))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[([(addr 1 0) (() (goto A))])
                              ()
                              ()]
                            `(addr 2 0)
                            `(() (goto A)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(collective-addr 2)
                            `(() (goto A)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(collective-addr 1)
                            `(() (goto A)))
   'eq)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([() (goto A)]
                                 [() (goto B)])])
                              ()]
                            `(collective-addr 1)
                            `(() (goto C)))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([() (goto A (list-val))]
                                 [() (goto B)])])
                              ()]
                            `(collective-addr 1)
                            `(() (goto A (list-val abs-nat))))
   'gt)
  (check-equal?
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([() (goto A (list-val abs-nat))]
                                 [() (goto B)])])
                              ()]
                            `(collective-addr 1)
                            `(() (goto A (list-val))))
   'lt)
  (test-equal? "Blurred actor with different state defs (faking different constructor args)"
   (compare-pseudo-behavior `[()
                              ([(collective-addr 1)
                                ([((define-state (A))) (goto A)])])
                              ()]
                            `(collective-addr 1)
                            `(() (goto A)))
   'gt))

;; ---------------------------------------------------------------------------------------------------
;; Trigger update test

(define (csa#-trigger-updated-by-step? trigger prev-trigger prev-config spawn-locs)
  ;; A step updates a trigger (i.e. makes it so that running the handler for the trigger *might*
  ;; result in a transition that wouldn't have been possible before this step) if one of the following
  ;; holds:
  ;; 1. The trigger is for the updated actor from the i-step
  ;; 2. The trigger is for an actor that shares a spawn location with a spawn from the i-step
  ;; 3. The trigger is an internal message that did not exist in the previous config
  (define trigger-addr (trigger-address trigger))
  (or (equal? trigger-addr (trigger-address prev-trigger))
      (match (address-location trigger-addr)
        [#f #f]
        [loc (member loc spawn-locs)])
      (match trigger
        [`(internal-receive ,target-addr ,message ,_)
         (not
          (findf (lambda (send) (and (equal? (first send) target-addr)
                                     (equal? (second send) message)))
                 (if prev-config (csa#-config-message-packets prev-config) null)))]
        [_ #f])))

(module+ test
  (check-not-false (csa#-trigger-updated-by-step? `(internal-receive (addr 1 0) abs-nat single)
                                                  `(internal-receive (addr 1 0) abs-string single)
                                                  #f
                                                  null))
  (check-not-false (csa#-trigger-updated-by-step? `(internal-receive (addr 1 0) abs-nat single)
                                                  `(internal-receive (addr INIT1 0) abs-string single)
                                                  #f
                                                  (list 1)))
  (check-not-false (csa#-trigger-updated-by-step? `(internal-receive (collective-addr 1) abs-nat single)
                                                  `(internal-receive (addr INIT1 0) abs-string single)
                                                  #f
                                                  (list 1)))
  (check-not-false (csa#-trigger-updated-by-step? `(internal-receive (addr INIT1 0) abs-nat single)
                                                  `(internal-receive (addr INIT2 0) abs-string single)
                                                  `(() () ([(addr INIT1 0) abs-string many]))
                                                  null))
  (check-false (csa#-trigger-updated-by-step? `(internal-receive (addr 1 0) abs-nat single)
                                              `(internal-receive (addr INIT2 0) abs-string single)
                                              `(() () ([(addr 1 0) abs-nat many]
                                                       [(addr 1) abs-nat many]))
                                              (list `[(addr 2 1) (() (goto S))]))))

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
  ;; (define spawn-behavior-change-test-config
  ;;   (redex-let csa# ([i#
  ;;                     (term
  ;;                      (([(addr the-loc 0)
  ;;                         (() (goto A))]
  ;;                        [(addr second-loc 0)
  ;;                         (() (goto A))]
  ;;                        [(addr third-loc 0)
  ;;                         (() (goto A))])
  ;;                       ([(collective-addr the-loc)
  ;;                         ((() (goto A)))]
  ;;                        [(collective-addr second-loc)
  ;;                         ((() (goto B)))])
  ;;                       ()))])
  ;;     (term i#)))

  ;; (test-equal? "effect matches existing spawn behavior, no blurred version"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto B)))]
  ;;      [(spawn-addr third-loc)
  ;;       (() (goto A))])
  ;;     ())))
  ;;  'gt)
  ;; (test-equal? "effect matches existing spawn behavior, blurred behavior also exists"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'eq)
  ;; (test-equal? "effect matches existing spawn behavior, blurred actor with other behavior exists"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto A)) (() (goto B)))])
  ;;     ())))
  ;;  'gt)
  ;; (test-equal? "effect changes existing spawn behavior"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'not-gteq)
  ;; (test-equal? "config has no actor for corresponding spawn"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'not-gteq)
  ;; (test-equal? "effect has no spawns"
  ;;  (csa#-transition-effect-compare-spawn-behavior
  ;;   (csa#-transition-effect '(timeout (addr 0 0))
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
  ;;     ([(collective-addr the-loc)
  ;;       ((() (goto A)))]
  ;;      [(collective-addr second-loc)
  ;;       ((() (goto B)))])
  ;;     ())))
  ;;  'eq)
  )

;; (module+ test
;;   (test-equal? "actor-compare-behavior: new atomic behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout (addr 1 0)) '(() (goto D)) null null)
;;      (term (([(addr 1 0) (() (goto D))])
;;            ([(collective-addr 2)
;;              ((() (goto B))
;;               (() (goto C)))])
;;            ())))
;;     'not-gteq)
;;   (test-equal? "actor-compare-behavior: old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout (addr 1 0)) '(() (goto A)) null null)
;;      behavior-test-config)
;;     'eq)
;;   (test-equal? "actor-compare-behavior: adding to vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(addr 1 0) (() (goto A (vector-val (variant A))))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout (addr 1 0)) '(() (goto A (vector-val (variant B) (variant A)) )) null null)
;;      (term (([(addr 1 0) (() (goto A (vector-val (variant B) (variant A))))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'gt)
;;   (test-equal? "actor-compare-behavior: same vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(addr 1 0) (() (goto A (vector-val (variant A))))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout (addr 1 0)) '(() (goto A (vector-val (variant A)))) null null)
;;      (term (([(addr 1 0) (() (goto A (vector-val (variant A))))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'eq)
;;   (test-equal? "actor-compare-behavior: smaller vector in old atomic behavior"
;;     (csa#-actor-compare-behavior
;;      (term (([(addr 1 0) (() (goto A (vector-val (variant A))))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ()))
;;      (csa#-transition-effect
;;       `(timeout (addr 1 0)) '(() (goto A (vector-val))) null null)
;;      (term (([(addr 1 0) (() (goto A (vector-val)))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C)))])
;;             ())))
;;     'not-gteq)
;;   (test-equal? "actor-compare-behavior: new collective behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout (collective-addr 2)) '(() (goto D)) null null)
;;      (term (([(addr 1 0) (() (goto A))])
;;             ([(collective-addr 2)
;;               ((() (goto B))
;;                (() (goto C))
;;                (() (goto D)))])
;;             ())))
;;     'gt)
;;   (test-equal? "actor-compare-behavior: old collective behavior"
;;     (csa#-actor-compare-behavior
;;      behavior-test-config
;;      (csa#-transition-effect `(timeout (collective-addr 2)) '(() (goto B)) null null)
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

;; TODO: test the new message rule

;; (module+ test

;;   (define new-message-test-config
;;     (term (([(spawn-addr 0 OLD) (() (goto A))]
;;             [(spawn-addr 1 OLD) (() (goto A))]
;;             [(spawn-addr 2 OLD) (() (goto A))])
;;            ()
;;            ([(spawn-addr 1 OLD) abs-nat single]
;;             [(spawn-addr 2 OLD) abs-nat many]))))

;;   (test-equal? "Ensure that only internal messages are compared"
;;     (csa#-compare-new-messages
;;      new-message-test-config
;;      (csa#-transition-effect #f #f (list `[(obs-ext 1) abs-nat single]) null)
;;      new-message-test-config)
;;     'eq)

;;   ;; (define (compare-one-message m)
;;   ;;   (csa#-compare-new-messages
;;   ;;    new-message-test-config
;;   ;;    (csa#-transition-effect #f #f (list m) null)))

;;   ;; (test-equal? "single message to init-addr"
;;   ;;   (compare-one-message `((addr 3 0) abs-nat single))
;;   ;;   'gt)
;;   ;; (test-equal? "single message to OLD spawn-addr"
;;   ;;   (compare-one-message `((spawn-addr 1 OLD) abs-nat single))
;;   ;;   'gt)
;;   ;; (test-equal? "single message to collective address"
;;   ;;   (compare-one-message `((collective-addr 3) abs-nat single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send one"
;;   ;;   (compare-one-message `((spawn-addr 0 NEW) abs-nat single))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: OLD doesn't exist, send one"
;;   ;;   (compare-one-message `((spawn-addr 4 NEW) abs-nat single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send many"
;;   ;;   (compare-one-message `((spawn-addr 0 NEW) abs-nat many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had one, send one"
;;   ;;   (compare-one-message `((spawn-addr 1 NEW) abs-nat single))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had one, send many"
;;   ;;   (compare-one-message `((spawn-addr 1 NEW) abs-nat many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had many, send one"
;;   ;;   (compare-one-message `((spawn-addr 2 NEW) abs-nat single))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: had many, send many"
;;   ;;   (compare-one-message `((spawn-addr 2 NEW) abs-nat many))
;;   ;;   'gt)
;;   ;; (test-equal? "to NEW: had zero, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ()))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 0 NEW) (() (goto A))))))
;;   ;;   'eq)
;;   ;; (test-equal? "to NEW: had one, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 1 OLD) abs-nat single])))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 1 NEW) (() (goto A))))))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "to NEW: had many, send zero"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 2 OLD) abs-nat many])))
;;   ;;    (csa#-transition-effect #f #f null (list `((spawn-addr 2 NEW) (() (goto A))))))
;;   ;;   'not-gteq)
;;   ;; (test-equal? "had 1, NEW does not exist"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 1 OLD) abs-nat single])))
;;   ;;    (csa#-transition-effect #f #f null null))
;;   ;;   'eq)
;;   ;; (test-equal? "had many, NEW does not exist"
;;   ;;   (csa#-compare-new-messages
;;   ;;    (term (() () ([(spawn-addr 2 OLD) abs-nat many])))
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
  (check-equal? (compare-behavior (term (() (goto A (list-val (variant A) (variant B)))))
                                  (term (() (goto A (list-val (variant B)))))
                                  #t)
                'gt)
  (check-equal?
   (compare-behavior
    (term (((define-state (A) (m) (goto A)))         (goto A (list-val (variant B)))))
    (term (((define-state (A) (m) (goto A abs-nat))) (goto A (list-val (variant B)))))
    #t)
   'not-gteq)
  (check-equal?
   (compare-behavior
    (term (((define-state (A) (m) (goto A)))         (goto A (list-val (variant B)))))
    (term (((define-state (A) (m) (goto A abs-nat))) (goto A (list-val (variant B)))))
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
    [(list (list 'hash-val (list keys1 ...) (list vals1 ...))
           (list 'hash-val (list keys2 ...) (list vals2 ...)))
     (comp-result-and (compare-value-sets keys1 keys2)
                      (compare-value-sets vals1 vals2))]
    [_ (if (equal? v1 v2) 'eq 'not-gteq)]))

(module+ test
  (check-equal?
   (compare-value (term (variant A abs-nat))
                  (term (variant B abs-nat)))
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
    (compare-value `(record [a (list-val abs-nat)] [b abs-nat])
                   `(record [a (list-val)]         [b abs-nat]))
    'gt)
  (test-equal? "compare-value record 2"
    (compare-value `(record [a (list-val abs-nat)] [b abs-nat])
                   `(record [a (list-val abs-nat)] [b abs-nat]))
    'eq)
  (test-equal? "compare-value record 3"
    (compare-value `(record [a (list-val (variant A))] [b abs-nat])
                   `(record [a (list-val (variant B))] [b abs-nat]))
    'not-gteq)

  (test-equal? "compare-value variant 1"
    (compare-value `(variant A (list-val abs-nat) abs-nat)
                   `(variant A (list-val) abs-nat))
    'gt)
  (test-equal? "compare-value variant 2"
    (compare-value `(variant A (list-val abs-nat) abs-nat)
                   `(variant A (list-val abs-nat) abs-nat))
    'eq)
  (test-equal? "compare-value variant 3"
    (compare-value `(variant A (list-val) abs-nat)
                   `(variant A (list-val abs-nat) abs-nat))
    'lt)

  (test-equal? "compare-value list-val 1"
    (compare-value '(list-val abs-nat)
                   '(list-val))
    'gt)
  (test-equal? "compare-value list-val 2"
    (compare-value '(list-val abs-nat)
                   '(list-val abs-nat))
    'eq)
  (test-equal? "compare-value list-val 3"
    (compare-value '(list-val)
                   '(list-val abs-nat))
    'lt)
  (test-equal? "compare-value list-val 4"
    (compare-value '(list-val (variant A))
                   '(list-val (variant B)))
    'not-gteq)

  (test-equal? "compare-value hash-val 1"
    (compare-value '(hash-val () ())
                   '(hash-val () ()))
    'eq)
  (test-equal? "compare-value hash-val 2"
    (compare-value '(hash-val (abs-nat) ((variant A)))
                   '(hash-val () ()))
    'gt)
  (test-equal? "compare-value hash-val 3"
    (compare-value '(hash-val (abs-nat) ((variant A) (variant B)))
                   '(hash-val (abs-nat) ((variant A))))
    'gt)
  (test-equal? "compare-value hash-val 4"
    (compare-value '(hash-val ((variant A) (variant B)) (abs-nat))
                   '(hash-val ((variant A)) (abs-nat)))
    'gt)
  (test-equal? "compare-value hash-val 5"
    (compare-value '(hash-val (abs-nat) ((variant A)))
                   '(hash-val (abs-nat) ((variant A) (variant B))))
    'lt)
  (test-equal? "compare-value hash-val 6"
    (compare-value '(hash-val ((variant A)) (abs-nat))
                   '(hash-val ((variant A) (variant B)) (abs-nat)))
    'lt)
  (test-equal? "compare-value hash-val 7"
    (compare-value '(hash-val ((variant A)) (abs-nat))
                   '(hash-val ((variant B)) (abs-nat)))
    'not-gteq)

  (test-equal? "compare-value addresses 1"
    (compare-value `(marked (addr 1 0))
                   `(marked (addr 2 0)))
    'not-gteq)
  (test-equal? "compare-value addresses 3"
    (compare-value `(marked (addr 1 0))
                   `(marked (addr 1 0)))
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
;; given configuration; #f otherwise. Assumes the trigger will be a trigger that is enabled in a
;; configuration that can reach this config. Also assumes that internal receives that differ only in
;; multiplicity are the same for the purposes of this function.
(define (csa#-action-enabled? config trigger)
  ;; if it's not an internal messsage, or the received message will be available in the new config
  (match trigger
    [`(internal-receive ,addr ,message ,_)
     (findf (lambda (packet)
              (and (equal? (csa#-message-packet-address packet) addr)
                   (equal? (csa#-message-packet-value packet) message)))
            (csa#-config-message-packets config))]
    [`(timeout ,addr)
     (ormap get-timeout-handler-exp (csa#-behaviors-of config addr))]
    [`(external-receive ,marked-addr ,message)
     (findf (lambda (rec) (equal? (receptionist-marked-address rec) marked-addr))
            (csa#-config-receptionists config))]))

(module+ test
  (define enabled-action-test-config
    `(([(addr 0 0)
        (((define-state (A) (x) (goto A) ([timeout abs-nat] (goto A))))
         (goto A))]
       [(addr 1 0)
        (((define-state (A) (x) (goto A) ([timeout abs-nat] (goto A)))
          (define-state (B) (x) (goto B)))
         (goto B))])
      ()
      ([(addr 0 0) abs-nat many])
      ([Nat (marked (addr 0 0) 1)])))

  (test-true "enabled-action-test-config is valid config"
    (redex-match? csa# i# enabled-action-test-config))

  (test-not-false "Enabled internal receive"
    (csa#-action-enabled? enabled-action-test-config
                          '(internal-receive (addr 0 0) abs-nat single)))
  (test-false "Disabled internal receive"
    (csa#-action-enabled? enabled-action-test-config
                          '(internal-receive (addr 1 0) abs-nat single)))
  (test-not-false "Enabled timeout"
    (csa#-action-enabled? enabled-action-test-config
                          '(timeout (addr 0 0))))
  (test-false "Disabled timeout"
    (csa#-action-enabled? enabled-action-test-config
                          '(timeout (addr 1 0))))
  (test-not-false "Enabled external receive"
    (csa#-action-enabled? enabled-action-test-config
                          `(external-receive (marked (addr 0 0) 1) abs-nat)))
  (test-false "Disabled external receive"
    (csa#-action-enabled? enabled-action-test-config
                          `(external-receive (marked (addr 0 0) 2) abs-nat))))

;; ---------------------------------------------------------------------------------------------------
;; Debug helpers

(define (impl-config-without-state-defs config)
  (redex-let csa# ([(((any_addr (_ any_exp)) ...) ((any_addr-b ((_ any_exp-b) ...)) ...) any_msg any_recs)
                    config])
    (term (((any_addr any_exp) ...) ((any_addr-b (any_exp-b ...)) ...) any_msg any_recs))))

(define (impl-config-goto config)
  ;; NOTE: only suports single-actor impls for now
  (redex-let csa# ([(((a#int (_ e#))) any_blurred μ#) config])
             (term e#)))
