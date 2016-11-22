#lang racket

;; Abstract standard semantic domains for CSA#, and associated functions

(provide
 ;; Required by conformance checker
 (struct-out csa#-transition)
 csa#-messages-of-type
 csa#-enabled-internal-actions
 csa#-make-external-trigger
 csa#-abstract-config
 csa#-blur-config
 necessary-action?
 csa#-address-type
 csa#-address-strip-type
 ;; required for widening
 (struct-out csa#-transition-effect)
 csa#-transition-to-greater-config?
 csa#-eval-trigger
 csa#-apply-transition
 csa#-blur-and-duplicate-message

 ;; Required by conformance checker to select spawn-flag to blur; likely to change
 csa#-spawn-address?
 csa#-spawn-address-flag
 csa#-flags-that-know-externals

 ;; Required by APS#
 csa#-output-address
 csa#-output-message
 csa#-blur-addresses ; needed for blurring in APS#
 internals-in
 externals-in

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
 "csa.rkt"
 "sexp-helpers.rkt")

;; Abstract-interpretation version of CSA
(define-extended-language csa# csa-eval
  (i# (α# β# μ#))
  (α# ((a#int-precise b#) ...))
  (β# ((a#int-collective (b# ...)) ...)) ; blurred actors, represented by a set of abstract behaviors
  (b# ((Q# ...) e#)) ; behavior
  ;; TODO: refactor the packets to hold *un*typed addresses - will solve most of my address comparison
  ;; issues
  (μ# ((a#int v# m) ...)) ; message packets
  (m single many) ; m for "multiplicity"
  (Q# (define-state (q [x τ] ...) (x) e#)
      (define-state (q [x τ] ...) (x) e# [(timeout v#) e#]))
  (v# τa#
      (variant t v# ...)
      (record [l v#] ...)
      (folded τ v#)
      (* τ)
      (list-val v# ...)
      (vector-val v# ...)
      (hash-val v# ...))
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
  ;; H# = handler machine state (exp + outputs + loop outputs + spawns so far)
  (H# (e# ([a# v#] ...) ([a# v#] ...) ((a#int b#) ...)))
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
      (loop-context E#))
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
(define next-generated-address 100)

;; Returns an exhaustive list of abstract messages for the type of the given address
(define (csa#-messages-of-type type)
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
  [(messages-of-type/mf (Listof τ) _) ((* (Listof τ)))]
  [(messages-of-type/mf (Vectorof τ) _) ((* (Vectorof τ)))]
  [(messages-of-type/mf (Hash τ_1 τ_2) _) ((* (Hash τ_1 τ_2)))])

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
     (variant B (* String) (variant D)))))

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; TODO: give these structs better names

;; Represents the effects of a single handler-level transition of an actor, before the results are
;; applied to the pre-handler configuration. Used for the widening optimization.
(struct csa#-transition-effect (trigger behavior sends loop-sends spawns) #:transparent)

;; Represents a single handler-level transition of an actor. Trigger is the event that caused the
;; handler to run, outputs is the list of outputs to the external world that happened execution, and
;; final-config is the resulting abstract configuration.
;;
;; This is the result of applying a csa#-transition-effect
(struct csa#-transition
  (trigger ; follows trigger# above
   outputs ; list of abstract-addr/abstract-message 2-tuples
   loop-outputs ; list of abstract-addr/abstract-message 2-tuples
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
      (if (term (get-timeout-handler-exp/mf ,(actor-behavior actor)))
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
      (if (ormap (lambda (behavior) (term (get-timeout-handler-exp/mf ,behavior)))
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
     (match (term (get-timeout-handler-exp/mf ,behavior))
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
  (redex-let csa#
      ([((_ ... (define-state (q [x_q τ_q] ..._n) (x_m) e# any_timeout-clause ...) _ ...)
         (goto q v# ..._n))
        behavior])
    ;; TODO: deal with the case where x_m shadows an x_q
    (inject/H# (term (csa#-subst-n e# [x_m ,message] [x_q v#] ...)))))

;; Abstractly removes the entry in i# corresponding to the packet (a# v#), which will actually remove
;; it if its multiplicity is single, else leave it there if its multiplicity is many (because removing
;; a message from an abstract list of 0 or more yields a list of 0 or more).
(define-metafunction csa#
  config-remove-packet/mf : i# (a# v#) -> i#
  [(config-remove-packet/mf (any_precise any_blurred (any_pkt1 ... (a# v# single) any_pkt2 ...))
                            (a# v#))
   (any_precise any_blurred (any_pkt1 ... any_pkt2 ...))]
  ;; Case 2: if the multiplicity is not single, it must be many, so we just return the original config
  ;; because nothing is actually removed
  [(config-remove-packet/mf any_config _) any_config])

;; Returns the behavior's current timeout handler expression with all state arguments substituted in
;; if the current state has a timeout clause, else #f
(define-metafunction csa#
  get-timeout-handler-exp/mf : b# -> e# or #f
  [(get-timeout-handler-exp/mf ((_ ... (define-state (q [x_q τ_q] ..._n) _ _ [(timeout _) e#]) _ ...)
                                (goto q v# ..._n)))
   (csa#-subst-n e# [x_q v#] ...)]
  [(get-timeout-handler-exp/mf _) #f])

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
    [else
     (term (blurred-actor-behaviors-by-address/mf ,config ,address))]))

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
         (define all-final-states
           ;; Remove states stuck as a result of over-abstraction; we can assume these would never
           ;; happen at run-time
           (filter (negate stuck-at-empty-list-ref?)
                   (apply-reduction-relation* handler-step# handler-machine #:cache-all? #t)))
         (unless (andmap complete-handler-config? all-final-states)
           (error 'eval-handler
                  "Abstract evaluation did not complete\nInitial state: ~s\nFinal stuck states:~s"
                  handler-machine
                  (filter (negate complete-handler-config?) all-final-states)))
         (hash-set! eval-cache handler-machine all-final-states)
         all-final-states]
        [cached-results cached-results]))

    (for/list ([machine-state final-machine-states])
      ;; TODO: rename outputs to something like "transmissions", because some of them stay internal
      ;; to the configuration
      (match-define (list final-exp outputs loop-outputs spawns) machine-state)
      ;; TODO: check that there are no internal loop outputs, or refactor that code entirely
      (redex-let csa# ([(in-hole E# (goto q v#_param ...)) final-exp])
        (csa#-transition-effect
         trigger
         (term (,state-defs (goto q v#_param ...)))
         outputs
         loop-outputs
         spawns)))))

;; Returns #t if the given handler machine state is unable to step because of an over-approximation in
;; the abstraction (assumes that there are no empty vector/list/hash references in the actual running
;; progrm)
(define (stuck-at-empty-list-ref? h)
  (redex-let csa# ([(e# _ _ _) h])
    (or (redex-match? csa# (in-hole E# (list-ref   (list-val)   v#)) (term e#))
        (redex-match? csa# (in-hole E# (vector-ref (vector-val) v#)) (term e#))
        (redex-match? csa# (in-hole E# (hash-ref   (hash-val)   v#)) (term e#)))))

(module+ test
  (test-true "stuck config 1"
    (stuck-at-empty-list-ref? (inject/H# (term (vector-ref (vector-val) (* Nat))))))
  (test-true "stuck config 2"
    (stuck-at-empty-list-ref? (inject/H# (term (list-ref (list-val) (* Nat))))))
  (test-true "stuck config 3"
    (stuck-at-empty-list-ref? (inject/H# (term (hash-ref (hash-val) (* Nat)))))))

(define (complete-handler-config? c)
  (redex-match csa# ((in-hole E# (goto q v#_param ...)) any_output any_loop-output any_spawns) c))

(define (inject/H# exp)
  (redex-let csa#
             ([e# exp]
              [H# (term (,exp () () ()))])
             (term H#)))

(define abort-evaluation-param (make-parameter #f))

(define handler-step#
  (reduction-relation csa#
    #:domain H#

    ;; let, match, begin, send, goto
    (==> (begin v# e# e#_rest ...)
         (begin e# e#_rest ...)
         Begin1)
    (==> (begin v#)
         v#
         Begin2)

    (==> (case (* (Union _ ... [t τ ..._n] _ ...))
           [(t x ..._n) e#]
           _ ...)
         (csa#-subst-n e# [x (* τ)] ...)
         CaseWildcardSuccess)
    (==> (case (* (Union [t_val τ_val ...] ...))
           ;; Only fail if there is at least one more clause; type safety guarantees that at least one
           ;; clause matches
           [(t_1 x_1 ...) e#_1]
           [(t_2 x_2 ...) e#_2]
           [(t_rest x_rest ...) e#_rest] ...)
         (case (* (Union [t_val τ_val ...] ...))
           [(t_2 x_2 ...) e#_2]
           [(t_rest x_rest ...) e#_rest] ...)
         CaseWildcardFailure)
    (==> (case (variant t v# ..._n)
           [(t x ..._n) e#]
           _ ...)
         (csa#-subst-n e# [x v#] ...)
         CaseVariantSuccess)
    (==> (case (variant t v# ...)
           [(t_other x ...) e#]
           [(t_rest x_rest ...) e#_rest] ...)
         (case (variant t v# ...)
           [(t_rest x_rest ...) e#_rest] ...)
         (side-condition (not (equal? (term t) (term t_other))))
         CaseVariantFailure)

    ;; Let
    (==> (let ([x v#] ...) e#)
         (csa#-subst-n e# [x v#] ...)
         Let)

    ;; Records
    (==> (: (record _ ... [l v#] _ ...) l)
         v#
         RecordLookup)
    (==> (: (* (Record _ ... [l τ] _ ...)) l)
         (* τ)
         RecordWildcardLookup)
    (==> (! (record any_1 ... [l _] any_2 ...) [l v#])
         (record any_1 ... [l v#] any_2 ...)
         RecordUpdate)
    (==> (! (* (Record any_1 ... [l τ] any_2 ...)) [l v#])
         (* (Record any_1 ... [l τ] any_2 ...))
         RecordWildcardUpdate)

    ;; Recursive Types

    (==> (fold τ (* _))
         (* τ)
         FoldWildcard)
    (==> (fold τ v#)
         (folded τ v#)
         (side-condition (not (redex-match? csa# (* _) (term v#))))
         (side-condition (< (term (fold-depth/mf v#)) MAX-RECURSION-DEPTH))
         FoldPreMaxDepth)
    (==> (fold τ v#)
         (* τ)
         (side-condition (not (redex-match? csa# (* _) (term v#))))
         (side-condition (= (term (fold-depth/mf v#)) MAX-RECURSION-DEPTH))
         ;; We're currently not able to give any addresses in a "folded" past our maximum fold-depth a
         ;; sound abstraction if the address is an internal address or an external address observed by
         ;; the spec, so we take the easy way out here and just bail out if the value to be folded
         ;; contains *any* address.
         (side-condition (when (csa#-contains-address? (term v#)) ((abort-evaluation-param))))
         FoldAtMaxDepth)
    (==> (unfold τ (folded τ v#))
         v#
         Unfold)
    (==> (unfold τ (* (minfixpt X τ)))
         (* (type-subst τ X (minfixpt X τ)))
         UnfoldWildcard)

    ;; Primops
    (==> (primop (* Nat) (* Nat))
         (variant True)
         (side-condition (member (term primop) (list '< '<= '> '>= '=)))
         BinaryNumericPredicate1)
    (==> (primop (* Nat) (* Nat))
         (variant False)
         (side-condition (member (term primop) (list '< '<= '> '>= '=)))
         BinaryNumericPredicate2)

    (==> (primop (* Nat) (* Nat))
         (* Nat)
         (side-condition (member (term primop) (list '+ '- '* '/)))
         Arith)

    (==> (primop (* Nat))
         (* Nat)
         (side-condition (member (term primop) (list 'random 'ceiling)))
         UnaryNumericOp)

    (==> (and v#_1 v#_2)
         (csa#-and (canonicalize-boolean v#_1) (canonicalize-boolean v#_2))
         And)
    (==> (or v#_1 v#_2)
         (csa#-or (canonicalize-boolean v#_1) (canonicalize-boolean v#_2))
         Or)
    (==> (not v#)
         (csa#-not (canonicalize-boolean v#))
         Not)

    ;; For now, we're conservative and always assume both results are possible
    (==> (= τa#_1 τa#_2)
         (variant True)
         AddressEqualityTrue)
    (==> (= τa#_1 τa#_2)
         (variant False)
         AddressEqualityFalse)
    (==> (= (* String) (* String))
         (variant True)
         StringEqualityTrue)
    (==> (= (* String) (* String))
         (variant False)
         StringEqualityFalse)
    (==> (= (* Nat) (* Nat))
         (variant True)
         NatEqualityTrue)
    (==> (= (* Nat) (* Nat))
         (variant False)
         NatEqualityFalse)

    ;; Vectors, Lists, and Hashes

    (==> (list v# ...)
         (normalize-collection (list-val v# ...))
         ListEval)
    (==> (cons v#_new (list-val v# ...))
         (normalize-collection (list-val v#_new v# ...))
         Cons)
    (==> (cons v# (* (Listof τ)))
         (* (Listof τ))
         WildcardCons)
    (==> (list-ref (list-val _ ... v# _ ...) (* Nat))
         v#
         ListRef)
    (==> (list-ref (* (Listof τ)) (* Nat))
         (* τ)
         WildcardListRef)
    (==> (length (list-val v# ...))
         (* Nat)
         ListLength)
    (==> (length (* (Listof _)))
         (* Nat)
         WildcardListLength)
    (==> (vector v# ...)
         (normalize-collection (vector-val v# ...))
         VectorEval)
    (==> (vector-ref (vector-val _ .... v# _ ...) (* Nat))
         v#
         VectorRef)
    (==> (vector-ref (* (Vectorof τ)) (* Nat))
         (* τ)
         VectorWildcardRef)
    (==> (vector-take (vector-val v# ...) (* Nat))
         (vector-val v# ...)
         VectorTake)
    (==> (vector-take (* (Vectorof τ)) (* Nat))
         (* (Vectorof τ))
         VectorWildcardTake)
    (==> (vector-length (vector-val v# ...))
         (* Nat)
         VectorLength)
    (==> (vector-length (* (Vectorof τ)))
         (* Nat)
         VectorWildcardLength)
    (==> (vector-copy (vector-val v# ...) (* Nat) (* Nat))
         (vector-val v# ...)
         VectorCopy)
    (==> (vector-copy (* (Vectorof τ)) (* Nat) (* Nat))
         (* (Vectorof τ))
         VectorWildcardCopy)
    ;; TODO: figure out if the type is ever *not* big enough to also cover the other vector
    (==> (vector-append (vector-val v#_1 ...) (vector-val v#_2 ...))
         (normalize-collection (vector-val v#_1 ... v#_2 ...))
         VectorAppend)
    (==> (vector-append (* (Vectorof τ)) _)
         (* (Vectorof τ))
         VectorWildcardAppend1)
    (==> (vector-append _ (* (Vectorof τ)))
         (* (Vectorof τ))
         VectorWildcardAppend2)
    (==> (hash [v#_key v#_val] ...)
         (normalize-collection (hash-val v#_val ...))
         HashEval)
    (==> (hash-ref (hash-val v#_1 ... v# v#_2 ...) v#_key)
         (variant Just v#)
         HashRefSuccess)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Just (* τ_2))
         HashWildcardRefSuccess)
    (==> (hash-ref (hash-val v#_other ...) v#_key)
         (variant Nothing)
         HashRefFailure)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Nothing)
         HashWildcardRefFailure)
    (==> (hash-set (hash-val v#_1 ... v#_value v#_2 ...) v#_key v#_value)
         (hash-val v#_1 ... v#_value v#_2 ...)
         HashSetExists)
    (==> (hash-set (hash-val v#_current ...) v#_key v#_value)
         (normalize-collection (hash-val v#_current ... v#_value))
         (side-condition (not (member (term v#_value) (term (v#_current ...)))))
         HashSetNewItem)
    (==> (hash-set (* Hash τ_1 τ_2) v#_key v#_value)
         (* Hash τ_1 τ_2)
         HashWildcardSet)
    (==> (hash-has-key? (hash-val v# ...) v#_key)
         (variant True)
         HashHasKeyTrue)
    (==> (hash-has-key? (hash-val v# ...) v#_key)
         (variant False)
         HashHasKeyFalse)
    (==> (hash-has-key? (* (Hash τ_1 τ_2)) v#_key)
         (variant True)
         WildcardHashHasKeyTrue)
    (==> (hash-has-key? (* (Hash τ_1 τ_2)) v#_key)
         (variant False)
         WildcardHashHasKeyFalse)

    ;; Loops
    (==> (for/fold ([x_fold v#_fold])
                   ;; the "any" pattern lets us match both lists and vectors
                   ([x_item (any_constructor v#_1 ... v#_item v#_2 ...)])
           e#_body)
         (for/fold ([x_fold e#_unrolled-body])
                   ([x_item (any_constructor v#_1 ... v#_item v#_2 ...)])
           e#_body)
         (side-condition (member (term any_constructor) (list 'list 'vector)))
         (where e#_unrolled-body
                (loop-context (csa#-subst-n e#_body [x_fold v#_fold] [x_item v#_item])))
         ForLoop1)
    (==> (for/fold ([x_fold v#_fold])
                   ;; the "any" here lets us abstract over Listof/Vectorof
                   ([x_item (* (any_type τ))])
           e#_body)
         (for/fold ([x_fold e#_unrolled-body])
                   ([x_item (* (any_type τ))])
           e#_body)
         (side-condition (member (term any_type) (list 'Listof 'Vectorof)))
         (where e#_unrolled-body
                (loop-context (csa#-subst-n e#_body [x_fold v#_fold] [x_item (* τ)])))
         ForLoopWildcard1)
    (==> (for/fold ([x_fold v#_fold]) _ _)
         v#_fold
         ForLoop2)

    (==> (loop-context v#)
         v#
         RemoveLoopContext)

    (==> (sort-numbers-descending v#)
         v#
         Sort)

    ;; Communication

    (--> ((in-hole E# (send τa# v#)) (any_outputs ...) any_loop-outputs any_spawns)
         ((in-hole E# v#)            (any_outputs ... [a# (coerce v# τ)]) any_loop-outputs any_spawns)
         ;; regular send only occurs outside of loop contexts
         (side-condition (not (redex-match csa# (in-hole E# (loop-context E#_2)) (term E#))))
         (where τ (address-type/mf τa#))
         (where a# (address-strip-type/mf τa#))
         Send)
    (--> ((in-hole E# (loop-context (in-hole E#_2 (send τa# v#))))
          any_outputs
          any_loop-outputs
          any_spawns)
         ((in-hole E# (loop-context (in-hole E#_2 v#)))
          any_outputs
          ,(sort (remove-duplicates (append (term any_loop-outputs) (list (term [a# (coerce v# τ)]))))
                 sexp<?)
          any_spawns)
         (where τ (address-type/mf τa#))
         (where a# (address-strip-type/mf τa#))
         LoopSend)

    ;; Spawn
    (==> (spawn any_location τ e# Q# ...)
         (spawning a#int τ (csa#-subst-n e# [self (τ a#int)]) (csa#-subst/Q# Q# self (τ a#int)) ...)
         (where a#int (spawn-addr any_location NEW))
         SpawnStart)
    (--> ((in-hole E# (spawning a#int τ (in-hole E#_2 (goto q v# ...)) Q# ...))
          any_outputs
          any_loop-outputs
          (any_spawns ...))
         ((in-hole E# (τ a#int))
          any_outputs
          any_loop-outputs
          (any_spawns ... (a#int ((Q# ...) (goto q v# ...)))))
         SpawnFinish)

    ;; Debugging

    (==> (printf string v# ...)
         (* Nat)
         (side-condition (apply printf (term (string v# ...))))
         Printf)

    (==> (print-len (list v# ...))
         (* Nat)
         (side-condition (printf "~s" (length (term (v# ...)))))
         PrintLenList)
    (==> (print-len (* (Listof _)))
         (* Nat)
         (side-condition (printf "1"))
         PrintLenListWildcard)
    (==> (print-len (vector-val v# ...))
         (* Nat)
         (side-condition (printf "~s" (length (term (v# ...)))))
         PrintLenVector)
    (==> (print-len (* (Vectorof _)))
         (* Nat)
         (side-condition (printf "1"))
         PrintLenVectorWildcard)

    with
    [(--> ((in-hole E# old) any_outputs any_loop-outputs any_spawns)
          ((in-hole E# new) any_outputs any_loop-outputs any_spawns))
     (==> old new)]))

(module+ test
  (define (csa#-make-simple-test-config exp)
    (redex-let* csa# ([a# (term (init-addr 0))]
                      [b# (term (((define-state (Always) (long-unused-name) (begin ,exp (goto Always))))
                                 (begin ,exp (goto Always))))]
                      [α# (term ([a# b#]))]
                      [μ# (term ())])
                (term (α# μ# ()))))

  (check-not-false (redex-match csa# i# (csa#-make-simple-test-config (term (* Nat)))))

  (define-check (check-exp-steps-to? e1 e2)
    (define next-steps (apply-reduction-relation handler-step# (inject/H# e1)))
    (unless (equal? next-steps (list (inject/H# e2)))
      (fail-check (format "There were ~s next steps: ~s" (length next-steps) next-steps))))
  (define-check (check-exp-steps*-to? e1 e2)
    (define next-steps (apply-reduction-relation* handler-step# (inject/H# e1)))
    (unless (equal? next-steps (list (inject/H# e2)))
      (fail-check (format "There were ~s next steps: ~s" (length next-steps) next-steps))))

  (check-exp-steps*-to? (term (fold   (Union [A]) (variant A)))
                        (term (folded (Union [A]) (variant A))))
  (define nat-list-type (term (minfixpt NatList (Union (Null) (Cons Nat NatList)))))
  (check-exp-steps*-to? (term (fold   ,nat-list-type (variant Null)))
                        (term (folded ,nat-list-type (variant Null))))
  (check-exp-steps*-to? (term (fold   ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type))))
                        (term (folded ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type)))))
  (check-exp-steps*-to? (term (fold ,nat-list-type (variant Cons (* Nat)
                               (fold ,nat-list-type (variant Cons (* Nat)
                                 (fold ,nat-list-type (variant Null)))))))
                        (term (folded ,nat-list-type (variant Cons (* Nat) (* ,nat-list-type)))))

  (define-check (check-exp-steps-to-all exp expected-exp-results)
    (define next-steps (apply-reduction-relation* handler-step# (inject/H# exp)))
    ;; TODO: Pick up here on Wednesday
    (unless (equal? (list->set next-steps) (list->set (map inject/H# expected-exp-results)))
      (fail-check (format "Actual next steps were ~s, expected ~s"
                          next-steps
                          (map inject/H# expected-exp-results)))))

  ;; Equality checks
  (check-exp-steps-to-all (term (= (* String) (* String)))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all (term (= (* Nat) (* Nat)))
                          (list (term (variant True)) (term (variant False))))
  (check-exp-steps-to-all (term (= (* (Addr Nat)) (Nat (obs-ext 1))))
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
  ;; hash
  (check-exp-steps-to?
   (term (hash [(* Nat) (variant B)] [(* Nat) (variant A)]))
   (term (hash-val (variant A) (variant B))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (variant B) (variant C)) (* Nat) (variant A)))
   (term (hash-val (variant A) (variant B) (variant C))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (variant C) (variant B)) (* Nat) (variant A)))
   (term (hash-val (variant A) (variant B) (variant C))))
  (check-exp-steps-to?
   (term (hash-set (hash-val) (* Nat) (variant A)))
   (term (hash-val (variant A))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (variant B) (variant C)) (* Nat) (variant D)))
   (term (hash-val (variant B) (variant C) (variant D))))
  (check-exp-steps-to?
   (term (hash-set (hash-val (variant B) (variant C)) (* Nat) (variant B)))
   (term (hash-val (variant B) (variant C))))

  ;; Check for sorting of loop sends
  (check-equal?
   (apply-reduction-relation handler-step#
                             (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant A)))
                                    ()
                                    ([(obs-ext 1) (variant B)])
                                    ())))
   (list (term ((loop-context (variant A))
                ()
                ([(obs-ext 1) (variant A)]
                 [(obs-ext 1) (variant B)])
                ()))))
  (check-equal?
   (apply-reduction-relation handler-step#
                             (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
                                    ()
                                    ([(obs-ext 1) (variant A)])
                                    ())))
   (list (term ((loop-context (variant B))
                ()
                ([(obs-ext 1) (variant A)]
                 [(obs-ext 1) (variant B)])
                ()))))
  (check-equal?
   (apply-reduction-relation handler-step#
                             (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
                                    ()
                                    ([(obs-ext 1) (variant A)]
                                     [(obs-ext 1) (variant B)])
                                    ())))
   (list (term ((loop-context (variant B))
                ()
                ([(obs-ext 1) (variant A)]
                 [(obs-ext 1) (variant B)])
                ()))))
  (check-equal?
   (apply-reduction-relation handler-step#
                             (term ((loop-context (send ((Union [A] [B]) (obs-ext 1)) (variant B)))
                                    ()
                                    ()
                                    ())))
   (list (term ((loop-context (variant B))
                ()
                ([(obs-ext 1) (variant B)])
                ()))))

  ;; Check that internal addresses in the transmissions do not change the evaluation (had a problem
  ;; with this before)
  (check-equal?
   (apply-reduction-relation* handler-step# (inject/H# (term (begin (send (Nat (init-addr 1)) (* Nat)) (goto A)))))
   (list (term ((begin (goto A)) (((init-addr 1) (* Nat))) () ()))))

  (check-equal?
   (apply-reduction-relation* handler-step#
     (inject/H# (term (begin (spawn L Nat (goto A) (define-state (A) (x) (goto A))) (goto B)))))
   (list (term ((begin (goto B)) () () ([(spawn-addr L NEW) [((define-state (A) (x) (goto A))) (goto A)]]))))))

;; Puts the given abstract collection value (a list, vector, or hash) and puts it into a canonical
;; form
(define-metafunction csa#
  normalize-collection : v# -> v#
  [(normalize-collection (list-val v# ...))
   (list-val ,@(sort (remove-duplicates (term (v# ...))) sexp<?))]
  [(normalize-collection (vector-val v# ...))
   (vector-val ,@(sort (remove-duplicates (term (v# ...))) sexp<?))]
  [(normalize-collection (hash-val v# ...))
   (hash-val ,@(sort (remove-duplicates (term (v# ...))) sexp<?))])

;; i# csa#-transition-effect -> csa#-transition
(define (csa#-apply-transition config transition-effect)
  (define trigger (csa#-transition-effect-trigger transition-effect))
  (define addr (trigger-address trigger))
  ;; 1. If the handler was triggered by an internal message, remove the message
  (define with-trigger-message-removed
    (match trigger
      [`(internal-receive ,_ ,message) (term (config-remove-packet/mf ,config ,(list addr message)))]
      [_ config]))
  ;; 2. update the behavior
  (define new-behavior (csa#-transition-effect-behavior transition-effect))
  (define with-updated-behavior
    (if (precise-internal-address? addr)
        (update-behavior/precise with-trigger-message-removed addr new-behavior)
        (update-behavior/blurred with-trigger-message-removed addr new-behavior)))
  ;; 3. add spawned actors
  (define with-spawns (merge-new-actors with-updated-behavior (csa#-transition-effect-spawns transition-effect)))
  ;; 4. add sent messages
  ;; TODO: merge in the loop outputs, if I'm not checking that there are none
  (define-values (internal-sends external-sends)
    (partition internal-output? (csa#-transition-effect-sends transition-effect)))
  (define-values (internal-loop-sends external-loop-sends)
    (partition internal-output? (csa#-transition-effect-loop-sends transition-effect)))
  (csa#-transition trigger
                   external-sends
                   external-loop-sends
                   (merge-messages-into-config with-spawns internal-sends)))

;; Sets the behavior for the actor with the given precise address to the given expression
(define (update-behavior/precise config address behavior)
  (redex-let csa# ([((any_actors1 ...) (a# _) (any_actors2 ...))
                    (config-actor-and-rest-by-address config address)])
    (term ((any_actors1 ... (a# ,behavior) any_actors2 ...)
           ,(csa#-config-blurred-actors config)
           ,(csa#-config-message-packets config)))))

(define (update-behavior/blurred config address behavior)
  (term (update-behavior/blurred/mf ,config ,address ,behavior)))

;; Adds the given behavior as a possible behavior for the given blurred address in the given config
(define-metafunction csa#
  update-behavior/blurred/mf : i# a#int-collective b# -> i#
  [(update-behavior/blurred/mf
    (any_precise-actors
     (any_blurred1 ... (a#int-collective (b#_old ...)) any_blurred2 ...)
     any_packets)
    a#int-collective
    b#_new)
   (any_precise-actors
    (any_blurred1 ...
     (a#int-collective ,(remove-duplicates (term (b#_old ... b#_new))))
     any_blurred2 ...)
    any_packets)])

(module+ test
  (test-case "update-behavior/blurred/mf"
  (redex-let* csa# ([b#_1 '(() (goto A))]
                    [b#_2 '(() (goto B))]
                    [b#_3 '(() (goto C))]
                    [b#_4 '(() (goto D))]
                    [i# (term (()
                               (((blurred-spawn-addr 1) (b#_1 b#_2))
                                ((blurred-spawn-addr 2) (b#_3)))
                               ()))])
    (check-equal?
      (term (update-behavior/blurred/mf i# (blurred-spawn-addr 1) b#_2))
      (term i#))
    (check-equal?
     (term (update-behavior/blurred/mf i# (blurred-spawn-addr 1) b#_4))
     (term (()
            (((blurred-spawn-addr 1) (b#_1 b#_2 b#_4))
             ((blurred-spawn-addr 2) (b#_3)))
           ()))))))

;; Abstractly adds the set of new packets to the packet set in the given config.
(define (merge-messages-into-config config new-message-list)
  (redex-let csa# ([(any_actors any_blurred any_packets) config])
    (term (any_actors
           any_blurred
           ,(merge-messages-into-packet-set (term any_packets) new-message-list)))))

;; Abstractly adds the set of new packets to the given set.
(define (merge-messages-into-packet-set packet-set new-message-list)
  (redex-let csa# ([((a# v#) ...) new-message-list])
    (term ,(deduplicate-packets (append packet-set (term ((a# v# single) ...)))))))

(module+ test
  (check-equal?
   (merge-messages-into-config (term (() () ())) (list (term ((init-addr 0) (* Nat)))))
   (term (() () (((init-addr 0) (* Nat) single)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0) (* Nat) single))))
                       (list (term ((init-addr 0) (* Nat)))))
   (term (() () (((init-addr 0) (* Nat) many)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0) (* Nat) single))))
                       (list (term ((init-addr 1) (* Nat)))))
   (term (() () (((init-addr 0) (* Nat) single) ((init-addr 1) (* Nat) single)))))

  (check-equal?
   (merge-messages-into-config (term (()
                                      ()
                                      (((init-addr 1) (* (Addr Nat)) single)
                                       ((init-addr 1) (Nat (obs-ext 0)) single))))
                               (term (((init-addr 1) (* (Addr Nat))))))
   (term (()
          ()
          (((init-addr 1) (* (Addr Nat)) many)
           ((init-addr 1) (Nat (obs-ext 0)) single))))))

(define (merge-new-actors config new-actors)
  (redex-let csa# ([((any_actors ...) any_blurred any_messages) config])
             (term (,(append (term (any_actors ...)) new-actors)
                    any_blurred
                    any_messages))))

(module+ test
  (define new-spawn1
    (term ((spawn-addr foo NEW) (((define-state (A) (x) (goto A))) (goto A)))))
  (define init-actor1
    (term ((init-addr 0) (((define-state (B) (x) (goto B))) (goto B)))))
  (test-equal? "merge-new-actors test"
               (merge-new-actors
                (make-single-actor-abstract-config init-actor1)
                (list new-spawn1))
               (term ((,init-actor1 ,new-spawn1) () ()))))

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

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction csa#
  csa#-subst-n : e# (x v#) ... -> e#
  [(csa#-subst-n e#) e#]
  [(csa#-subst-n e# (x v#) any_rest ...)
   (csa#-subst-n (csa#-subst e# x v#) any_rest ...)])

(define-metafunction csa#
  csa#-subst : e# x v# -> e#
  [(csa#-subst x x v#) v#]
  [(csa#-subst x x_2 v#) x]
  ;; [(csa#-subst n x v) n]
  [(csa#-subst (* τ) _ _) (* τ)]
  [(csa#-subst τa# _ _) τa#]
  [(csa#-subst (spawn any_location τ e# Q# ...) self v#) (spawn any_location τ e# Q# ...)]
  [(csa#-subst (spawn any_location τ e# Q# ...) x v#)
    (spawn any_location τ (csa#-subst e# x v#) (csa#-subst/Q# Q# x v#) ...)]
  [(csa#-subst (goto q e# ...) x v#) (goto q (csa#-subst e# x v#) ...)]
  [(csa#-subst (send e#_1 e#_2) x v#)
   (send (csa#-subst e#_1 x v#) (csa#-subst e#_2 x v#))]
  [(csa#-subst (begin e# ...) x v#) (begin (csa#-subst e# x v#) ...)]
  [(csa#-subst (let ([x_let e#] ...) e#_body) x v#)
   (let ([x_let (csa#-subst e# x v#)] ...) e#_body)
   (where (_ ... x _ ...) (x_let ...))] ; check that x is in the list of bound vars
  [(csa#-subst (let ([x_let e#] ...) e#_body) x v#)
   (let ([x_let (csa#-subst e# x v#)] ...) (csa#-subst e#_body x v#))]
  [(csa#-subst (case e# [(t x_clause ...) e#_clause] ...) x v#)
   (case (csa#-subst e# x v#) (csa#-subst/case-clause [(t x_clause ...) e#_clause] x v#) ...)]
  [(csa#-subst (variant t e# ...) x v#) (variant t (csa#-subst e# x v#) ...)]
  [(csa#-subst (printf string e# ...) x v#) (printf string (csa#-subst e# x v#) ...)]
  [(csa#-subst (primop e# ...) x v#) (primop (csa#-subst e# x v#) ...)]
  [(csa#-subst (record [l e#] ...) x v#) (record [l (csa#-subst e# x v#)] ...)]
  [(csa#-subst (: e# l) x v#) (: (csa#-subst e# x v#) l)]
  [(csa#-subst (! e#_1 [l e#_2]) x v#)
   (! (csa#-subst e#_1 x v#) [l (csa#-subst e#_2 x v#)])]
  [(csa#-subst (fold τ e#) x v#) (fold τ (csa#-subst e# x v#))]
  [(csa#-subst (folded τ e#) x v#) (folded τ (csa#-subst e# x v#))]
  [(csa#-subst (unfold τ e#) x v#) (unfold τ (csa#-subst e# x v#))]
  [(csa#-subst (list e# ...) x v#) (list (csa#-subst e# x v#) ...)]
  [(csa#-subst (list-val e# ...) x v#) (list-val (csa#-subst e# x v#) ...)]
  [(csa#-subst (vector e# ...) x v#) (vector (csa#-subst e# x v#) ...)]
  [(csa#-subst (vector-val e# ...) x v#) (vector-val (csa#-subst e# x v#) ...)]
  [(csa#-subst (hash [e#_key e#_val] ...) x v#)
   (hash [(csa#-subst e#_key x v#) (csa#-subst e#_val x v#)] ...)]
  [(csa#-subst (hash-val v#_element ...) x v#) (hash-val (csa#-subst v#_element x v#) ...)]
  [(csa#-subst (hash-val v#_element ...) x v#) (hash-val (csa#-subst v#_element x v#) ...)]
  [(csa#-subst (for/fold ([x_1 e#_1]) ([x_2 e#_2]) e#_3) x_1 v#)
   (for/fold ([x_1 (csa#-subst e#_1 x_1 v#)]) ([x_2 (csa#-subst e#_2 x_1 v#)]) e#_3)]
  [(csa#-subst (for/fold ([x_1 e#_1]) ([x_2 e#_2]) e#_3) x_2 v#)
   (for/fold ([x_1 (csa#-subst e#_1 x_2 v#)]) ([x_2 (csa#-subst e#_2 x_2 v#)]) e#_3)]
  [(csa#-subst (for/fold ([x_1 e#_1]) ([x_2 e#_2]) e#_3) x v#)
   (for/fold ([x_1 (csa#-subst e#_1 x v#)]) ([x_2 (csa#-subst e#_2 x v#)]) (csa#-subst e#_3 x v#))]
  [(csa#-subst (loop-context e#) x v#) (loop-context (csa#-subst e# x v#))])

(define-metafunction csa#
  csa#-subst/case-clause : [(t x ...) e#] x v# -> [(t x ...) e#]
  [(csa#-subst/case-clause [(t x_1 ... x x_2 ...) e#] x v#)
   [(t x_1 ... x x_2 ...) e#]]
  [(csa#-subst/case-clause [(t x_other ...) e#] x v#)
   [(t x_other ...) (csa#-subst e# x v#)]])

(define-metafunction csa#
  csa#-subst/Q# : Q# x v# -> Q#
  ;; Case 1: no timeout, var is shadowed
  [(csa#-subst/Q# (define-state (q [x_q τ] ...) (x_m) e#) x v#)
   (define-state (q [x_q τ] ...) (x_m) e#)
   (where (_ ... x _ ...) (x_q ... x_m))]
  ;; Case 2: timeout, var shadowed by state param
  [(csa#-subst/Q# (define-state (q [x_q τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x v#)
   (define-state (q [x_q τ] ...) (x_m) e# [(timeout v#_t) e#_t])
   (where (_ ... x _ ...) (x_q ...))]
  ;; Case 3: timeout, var shadowed by message param
  [(csa#-subst/Q# (define-state (q [x_q τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x_m v#)
   (define-state (q [x_q τ] ...) (x_m) e# [(timeout v#_t) (csa#-subst e#_t x_m v#)])]
  ;; Case 4: timeout, no shadowing
  [(csa#-subst/Q# (define-state (q [x_q τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x v#)
   (define-state (q [x_q τ] ...) (x_m)
     (csa#-subst e# x v#)
     [(timeout v#_t) (csa#-subst e#_t x v#)])]
  ;; Case 5: no timeout, no shadowing
  [(csa#-subst/Q# (define-state (q [x_q τ] ...) (x_m) e#) x v#)
   (define-state (q [x_q τ] ...) (x_m) (csa#-subst e# x v#))])

(module+ test
  (check-equal? (term (csa#-subst/case-clause [(Cons p) (begin p x)] p (* Nat)))
                (term [(Cons p) (begin p x)]))
  (check-equal? (term (csa#-subst/case-clause [(Cons p) (begin p x)] x (* Nat)))
                (term [(Cons p) (begin p (* Nat))]))
  (check-equal? (term (csa#-subst (list (* Nat) x) x (* Nat)))
                (term (list (* Nat) (* Nat))))
  (check-equal? (term (csa#-subst (vector (* Nat) x) x (* Nat)))
                (term (vector (* Nat) (* Nat))))
  (test-equal? "spawn subst 1" (term (csa#-subst (spawn loc
                                         Nat
                                         (goto A self (* Nat))
                                         (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                                  self
                                  (Nat (init-addr 2))))
                (term (spawn loc
                             Nat
                             (goto A self (* Nat))
                             (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 2"
               (term (csa#-subst (spawn loc
                                         Nat
                                         (goto A self (* Nat))
                                         (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                                  x
                                  (Nat (init-addr 2))))
                (term (spawn loc
                             Nat
                             (goto A self (* Nat))
                             (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))))
  (test-equal? "spawn subst 3"
               (term (csa#-subst (spawn loc
                                         Nat
                                         (goto A self (* Nat))
                                         (define-state (A [s Nat] [a Nat]) (x) (goto A x y self)))
                                  y
                                  (Nat (init-addr 2))))
                (term (spawn loc
                             Nat
                             (goto A self (* Nat))
                             (define-state (A [s Nat] [a Nat]) (x) (goto A x (Nat (init-addr 2)) self))))))

(module+ test
  (check-equal? (term (csa#-subst (variant Foo (* Nat)) a (* Nat))) (term (variant Foo (* Nat)))))

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
  [(abstract-Q (define-state (q [x τ] ...) (x_m) e [(timeout n) e_timeout]) (a ...) natural_depth)
   (define-state (q [x τ] ...) (x_m)
     (abstract-e e (a ...) natural_depth)
     [(timeout (* Nat)) (abstract-e e_timeout (a ...) natural_depth)])])

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
   (normalize-collection (list-val (abstract-e v (a ...) natural_depth) ...))]
  [(abstract-e (list e ...) (a ...) natural_depth)
   (list (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (vector v ...) (a ...) natural_depth)
   (normalize-collection (vector-val (abstract-e v (a ...) natural_depth) ...))]
  [(abstract-e (vector e ...) (a ...) natural_depth)
   (vector (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (hash [v v_val] ...) (a ...) natural_depth)
   (normalize-collection (hash-val (abstract-e v_val (a ...) natural_depth) ...))]
  [(abstract-e (hash [e_key e_val] ...) (a ...) natural_depth)
   (hash [(abstract-e e_key (a ...) natural_depth) (abstract-e e_val (a ...) natural_depth)] ...)]
  [(abstract-e (for/fold ([x_1 e_1]) ([x_2 e_2]) e) (a ...) natural)
   (for/fold ([x_1 (abstract-e e_1 (a ...) natural)])
             ([x_2 (abstract-e e_2 (a ...) natural)])
     (abstract-e e (a ...) natural))])

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
                (term (hash-val (variant A) (variant B))))
  (check-equal? (term (abstract-e (hash [1 2] [3 4]) () 10))
                (term (hash-val (* Nat))))
  (check-equal? (term (abstract-e (hash) () 10))
                (term (hash-val)))
  (check-equal? (term (abstract-e (hash [1 (let ([x 1]) x)] [3 4]) () 10))
                (term (hash [(* Nat) (let ([x (* Nat)]) x)] [(* Nat) (* Nat)])))
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
  ;; 4. Merge blurred behaviors in
  (define updated-blurred-actors
    (add-blurred-behaviors (csa#-config-blurred-actors renamed-config) renamed-removed-actors))
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
     (list '(spawn-addr 1 OLD)))))

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
         (csa#-config-actor-by-address config (term (switch-spawn-flag/mf ,addr)))))
  (redex-let csa# ([(α# any_blurred μ#) config])
    (define-values (removed-actors remaining-actors)
      (partition should-be-removed? (csa#-config-actors config)))
    (list (term (,remaining-actors
                 ,(csa#-config-blurred-actors config)
                 ,(csa#-config-message-packets config)))
          removed-actors)))

(define-metafunction csa#
  switch-spawn-flag/mf : a#int -> a#int
  [(switch-spawn-flag/mf (spawn-addr any_loc NEW)) (spawn-addr any_loc OLD)]
  [(switch-spawn-flag/mf (spawn-addr any_loc OLD)) (spawn-addr any_loc NEW)])

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
;; Renames internal addresses in internals-to-bour and external addresses *not* in
;; relevant-externals to their respective imprecise forms
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
     (term (normalize-collection (,keyword ,@blurred-args)))]
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
        ([e# (term (hash-val (Nat (obs-ext 1))
                             (Nat (obs-ext 2))
                             (Nat (obs-ext 3))
                             (Nat (obs-ext 4))))])
      (term e#))
    null
    '((obs-ext 1) (obs-ext 3)))
   ;; Some reordering happens as a result of normalize-collection
   (term (hash-val (* (Addr Nat)) (Nat (obs-ext 1)) (Nat (obs-ext 3)))))

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
    `(vector-val ((Union [A] [B]) (blurred-spawn-addr 1))
                 ((Union [A] [B]) (obs-ext 3))
                 ((Union [A] [B]) (spawn-addr 2 OLD))
                 ((Union [A]) (blurred-spawn-addr 1))
                 ((Union [A]) (obs-ext 3))
                 ((Union [A]) (spawn-addr 2 OLD))
                 (* (Addr (Union [A] [B])))
                 (* (Addr (Union [A]))))))

;; Returns #t if the address is of the form (spawn-addr _ flag _), #f otherwise.
(define (has-spawn-flag? addr flag)
  (match addr
    [`(spawn-addr ,_ ,addr-flag)
     (equal? addr-flag flag)]
    [_ #f]))

;; β# (Listof (List a#int b#)) -> β#
;;
;; Adds each address/behavior pair in behaviors-to-add as possible behaviors in blurred-actors.
(define (add-blurred-behaviors blurred-actors behaviors-to-add)
  (for/fold ([blurred-actors blurred-actors])
            ([behavior-to-add behaviors-to-add])
    (term (add-blurred-behavior/mf ,blurred-actors ,behavior-to-add))))

;; Adds the given address/behavior pair as a possible behavior in the given set of blurred actors.
(define-metafunction csa#
  add-blurred-behavior/mf : β# (a#int b#) -> β#
  [(add-blurred-behavior/mf (any_1 ... (a#int (b#_old ...)) any_2 ...) (a#int b#_new))
   (any_1 ... (a#int ,(remove-duplicates (term (b#_old ... b#_new)))) any_2 ...)]
  [(add-blurred-behavior/mf (any ...) (a#int b#))
   (any ... (a#int (b#)))])

(module+ test
  (define behavior1
    (term (((define-state (A) (x) (goto A))) (goto A))))
  (define behavior2
    (term (((define-state (B) (r) (begin (send r (* Nat)) (goto B)))) (goto B))))
  (define behavior3
    (term (((define-state (C) (r) (begin (send r (* Nat)) (goto C)))) (goto C))))

  (test-begin
    (check-true (redex-match? csa# b# behavior1))
    (check-true (redex-match? csa# b# behavior2))
    (check-true (redex-match? csa# b# behavior3)))

  (test-equal? "add-blurred-behaviors"
    (add-blurred-behaviors (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2))
                                  ((blurred-spawn-addr 2) (,behavior3))))
                           (list (term ((blurred-spawn-addr 1) ,behavior3))
                                 (term ((blurred-spawn-addr 3) ,behavior3))
                                 (term ((blurred-spawn-addr 1) ,behavior1))))
    (term (((blurred-spawn-addr 1) (,behavior1 ,behavior2 ,behavior3))
           ((blurred-spawn-addr 2) (,behavior3))
           ((blurred-spawn-addr 3) (,behavior3))))))

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
             (redex-let csa# ([(any_addr any_value _) message]) (term (any_addr any_value many)))))
       (loop (append processed-messages (list new-message))
             remaining-without-duplicates)])))

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
  (redex-let csa# ([(α# _ ...) config])
             (term α#)))

;; Returns the list of blurred actors in the config
(define (csa#-config-blurred-actors config)
  (redex-let csa# ([(_ β# _) config])
    (term β#)))

;; Returns the configuration's set of in-flight message packets
(define (csa#-config-message-packets config)
  (redex-let csa# ([(_ _ μ#) config])
             (term μ#)))

(define (config-actor-and-rest-by-address config addr)
  (term (config-actor-and-rest-by-address/mf ,config ,addr)))

(define-metafunction csa#
  config-actor-and-rest-by-address/mf : i# a#int -> (([a# b#] ...) [a# b#] ([a# b#] ...))
  [(config-actor-and-rest-by-address/mf ((any_1 ... (name the-actor (a#int _)) any_2 ...) _ ...)
                                        a#int)
   ((any_1 ...) the-actor (any_2 ...))])

;; Returns the given precise actor with the given address, or #f if it's not in the given config
(define (csa#-config-actor-by-address config addr)
  (term (actor-by-address/mf ,(csa#-config-actors config) ,addr)))

(define-metafunction csa#
  actor-by-address/mf : α# a#int -> #f or [a# b#]
  [(actor-by-address/mf () _) #f]
  [(actor-by-address/mf ((a#int any_behavior) _ ...) a#int)
   (a#int any_behavior)]
  [(actor-by-address/mf (_ any_rest ...) a#int)
   (actor-by-address/mf (any_rest ...) a#int)])

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
  (redex-let* csa# ([(a#int _) a])
    (term a#int)))

(define (csa#-blurred-actor-address a)
  (redex-let csa# ([(a#int _) a])
    (term a#int)))

(define (csa#-blurred-actor-behaviors a)
  (redex-let csa# ([(_ (b# ...)) a])
    (term (b# ...))))

;; (a#int v# multiplicity) -> (a#int v#)
(define (csa#-packet-entry->packet entry)
  (redex-let csa# ([(a#int v# _) entry])
    (term (a#int v#))))

(define (csa#-message-packet-address packet)
  (first packet))

(define (csa#-message-packet-value packet)
  (second packet))

(define csa#-output-address car)

(define csa#-output-message cadr)

;; (a# b#) -> b#
(define (actor-behavior actor)
  (second actor))

;; Returns the behaviors of the actor for the indicated collective OR atomic address
(define (csa#-behaviors-of config addr)
  (term (csa#-behaviors-of/mf ,config ,addr)))

(define-metafunction csa#
  csa#-behaviors-of/mf : i# a#int -> (b# ...)
  [(csa#-behaviors-of/mf i# a#int-precise)
   ,(list (actor-behavior (csa#-config-actor-by-address (term i#) (term a#int-precise))))]
  [(csa#-behaviors-of/mf i# a#int-collective)
   ,(csa#-blurred-actor-behaviors
     (findf (lambda (a) (equal? (csa#-blurred-actor-address a) (term a#int-collective)))
            (csa#-config-blurred-actors (term i#))))])

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
(define-metafunction csa#
  blurred-actor-behaviors-by-address/mf : i# a#int -> (b# ...)
  [(blurred-actor-behaviors-by-address/mf (_ (_ ... (a#int any_behaviors) _ ...) _) a#int)
   any_behaviors])

(module+ test
  (test-case "Blurred actor behaviors by address"
    (redex-let csa# ([i# (term (()
                                (((blurred-spawn-addr 1) ())
                                 ((blurred-spawn-addr 2) ((() (goto A)))))
                                ()))])
      (check-equal? (term (blurred-actor-behaviors-by-address/mf i# (blurred-spawn-addr 2)))
                    (list (term (() (goto A))))))))

;; Returns the state definitions of the given behavior
(define (behavior-state-defs behavior)
  (first behavior))

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
  (redex-match? csa# (a#int _) output))

(module+ test
  (check-true (internal-output? (term ((init-addr 1) (* Nat)))))
  (check-false (internal-output? (term ((obs-ext 2) (* Nat))))))

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
  coerce : v# τ -> v#
  ;; wildcard
  [(coerce (* _) τ) (* τ)]
  ;; addresses
  [(coerce (_ (init-addr natural)) (Addr τ))
   (τ (init-addr natural))]
  [(coerce (_ (spawn-addr any_loc spawn-flag)) (Addr τ))
   (τ (spawn-addr any_loc spawn-flag))]
  [(coerce (_ (blurred-spawn-addr any_loc)) (Addr τ))
   (τ (blurred-spawn-addr any_loc))]
  [(coerce (_ (obs-ext natural)) (Addr τ))
   (τ (obs-ext natural))]
  ;; variants and records
  [(coerce (variant t v# ..._n) (Union _ ... [t τ ..._n] _ ...))
   (variant t (coerce v# τ) ...)]
  [(coerce (record [l v#] ..._n) (Record [l τ] ..._n))
   (record [l (coerce v# τ)] ...)]
  ;; fold
  [(coerce (folded _ v#) (minfixpt X τ))
   (folded (minfixpt X τ) (coerce v# (type-subst τ X (minfixpt X τ))))]
  ;; lists, vectors, and hashes
  [(coerce (list-val v# ...) (Listof τ))
   (normalize-collection (list-val (coerce v# τ) ...))]
  [(coerce (vector-val v# ...) (Vectorof τ))
   (normalize-collection (vector-val (coerce v# τ) ...))]
  [(coerce (hash-val v# ...) (Hash _ τ))
   (normalize-collection (hash-val (coerce v# τ) ...))])

(module+ test
  (test-equal? "coerce wildcard 1" (term (coerce (* Nat) Nat)) (term (* Nat)))
  (test-equal? "coerce wildcard 2"
    (term (coerce (* (Addr (Union [A] [B]))) (Addr (Union [A]))))
    (term (* (Addr (Union [A])))))
  (test-equal? "coerce init-addr"
    (term (coerce ((Union [A] [B]) (init-addr 1)) (Addr (Union [A]))))
    (term ((Union [A]) (init-addr 1))))
  (test-equal? "coerce spawn-addr"
    (term (coerce ((Union [A] [B]) (spawn-addr 1 OLD)) (Addr (Union [A]))))
    (term ((Union [A]) (spawn-addr 1 OLD))))
  (test-equal? "coerce blurred-spawn-addr"
    (term (coerce ((Union [A] [B]) (blurred-spawn-addr 1)) (Addr (Union [A]))))
    (term ((Union [A]) (blurred-spawn-addr 1))))
  (test-equal? "coerce obs-ext"
    (term (coerce ((Union [A] [B]) (obs-ext 1)) (Addr (Union [A]))))
    (term ((Union [A]) (obs-ext 1))))
  (test-equal? "coerce variant"
    (term (coerce (variant Z (* (Addr (Union [A] [B])))) (Union [Z (Addr (Union [A]))])))
    (term (variant Z (* (Addr (Union [A]))))))
  (test-equal? "coerce record"
    (term (coerce (record [foo (* (Addr (Union [A] [B])))]) (Record [foo (Addr (Union [A]))])))
    (term (record [foo (* (Addr (Union [A])))])))
  (test-equal? "coerce fold"
    (term (coerce (folded (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A] [B])) AddrList]))
                          (* (Union [Empty]
                                    [Cons (Addr (Union [A] [B]))
                                          (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A] [B])) AddrList]))])))
                  (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))))
    (term (folded (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))
                  (* (Union [Empty]
                            [Cons (Addr (Union [A]))
                                  (minfixpt AddrList (Union [Empty] [Cons (Addr (Union [A])) AddrList]))])))))
  (test-equal? "coerce list"
    (term (coerce (list-val (* (Addr (Union [A] [B]))) (* (Addr (Union [A]))))
                  (Listof (Addr (Union [A])))))
    (term (list-val (* (Addr (Union [A]))))))
  (test-equal? "coerce vector"
    (term (coerce (vector-val (* (Addr (Union [A] [B]))) (* (Addr (Union [A]))))
                  (Vectorof (Addr (Union [A])))))
    (term (vector-val (* (Addr (Union [A]))))))
  (test-equal? "coerce hash"
    (term (coerce (hash-val (* (Addr (Union [A] [B]))) (* (Addr (Union [A]))))
                  (Hash Nat (Addr (Union [A])))))
    (term (hash-val (* (Addr (Union [A])))))))

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

;; Returns the list of all external addresses in the given term
(define (externals-in the-term)
  (remove-duplicates (term (externals-in/mf ,the-term))))

(define-metafunction csa#
  externals-in/mf : any -> (a#ext ...)
  [(externals-in/mf a#ext) (a#ext)]
  [(externals-in/mf (any ...))
   (any_addr ... ...)
   (where ((any_addr ...) ...) ((externals-in/mf any) ...))]
  [(externals-in/mf _) ()])

(module+ test
  (check-same-items?
   (externals-in (term ((Nat (obs-ext 1))
                        (Nat (obs-ext 2))
                        (Nat (obs-ext 2))
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
;; Tests for use during widening

;; NOTE: for various comparisons here, I need to record if a transition takes the config to a new
;; configuration that is greater than the old one (in terms of the abstract interpretation), the same
;; as the old one, or neither of those. I represent those results with 'gt, 'eq, and 'not-gteq,
;; respectively

;; i# csa#-transition-effect -> Boolean
;;
;; Returns #t if the transition effect results in a configuration strictly larger than the given one
(define (csa#-transition-to-greater-config? i transition-result)
  ;; If any spawned actor has a behavior different than an existing current atomic actor for the
  ;; same spawn location, throw this effect out. Blurring makes this step lead to a state that
  ;; might not be greater than the current one
  (define spawn-behavior-comp (csa#-transition-effect-compare-spawn-behavior transition-result i))

  ;; if any internal address mentioned in these effects has been blurred into a collective actor
  ;; since we ran this transition, just throw the transition away. The same transition with the
  ;; blurred instance of that address would have been picked up and enqueued after the blurring
  ;; action
  (define nonex-address
    (if (csa#-transition-effect-has-nonexistent-addresses? transition-result i) 'not-gteq 'eq))

  (define new-message-comp (csa#-compare-new-messages i transition-result))

  ;; If the transition was on an atomic actor, then the new behavior must be the same as the old
  ;; one
  (define self-behavior-comp (csa#-actor-compare-behavior i transition-result))

  ;; The action must be repeatable (timeouts are always repeatable in the same behavior, but an
  ;; internal message is only repeatable if there is another in the queue)
  (define repeatable-comp (if (csa#-repeatable-action? i transition-result) 'eq 'not-gteq))

  ;; TODO: also account for the case where growth happens by expanding the set of receptionists

  (define all-comparisons
    (list spawn-behavior-comp nonex-address new-message-comp self-behavior-comp repeatable-comp))
  ;; nothing is not-gteq, at least one is gt
  (and (andmap (negate (curry eq? 'not-gteq)) all-comparisons)
       (ormap (curry eq? 'gt) all-comparisons)))

;; Returns 'gt if the behaviors of the effect's spawn would make for a greater config, 'eq for the
;; same config (i.e. no effect), and 'not-gteq otherwise
(define (csa#-transition-effect-compare-spawn-behavior transition-result i)
  (for/fold ([comp-result 'eq])
            ([spawn (csa#-transition-effect-spawns transition-result)])
    (define spawn-addr (first spawn))
    (define existing-addr `(spawn-addr ,(second spawn-addr) OLD))
    (define collective-addr `(blurred-spawn-addr ,(second spawn-addr)))
    (define new-behavior (second spawn))
    (comp-result-and
     comp-result
     (match (csa#-config-actor-by-address i existing-addr)
       [#f 'not-gteq]
       [(list _ existing-behavior)
        (cond
          [(not (equal? existing-behavior new-behavior))
           'not-gteq]
          [else
           (match (csa#-config-collective-actor-by-address i collective-addr)
             [#f 'gt]
             [collective-actor
              (if (member new-behavior (csa#-blurred-actor-behaviors collective-actor))
                  'eq
                  'gt)])])]))))

(module+ test
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
  (test-equal? "effect matches existing spawn behavior, no blurred version"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            (list '((spawn-addr third-loc NEW) (() (goto A)))))
    spawn-behavior-change-test-config)
   'gt)
  (test-equal? "effect matches existing spawn behavior, blurred behavior also exists"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            (list '((spawn-addr the-loc NEW) (() (goto A)))))
    spawn-behavior-change-test-config)
   'eq)
  (test-equal? "effect matches existing spawn behavior, blurred actor with other behavior exists"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            (list '((spawn-addr second-loc NEW) (() (goto A)))))
    spawn-behavior-change-test-config)
   'gt)
  (test-equal? "effect changes existing spawn behavior"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            (list '((spawn-addr the-loc NEW) (() (goto C)))))
    spawn-behavior-change-test-config)
   'not-gteq)
  (test-equal? "config has no actor for corresponding spawn"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            (list '((spawn-addr other-loc NEW) (() (goto C)))))
    spawn-behavior-change-test-config)
   'not-gteq)
  (test-equal? "effect has no spawns"
   (csa#-transition-effect-compare-spawn-behavior
    (csa#-transition-effect '(timeout/empty-queue (init-addr 0))
                            '(() (goto B))
                            null
                            null
                            null)
    spawn-behavior-change-test-config)
   'eq))

;; comparison-result comparison-result -> comparison-result
(define (comp-result-and c1 c2)
  (cond
    [(or (eq? c1 'not-gteq) (eq? c2 'not-gteq))
     'not-gteq]
    [(or (eq? c1 'gt) (eq? c2 'gt))
     'gt]
    [else 'eq]))

(module+ test
  (test-equal? "comp-result-and gt eq" (comp-result-and 'gt 'eq) 'gt)
  (test-equal? "comp-result-and not-gteq eq" (comp-result-and 'not-gteq 'eq) 'not-gteq)
  (test-equal? "comp-result-and not-gteq gt" (comp-result-and 'not-gteq 'gt) 'not-gteq)
  (test-equal? "comp-result-and gt eq 2" (comp-result-and 'eq 'gt) 'gt)
  (test-equal? "comp-result-and not-gteq eq 2" (comp-result-and 'eq 'not-gteq) 'not-gteq)
  (test-equal? "comp-result-and not-gteq gt 2" (comp-result-and 'gt 'not-gteq) 'not-gteq))

;; Returns #t if the transition effect contains any internal addresses that no longer refer
;; to actors (atomic or collective), other than those referring to spawns of the effect
(define (csa#-transition-effect-has-nonexistent-addresses? effect config)
  (define effect-term
    (match-let ([(csa#-transition-effect e1 e2 e3 e4 e5) effect])
      (list e1 e2 e3 e4 e5)))
  (define all-internal-effect-addresses
    (filter csa#-internal-address? (csa#-contained-addresses effect-term)))
  (define all-current-and-new-spawn-addresses
    (append
     (map first (csa#-config-actors config))
     (map first (csa#-config-blurred-actors config))
     (map first (csa#-transition-effect-spawns effect))))
  (not (andmap (curryr member all-current-and-new-spawn-addresses) all-internal-effect-addresses)))

(module+ test
  (define old-address-test-config
    (redex-let csa# ([i#
                      (term
                       (([(spawn-addr the-loc OLD)
                          (() (goto A))]
                         [(init-addr 0)
                          (() (goto A))])
                        ([(blurred-spawn-addr the-loc)
                          ((() (goto A)))])
                        ()))])
      (term i#)))
  (test-false "nonexistent address: none"
    (csa#-transition-effect-has-nonexistent-addresses?
     (csa#-transition-effect '(timeout/empty-queue (init-addr 0)) '(() (goto A)) null null null)
     old-address-test-config))
  (test-not-false "nonexistent address: atomic"
    (csa#-transition-effect-has-nonexistent-addresses?
     (csa#-transition-effect '(timeout/empty-queue (spawn-addr other-loc OLD)) '(() (goto A)) null null null)
     old-address-test-config))
  (test-not-false "nonexistent address: collective"
    (csa#-transition-effect-has-nonexistent-addresses?
     (csa#-transition-effect '(timeout/empty-queue (blurred-spawn-addr other-loc)) '(goto A) null null null)
     old-address-test-config))
  (test-false "nonexistent address: address from a new spawn"
    (csa#-transition-effect-has-nonexistent-addresses?
     (csa#-transition-effect '(timeout/empty-queue (blurred-spawn-addr the-loc))
                             '(goto A)
                             null
                             null
                             '([(spawn-addr the-loc NEW) (() (goto A (spawn-addr the-loc NEW)))]))
     old-address-test-config))
  (test-false "nonexistent address: external address"
    (csa#-transition-effect-has-nonexistent-addresses?
     (csa#-transition-effect '(external-receive (init-addr 0) (Nat (obs-ext 1))) '(goto A) null null null)
     old-address-test-config)))

;; Returns true if the given expression contains *any* address
(define (csa#-contains-address? e)
  (not (empty? (csa#-contained-addresses e))))

;; Returns the list of all addresses in the given term (possibly with duplicates)
(define (csa#-contained-addresses t)
  (term (csa#-contained-addresses/mf ,t)))

(define-metafunction csa#
  csa#-contained-addresses/mf : any -> (a# ...)
  [(csa#-contained-addresses/mf a#) (a#)]
  [(csa#-contained-addresses/mf (any ...))
   (any_addr ... ...)
   (where ((any_addr ...) ...) ((csa#-contained-addresses/mf any) ...))]
  [(csa#-contained-addresses/mf _) ()])

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

(define (csa#-internal-address? a)
  (redex-match? csa# a#int a))

(module+ test
  (check-true (csa#-internal-address? `(init-addr 0)))
  (check-true (csa#-internal-address? `(spawn-addr the-loc NEW)))
  (check-true (csa#-internal-address? `(blurred-spawn-addr the-loc)))
  (check-false (csa#-internal-address? `(* (Addr Nat))))
  (check-false (csa#-internal-address? `(obs-ext 1))))


;; Returns 'gt if any of the transmissions sent by the transition result lead to a greater config
;; (because they were never sent before or only sent as one-ofs); 'eq otherwise
(define (csa#-compare-new-messages i transition-result)
  (define existing-packets (csa#-config-message-packets i))
  (if
   (for/or ([transmission (append (csa#-transition-effect-sends transition-result)
                                  (csa#-transition-effect-loop-sends transition-result))])
     (define many-of-packet `(,(first transmission) ,(second transmission) many))
     (not (member many-of-packet existing-packets)))
   'gt
   'eq))

(module+ test
  (define new-message-test-config
    (term (()
           ()
           ([(init-addr 1) (* Nat) single]
            [(init-addr 2) (* Nat) many]))))
  (test-equal? "new message from regular sends"
    (csa#-compare-new-messages
     new-message-test-config
     (csa#-transition-effect #f #f (list `((init-addr 3) (* Nat))) null null))
    'gt)
  (test-equal? "new message from loop sends"
    (csa#-compare-new-messages
     new-message-test-config
     (csa#-transition-effect #f #f null (list `((init-addr 3) (* Nat))) null))
    'gt)
  (test-equal? "many-of message from regular sends"
    (csa#-compare-new-messages
     new-message-test-config
     (csa#-transition-effect #f #f (list `((init-addr 1) (* Nat))) null null))
    'gt)
  (test-equal? "many-of message from loop sends"
    (csa#-compare-new-messages
     new-message-test-config
     (csa#-transition-effect #f #f null (list `((init-addr 1) (* Nat))) null))
    'gt)
  (test-equal? "no new messages message from loop sends"
    (csa#-compare-new-messages
     new-message-test-config
     (csa#-transition-effect #f #f (list `((init-addr 2) (* Nat)))  (list `((init-addr 2) (* Nat))) null))
    'eq))

(define (csa#-actor-compare-behavior config transition-result)
  (define addr (trigger-address (csa#-transition-effect-trigger transition-result)))
  (define new-behavior (csa#-transition-effect-behavior transition-result))
  (define old-behaviors (csa#-behaviors-of config addr))

  (if (member new-behavior old-behaviors)
      'eq
      (if (precise-internal-address? addr)
          'not-gteq
          'gt)))

(module+ test
  (test-equal? "actor-compare-behavior: new atomic behavior"
    (csa#-actor-compare-behavior
     behavior-test-config
     (csa#-transition-effect `(timeout/empty-queue (init-addr 1)) '(() (goto D)) null null null))
    'not-gteq)
  (test-equal? "actor-compare-behavior: old atomic behavior"
    (csa#-actor-compare-behavior
     behavior-test-config
     (csa#-transition-effect `(timeout/empty-queue (init-addr 1)) '(() (goto A)) null null null))
    'eq)
  (test-equal? "actor-compare-behavior: new collective behavior"
    (csa#-actor-compare-behavior
     behavior-test-config
     (csa#-transition-effect `(timeout/empty-queue (blurred-spawn-addr 2)) '(() (goto D)) null null null))
    'gt)
  (test-equal? "actor-compare-behavior: old collective behavior"
    (csa#-actor-compare-behavior
     behavior-test-config
     (csa#-transition-effect `(timeout/empty-queue (blurred-spawn-addr 2)) '(() (goto B)) null null null))
    'eq))

;; Returns #t if the action represented by the effect's trigger can happen again after applying the
;; given transition effect to the config, assuming the transition effect transitions the actor to the
;; exact same behavior
(define (csa#-repeatable-action? config transition-effect)
  ;; if it's not an internal messsage, or the received message will be available in the new config
  (match (csa#-transition-effect-trigger transition-effect)
    [`(internal-receive ,addr ,message)
     ;; the message is in the effects, or it's in the config with a many-of multiplicity
     (or (member (list addr message) (append (csa#-transition-effect-sends transition-effect)
                                             (csa#-transition-effect-loop-sends transition-effect)))
         (member (list addr message 'many) (csa#-config-message-packets config)))]
    [_ #t]))

(module+ test
  ;; timeout, internal receive repeatable (in effects), internal repeatable (many-of in config),
  ;; internal not repeatable
  (define repeatable-action-test-config
    (redex-let csa# ([i# `(() () ([(init-addr 0) (* Nat) many] [(init-addr 1) (* Nat) single]))])
      (term i#)))
  (define (make-trigger-only-effect trigger)
    (csa#-transition-effect trigger '(() (goto A)) null null null))
  (test-false "Not repeatable action"
    (csa#-repeatable-action? repeatable-action-test-config
                             (make-trigger-only-effect '(internal-receive (init-addr 1) (* Nat)))))
  (test-not-false "Repeatable timeout"
    (csa#-repeatable-action? repeatable-action-test-config
                             (make-trigger-only-effect '(timeout/empty-queue (init-addr 1)))))
  (test-not-false "Repeatable internal receive (many-of message)"
    (csa#-repeatable-action? repeatable-action-test-config
                             (make-trigger-only-effect '(internal-receive (init-addr 0) (* Nat)))))
  (test-not-false "Repeatable internal receive (from effect)"
    (csa#-repeatable-action? repeatable-action-test-config
                             (csa#-transition-effect '(internal-receive (init-addr 1) (* Nat))
                                                     '(() (goto A))
                                                     (list `((init-addr 1) (* Nat)))
                                                     null
                                                     null))))

;; Blurs the destination address of the given message and ensures it is represented as a "many-of"
;; value in the config (assuming at least one instance of the message already exists)
(define (csa#-blur-and-duplicate-message impl message)
  (term (csa#-blur-and-duplicate-message/mf ,impl ,message)))

(define-metafunction csa#
  csa#-blur-and-duplicate-message/mf : i# [a# v#] -> i#
  [(csa#-blur-and-duplicate-message/mf
    (any_atomic any_collective (any_msg1 ... [(blurred-spawn-addr any_loc) v# _] any_msg2 ...))
    [(spawn-addr any_loc _) v#])
   (any_atomic any_collective (any_msg1 ... [(blurred-spawn-addr any_loc) v# many] any_msg2 ...))])

(module+ test
  (test-equal? "blur and duplicate message"
    (csa#-blur-and-duplicate-message
     (term (() () ([(blurred-spawn-addr the-loc) (* Nat) single])))
     (term [(spawn-addr the-loc NEW) (* Nat)]))
    (term (() () ([(blurred-spawn-addr the-loc) (* Nat) many])))))

;; ---------------------------------------------------------------------------------------------------
;; Debug helpers

(define (impl-config-without-state-defs config)
  (redex-let csa# ([(((a#int (_ e#)) ...) ((a#int_b ((_ e#_b) ...)) ...) μ#) config])
             (term (((a#int e#) ...) ((a#int_b (e#_b ...)) ...) μ#))))

(define (impl-config-goto config)
  ;; NOTE: only suports single-actor impls for now
  (redex-let csa# ([(((a#int (_ e#))) any_blurred μ#) config])
             (term e#)))
