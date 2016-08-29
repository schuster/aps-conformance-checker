#lang racket

;; Abstract standard semantic domains for CSA#, and associated functions

(provide
 ;; Required by conformance checker
 (struct-out csa#-transition)
 csa#-messages-of-address-type
 csa#-handle-external-message
 csa#-handle-all-internal-actions
 csa#-abstract-config
 csa#-blur-config
 necessarily-enabled?

 ;; Required by conformance checker to select spawn-flag to blur; likely to change
 csa#-spawn-address?
 csa#-spawn-address-flag
 csa#-flags-that-know-externals

 ;; Required by APS#
 csa#-output-address
 csa#-output-message
 csa#-blur-internal-addresses ; needed for blurring in APS#
 internals-in
 externals-in

 ;; Required by APS#; should go into a "common" language instead
 csa#
 csa#-abstract-address
 same-internal-address-without-type?
 same-external-address-without-type?
 type-join

 ;; Testing helpers
 make-single-actor-abstract-config

 ;; Debug helpers
 impl-config-without-state-defs
 impl-config-goto)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "csa.rkt")

;; Abstract-interpretation version of CSA
(define-extended-language csa# csa-eval
  (K# (α# β# μ#))
  (α# (α#n ...))
  (β# ((a#int (b# ...)) ...)) ; blurred actors, represented by a set of abstract behaviors
  (α#n (a#int b#))
  (b# ((S# ...) e#)) ; behavior
  ;; TODO: refactor the packets to hold *un*typed addresses - will solve most of my address comparison
  ;; issues
  (μ# ((a#int v# multiplicity) ...)) ; message packets
  (multiplicity 1 *)
  (S# (define-state (s [x τ] ...) (x) e#)
      (define-state (s [x τ] ...) (x) e# [(timeout v#) e#]))
  (v# a#
      (variant t v# ...)
      (record [l v#] ...)
      (folded τ v#)
      (* τ)
      (list v# ...)
      (vector v# ...)
      (hash v# ...))
  (e# (spawn any_location τ e# S# ...)
      (spawning a#int τ e# S# ...)
      (goto s e# ...)
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
      (hash)
      (for/fold ([x e#]) ([x e#]) e#)
      (loop-context e#)
      x
      v#)
  (a# a#int a#ext) ; internal and external addresses
  (a#int a#int-precise
         (blurred-spawn-addr any_location τ))
  (a#int-precise (init-addr natural τ)
                 (spawn-addr any_location spawn-flag τ))
  ;; OLD means it is a unique actor that existed before the current handler was run, NEW means it was
  ;; spawned in the current handler (should all be OLD between runs, after blur/canonicalize)
  (spawn-flag NEW OLD)
  (a#ext
   (* (Addr τ)) ; unobserved address
   ;; NOTE: only a finite number of addresses in the initial config, so we can use natural numbers
   ;; here
   (obs-ext natural τ))
  (ρ# (a#int ...))
  ;; H# = handler machine state (exp + outputs + loop outputs + spawns so far)
  (H# (e# ([a# v#] ...) ([a# v#] ...) (α#n ...)))
  (E# hole
      (spawning a#int τ E# S# ...)
      (goto s v# ... E# e# ...)
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
(define (csa#-messages-of-address-type address)
  (term (messages-of-type/mf (receptionist-type ,address) ,MAX-RECURSION-DEPTH)))

;; Returns the type of the given internal address
(define-metafunction csa#
  receptionist-type : a#int -> τ
  [(receptionist-type (init-addr natural τ)) τ]
  [(receptionist-type (spawn-addr _ _ τ)) τ]
  [(receptionist-type (blurred-spawn-addr _ τ)) τ])

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
   (messages-of-type/mf (type-subst τ X (minfixpt X τ)) ,(sub1 (term natural_max-depth)))]
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
      (term ((obs-ext ,next-generated-address τ))))]
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
   (list '(* Nat)))
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
   (list `(variant Null) `(variant Cons (* Nat) (* ,list-of-nat))))
  (test-same-items?
   (term (messages-of-type/mf ,list-of-nat 2))
   (list `(variant Null)
         `(variant Cons (* Nat) (variant Null))
         `(variant Cons (* Nat) (variant Cons (* Nat) (* ,list-of-nat)))))
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

;; Represents a single handler-level transition of an actor. Trigger is the event that caused the
;; handler to run, outputs is the list of outputs to the external world that happened execution, and
;; final-config is the resulting abstract configuration.
(struct csa#-transition
  (trigger ; follows trigger# above
   outputs ; list of abstract-addr/abstract-message 2-tuples
   final-config) ; an abstract implementation configuration
  #:transparent)

;; impl-config a#int v# -> (Listof csa#-transition)
;;
;; Evaluates the handler triggered by sending message to actor-address in impl-config, returning the
;; list of possible csa#-transitions.
(define (csa#-handle-external-message impl-config actor-address message)
  (handle-message impl-config
                  actor-address
                  message
                  (term (external-receive ,actor-address ,message))))

;; Evaluates the handler triggered by the actor corresponding to actor-address receiving message,
;; returning the list of possible csa#-transitions.
(define (handle-message impl-config actor-address message trigger)
  (append*
   (for/list ([behavior (current-behaviors-for-address impl-config actor-address)])
     (define init-handler-machine (handler-machine-for-message behavior message))
     (define update-behavior
       (if (precise-internal-address? actor-address)
           update-behavior/precise
           (make-update-behavior/blurred (behavior-state-defs behavior))))
     (eval-handler init-handler-machine
                   trigger
                   actor-address
                   impl-config
                   update-behavior))))

;; impl-config -> (Listof #f or csa#-transition)
;;
;; Evaluates all handlers triggered by a timeout or the receipt of some in-transit message in
;; impl-config, returning the list of possible results (either csa#-transition or #f if a transition
;; led to an unverifiable state)
(define (csa#-handle-all-internal-actions impl-config)
  (append (csa#-handle-all-internal-messages impl-config)
          (csa#-handle-all-timeouts impl-config)))

;; impl-config -> (Listof #f or csa#-transition)
;;
;; Evaluates all handlers triggered by the receipt of some in-transit message in impl-config,
;; returning the list of possible results (either csa#-transition or #f if a transition led to an
;; unverifiable state)
(define (csa#-handle-all-internal-messages impl-config)
  (append*
   (for/list ([packet-entry (csa#-config-message-packets impl-config)])
     (define packet (csa#-packet-entry->packet packet-entry))
     (define address (csa#-message-packet-address packet))
     (define message (csa#-message-packet-value packet))
     (handle-message (term (config-remove-packet/mf ,impl-config ,packet))
                     address
                     message
                     (term (internal-receive ,address ,message))))))

;; Returns a handler machine primed with the handler expression from the given behavior, with all
;; state arguments and the message substituted for the appropriate variables
(define (handler-machine-for-message behavior message)
  (redex-let csa#
      ([((_ ... (define-state (s [x_s τ_s] ..._n) (x_m) e# any_timeout-clause ...) _ ...)
         (goto s v# ..._n))
        behavior])
    ;; TODO: deal with the case where x_m shadows an x_s
    (inject/H# (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...)))))

;; Abstractly removes the entry in K# corresponding to the packet (a# v#), which will actually remove
;; it if its multiplicity is 1, else leave it there if its multiplicity is * (because removing a
;; message from an abstract list of 0 or more yields a list of 0 or more).
(define-metafunction csa#
  config-remove-packet/mf : K# (a# v#) -> K#
  [(config-remove-packet/mf (any_precise any_blurred (any_pkt1 ... (a# v# 1) any_pkt2 ...)) (a# v#))
   (any_precise any_blurred (any_pkt1 ... any_pkt2 ...))]
  ;; Case 2: if the multiplicity is not 1, it must be *, so we just return the original config because
  ;; nothing is actually removed
  [(config-remove-packet/mf any_config _) any_config])

;; impl-config -> (Listof csa#-transition)
;;
;; Evaluates all handlers triggered by a timeout impl-config, returning the list of possible
;; csa#-transitions
(define (csa#-handle-all-timeouts impl-config)
  (append
   ;; transitions for precise actors
   (append*
    (for/list ([actor (csa#-config-actors impl-config)])
      (csa#-handle-maybe-timeout (csa#-actor-address actor)
                                 (actor-behavior actor)
                                 impl-config
                                 update-behavior/precise)))
   ;; transitions for blurred actors
   (append*
    (for/list ([blurred-actor (csa#-config-blurred-actors impl-config)])
      (append*
       (for/list ([behavior (csa#-blurred-actor-behaviors blurred-actor)])
         (define update-behavior (make-update-behavior/blurred (behavior-state-defs behavior)))
         (csa#-handle-maybe-timeout (csa#-blurred-actor-address blurred-actor)
                                    behavior
                                    impl-config
                                    update-behavior)))))))

;; a#int b# K# (K# a#int e# -> K#) -> (Listof csa#-transition)
;;
;; Returns all possible transitions enabled by taking a timeout on the given behavior for the actor
;; with the given address (if such a timeout exists). If no such timeout exists, the empty list is
;; returned.
(define (csa#-handle-maybe-timeout address behavior config update-behavior)
  (match (term (get-timeout-handler-exp/mf ,behavior))
    [#f null]
    [handler-exp
     (eval-handler (inject/H# handler-exp)
                   (if (any-messages-for? config address)
                       (term (timeout/non-empty-queue ,address))
                       (term (timeout/empty-queue ,address)))
                   address
                   config
                   update-behavior)]))

;; Returns the behavior's current timeout handler expression with all state arguments substituted in
;; if the current state has a timeout clause, else #f
(define-metafunction csa#
  get-timeout-handler-exp/mf : b# -> e# or #f
  [(get-timeout-handler-exp/mf ((_ ... (define-state (s [x_s τ_s] ..._n) _ _ [(timeout _) e#]) _ ...)
                                (goto s v# ..._n)))
   (csa#-subst-n e# [x_s v#] ...)]
  [(get-timeout-handler-exp/mf _) #f])

;; Returns #t if the configuration has any in-transit messages for the given internal address; #f
;; otherwise.
(define (any-messages-for? config address)
  (redex-let csa# ([(_ _ ((a#int _ _) ...)) config])
    ;; member does not return #t, so we normalize that result
    (if (member address (term (a#int ...))) #t #f)))

(module+ test
  (test-true "any-messages-for? 1"
    (any-messages-for? (term (() () ([(init-addr 1 Nat) (* Nat) 1]))) (term (init-addr 1 Nat))))
  (test-false "any-messages-for? 2"
    (any-messages-for? (term (() () ([(init-addr 2 Nat) (* Nat) 1]))) (term (init-addr 1 Nat))))
  (test-false "any-messages-for? 1"
    (any-messages-for? (term (() () ())) (term (init-addr 1 Nat)))))

;; Returns all behaviors currently available in the given config for the actor with the given address
;; (will only be a single behavior for precise addresses, one or more for blurred ones).
(define (current-behaviors-for-address config address)
  (cond
    [(precise-internal-address? address)
     (list (actor-behavior (csa#-config-actor-by-address config address)))]
    [else
     (term (blurred-actor-behaviors-by-address/mf ,config ,address))]))

;; H# trigger# a#int impl-config (impl-config a#int e# -> impl-config) -> (Listof csa#-transition)
;;
;; Evaluates the given handler machine for the given trigger at the given actor address, updating the
;; given configuration with the encoutered effects and using the update-behavior function to update
;; the actor with its new behavior. Returns a list of csa#-transitions representing each possible
;; transition.
(define (eval-handler handler-machine trigger address config update-behavior)
  (define final-machine-states
    ;; Remove states stuck as a result of over-abstraction; we can assume these would never happen at
    ;; run-time
    (filter (negate stuck-at-empty-list-ref?)
            (apply-reduction-relation* handler-step# handler-machine #:cache-all? #t)))
  (unless (andmap complete-handler-config? final-machine-states)
    (error 'eval-handler
           "Abstract evaluation did not complete\nInitial state: ~s\nFinal stuck states:~s"
           handler-machine
           (filter (negate complete-handler-config?) final-machine-states)))
  (for/list ([machine-state final-machine-states])
    ;; TODO: rename outputs to something like "transmissions", because some of them stay internal to
    ;; the configuration
    (match-define (list final-exp outputs loop-outputs spawns) machine-state)
    ;; TODO: check that there are no internal loop outputs, or refactor that code entirely
    (define new-config (update-config-with-handler-results config address final-exp outputs spawns update-behavior))
    (csa#-transition trigger (filter (negate internal-output?) outputs) new-config)))

;; Returns #t if the given handler machine state is unable to step because of an over-approximation in
;; the abstraction (assumes that there are no empty vector/list/hash references in the actual running
;; progrm)
(define (stuck-at-empty-list-ref? h)
  (redex-let csa# ([(e# _ _ _) h])
    (or (redex-match? csa# (in-hole E# (list-ref   (list)   v#)) (term e#))
        (redex-match? csa# (in-hole E# (vector-ref (vector) v#)) (term e#))
        (redex-match? csa# (in-hole E# (hash-ref   (hash)   v#)) (term e#)))))

(module+ test
  (test-true "stuck config 1"
    (stuck-at-empty-list-ref? (inject/H# (term (vector-ref (vector) (* Nat))))))
  (test-true "stuck config 2"
    (stuck-at-empty-list-ref? (inject/H# (term (list-ref (list) (* Nat))))))
  (test-true "stuck config 3"
    (stuck-at-empty-list-ref? (inject/H# (term (hash-ref (hash) (* Nat)))))))

(define (complete-handler-config? c)
  (redex-match csa# ((in-hole E# (goto s v#_param ...)) any_output any_loop-output any_spawns) c))

(define (inject/H# exp)
  (redex-let csa#
             ([e# exp]
              [H# (term (,exp () () ()))])
             (term H#)))

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

    (==> (= a#_1 a#_2)
         (variant True)
         AddressEqualityTrue)
    (==> (= a#_1 a#_2)
         (variant False)
         AddressEqualityFalse)

    ;; Vectors, Lists, and Hashes
    ;; TODO: keep the elements in a canonical order, so that equivalent abstract values are equal?

    (==> (cons v#_new (list v# ...))
         (list v#_all ...)
         (where (v#_all ...) ,(set->list (set-add (list->set (term (v# ...))) (term v#_new))))
         Cons)
    (==> (cons v# (* (Listof τ)))
         (* (Listof τ))
         WildcardCons)
    (==> (list-ref (list _ ... v# _ ...) (* Nat))
         v#
         ListRef)
    (==> (list-ref (* (Listof τ)) (* Nat))
         (* τ)
         WildcardListRef)
    (==> (length (list v# ...))
         (* Nat)
         ListLength)
    (==> (length (* (Listof _)))
         (* Nat)
         WildcardListLength)
    (==> (vector-ref (vector _ .... v# _ ...) (* Nat))
         v#
         VectorRef)
    (==> (vector-ref (* (Vectorof τ)) (* Nat))
         (* τ)
         VectorWildcardRef)
    (==> (vector-take (vector v# ...) (* Nat))
         (vector v# ...)
         VectorTake)
    (==> (vector-take (* (Vectorof τ)) (* Nat))
         (* (Vectorof τ))
         VectorWildcardTake)
    (==> (vector-length (vector v# ...))
         (* Nat)
         VectorLength)
    (==> (vector-length (* (Vectorof τ)))
         (* Nat)
         VectorWildcardLength)
    (==> (vector-copy (vector v# ...) (* Nat) (* Nat))
         (vector v# ...)
         VectorCopy)
    (==> (vector-copy (* (Vectorof τ)) (* Nat) (* Nat))
         (* (Vectorof τ))
         VectorWildcardCopy)
    ;; TODO: figure out if the type is ever *not* big enough to also cover the other vector
    (==> (vector-append (vector v#_1 ...) (vector v#_2 ...))
         ,(cons 'vector (set->list (list->set (term (v#_1 ... v#_2 ...)))))
         VectorAppend)
    (==> (vector-append (* (Vectorof τ)) _)
         (* (Vectorof τ))
         VectorWildcardAppend1)
    (==> (vector-append _ (* (Vectorof τ)))
         (* (Vectorof τ))
         VectorWildcardAppend2)
    (==> (hash-ref (hash v#_1 ... v# v#_2 ...) v#_key)
         (variant Just v#)
         HashRefSuccess)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Just (* τ_2))
         HashWildcardRefSuccess)
    (==> (hash-ref (hash v#_other ...) v#_key)
         (variant Nothing)
         HashRefFailure)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Nothing)
         HashWildcardRefFailure)
    (==> (hash-set (hash v#_1 ... v#_value v#_2 ...) v#_key v#_value)
         (hash v#_1 ... v#_value v#_2 ...)
         HashSetExists)
    (==> (hash-set (hash v#_current ...) v#_key v#_value)
         (hash v#_current ... v#_value)
         (side-condition (not (member (term v#_value) (term (v#_current ...)))))
         HashSetNewItem)
    (==> (hash-set (* Hash τ_1 τ_2) v#_key v#_value)
         (* Hash τ_1 τ_2)
         HashWildcardSet)
    (==> (hash-has-key? (hash v# ...) v#_key)
         (variant True)
         HashHasKeyTrue)
    (==> (hash-has-key? (hash v# ...) v#_key)
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

    (--> ((in-hole E# (send a# v#)) (any_outputs ...) any_loop-outputs any_spawns)
         ((in-hole E# v#)           (any_outputs ... [a# v#]) any_loop-outputs any_spawns)
         ;; regular send only occurs outside of loop contexts
         (side-condition (not (redex-match csa# (in-hole E# (loop-context E#_2)) (term E#))))
         Send)
    (--> ((in-hole E# (loop-context (in-hole E#_2 (send a# v#)))) any_outputs any_loop-outputs any_spawns)
         ((in-hole E# (loop-context (in-hole E#_2 v#)))
          any_outputs
          ,(remove-duplicates (append (term any_loop-outputs) (list (term [a# v#]))))
          any_spawns)
         LoopSend)

    ;; Spawn
    (==> (spawn any_location τ e# S# ...)
         (spawning a#int τ (csa#-subst-n e# [self a#int]) (csa#-subst/S# S# self a#int) ...)
         (where a#int (spawn-addr any_location NEW τ))
         SpawnStart)
    (--> ((in-hole E# (spawning a#int τ (in-hole E#_2 (goto s v# ...)) S# ...))
          any_outputs
          any_loop-outputs
          (any_spawns ...))
         ((in-hole E# a#int)
          any_outputs
          any_loop-outputs
          (any_spawns ... (a#int ((S# ...) (goto s v# ...)))))
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
    (==> (print-len (vector v# ...))
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
    (redex-let* csa# ([α#n (term [(init-addr 0 Nat)
                                  (((define-state (Always) (long-unused-name) (begin ,exp (goto Always))))
                                   (begin ,exp (goto Always)))])]
                      [α# (term (α#n))]
                      [μ# (term ())])
                (term (α# μ# ()))))

  (check-not-false (redex-match csa# K# (csa#-make-simple-test-config (term (* Nat)))))

  (define-check (check-exp-steps-to? e1 e2)
    (define next-steps (apply-reduction-relation handler-step# (inject/H# e1)))
    (unless (equal? next-steps (list (inject/H# e2)))
      (fail-check (format "There were ~s next steps: ~s" (length next-steps) next-steps))))
  (define-check (check-exp-steps*-to? e1 e2)
    (define next-steps (apply-reduction-relation* handler-step# (inject/H# e1)))
    (unless (equal? next-steps (list (inject/H# e2)))
      (fail-check (format "There were ~s next steps: ~s" (length next-steps) next-steps))))

  ;; TODO: rewrite all of these tests with case statements
  ;; (csa#-exp-steps-to? (term (match (tuple 'a 'b)
  ;;                             ['c (* Nat)]
  ;;                             [(tuple 'a item) item]))
  ;;                     (term (match (tuple 'a 'b)
  ;;                             [(tuple 'a item) item])))
  ;; (csa#-exp-steps-to? (term (match (tuple 'a 'b)
  ;;                             [(tuple 'a item) item]))
  ;;                     (term 'b))

  ;; (csa#-exp-steps-to? (term (match (* Nat)
  ;;                             [(tuple) (goto S1 (* Nat))]
  ;;                             [_ (goto S2 (* Nat))]))
  ;;                     (term (match (* Nat)
  ;;                             [_ (goto S2 (* Nat))]) ))
  ;; (csa#-exp-steps-to? (term (match (* Nat)
  ;;                             [_ (goto S2 (* Nat))]))
  ;;                     (term (goto S2 (* Nat)) ))
  ;; (csa#-exp-steps-to? (term (match (* Nat)
  ;;                             [(tuple) (goto S2 (* Nat))]))
  ;;                     (term (match (* Nat))))

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

  ;; Check that internal addresses in the transmissions do not change the evaluation (had a problem
  ;; with this before)
  (check-equal?
   (apply-reduction-relation* handler-step# (inject/H# (term (begin (send (init-addr 1 Nat) (* Nat)) (goto A)))))
   (list (term ((begin (goto A)) (((init-addr 1 Nat) (* Nat))) () ()))))

  (check-equal?
   (apply-reduction-relation* handler-step#
     (inject/H# (term (begin (spawn L Nat (goto A) (define-state (A) (x) (goto A))) (goto B)))))
   (list (term ((begin (goto B)) () () ([(spawn-addr L NEW Nat) [((define-state (A) (x) (goto A))) (goto A)]]))))))

(define (update-config-with-handler-results config address final-exp outputs spawns update-behavior)
  ;; 1. update the behavior
  (define with-updated-behavior
    (redex-let csa# ([(in-hole E# (goto s v# ...)) final-exp])
      (update-behavior config address (term (goto s v# ...)))))
  ;; 2. add spawned actors
  (define with-spawns (merge-new-actors with-updated-behavior spawns))
  ;; 3. add sent messages
  (merge-messages-into-config with-spawns (filter internal-output? outputs)))

;; Sets the behavior for the actor with the given precise address to the given expression
(define (update-behavior/precise config address goto-exp)
  (redex-let csa# ([((any_actors1 ...) (a# (any_state-defs _)) (any_actors2 ...))
                    (config-actor-and-rest-by-address config address)])
    (term ((any_actors1 ... (a# (any_state-defs ,goto-exp)) any_actors2 ...)
           ,(csa#-config-blurred-actors config)
           ,(csa#-config-message-packets config)))))

(define (make-update-behavior/blurred state-defs)
  (lambda (config address goto-exp)
    (term (update-behavior/blurred/mf ,config ,address (,state-defs ,goto-exp)))))

(define-metafunction csa#
  update-behavior/blurred/mf : K# a#int b# -> K#
  [(update-behavior/blurred/mf
    (any_precise-actors
     (any_blurred1 ... (a#int (b#_old ...)) any_blurred2 ...)
     any_packets)
    a#int
    b#_new)
   (any_precise-actors
    (any_blurred1 ... (a#int ,(remove-duplicates (term (b#_old ... b#_new)))) any_blurred2 ...)
    any_packets)])

;; Abstractly adds the set of new packets to the packet set in the given config.
(define (merge-messages-into-config config new-message-list)
  (redex-let csa# ([(any_actors any_blurred any_packets) config])
    (term (any_actors
           any_blurred
           ,(merge-messages-into-packet-set (term any_packets) new-message-list)))))

;; Abstractly adds the set of new packets to the given set.
(define (merge-messages-into-packet-set packet-set new-message-list)
  (redex-let csa# ([((a# v#) ...) new-message-list])
    (term ,(deduplicate-packets (append packet-set (term ((a# v# 1) ...)))))))

(module+ test
  (check-equal?
   (merge-messages-into-config (term (() () ())) (list (term ((init-addr 0 Nat) (* Nat)))))
   (term (() () (((init-addr 0 Nat) (* Nat) 1)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0 Nat) (* Nat) 1))))
                       (list (term ((init-addr 0 Nat) (* Nat)))))
   (term (() () (((init-addr 0 Nat) (* Nat) *)))))

  (check-equal?
   (merge-messages-into-config (term (() () (((init-addr 0 Nat) (* Nat) 1))))
                       (list (term ((init-addr 1 Nat) (* Nat)))))
   (term (() () (((init-addr 0 Nat) (* Nat) 1) ((init-addr 1 Nat) (* Nat) 1)))))

  (check-equal?
   (merge-messages-into-config (term (()
                              ()
                              (((init-addr 1 Nat) (* (Addr Nat)) 1)
                               ((init-addr 1 Nat) (obs-ext 0 Nat) 1))))
                       (term (((init-addr 1 Nat) (* (Addr Nat))))))
   (term (()
          ()
          (((init-addr 1 Nat) (* (Addr Nat)) *)
           ((init-addr 1 Nat) (obs-ext 0 Nat) 1))))))

(define (merge-new-actors config new-actors)
  (redex-let csa# ([((any_actors ...) any_blurred any_messages) config])
             (term (,(append (term (any_actors ...)) new-actors)
                    any_blurred
                    any_messages))))

(module+ test
  (define new-spawn1
    (term ((spawn-addr foo NEW Nat) (((define-state (A) (x) (goto A))) (goto A)))))
  (define init-actor1
    (term ((init-addr 0 Nat) (((define-state (B) (x) (goto B))) (goto B)))))
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
  [(csa#-subst a# _ _) a#]
  [(csa#-subst (spawn any_location τ e# S# ...) self v#) (spawn any_location τ e# S# ...)]
  [(csa#-subst (spawn any_location τ e# S# ...) x v#)
    (spawn any_location τ (csa#-subst e# x v#) (csa#-subst/S# S# x v#) ...)]
  [(csa#-subst (goto s e# ...) x v#) (goto s (csa#-subst e# x v#) ...)]
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
  [(csa#-subst (vector e# ...) x v#) (vector (csa#-subst e# x v#) ...)]
  [(csa#-subst (hash v#_element ...) x v#) (hash (csa#-subst v#_element x v#) ...)]
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
  csa#-subst/S# : S# x v# -> S#
  ;; Case 1: no timeout, var is shadowed
  [(csa#-subst/S# (define-state (s [x_s τ] ...) (x_m) e#) x v#)
   (define-state (s [x_s τ] ...) (x_m) e#)
   (where (_ ... x _ ...) (x_s ... x_m))]
  ;; Case 2: timeout, var shadowed by state param
  [(csa#-subst/S# (define-state (s [x_s τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x v#)
   (define-state (s [x_s τ] ...) (x_m) e# [(timeout v#_t) e#_t])
   (where (_ ... x _ ...) (x_s ...))]
  ;; Case 3: timeout, var shadowed by message param
  [(csa#-subst/S# (define-state (s [x_s τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x_m v#)
   (define-state (s [x_s τ] ...) (x_m) e# [(timeout v#_t) (csa#-subst e#_t x_m v#)])]
  ;; Case 4: timeout, no shadowing
  [(csa#-subst/S# (define-state (s [x_s τ] ...) (x_m) e# [(timeout v#_t) e#_t]) x v#)
   (define-state (s [x_s τ] ...) (x_m)
     (csa#-subst e# x v#)
     [(timeout v#_t) (csa#-subst e#_t x v#)])]
  ;; Case 5: no timeout, no shadowing
  [(csa#-subst/S# (define-state (s [x_s τ] ...) (x_m) e#) x v#)
   (define-state (s [x_s τ] ...) (x_m) (csa#-subst e# x v#))])

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
                                  (init-addr 2 Nat)))
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
                                  (init-addr 2 Nat)))
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
                                  (init-addr 2 Nat)))
                (term (spawn loc
                             Nat
                             (goto A self (* Nat))
                             (define-state (A [s Nat] [a Nat]) (x) (goto A x (init-addr 2 Nat) self))))))

(module+ test
  (check-equal? (term (csa#-subst (variant Foo (* Nat)) a (* Nat))) (term (variant Foo (* Nat)))))

;; Substitutes the second type for X in the first type
(define-metafunction csa#
  type-subst : τ X τ -> τ
  [(type-subst Nat _ _) Nat]
  [(type-subst (minfixpt X τ_1) X τ_2)
   (minfixpt X τ_1)]
  ;; TODO: do the full renaming here
  [(type-subst (μ X_1 τ_1) X_2 τ_2)
   (μ X_1 (type-subst τ_1 X_2 τ_2))]
  [(type-subst X X τ) τ]
  [(type-subst X_1 X_2 τ) X_1]
  [(type-subst (Union [t τ ...] ...) X τ_2)
   (Union [t (type-subst τ X τ_2) ...] ...)]
  ;; TODO: Record
  [(type-subst (Addr τ) X τ_2)
   (Addr (type-subst τ X τ_2))])

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; Abstracts the given CSA configuration, with a maximum recursion depth for values
;;
;; NOTE: currently supports only no-messages, no-externals configs
(define (csa#-abstract-config concrete-config internal-addresses)
  (term (abstract-config/mf ,concrete-config ,internal-addresses ,MAX-RECURSION-DEPTH)))

(define-metafunction csa#
  abstract-config/mf : K (a_internal ...) natural_recursion-depth -> K#
  [(abstract-config/mf ((αn ...) ; actors
                 () ; messages-in-transit
                 _ ; receptionists (ignored because the spec config manages these)
                 _ ; externals (ignored because the spec config manages these)
                 )
                (a_internal ...)
                natural_depth)
   ((α#n ...) () ())
   (where (α#n ...) ((abstract-actor αn (a_internal ...) natural_depth) ...))])

(define-metafunction csa#
  abstract-actor : αn (a_internals ...) natural_depth -> α#n
  [(abstract-actor (a_this ((S ...) e)) (a ...) natural_depth)
   ((abstract-e a_this (a ...) natural_depth)
    (((abstract-S S (a ...) natural_depth) ...)
     (abstract-e e (a ...) natural_depth)))])

(define-metafunction csa#
  abstract-S : S (a_internals ...) natural_depth -> S#
  [(abstract-S (define-state (s [x τ] ...) (x_m) e) (a ...) natural_depth)
   (define-state (s [x τ] ...) (x_m) (abstract-e e (a ...) natural_depth))]
  [(abstract-S (define-state (s [x τ] ...) (x_m) e [(timeout n) e_timeout]) (a ...) natural_depth)
   (define-state (s [x τ] ...) (x_m)
     (abstract-e e (a ...) natural_depth)
     [(timeout (* Nat)) (abstract-e e_timeout (a ...) natural_depth)])])

;; Abstracts the given expression to the given depth, with the given address list indicating the set
;; of internal addresses
(define-metafunction csa#
  abstract-e : e (a ...) natural_depth -> e#
  [(abstract-e natural _ _) (* Nat)]
  [(abstract-e string _ _) (* String)]
  [(abstract-e x _ _) x]
  [(abstract-e a (a_int ...) _) (abstract-address a (a_int ...))]
  [(abstract-e (goto s e ...) (a ...) natural_depth)
   (goto s (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (begin e ...) (a ...) natural_depth) (begin (abstract-e e (a ...) natural_depth) ...)]
  [(abstract-e (send e_1 e_2) (a ...) natural_depth)
   (send (abstract-e e_1 (a ...) natural_depth) (abstract-e e_2 (a ...) natural_depth))]
  [(abstract-e (spawn any_location τ e S ...) (a ...) natural_depth)
   (spawn any_location
          τ
          (abstract-e e (a ...) natural_depth)
          (abstract-S S (a ...) natural_depth) ...)]
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
   (* τ)]
  [(abstract-e (folded τ e) (a ...) natural_depth)
   (folded τ (abstract-e e (a ...) ,(sub1 (term natural_depth))))]
  [(abstract-e (fold τ e) (a ...) natural_depth)
   (fold τ (abstract-e e (a ...) natural_depth))]
  [(abstract-e (unfold τ e) (a ...) natural_depth)
   (unfold τ (abstract-e e (a ...) natural_depth))]
  [(abstract-e (list e ...) (a ...) natural_depth)
   (list e#_unique ...)
   (where (e# ...) ((abstract-e e (a ...) natural_depth) ...))
   (where (e#_unique ...) ,(set->list (list->set (term (e# ...)) )))]
  [(abstract-e (vector e ...) (a ...) natural_depth)
   (vector e#_unique ...)
   (where (e# ...) ((abstract-e e (a ...) natural_depth) ...))
   (where (e#_unique ...) ,(set->list (list->set (term (e# ...)) )))]
  [(abstract-e (hash) _ _) (hash)]
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
  [(abstract-address (addr natural τ) (_ ... (addr natural _) _ ...)) (init-addr natural τ)]
  [(abstract-address (addr natural τ) _) (obs-ext natural τ)])

(module+ test
  (check-equal? (term (abstract-e (record [f1 1] [f2 2]) () 1))
                (term (record [f1 (* Nat)] [f2 (* Nat)])))
  (check-not-false
   (redex-match? csa#
                 (variant Foo (init-addr 1 Nat) (obs-ext 2 Nat))
                 (term (abstract-e (variant Foo (addr 1 Nat) (addr 2 Nat)) ((addr 1 Nat)) 10))))
  (check-equal? (term (abstract-e (list 1 2) () 10))
                (term (list (* Nat))))
  (check-equal? (term (abstract-e (vector 1 2) () 10))
                (term (vector (* Nat))))
  (test-equal? "Abstraction on non-matching addresses"
               (term (abstract-e (addr 1 (Union [A])) ((addr 1 (Union [B]))) 0))
               (term (init-addr 1 (Union [A]))))
  (test-equal? "Abstraction on non-matching addresses"
               (term (abstract-e (addr 2 (Union [A])) ((addr 1 (Union [B]))) 0))
               (term (obs-ext 2 (Union [A])))))

;; ---------------------------------------------------------------------------------------------------
;; Selecting the spawn flag to blur

(define (csa#-spawn-address? a)
  (redex-match? csa# (spawn-addr _ _ _) a))

(module+ test
  (test-case "New-span-addr? check"
    (define a (term (spawn-addr 5 NEW Nat)))
    (define b (term (spawn-addr 6 OLD Nat)))
    (define c (term (init-addr 7 Nat)))
    (check-not-false (redex-match csa# a#int a))
    (check-not-false (redex-match csa# a#int b))
    (check-not-false (redex-match csa# a#int c))
    (check-true (csa#-spawn-address? a))
    (check-true (csa#-spawn-address? b))
    (check-false (csa#-spawn-address? c))))

(define (csa#-spawn-address-flag a)
  (redex-let csa# ([(spawn-addr _ spawn-flag _) a])
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
    (blur-addresses (list remaining-config removed-actors)
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
            (((init-addr 2 Nat) (obs-ext 1 Nat) 1)
             ((init-addr 2 Nat) (obs-ext 2 Nat) 1)
             ((init-addr 2 Nat) (obs-ext 3 Nat) 1))))
     'NEW
     (list '(obs-ext 3 Nat)))
    (list
     (term (()
            ()
            (((init-addr 2 Nat) (* (Addr Nat)) *)
             ((init-addr 2 Nat) (obs-ext 3 Nat) 1))))
     null)))

;; impl-config spawn-flag -> impl-config (α#n ...)
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
  [(switch-spawn-flag/mf (spawn-addr any_loc NEW any_type)) (spawn-addr any_loc OLD any_type)]
  [(switch-spawn-flag/mf (spawn-addr any_loc OLD any_type)) (spawn-addr any_loc NEW any_type)])

(module+ test
  (test-equal? "remove-actors test"
    (remove-actors-by-flag
     (term
      ((((spawn-addr 1 OLD Nat) ,test-behavior1)
        ((spawn-addr 1 NEW Nat) ,test-behavior1)
        ((spawn-addr 2 OLD Nat) ,test-behavior1)
        ((spawn-addr 3 NEW Nat) ,test-behavior1))
       ()
       ()))
     'NEW)
    (list
     (term
      ((((spawn-addr 1 OLD Nat) ,test-behavior1)
        ((spawn-addr 2 OLD Nat) ,test-behavior1)
        ((spawn-addr 3 NEW Nat) ,test-behavior1))
       ()
       ()))
     (list (term ((spawn-addr 1 NEW Nat) ,test-behavior1))))))

;; For a term assumed to contain no external addresses, renames the addresses in internals-to-blur as
;; done in the blurring process.
(define (csa#-blur-internal-addresses some-term internals-to-blur)
  (blur-addresses some-term internals-to-blur null))

;; term (a#int ...) (a#ext ...) -> term
;;
;; Renames internal addresses in internals-to-bour and external addresses *not* in
;; relevant-externals to their respective imprecise forms
(define (blur-addresses some-term internals-to-blur relevant-externals)
  (match some-term
    [(and addr `(spawn-addr ,loc ,_ ,type))
     (if (member addr internals-to-blur)
         (term (blurred-spawn-addr ,loc ,type))
         addr)]
    [(and addr `(obs-ext ,_ ,type))
     (if (member addr relevant-externals)
         addr
         (term (* (Addr ,type))))]
    [(list (and keyword (or `vector 'list 'hash)) terms ...)
     (define blurred-args (map (curryr blur-addresses internals-to-blur relevant-externals) terms))
     (term (,keyword ,@(remove-duplicates blurred-args)))]
    [(list terms ...)
     (map (curryr blur-addresses internals-to-blur relevant-externals) terms)]
    [_ some-term]))

(module+ test
  (test-equal? "blur test"
    (blur-addresses
     (term (((spawn-addr foo OLD Nat) (spawn-addr foo NEW Nat))
            (spawn-addr bar NEW Nat)
            (obs-ext 1 Nat)
            (obs-ext 2 Nat)
            (spawn-addr bar OLD Nat)
            (spawn-addr baz OLD Nat)
            (spawn-addr quux NEW Nat)))
     (list (term (spawn-addr foo NEW Nat)) (term (spawn-addr bar NEW Nat)))
     (list '(obs-ext 2 Nat)))
    (term (((spawn-addr foo OLD Nat) (blurred-spawn-addr foo Nat))
           (blurred-spawn-addr bar Nat)
           (* (Addr Nat))
           (obs-ext 2 Nat)
           (spawn-addr bar OLD Nat)
           (spawn-addr baz OLD Nat)
           (spawn-addr quux NEW Nat))))

  (test-equal? "blur test 2"
    (blur-addresses
     (redex-let* csa#
                 ([α#n (term
                        ((init-addr 0 Nat)
                         (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                             (begin
                               (send (obs-ext 1 Nat) (* Nat))
                               (send (obs-ext 2 Nat) (* Nat))
                               (goto A x y z))))
                          (goto A (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))))]
                  [K# (term ((α#n) () ()))])
                 (term K#))
     null
     (term ((obs-ext 1 Nat) (obs-ext 3 Nat))))
    (redex-let* csa#
                ([α#n (term
                       ((init-addr 0 Nat)
                        (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                            (begin
                              (send (obs-ext 1 Nat) (* Nat))
                              (send (* (Addr Nat)) (* Nat))
                              (goto A x y z))))
                         (goto A (* (Addr Nat)) (obs-ext 3 Nat) (* (Addr Nat))))))]
                 [K# (term ((α#n) () ()))])
                (term K#)))

  ;; Make sure duplicates are removed from vectors, lists, and hashes
  (test-equal? "blur test 3"
   (blur-addresses
    (redex-let csa#
        ([e# (term (hash (obs-ext 1 Nat)
                         (obs-ext 2 Nat)
                         (obs-ext 3 Nat)
                         (obs-ext 4 Nat)))])
       (term e#))
    null
    '((obs-ext 1 Nat) (obs-ext 3 Nat)))
   (term (hash (obs-ext 1 Nat) (* (Addr Nat)) (obs-ext 3 Nat))))

  (test-equal? "blur test 4"
   (blur-addresses
    (redex-let csa#
        ([e# (term (list (obs-ext 1 Nat)
                         (obs-ext 2 Nat)
                         (obs-ext 3 Nat)
                         (obs-ext 4 Nat)))])
      (term e#))
    null
    null)
   (term (list (* (Addr Nat)))))

  (test-equal? "blur test 5"
   (blur-addresses
    (redex-let csa#
        ([e# (term (vector (obs-ext 1 Nat)
                           (obs-ext 2 Nat)
                           (obs-ext 3 Nat)
                           (obs-ext 4 Nat)))])
      (term e#))
    null
    `((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))
   (term (vector (obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))))

;; Returns #t if the address is of the form (spawn-addr _ flag _), #f otherwise.
(define (has-spawn-flag? addr flag)
  (match addr
    [`(spawn-addr ,_ ,addr-flag ,_)
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
    (add-blurred-behaviors (term (((blurred-spawn-addr 1 Nat) (,behavior1 ,behavior2))
                                  ((blurred-spawn-addr 2 Nat) (,behavior3))))
                           (list (term ((blurred-spawn-addr 1 Nat) ,behavior3))
                                 (term ((blurred-spawn-addr 3 Nat) ,behavior3))
                                 (term ((blurred-spawn-addr 1 Nat) ,behavior1))))
    (term (((blurred-spawn-addr 1 Nat) (,behavior1 ,behavior2 ,behavior3))
           ((blurred-spawn-addr 2 Nat) (,behavior3))
           ((blurred-spawn-addr 3 Nat) (,behavior3))))))

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
             (redex-let csa# ([(any_addr any_value _) message]) (term (any_addr any_value *)))))
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
    (term (((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1))))
   (term (((obs-ext 1 Nat) (* Nat) *))))

    (check-equal?
   (deduplicate-packets
    (term (((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1))))
   (term (((obs-ext 1 Nat) (* Nat) *))))

  (check-equal?
   (deduplicate-packets
    (term (((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 2 Nat) (* Nat) 1)
           ((obs-ext 3 Nat) (* Nat) *)
           ((* (Addr Nat)) (* Nat) *)
           ((obs-ext 1 Nat) (* Nat) 1)
           ((* (Addr Nat)) (* Nat) 1))))
   (term (((obs-ext 1 Nat) (* Nat) *)
          ((obs-ext 2 Nat) (* Nat) 1)
          ((obs-ext 3 Nat) (* Nat) *)
          ((* (Addr Nat)) (* Nat) *)))))

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (make-single-actor-abstract-config actor)
  (term (make-single-actor-abstract-config/mf ,actor)))

(define-metafunction csa#
  make-single-actor-abstract-config/mf : α#n -> K#
  [(make-single-actor-abstract-config/mf α#n)
   ((α#n) () ())])

;; ---------------------------------------------------------------------------------------------------
;; Selectors

;; Returns a list of actors (α#n's)
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
  config-actor-and-rest-by-address/mf : K# a#int -> ((α#n ...) α#n (α#n ...))
  [(config-actor-and-rest-by-address/mf ((any_1 ... (name the-actor (a#int _)) any_2 ...) _ ...)
                                        a#int_target)
   ((any_1 ...) the-actor (any_2 ...))
   (judgment-holds (same-internal-address-without-type? a#int a#int_target))])

;; Returns the given precise actor with the given address, or #f if it's not in the given config
(define (csa#-config-actor-by-address config addr)
  (term (actor-by-address/mf ,(csa#-config-actors config) ,addr)))

(define-metafunction csa#
  actor-by-address/mf : α# a#int -> #f or α#n
  [(actor-by-address/mf () _) #f]
  [(actor-by-address/mf ((a#int any_behavior) _ ...) a#int_target)
   (a#int any_behavior)
   (judgment-holds (same-internal-address-without-type? a#int a#int_target))]
  [(actor-by-address/mf (_ any_rest ...) a#int)
   (actor-by-address/mf (any_rest ...) a#int)])

(define-judgment-form csa#
  #:mode (same-internal-address-without-type? I I)
  #:contract (same-internal-address-without-type? a#int a#int)
  [------
   (same-internal-address-without-type? (init-addr natural _) (init-addr natural _))]
  [------
   (same-internal-address-without-type? (spawn-addr any_loc NEW _) (spawn-addr any_loc NEW _))]
  [------
   (same-internal-address-without-type? (spawn-addr any_loc OLD _) (spawn-addr any_loc OLD _))]
  [------
   (same-internal-address-without-type? (blurred-spawn-addr any_loc _)
                                        (blurred-spawn-addr any_loc _))])

(define-judgment-form csa#
  #:mode (same-external-address-without-type? I I)
  #:contract (same-external-address-without-type? a#ext a#ext)
  [------
   (same-external-address-without-type? (obs-ext natural _) (obs-ext natural _))])

(define (csa#-actor-address a)
  (redex-let* csa# ([α#n a]
                    [(a#int _) (term α#n)])
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

;; α#n -> b#
(define (actor-behavior actor)
  (second actor))

;; Returns all behaviors assigned to the blurred actor with the given address in the given config
(define-metafunction csa#
  blurred-actor-behaviors-by-address/mf : K# a#int -> (b# ...)
  [(blurred-actor-behaviors-by-address/mf (_ (_ ... (a#int any_behaviors) _ ...) _) a#int_target)
   any_behaviors
   (judgment-holds (same-internal-address-without-type? a#int a#int_target))])

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

;; ---------------------------------------------------------------------------------------------------
;; Predicates

;; Returns true if the output is to an internal address, false otherwise
(define (internal-output? output)
  (redex-match? csa# (a#int _) output))

(module+ test
  (check-true (internal-output? (term ((init-addr 1 Nat) (* Nat)))))
  (check-false (internal-output? (term ((obs-ext 2 Nat) (* Nat))))))

;; Returns #t if the address is a precise internal address (meaning it represents a single concrete
;; address in the concretized configuration), #f otherwise
(define (precise-internal-address? addr)
  (redex-match? csa# a#int-precise addr))

(define (necessarily-enabled? trigger)
  (judgment-holds (necessarily-enabled?/j ,trigger)))

(define-judgment-form csa#
  #:mode (necessarily-enabled?/j I)
  #:contract (necessarily-enabled?/j trigger#)

  [-----------------------------------------------------
   (necessarily-enabled?/j (timeout/empty-queue a#int))]

  [-----------------------------------------------------
   (necessarily-enabled?/j (internal-receive a#int v#))])

(module+ test
  (test-true "necessarily-enabled 1"
    (necessarily-enabled? (term (timeout/empty-queue (init-addr 1 Nat)))))
  (test-false "necessarily-enabled 2"
    (necessarily-enabled? (term (timeout/non-empty-queue (init-addr 1 Nat)))))
  (test-true "necessarily-enabled 3"
    (necessarily-enabled? (term (internal-receive (init-addr 1 Nat) (* Nat)))))
  (test-false "necessarily-enabled 4"
    (necessarily-enabled? (term (external-receive (init-addr 1 Nat) (* Nat))))))

;; ---------------------------------------------------------------------------------------------------
;; Types

(define-metafunction csa#
  type-join : τ τ -> τ
  [(type-join (Union [t_1 τ_1 ...] ...) (Union [t_2 τ_2 ...] ...))
   (Union [t_3 τ_3 ...] ...)
   (where ([t_3 τ_3 ...] ...)
          ,(remove-duplicates (term ([t_1 τ_1 ...] ... [t_2 τ_2 ...] ...))))]
  ;; TODO: allow for more sophisticated joins that look at the inner types of records, variants,
  ;; etc. and go recur into Union fields
  [(type-join τ τ) τ])

(module+ test
  (test-equal? "type-join 1" (term (type-join Nat Nat)) 'Nat)
  (test-equal? "type-join 2"
               (term (type-join (Union [A]) (Union [B])))
               '(Union [A] [B]))
  (test-equal? "type-join 3"
               (term (type-join (Union [A] [B]) (Union [B])))
               '(Union [A] [B])))

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
   (externals-in (term ((obs-ext 1 Nat)
                      (obs-ext 2 Nat)
                      (obs-ext 2 Nat)
                      (foo bar (baz (init-addr 2 Nat) (obs-ext 3 Nat))))))
   (term ((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat)))))

;; Returns the list of all internal addresses in the given term
(define (internals-in the-term)
  (remove-duplicates (term (internals-in/mf ,the-term))))

(define-metafunction csa#
  internals-in/mf : any -> (a#int ...)
  [(internals-in/mf a#int) (a#int)]
  [(internals-in/mf (any ...))
   (any_addr ... ...)
   (where ((any_addr ...) ...) ((internals-in/mf any) ...))]
  [(internals-in/mf _) ()])

(module+ test
  (check-same-items?
   (internals-in (term ((init-addr 1 Nat)
                        (init-addr 1 Nat)
                        (obs-ext 2 Nat)
                        (spawn-addr 3 NEW Nat)
                      (foo bar (baz (init-addr 2 Nat) (obs-ext 3 Nat))))))
   (term ((init-addr 1 Nat) (spawn-addr 3 NEW Nat) (init-addr 2 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Debug helpers

(define (impl-config-without-state-defs config)
  (redex-let csa# ([(((a#int (_ e#)) ...) ((a#int_b ((_ e#_b) ...)) ...) μ#) config])
             (term (((a#int e#) ...) ((a#int_b (e#_b ...)) ...) μ#))))

(define (impl-config-goto config)
  ;; NOTE: only suports single-actor impls for now
  (redex-let csa# ([(((a#int (_ e#))) any_blurred μ#) config])
             (term e#)))
