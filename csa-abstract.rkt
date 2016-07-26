;; Defines the abstract interpretation of CSA programs/configurations

#lang racket

(provide
 csa#
 generate-abstract-messages
 csa#-handle-message
 csa#-handle-all-internal-messages
 csa#-handle-all-timeouts
 (struct-out csa#-transition)
 csa#-internal-trigger?
 csa#-output-address
 csa#-output-message
 α-config
 α-e
 α-receptionists
 blur-irrelevant-actors
 csa#-blur-and-age-receptionists
 csa#-age-internal-addrs
 blur-externals
 csa#-merge-duplicate-messages
 make-single-actor-abstract-config
 csa#-receptionist-type
 csa#-new-spawn-address?
 csa#-sort-escapes
 same-internal-address-without-type?

 ;; Debug helpers
 prog-config-without-state-defs
 prog-config-goto
 ;; handler-step#
 )

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "csa.rkt")

;; Abstract interpretation version of CSA
;;
;; TODO: make the language inheritance hierarchy correct (or consider merging them all into a single
;; mega-language)
(define-extended-language csa# csa-eval
  (K# (α# μ# ρ# (a#ext_escaped-observables ...)))
  (α# (α#n ...))
  (α#n (a#int ((S# ...) e#)))
  (μ# ((a#int v# multiplicity) ...))
  (multiplicity 1 *)
  (S# (define-state (s [x τ] ...) (x) e#)
      (define-state (s [x τ] ...) (x) e# [(timeout v#) e#]))
  (v# a#
      (variant t v# ...)
      (record [l v#] ...)
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
  (a#int (init-addr natural τ)
         ;; OLD means it existed before the current handler was run, NEW means it was spawned in the
         ;; current handler (should all be OLD between runs, after blur/canonicalize)
         (spawn-addr any_location OLD τ)
         (spawn-addr any_location NEW τ)
         blurred-internal)
  (a#ext
   (* (Addr τ)) ; unobserved address
   ;; NOTE: only a finite number of addresses in the initial config, so we can use natural numbers
   ;; here
   (obs-ext natural τ))
  (ρ# (a#int ...))
  ;; H# = handler config (exp + outputs + loop outputs so far)
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
      (primop v# ... E# e# ...)
      (printf string v# ... E# e# ...)
      (list v# ... E# e# ...)
      (vector v# ... E# e# ...)
      (for/fold ([x E#]) ([x e#]) e#)
      (for/fold ([x v#]) ([x E#]) e#)
      (loop-context E#))
  ;; TODO: make these more like labels, or something
  (trigger# (timeout a#int)
            ;; TODO: maybe distinguish timeout when messages are there or not
            (internal-receive a#int v#)
            (external-receive a#int v#)))

;; ---------------------------------------------------------------------------------------------------
;; Message generation

;; TODO: create a second type of "fresh" external address instead (one that gets converted into the
;; other one during canonicalization), so I don't have to worry about overlapping with existing
;; addresses
(define next-generated-address 100)

(define (generate-abstract-messages type max-depth)
  (term (generate-abstract-messages/mf ,type ,max-depth)))

(define-metafunction csa#
  generate-abstract-messages/mf : τ natural -> (v# ...)
  [(generate-abstract-messages/mf Nat _) ((* Nat))]
  [(generate-abstract-messages/mf String _) ((* String))]
  [(generate-abstract-messages/mf (Union) _) ()]
  [(generate-abstract-messages/mf (Union [t τ ...] ...) 0) ((* (Union [t τ ...] ...)))]
  [(generate-abstract-messages/mf (Union [t_1 τ_1 ...] [t_rest τ_rest ...] ...) natural_max-depth)
   (v#_1 ... v#_rest ...)
   ;; (side-condition (displayln "generate-abs-var"))
   (where (v#_1 ...) (generate-variants natural_max-depth t_1 τ_1 ...))
   (where (v#_rest ...)
          (generate-abstract-messages/mf (Union [t_rest τ_rest ...] ...) natural_max-depth))]
  [(generate-abstract-messages/mf (Union) _) ()]
  [(generate-abstract-messages/mf (minfixpt X τ) natural_max-depth)
   (generate-abstract-messages/mf (type-subst τ X (minfixpt X τ)) natural_max-depth)]
  [(generate-abstract-messages/mf (Record [l τ] ...) 0)
   ((* (Record [l τ] ...)))]
  ;; TODO: max-depth should refer to the number of unrollings of the fixpoint; that's it
  [(generate-abstract-messages/mf (Record [l_1 τ_1] [l_rest τ_rest] ...) natural_max-depth)
   ,(for/fold ([records-so-far null])
              ([sub-record (term (generate-abstract-messages/mf (Record [l_rest τ_rest] ...) natural_max-depth))])
      (append
       ;; TODO: do I need to do a (max 0) on natural_max-depth here?
       (for/list ([generated-v (term (generate-abstract-messages/mf τ_1 ,(sub1 (term natural_max-depth))))])
         (redex-let csa# ([(record [l_other v#_other] ...) sub-record]
                          [v#_1 generated-v])
           (term (record [l_1 v#_1] [l_other v#_other] ...))))
       records-so-far))]
  [(generate-abstract-messages/mf (Record) natural_max-depth)
   ((record))]
  [(generate-abstract-messages/mf (Addr τ) _)
   ,(begin
      (set! next-generated-address (add1 next-generated-address))
      (term ((obs-ext ,next-generated-address τ))))]
  [(generate-abstract-messages/mf (Listof τ) _) ((* (Listof τ)))]
  [(generate-abstract-messages/mf (Vectorof τ) _) ((* (Vectorof τ)))]
  [(generate-abstract-messages/mf (Hash τ_1 τ_2) _) ((* (Hash τ_1 τ_2)))])

(define-metafunction csa#
  generate-variants : natural t τ ... -> ((variant t v# ...) ...)
  [(generate-variants _ t) ((variant t))]
  [(generate-variants natural_max-depth t τ_1 τ_rest ...)
   ,(for/fold ([variants-so-far null])
              ([sub-variant (term (generate-variants natural_max-depth t τ_rest ...))])
      (append
       ;; TODO: do I need to do a (max 0) on natural_max-depth here?
       (for/list ([generated-v (term (generate-abstract-messages/mf τ_1 ,(sub1 (term natural_max-depth))))])
         (redex-let csa# ([(variant t v#_other ...) sub-variant]
                          [v#_1 generated-v])
           (term (variant t v#_1 v#_other ...))))
       variants-so-far))
   ;; (side-condition (printf "generate-variants: ~s\n" (term ( t τ_1 τ_rest ...))))
   ])

(module+ test
  (require
   rackunit
   "rackunit-helpers.rkt")

  (check-same-items?
   (term (generate-abstract-messages/mf Nat 0))
   (term ((* Nat))))
  ;; tuples of both depths
  ;; addresses...?
  ;; symbols
  ;; recursive types (list of Nat, up to certain depth

  ;; TODO: rewrite these tests using records and variants
  ;; (check-same-items? (term (generate-abstract-messages/mf 'Begin 0)) (term ('Begin)))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Union 'A 'B) 0))
  ;;  (term ('A 'B)))
  ;; ;; check: allow reordering
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Union 'A 'B) 0))
  ;;  (term ('B 'A)))
  ;; (check-same-items? (term (generate-abstract-messages/mf (Union) 0)) (term ()))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (minfixpt Dummy Nat) 0))
  ;;  (term ((* Nat))))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Tuple Nat Nat) 0))
  ;;  (term ((* (Tuple Nat Nat)))))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Tuple Nat Nat) 1))
  ;;  (term ((tuple (* Nat) (* Nat)))))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Tuple (Union 'A 'B) (Union 'C 'D)) 0))
  ;;  (term ((* (Tuple (Union 'A 'B) (Union 'C 'D))))))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf (Tuple (Union 'A 'B) (Union 'C 'D)) 1))
  ;;  (term ((tuple 'A 'C) (tuple 'A 'D) (tuple 'B 'C) (tuple 'B 'D))))
  ;; (define list-of-nat (term (minfixpt NatList (Union 'Null (Tuple 'Cons Nat NatList)))))
  ;; TODO: get this fixpoint test to work
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf ,list-of-nat 0))
  ;;  (term ('Null (* ,list-of-nat))))
  (check-same-items?
   (term (generate-abstract-messages/mf (Union) 0))
   (term ()))
  (check-same-items?
   (term (generate-abstract-messages/mf (Union) 1))
   (term ()))
  (check-same-items?
   (term (generate-abstract-messages/mf (Union [A] [B String (Union [C] [D])]) 5))
   (term ((variant A)
          (variant B (* String) (variant C))
          (variant B (* String) (variant D)))))
  ;; (check-same-items?
  ;;  (term (generate-abstract-messages/mf
  ;;         (Union (AppendRejected Nat Nat (Addr Nat))
  ;;                (AppendSuccessful Nat Nat (Addr Nat)))
  ;;         5))
  ;;  (term ((variant AppendRejected (* Nat) (* Nat) ADDR-HOLE)
  ;;         (variant AppendSuccessful (* Nat) (* Nat) ADDR-HOLE))))
  )

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

(struct csa#-transition
  (trigger ; follows trigger# above
   outputs ; list of abstract-addr/abstract-message 2-tuples
   final-config) ; an abstract program configuration
  #:transparent)

(define (csa#-internal-trigger? trigger)
  (match trigger
    ['timeout #t]
    [`(internal-message ,_) #t]
    [_ #f]))

(define csa#-output-address car)
(define csa#-output-message cadr)

;; Evaluates the handler triggered by sending message to actor-address, return the list of possible
;; results (which are tuples of the final behavior expression and the list of outputs)
(define (csa#-handle-message prog-config actor-address message)
  (redex-let csa# ([(any_actors-before
                     (a# ((name state-defs (_ ... (define-state (s [x_s τ_s] ..._n) (x_m) e# any_timeout-clause ...) _ ...)) (in-hole E# (goto s v# ..._n))))
                     any_actors-after)
                    (config-actor-and-rest-by-address prog-config actor-address)]
                   [(_ any_messages any_receptionists any_externals) prog-config])
    ;; TODO: deal with the case where x_m shadows an x_s
    (define initial-config (inject/H# (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...))))
    (define prog-config-context
      (term (,(append (term any_actors-before)
                      (list (term (a# (state-defs hole))))
                      (term any_actors-after))
             any_messages
             any_receptionists
             any_externals)))
    (eval-handler initial-config
                  (term (external-receive ,actor-address ,message))
                  actor-address
                  prog-config-context)))

;; Returns all transitions possible from this program configuration by handling an internal message
(define (csa#-handle-all-internal-messages prog-config)
  (let loop ([transitions-so-far null]
             [processed-messages null]
             [messages-to-process (csa#-config-messages prog-config)])
    (match messages-to-process
      [(list) transitions-so-far]
      [(list message messages-to-process ...)
       (redex-let* csa#
         ([(a#int v#_msg multiplicity) message]
          [(any_actors-before
            (_ ((name state-defs (_ ... (define-state (s [x_s τ_s] ..._n) (x_m) e# any_timeout-clause ...) _ ...)) (in-hole E# (goto s v# ..._n))))
            any_actors-after)
           (config-actor-and-rest-by-address prog-config (term a#int))]
          [(_ _ any_receptionists any_externals) prog-config])
         ;; TODO: deal with the case where x_m shadows an x_s
         (define initial-config (inject/H# (term (csa#-subst-n e# [x_m v#_msg] [x_s v#] ...))))
         (define prog-config-context
           (term (,(append (term any_actors-before)
                           (list (term (a#int (state-defs hole))))
                           (term any_actors-after))
                  ,(append processed-messages
                           (if (redex-match? csa# * (term multiplicity)) (list message) null)
                           messages-to-process)
                  any_receptionists
                  any_externals)))
         (define new-transitions
           (eval-handler initial-config
                         (term (internal-receive a#int v#_msg))
                         (term a#int)
                         prog-config-context))
         (loop (append transitions-so-far new-transitions)
               (append processed-messages (list message))
               messages-to-process))])))

;; Returns all transitions possible from this program configuration by taking a timeout
(define (csa#-handle-all-timeouts prog-config)
  (redex-let csa# ([(any_actors any_messages any_receptionists any_externals) prog-config])
    (let loop ([transitions-so-far null]
               [actors-before null]
               [actors-after (term any_actors)])
      (match actors-after
        [(list) transitions-so-far]
        [(list actor actors-after ...)
         (define new-transitions
           (csa#-handle-actor-maybe-timeout actors-before
                                            actor
                                            actors-after
                                            (term any_messages)
                                            (term any_receptionists)
                                            (term any_externals)))
         (loop (append transitions-so-far new-transitions)
               (append actors-before (list actor))
               actors-after)]))))

;; Returns the transitions that happen by executing this actor's timeout if it has one, or null if not
(define (csa#-handle-actor-maybe-timeout actors-before
                                         actor
                                         actors-after
                                         messages
                                         receptionists
                                         externals)
  (define matches
    (redex-match csa#
                 (any_address ((name state-defs (_ ... (define-state (s [x_s τ_s] ..._n)  _    _  [(timeout _) e#]) _ ...)) (in-hole E# (goto s v# ..._n))))
                 actor))
  (match matches
    [#f null]
    [(list the-match)
     (define (get-binding name) (bind-exp (findf (lambda (binding) (eq? (bind-name binding) name)) (match-bindings the-match))))
     (redex-let csa# ([(x_s ...) (get-binding 'x_s)]
                      [(v# ...) (get-binding 'v#)]
                      [e# (get-binding 'e#)]
                      [any_address (get-binding 'any_address)]
                      [(name state-defs _) (get-binding 'state-defs)])
       (define prog-config-context
         (term (,(append actors-before (term ((any_address (state-defs hole)))) actors-after)
                ,messages
                ,receptionists
                ,externals)))
       (eval-handler (inject/H# (term (csa#-subst-n e# [x_s v#] ...)))
                     (term (timeout any_address))
                     (term any_address)
                     prog-config-context))]
    [_ (error 'csa#-handle-actor-maybe-timeout "Got multiple matches for actor: ~s\n" actor)]))

(define (eval-handler handler-config trigger address config-context)
  (define final-configs (apply-reduction-relation* handler-step# handler-config #:cache-all? #t))
  (define non-abstraction-stuck-final-configs
    ;; Filter out those stuck because of over-abstraction
    (filter (compose not stuck-abstraction-handler-config?) final-configs))

  ;; Debugging
  ;; (printf "The initial config: ~s\n" initial-config)
  ;; (printf "Number of raw results: ~s\n" (length final-configs))
  ;; (printf "Number of non-stuck results: ~s\n" (length non-abstraction-stuck-final-configs))

  (unless (andmap complete-handler-config? non-abstraction-stuck-final-configs)
    (error 'eval-handler
           "Abstract evaluation did not complete\nInitial config: ~s\nFinal stuck configs:~s"
           handler-config
           (filter (compose not complete-handler-config?) non-abstraction-stuck-final-configs)))
  (for/list ([config non-abstraction-stuck-final-configs])
    ;; TODO: rename outputs to something like "transmissions", because some of them stay internal to
    ;; the program
    (match-define (list behavior-exp outputs loop-outputs spawns) config)
    ;; TODO: check that there are no internal loop outputs, or refactor that code entirely
    (define new-prog-config
      (merge-new-messages
       (merge-new-actors (plug config-context behavior-exp) spawns)
       (filter internal-output? outputs)))
    (define next-state (redex-let csa# ([(in-hole E# (goto s _ ...)) behavior-exp]) (term s)))
    (csa#-transition trigger (filter (negate internal-output?) outputs) new-prog-config)))

;; Returns true if the config is one that is unable to step because of an over-approximation in the
;; abstraction
(define (stuck-abstraction-handler-config? c)
  (or (redex-match csa#
                   ((in-hole E# (list-ref (list) v#)) ([a#ext v#_out] ...) any_loop)
                   c)
      (redex-match csa#
                   ((in-hole E# (vector-ref (vector) v#)) ([a#ext v#_out] ...) any_loop)
                   c)
      (redex-match csa#
                   ((in-hole E# (hash-ref (hash) v# v#_2)) ([a#ext v#_out] ...) any_loop)
                   c)))

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
          (redex-set-add any_loop-outputs [a# v#])
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

    ;; Goto context removal
    (--> ((in-hole E# (goto s v# ...)) (any_outputs ...) any_loop-outputs any_spawns)
         ((goto s v# ...) (any_outputs ...) any_loop-outputs any_spawns)
         (side-condition (not (redex-match csa# hole (term E#))))
         (side-condition (not (redex-match csa# (in-hole E#_2 (spawning _ _ hole _ ...)) (term E#))))
         ;; (side-condition (printf "running goto rule: ~s\n" (term (in-hole E# (goto s v# ...)))))
         ;; (side-condition (printf "goto result: ~s\n" (term (goto s v# ...))))
         GotoRemoveContext)

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
                      [μ# (term ())]
                      [ρ# (term ((init-addr 0 Nat)))])
                (term (α# μ# ρ# ()))))

  (check-not-false (redex-match csa# K# (csa#-make-simple-test-config (term (* Nat)))))

  (define-check (csa#-exp-steps-to? e1 e2)
    (define next-steps (apply-reduction-relation handler-step# (inject/H# e1)))
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

  ;; Check that internal addresses in the transmissions do not change the evaluation (had a problem
  ;; with this before)
  (check-equal?
   (apply-reduction-relation* handler-step# (inject/H# (term (begin (send (init-addr 1 Nat) (* Nat)) (goto A)))))
   (list (term ((goto A) (((init-addr 1 Nat) (* Nat))) () ()))))

  (check-equal?
   (apply-reduction-relation* handler-step#
     (inject/H# (term (begin (spawn L Nat (goto A) (define-state (A) (x) (goto A))) (goto B)))))
   (list (term ((goto B) () () ([(spawn-addr L NEW Nat) [((define-state (A) (x) (goto A))) (goto A)]]))))))

(define (csa#-merge-duplicate-messages prog-config)
  (redex-let csa# ([(any_actors any_messages any_rec any_ext) prog-config])
    (term (any_actors
           ,(merge-duplicate-messages-from-list (term any_messages))
           any_rec
           any_ext))))

(define (merge-duplicate-messages-from-list message-list)
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

;; For two "messages" (the things inside the message queue in a program config), returns true if they
;; have the same address and value
(define (same-message? m1 m2)
  (redex-let csa# ([(a#_1 v#_1 _) m1]
                   [(a#_2 v#_2 _) m2])
    (equal? (term (a#_1 v#_1)) (term (a#_2 v#_2)))))

(module+ test
  (check-equal?
   (merge-duplicate-messages-from-list
    (term (((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1))))
   (term (((obs-ext 1 Nat) (* Nat) *))))

    (check-equal?
   (merge-duplicate-messages-from-list
    (term (((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1)
           ((obs-ext 1 Nat) (* Nat) 1))))
   (term (((obs-ext 1 Nat) (* Nat) *))))

  (check-equal?
   (merge-duplicate-messages-from-list
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

;; Abstractly adds the set of new messages to the existing set
(define (merge-new-messages config new-message-list)
  (redex-let csa# ([(any_actors any_messages any_rec any_ext) config]
                   [((a# v#) ...) new-message-list])
    (term (any_actors
           ,(merge-duplicate-messages-from-list (append (term any_messages) (term ((a# v# 1) ...))))
           any_rec
           any_ext))))

(module+ test
  (check-equal?
   (merge-new-messages (term (() () () ())) (list (term ((init-addr 0 Nat) (* Nat)))))
   (term (() (((init-addr 0 Nat) (* Nat) 1)) () ())))

  (check-equal?
   (merge-new-messages (term (() (((init-addr 0 Nat) (* Nat) 1)) () ()))
                       (list (term ((init-addr 0 Nat) (* Nat)))))
   (term (() (((init-addr 0 Nat) (* Nat) *)) () ())))

  (check-equal?
   (merge-new-messages (term (() (((init-addr 0 Nat) (* Nat) 1)) () ()))
                       (list (term ((init-addr 1 Nat) (* Nat)))))
   (term (() (((init-addr 0 Nat) (* Nat) 1) ((init-addr 1 Nat) (* Nat) 1)) () ())))

  (check-equal?
   (merge-new-messages (term (()
                              (((init-addr 1 Nat) (* (Addr Nat)) 1)
                               ((init-addr 1 Nat) (obs-ext 0 Nat) 1))
                              ()
                              ()))
                       (term (((init-addr 1 Nat) (* (Addr Nat))))))
   (term (()
          (((init-addr 1 Nat) (* (Addr Nat)) *)
           ((init-addr 1 Nat) (obs-ext 0 Nat) 1))
          ()
          ()))))

(define (merge-new-actors config new-actors)
  (redex-let csa# ([((any_actors ...) any_messages any_rec any_ext) config])
             (term (,(append (term (any_actors ...)) new-actors)
                    any_messages
                    any_rec
                    any_ext))))

(module+ test
  (define new-spawn1
    (term ((spawn-addr foo NEW Nat) (((define-state (A) (x) (goto A))) (goto A)))))
  (define init-actor1
    (term ((init-addr 0 Nat) (((define-state (B) (x) (goto B))) (goto B)))))
  (test-equal? "merge-new-actors test"
               (merge-new-actors
                (make-single-actor-abstract-config init-actor1)
                (list new-spawn1))
               (term ((,init-actor1 ,new-spawn1) () ((init-addr 0 Nat)) ()))))

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

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; Abstracts the given CSA program configuration, with a maximum recursion depth for values
;;
;; NOTE: currently supports only no-messages, no-externals configs
(define (α-config concrete-config internal-addresses max-depth)
  (term (α-config/mf ,concrete-config ,internal-addresses ,max-depth)))

(define-metafunction csa#
  α-config/mf : K (a_internal ...) natural_recursion-depth -> K#
  [(α-config/mf ((αn ...) ; actors
                 () ; messages-in-transit
                 (a_rec ...) ; receptionists
                 () ; externals
                 )
                (a_internal ...)
                natural_depth)
   ((α#n ...) () ((α-e a_rec (a_internal ...) natural_depth) ...) ())
   (where (α#n ...) ((α-actor αn (a_internal ...) natural_depth) ...))])

(define-metafunction csa#
  α-actor : αn (a_internals ...) natural_depth -> α#n
  [(α-actor (a_this ((S ...) e)) (a ...) natural_depth)
   ((α-e a_this (a ...) natural_depth)
    (((α-S S (a ...) natural_depth) ...)
     (α-e e (a ...) natural_depth)))])

(define-metafunction csa#
  α-S : S (a_internals ...) natural_depth -> S#
  [(α-S (define-state (s [x τ] ...) (x_m) e) (a ...) natural_depth)
   (define-state (s [x τ] ...) (x_m) (α-e e (a ...) natural_depth))]
  [(α-S (define-state (s [x τ] ...) (x_m) e [(timeout n) e_timeout]) (a ...) natural_depth)
   (define-state (s [x τ] ...) (x_m)
     (α-e e (a ...) natural_depth)
     [(timeout (* Nat)) (α-e e_timeout (a ...) natural_depth)])])

;; Abstracts the given expression to the given depth, with the given address list indicating the set
;; of internal addresses
(define-metafunction csa#
  α-e : e (a ...) natural_depth -> e#
  [(α-e natural _ _) (* Nat)]
  [(α-e string _ _) (* String)]
  [(α-e x _ _) x]
  [(α-e (addr natural τ) (_ ... (addr natural τ) _ ...) _) (init-addr natural τ)]
  [(α-e (addr natural τ) _ _) (obs-ext natural τ)]
  [(α-e (goto s e ...) (a ...) natural_depth) (goto s (α-e e (a ...) natural_depth) ...)]
  [(α-e (begin e ...) (a ...) natural_depth) (begin (α-e e (a ...) natural_depth) ...)]
  [(α-e (send e_1 e_2) (a ...) natural_depth)
   (send (α-e e_1 (a ...) natural_depth) (α-e e_2 (a ...) natural_depth))]
  [(α-e (spawn any_location τ e S ...) (a ...) natural_depth)
   (spawn any_location τ (α-e e (a ...) natural_depth) (α-S S (a ...) natural_depth) ...)]
  [(α-e (let ([x e_binding] ...) e_body) (a ...) natural)
   (let ([x (α-e e_binding (a ...) natural)] ...) (α-e e_body (a ...) natural))]
  [(α-e (case e_val [(t x ...) e_clause] ...) (a ...) natural_depth)
   (case (α-e e_val (a ...) natural_depth) [(t x ...) (α-e e_clause (a ...) natural_depth)] ...)]
  [(α-e (printf string e ...) (a ...) natural_depth)
   (printf string (α-e e (a ...) natural_depth) ...)]
  [(α-e (primop e ...) (a ...) natural_depth) (primop (α-e e (a ...) natural_depth) ...)]
  ;; TODO: check for the depth=0 case on variants
  [(α-e (variant t e ...) (a ...) natural_depth)
   ;; TODO: take out the "max" issue here
   (variant t (α-e e (a ...) ,(max 0 (- (term natural_depth) 1))) ...)]
  ;; TODO: check for the depth=0 case on records
  [(α-e (record [l e] ...) (a ...) natural_depth)
   ;; TODO: take out the "max" issue here
   (record [l (α-e e (a ...) ,(max 0 (sub1 (term natural_depth))))] ...)]
  [(α-e (: e l) (a ...) natural_depth) (: (α-e e (a ...) natural_depth) l)]
  [(α-e (! e_1 [l e_2]) (a ...) natural_depth)
   (! (α-e e_1 (a ...) natural_depth) [l (α-e e_2 (a ...) natural_depth)])]
  ;; TODO: check for the depth=0 case on lists and vectors
  [(α-e (list e ...) (a ...) natural_depth)
   (list e#_unique ...)
   (where (e# ...) ((α-e e (a ...) ,(max 0 (sub1 (term natural_depth)))) ...))
   (where (e#_unique ...) ,(set->list (list->set (term (e# ...)) )))]
  [(α-e (vector e ...) (a ...) natural_depth)
   (vector e#_unique ...)
   (where (e# ...) ((α-e e (a ...) ,(max 0 (sub1 (term natural_depth)))) ...))
   (where (e#_unique ...) ,(set->list (list->set (term (e# ...)) )))]
  [(α-e (hash) _ _) (hash)]
  [(α-e (for/fold ([x_1 e_1]) ([x_2 e_2]) e) (a ...) natural)
   (for/fold ([x_1 (α-e e_1 (a ...) natural)])
             ([x_2 (α-e e_2 (a ...) natural)])
     (α-e e (a ...) natural))])

(module+ test
  (check-equal? (term (α-e (record [f1 1] [f2 2]) () 1))
                (term (record [f1 (* Nat)] [f2 (* Nat)])))
  (check-not-false
   (redex-match? csa#
                 (variant Foo (init-addr 1 Nat) (obs-ext 2 Nat))
                 (term (α-e (variant Foo (addr 1 Nat) (addr 2 Nat)) ((addr 1 Nat)) 10))))
  (check-equal? (term (α-e (list 1 2) () 10))
                (term (list (* Nat))))
  (check-equal? (term (α-e (vector 1 2) () 10))
                (term (vector (* Nat)))))

(define (α-receptionists addresses)
  (redex-let csa# ([(a ...) addresses])
             (term ((α-a a) ...))))

(define-metafunction csa#
  α-a : a -> a#int
  [(α-a (addr natural τ)) (init-addr natural τ)])

(module+ test
  (check-equal? (α-receptionists (term ((addr 0 Nat))))
                (term ((init-addr 0 Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Further Abstraction

(define (blur-irrelevant-actors config flag-to-blur)
  (redex-let csa# ([((α#n ...) μ# ρ# any_escaped) config])
             (define all-actors (term (α#n ...)))
             ;; 1. Get list of addresses to blur
             (define actors-to-blur
               (filter (lambda (actor)
                         (address-has-flag? (csa#-actor-address actor) flag-to-blur))
                       all-actors))
             (define addrs-to-blur (map csa#-actor-address actors-to-blur))
             ;; 2. for each blurred actor, get its ext-obs addrs
             (define newly-escaped-externals (map obs-externals-in actors-to-blur))
             ;; 3. blur those actors
             (define remaining-actors
               (filter
                 (lambda (actor) (not (member (csa#-actor-address actor) addrs-to-blur)))
                 all-actors))
             ;; 4. rename those addresses throughout to "blurred-internal" and rename remaining flags
             ;; to OLD
             ;;
             ;; 5. merge ext-obs addrs into escape
             (term (,(blur-and-age-internal-addrs remaining-actors addrs-to-blur)
                    ,(blur-and-age-internal-addrs (term μ#) addrs-to-blur)
                    ,(blur-and-age-internal-addrs (term ρ#) addrs-to-blur)
                    ,(remove-duplicates (append (term any_escaped) addrs-to-blur))))))

;; TODO: remove this function; just use its parts
(define (blur-and-age-internal-addrs some-term addresses-to-blur)
  (csa#-age-internal-addrs (blur-internal-addrs some-term addresses-to-blur)))

(define (blur-internal-addrs some-term addresses-to-blur)
  (match some-term
    [(and addr `(spawn-addr ,loc ,flag ,type))
     (if (member addr addresses-to-blur)
         (term blurred-internal)
         addr)]
    [(list terms ...)
     (map (curryr blur-internal-addrs addresses-to-blur) terms)]
    [_ some-term]))

(define (csa#-age-internal-addrs some-term)
  (match some-term
    [(and addr `(spawn-addr ,loc ,flag ,type))
     (if (equal? flag 'NEW)
         (term (spawn-addr ,loc OLD ,type))
         addr)]
    [(list terms ...) (map csa#-age-internal-addrs terms)]
    [_ some-term]))

(module+ test
  (test-equal? "blur and age test"
    (blur-and-age-internal-addrs
     (term (((spawn-addr foo OLD Nat) (spawn-addr foo NEW Nat))
            (spawn-addr bar NEW Nat)
            (spawn-addr bar OLD Nat)
            (spawn-addr baz OLD Nat)
            (spawn-addr quux NEW Nat)))
     (list (term (spawn-addr foo NEW Nat)) (term (spawn-addr bar OLD Nat))))
    (term (((spawn-addr foo OLD Nat) blurred-internal)
           (spawn-addr bar OLD Nat)
           blurred-internal
           (spawn-addr baz OLD Nat)
           (spawn-addr quux OLD Nat)))))

(define (address-has-flag? addr flag)
  (match flag
    ['OLD (redex-match? csa# (spawn-addr _ OLD _) addr)]
    ['NEW (redex-match? csa# (spawn-addr _ NEW _) addr)]))

(define (obs-externals-in some-term)
  (term (obs-externals-in/mf ,some-term)))

(define-metafunction csa#
  obs-externals-in/mf : any -> (a#ext ...)
  [(obs-externals-in/mf (obs-ext natural any_type)) ((obs-ext natural any_type))]
  [(obs-externals-in/mf (any ...))
   (a#ext ... ...)
   (where ((a#ext ...) ...) ((obs-externals-in/mf any) ...))]
  [(obs-externals-in/mf _) ()])

(define (csa#-blur-and-age-receptionists receptionists spawn-flag-to-blur)
  (csa#-age-internal-addrs
   (filter (negate (curryr address-has-flag? spawn-flag-to-blur)) receptionists)))

(module+ test
  (test-equal? "Receptionist blur/age test"
    (csa#-blur-and-age-receptionists
     (list '(init-addr 1 Nat)
           '(init-addr 2 Nat)
           '(spawn-addr 1 OLD Nat)
           '(spawn-addr 2 OLD Nat)
           '(spawn-addr 2 NEW Nat))
     'OLD)
    (list '(init-addr 1 Nat)
          '(init-addr 2 Nat)
          '(spawn-addr 2 OLD Nat)))
  (test-equal? "Receptionist blur/age test 2"
    (csa#-blur-and-age-receptionists
     (list '(init-addr 1 Nat)
           '(init-addr 2 Nat)
           '(spawn-addr 1 OLD Nat)
           '(spawn-addr 2 OLD Nat)
           '(spawn-addr 2 NEW Nat))
     'NEW)
    (list '(init-addr 1 Nat)
          '(init-addr 2 Nat)
          '(spawn-addr 1 OLD Nat)
          '(spawn-addr 2 OLD Nat))))

;; TODO: rename this function (need a better term than "blur"; "fuzz" is taken
;;
;; "Blurs" out any address not in the given "relevant" list into an unobserved address
(define (blur-externals config relevant-external-addrs)
  (redex-let csa# ([(any_actors any_msg any_rec any_escapes) config])
             (term ((blur-externals/mf any_actors ,relevant-external-addrs)
                    (blur-externals/mf any_msg ,relevant-external-addrs)
                    (blur-externals/mf any_rec ,relevant-external-addrs)
                    ,(filter (curryr member relevant-external-addrs) (term any_escapes))))))

(define-metafunction csa#
  blur-externals/mf : any (a#ext ...) -> any
  [(blur-externals/mf (obs-ext natural any_type) (_ ... (obs-ext natural any_type) _ ...))
   (obs-ext natural any_type)]
  [(blur-externals/mf (obs-ext natural τ) _)
   (* (Addr τ))]
  [(blur-externals/mf (any_kw any ...) (any_addr ...))
   (any_kw any_result ...)
   (side-condition (member (term any_kw) (list 'vector 'list 'hash)))
   (where (any_result ...) ,(remove-duplicates (term ((blur-externals/mf any (any_addr ...)) ...))))]
  [(blur-externals/mf (any ...) (any_addr ...))
   ((blur-externals/mf any (any_addr ...)) ...)]
  [(blur-externals/mf any _) any])

(module+ test
  (check-equal?
   (blur-externals
      (redex-let* csa#
                  ([α#n (term
                         ((init-addr 0 Nat)
                          (((define-state (A [x (Addr Nat)] [y (Addr Nat)] [z (Addr Nat)]) (m)
                              (begin
                                (send (obs-ext 1 Nat) (* Nat))
                                (send (obs-ext 2 Nat) (* Nat))
                                (goto A x y z))))
                           (goto A (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat)))))]
                   [K# (term ((α#n) () ((init-addr 0 Nat)) ()))])
             (term K#))
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
                [K# (term ((α#n) () ((init-addr 0 Nat)) ()))])
               (term K#)))

  ;; Make sure duplicates are removed from vectors, lists, and hashes
  (check-equal?
   (term (blur-externals/mf
          ,(redex-let csa#
                      ([e# (term (hash (obs-ext 1 Nat)
                                       (obs-ext 2 Nat)
                                       (obs-ext 3 Nat)
                                       (obs-ext 4 Nat)))])
                      (term e#))
          ((obs-ext 1 Nat) (obs-ext 3 Nat))))
   (term (hash (obs-ext 1 Nat) (* (Addr Nat)) (obs-ext 3 Nat))))

  (check-equal?
   (term (blur-externals/mf
          ,(redex-let csa#
                      ([e# (term (list (obs-ext 1 Nat)
                                       (obs-ext 2 Nat)
                                       (obs-ext 3 Nat)
                                       (obs-ext 4 Nat)))])
                      (term e#))
          ()))
   (term (list (* (Addr Nat)))))

  (check-equal?
   (term (blur-externals/mf
          ,(redex-let csa#
                      ([e# (term (vector (obs-ext 1 Nat)
                                         (obs-ext 2 Nat)
                                         (obs-ext 3 Nat)
                                         (obs-ext 4 Nat)))])
                      (term e#))
          ((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat))))
   (term (vector (obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat))))

  (test-equal? "Just remove blurred addresses from escape list"
               (blur-externals
                (term (() () () ((obs-ext 1 Nat) (obs-ext 2 Nat) (obs-ext 3 Nat) (obs-ext 4 Nat))))
                (term ((obs-ext 1 Nat) (obs-ext 3 Nat))))
               (term (() () () ((obs-ext 1 Nat) (obs-ext 3 Nat))))))

;; ---------------------------------------------------------------------------------------------------
;; Canonicalization Help

(define (csa#-sort-escapes config)
  (redex-let csa# ([(any_actors any_messages any_receptionists any_escapes) config])
    (term (any_actors
           any_messages
           any_receptionists
           ,(sort (term any_escapes) obs-ext<)))))

(define (obs-ext< a b)
  (< (second a) (second b)))

(module+ test
  (test-case "Obs-ext address comparison"
    (define a (term (obs-ext 2 Nat)))
    (define b (term (obs-ext 4 Nat)))
    (check-not-false (redex-match csa# a#ext a))
    (check-not-false (redex-match csa# a#ext b))
    (check-true (obs-ext< a b))))

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (make-single-actor-abstract-config actor)
  (term (make-single-actor-abstract-config/mf ,actor)))

(define-metafunction csa#
  make-single-actor-abstract-config/mf : α#n -> K#
  [(make-single-actor-abstract-config/mf α#n)
   ((α#n) () (,(csa#-actor-address (term α#n))) ())])

;; ---------------------------------------------------------------------------------------------------
;; Selectors

;; Returns a list of actors (α#n's)
(define (csa#-config-actors config)
  (redex-let csa# ([(α# _ ...) config])
             (term α#)))

(define (csa#-config-messages config)
  (redex-let csa# ([(_ μ# _ ...) config])
             (term μ#)))

(define (config-actor-and-rest-by-address config addr)
  (term (config-actor-and-rest-by-address/mf ,config ,addr)))

(define-metafunction csa#
  config-actor-and-rest-by-address/mf : K# a#int -> ((α#n ...) α#n (α#n ...))
  [(config-actor-and-rest-by-address/mf ((any_1 ... (name the-actor (a#int _)) any_2 ...) _ _ _)
                                        a#int_target)
   ((any_1 ...) the-actor (any_2 ...))
   (judgment-holds (same-internal-address-without-type? a#int a#int_target))])

(define-judgment-form csa#
  #:mode (same-internal-address-without-type? I I)
  #:contract (same-internal-address-without-type? a#int a#int)
  [------
   (same-internal-address-without-type? (init-addr natural _) (init-addr natural _))]
  [------
   (same-internal-address-without-type? (spawn-addr any_loc NEW _) (spawn-addr any_loc NEW _))]
  [------
   (same-internal-address-without-type? (spawn-addr any_loc OLD _) (spawn-addr any_loc OLD _))])

(define (csa#-actor-address a)
  (redex-let* csa# ([α#n a]
                    [(a#int _) (term α#n)])
              (term a#int)))

(define (csa#-receptionist-type addr)
  (term (csa#-receptionist-type/mf ,addr)))

(define-metafunction csa#
  csa#-receptionist-type/mf : a#int -> τ
  [(csa#-receptionist-type/mf (init-addr natural τ)) τ]
  [(csa#-receptionist-type/mf (spawn-addr _ _ τ)) τ])

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

;; ---------------------------------------------------------------------------------------------------
;; Debug helpers

(define (prog-config-without-state-defs config)
  (redex-let csa# ([(((a#int (_ e#)) ...) μ# ρ# any_escapes) config])
             (term (((a#int e#) ...) μ# ρ# any_escapes))))

(define (prog-config-goto config)
  ;; NOTE: only suports single-actor progs for now
  (redex-let csa# ([(((a#int (_ e#))) μ# ρ# any_escapes) config])
             (term e#)))

;; ---------------------------------------------------------------------------------------------------
;; Generic Redex helpers

(define-metafunction csa#
  redex-set-add : (any ...) any -> (any ...)
  [(redex-set-add (any_1 ... any any_2 ...) any) (any_1 ... any any_2 ...)]
  [(redex-set-add (any_1 ...) any_2) (any_1 ... any_2)])

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define (csa#-new-spawn-address? a)
  (redex-match? csa# (spawn-addr _ NEW _) a))

(module+ test
  (test-case "New-span-addr? check"
    (define a (term (spawn-addr 5 NEW Nat)))
    (define b (term (spawn-addr 6 OLD Nat)))
    (check-not-false (redex-match csa# a#int a))
    (check-not-false (redex-match csa# a#int b))
    (check-true (csa#-new-spawn-address? a))
    (check-false (csa#-new-spawn-address? b))))
