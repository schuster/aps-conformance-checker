;; Defines the abstract interpretation of CSA programs/configurations

#lang racket

(provide
 csa#
 generate-abstract-messages
 csa#-eval-transition
 (struct-out csa#-transition)
 csa#-output-address
 csa#-output-message
 csa#-observable-output?
 csa#-transition-next-state
 α-config
 step-prog-final-behavior
 csa#-actor-address
 csa#-actor-current-state
 csa#-config-only-actor)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "csa.rkt")

;; Abstract interpretation version of CSA
;; NOTE: this handles only single-actor configurations right now
;; TODO: make the language inheritance hierarchy correct
(define-extended-language csa# csa-eval
  (K# (α# μ# ρ# χ#)) ; TODO: update this
  ;; NOTE: for now, assuming only the one special actor
  (α# (α#n)) ; NOTE: for now, does not handle configs with more than one actor
  (α#n (a#int ((S# ...) e#)))
  (μ# ()) ; NOTE: for now, assuming no internal sends
  (S# (define-state (s [x τ] ...) (x) e#)
      ;; TODO: not dealing with timeouts yet...
      ;; (define-state (s x ...) (x) e# [(timeout Nat) e#])
      )
  ;; TODO: these probably should be sets of values, right?
  (v# a# ; TODO: replace this one with a special pattern
      (variant t v# ...)
      (record [l v#] ...)
      (* τ)
      (list v# ...)
      (vector v# ...)
      (hash v# ...))
  (v#template
   ADDR-HOLE
   (variant t v#template ...)
   (record [l v#template] ...)
   (list v#template ...)
   (vector v#template ...)
   (hash v#template ...)
   (* τ))
  (e# (spawn τ e# S ...)
      (goto s e# ...)
      (send e# e#)
      self
      (begin e# ... e#)
      (let ([x e#] ...) e#)
      (case e# [(t x ...) e#] ...)
      (variant t e# ...)
      (record [l e#] ...)
      (: e# l)
      (! e# [l e#])
      (primop e# ...)
      (list e# ...)
      (vector e# ...)
      (hash)
      a#
      x
      (* τ))
  (a# a#int a#ext) ; internal and external addresses
  (a#int SINGLE-ACTOR-ADDR)
  (a#ext
   (* (Addr τ)) ; unobserved address
   ;; NOTE: only a finite number of addresses in the initial config, so we can use natural numbers
   ;; here
   (init-addr natural)
   (received-addr s v#template natural time-flag))
  (time-flag MOST-RECENT PREVIOUS)
  ;; TODO: include types in the receptionists and externals (maybe? Might not need them if they're
  ;; tracked elsewhere)
  (ρ# (SINGLE-ACTOR-ADDR))
  (χ# (a#ext ...))
  ;; H# = handler config (exp + outputs so far)
  (H# (e# ([a#ext v#] ...)))
  ;; (A# ((any_1 ... hole any_2 ...) () ρ χ)) ; TODO: update this
  (E# hole
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
      (list v# ... E# e# ...)
      (vector v# ... E# e# ...)))

  ;; (define-metafunction csa#
  ;;   abstract : K -> K#
  ;;   ;; TODO: handle messages already in the queue
  ;;   ;;
  ;;   ;; TODO: handle ρ and χ
  ;;   [(abstract (α () ρ χ))
  ;;    (α# () ρ χ)
  ;;    (where  ((a ((S ...) e)) ...) α)
  ;;    (where α# ((a (((abstract/S S) ...) (abstract/e e))) ...))])

  ;; (define-metafunction csa#
  ;;   abstract/e : e -> e#
  ;;   [(abstract/e n) Nat]
  ;;   ;; TODO: do something different for addresses (probably need a dictionary of things to substitute
  ;;   ;; for them?)
  ;;   [(abstract/e a) a]
  ;;   ;; TODO: do something more clever for tuples
  ;;   [(abstract/e (tuple e ...)) (tuple (abstract/e e ...))]
  ;;   [(abstract/e (rcv (x) e) [(timeout Nat)]) (rcv (x) (abstract/e e))]
  ;;   ;; The rest of these from here just do the normal tree-walking thing
  ;;   [(abstract/e (spawn e S ...)) (spawn (abstract/e e) (abstract/S S) ...)]
  ;;   [(abstract/e (goto s e ...)) (goto s (abstract/e e) ...)]
  ;;   [(abstract/e (send e_1 e_2)) (send (abstract/e e_1) (abstract/e e_2))]
  ;;   [(abstract/e self) self]
  ;;   [(abstract/e (begin e ...)) (begin (abstract/e e ...))]
  ;;   ;; TODO: let
  ;;   [(abstract/e (match e_1 [p e_2] ...)) (match (abstract/e e) [p (abstract/e e)] ...)]
  ;;   [(abstract/e t) t]
  ;;   [(abstract/e x) x]
  ;;   [(abstract/e (rcv (x) e)) (rcv (x) (abstract/e e))])

;; ---------------------------------------------------------------------------------------------------
;; Message generation

;; TODO: define this
(define (generate-abstract-messages type current-state-name max-depth observed?)
  (redex-let csa# ([(v#template ...) (term (generate-abstract-messages/mf ,type ,max-depth))])
             (if observed?
                 (term ((fill-template v#template ,current-state-name) ...))
                 (term ((fill-template/unobs v#template) ...)))))

(define-metafunction csa#
  generate-abstract-messages/mf : τ natural -> (v#template ...)
  [(generate-abstract-messages/mf Nat _) ((* Nat))]
  [(generate-abstract-messages/mf String _) ((* String))]
  [(generate-abstract-messages/mf (Union) _) ()]
  [(generate-abstract-messages/mf (Union [t τ ...] ...) 0) ((* (Union [t τ ...] ...)))]
  [(generate-abstract-messages/mf (Union [t_1 τ_1 ...] [t_rest τ_rest ...] ...) natural_max-depth)
   (v#template_1 ... v#template_rest ...)
   ;; (side-condition (displayln "generate-abs-var"))
   (where (v#template_1 ...) (generate-variants natural_max-depth t_1 τ_1 ...))
   (where (v#template_rest ...)
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
         (redex-let csa# ([(record [l_other v#template_other] ...) sub-record]
                          [v#template_1 generated-v])
           (term (record [l_1 v#template_1] [l_other v#template_other] ...))))
       records-so-far))]
  [(generate-abstract-messages/mf (Record) natural_max-depth)
   ((record))]
  [(generate-abstract-messages/mf (Addr τ) _) (ADDR-HOLE)])

(define-metafunction csa#
  generate-variants : natural t τ ... -> ((variant t v#template ...) ...)
  [(generate-variants _ t) ((variant t))]
  [(generate-variants natural_max-depth t τ_1 τ_rest ...)
   ,(for/fold ([variants-so-far null])
              ([sub-variant (term (generate-variants natural_max-depth t τ_rest ...))])
      (append
       ;; TODO: do I need to do a (max 0) on natural_max-depth here?
       (for/list ([generated-v (term (generate-abstract-messages/mf τ_1 ,(sub1 (term natural_max-depth))))])
         (redex-let csa# ([(variant t v#template_other ...) sub-variant]
                          [v#template_1 generated-v])
           (term (variant t v#template_1 v#template_other ...))))
       variants-so-far))
   ;; (side-condition (printf "generate-variants: ~s\n" (term ( t τ_1 τ_rest ...))))
   ])

;; TODO: write a test for the n-squared match of record message generation

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
  (check-same-items?
   (term (generate-abstract-messages/mf
          (Union (AppendRejected Nat Nat (Addr Nat))
                 (AppendSuccessful Nat Nat (Addr Nat)))
          5))
   (term ((variant AppendRejected (* Nat) (* Nat) ADDR-HOLE)
          (variant AppendSuccessful (* Nat) (* Nat) ADDR-HOLE)))))

(define-metafunction csa#
  fill-template : v#template s -> v#
  [(fill-template v#template s)
   v#
   (where (v# _) (fill-template/acc v#template v#template 0 s))])

;; Fills the abstract message template with address values, also returning the next index to be used
;; for an address
(define-metafunction csa#
  fill-template/acc : v#template_current v#template_whole natural_current-index s -> (v# natural_next-index)
  [(fill-template/acc ADDR-HOLE v#template natural_current s)
   ((received-addr s v#template natural_current MOST-RECENT) ,(+ 1 (term natural_current)))]
  [(fill-template/acc (variant t v#template_child1 v#template_child-rest ...) v#template natural_current s)
   ((variant t v#_1 v#_rest ...) natural_next-rest)
   (where (v#_1 natural_next1) (fill-template/acc v#template_child1 v#template natural_current s))
   (where ((variant t v#_rest ...) natural_next-rest)
          (fill-template/acc (variant t v#template_child-rest ...) v#template natural_next1 s))]
  [(fill-template/acc (variant t) v#template natural_current s)
   ((variant t) natural_current)]
  [(fill-template/acc (record [l_1 v#template_child1] [l_rest v#template_rest] ...)
                      v#template
                      natural_current
                      s)
   ((record [l_1 v#_1] [l_rest v#_rest] ...) natural_next-rest)
   (where (v#_1 natural_next1) (fill-template/acc v#template_child1 v#template natural_current s))
   (where ((record [l_rest v#_rest] ...) natural_next-rest)
          (fill-template/acc (record [l_rest v#template_rest] ...) v#template natural_next1 s))]
  [(fill-template/acc (record) v#template natural s)
   ((record) natural)]
  [(fill-template/acc (* τ) _ natural _)
   ((* τ) natural)])

(module+ test
  ;; TODO: write more tests here
  (check-equal? (term (fill-template (* Nat) Always))
                (term (* Nat)))
  ;; TODO: rewrite this test using records and variants
  ;; (define simple-pair-template (term (tuple ADDR-HOLE ADDR-HOLE)))
  ;; (check-equal? (term (fill-template ,simple-pair-template Always))
  ;;               (term (tuple (received-addr Always ,simple-pair-template 0 MOST-RECENT)
  ;;                            (received-addr Always ,simple-pair-template 1 MOST-RECENT))))
  )

;; Fills the given value template with unobservable addresses in each ADDR-HOLE
(define-metafunction csa#
  fill-template/unobs : v#template -> v#
  [(fill-template/unobs ADDR-HOLE) (* (Addr Nat))] ;; TODO:  fill in the real address type here
  [(fill-template/unobs t) t]
  [(fill-template/unobs (variant t v#template_child ...))
   (variant t (fill-template/unobs v#template_child) ...)]
  [(fill-template/unobs (record [x v#template] ...))
   (record [x (fill-template/unobs v#template)] ...)]
  [(fill-template/unobs (* τ)) (* τ)])

;; ---------------------------------------------------------------------------------------------------

(define (config-actor-by-address config addr)
  (term (config-actor-by-address/mf ,config ,addr)))

(define-metafunction csa#
  config-actor-by-address/mf : K# a#int -> α#n
  [(config-actor-by-address/mf ((_ ... (name the-agent (a#int _)) _ ...) _ _ _) a#int)
   the-agent])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

;; Outputs is a list of abstract-addr/abstract-message 2-tuples
(struct csa#-transition (message observed? outputs behavior-exp) #:transparent)

(define csa#-output-address car)
(define csa#-output-message cadr)

(define (csa#-observable-output? output)
  (if (redex-match csa# [(* (Addr _)) _] output) #f #t))

(module+ test
  (check-false (csa#-observable-output? (term [(* (Addr Nat)) 1])))
  (check-true (csa#-observable-output? (term [(init-addr 0) 1])))
  (check-true (csa#-observable-output? (term [(received-addr S1 ADDR-HOLE 0 MOST-RECENT) 1])))
  (check-true (csa#-observable-output? (term [(received-addr S1 ADDR-HOLE 0 PREVIOUS) 1]))))

(define (csa#-transition-next-state transition)
  (redex-let csa# ([(in-hole E# (goto s _ ...)) (csa#-transition-behavior-exp transition)])
    (term s)))

;; Evaluates the handler triggered by sending message to actor-address, return the list of possible
;; results (which are tuples of the final behavior expression and the list of outputs)
(define (csa#-eval-transition prog-config actor-address message)
  (redex-let csa# ([(_ ((_ ... (define-state (s [x_s τ_s] ..._n) (x_m) e#) _ ...) (in-hole E# (goto s v# ..._n))))
                    (config-actor-by-address prog-config actor-address)])
             ;; TODO: deal with the case where x_m shadows an x_s
             ;; (printf "Expression to be run: ~s\n" (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...)))
             (define initial-config (inject/H# (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...))))
             (define results (apply-reduction-relation* handler-step# initial-config))
             (define non-abstraction-stuck-results
               (filter (compose not stuck-abstraction-handler-config?) results))
             (unless (redex-match csa#
                                  (((in-hole E# (goto s v#_param ...)) ([a#ext v#_out] ...)) ...)
                                  non-abstraction-stuck-results)
               (error 'csa#-eval-transition
                      "Abstract evaluation did not complete\nInitial config: ~s\nFinal configs:~s"
                      initial-config
                      non-abstraction-stuck-results))
             non-abstraction-stuck-results))

;; Returns true if the config is one that is unable to step because of an over-approximation in the
;; abstraction
(define (stuck-abstraction-handler-config? c)
  (or (redex-match csa#
                   ((in-hole E# (list-ref (list) v#)) ([a#ext v#_out] ...))
                   c)
      (redex-match csa#
                   ((in-hole E# (vector-ref (vector) v#)) ([a#ext v#_out] ...))
                   c)
      (redex-match csa#
                   ((in-hole E# (hash-ref (hash) v# v#_2)) ([a#ext v#_out] ...))
                   c)))

(define (inject/H# exp)
  (redex-let csa#
             ([e# exp]
              [H# (term (,exp ()))])
             (term H#)))

;; TODO: make this relation work on a full abstract configuration (maybe?)
(define handler-step#
  (reduction-relation csa#
    #:domain H#

    ;; TODO: goto into rcv (with/without timeout)

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
         ;; TODO: should I do something more precise here? That might violate the depth rules,
         ;; though...
         (* (Record any_1 ... [l τ] any_2 ...))
         RecordWildcardUpdate)

    ;; Primops
    (==> (primop (* Nat) (* Nat))
         (variant True)
         (side-condition (member (term primop) (list '< '>)))
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

    ;; TODO: make a check that both operands are booleans
    (==> (and v#_1 v#_2)
         (csa#-and (canonicalize-boolean v#_1) (canonicalize-boolean v#_2))
         And)
    (==> (or v#_1 v#_2)
         (csa#-or (canonicalize-boolean v#_1) (canonicalize-boolean v#_2))
         Or)
    (==> (not v#)
         (csa#-not (canonicalize-boolean v#))
         Not)

    ;; Vectors, Lists, and Hashes
    ;; TODO: keep the elements in a canonical order, so that equivalent abstract values are equal?

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
    (==> (vector-length (vector v# ...))
         (* Nat)
         VectorLength)
    (==> (vector-length (* (VectorOf τ)))
         (* Nat)
         VectorWildcardLength)
    (==> (vector-copy (vector v# ...) (* Nat) (* Nat))
         (vector v# ...)
         VectorCopy)
    (==> (vector-copy (* (Vector τ)) (* Nat) (* Nat))
         (* (Vector τ))
         VectorWildcardCopy)
    (==> (hash-ref (hash _ ... v# _ ...) v#_key)
         (variant Just v#)
         HashRefSuccess)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Just (* τ_2))
         HashWildcardRefSuccess)
    (==> (hash-ref (hash _ ...) v#_key)
         (variant Nothing)
         HashRefFailure)
    (==> (hash-ref (* Hash τ_1 τ_2) v#_key)
         (variant Nothing)
         HashWildcardRefFailure)
    (==> (hash-set (hash v#_1 ... v#_value v#_2 ...) v#_key v#_value)
         (hash-set (hash v#_1 ... v#_value v#_2 ...) v#_key v#_value)
         HashSetExists)
    (==> (hash-set (hash v#_current ...) v#_key v#_value)
         (hash-set (hash v#_current ... v#_value))
         (side-condition (not (member (term v#_value) (term (v#_current ...)))))
         HashSetNewItem)
    (==> (hash-set (* Hash τ_1 τ_2) v#_key v#_value)
         (* Hash τ_1 τ_2)
         HashWildcardSet)

    ;; TODO: make an actual implementation here (although this might be the real implementation once I
    ;; figure out the representation for lsits
    (==> (sort-numbers-descending v#)
         v#
         Sort)

    ;; Communication

    (--> ((in-hole E# (send a# v#)) (any_outputs ...))
         ((in-hole E# v#)           (any_outputs ... [a# v#]))
         Send)

    with
    [(--> ((in-hole E# old) ([a#ext v#] ...))
          ((in-hole E# new) ([a#ext v#] ...)))
     (==> old new)]))

(module+ test
  (define (csa#-make-simple-test-config exp)
    (redex-let* csa# ([α#n (term [SINGLE-ACTOR-ADDR
                                  (((define-state (Always) (long-unused-name) (begin ,exp (goto Always))))
                                   (begin ,exp (goto Always)))])]
                      [α# (term (α#n))]
                      [μ# (term ())]
                      [ρ# (term (SINGLE-ACTOR-ADDR))]
                      [χ# (term ())])
                (term (α# μ# ρ# χ#))))

  ;; TODO: remove this one
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
  )

;; TODO: make this function less susceptible to breaking because of changes in the config's structure
(define (step-prog-final-behavior prog-config beahvior-exp)
  (redex-let csa# ([(((SINGLE-ACTOR-ADDR ((S# ...) _)))
                     ()
                     (SINGLE-ACTOR-ADDR)
                     ;; TODO: update χ# or just get rid of it
                     ())
                    prog-config])
             (term
              (((SINGLE-ACTOR-ADDR ((S# ...) ,beahvior-exp)))
               ()
               (SINGLE-ACTOR-ADDR)
               ;; TODO: update χ# or just get rid of it
               ()))))

;; ---------------------------------------------------------------------------------------------------
;; Substitution

;; TODO: see if I can use Paul's binding specs to write this code automatically

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
  ;; [(csa#-subst a x v) a]
  ;; [(csa#-subst (spawn e S ...) self v) (spawn e S ...)]
  ;; [(csa#-subst (spawn e S ...) x v)
  ;;   (spawn (csa#-subst e x v) (csa#-subst/S S x v) ...)]
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
  [(csa#-subst (primop e# ...) x v#) (primop (csa#-subst e# x v#) ...)]
  [(csa#-subst (record [l e#] ...) x v#) (record [l (csa#-subst e# x v#)] ...)]
  [(csa#-subst (: e# l) x v#) (: (csa#-subst e# x v#) l)]
  [(csa#-subst (! e#_1 [l e#_2]) x v#)
   (! (csa#-subst e#_1 x v#) [l (csa#-subst e#_2 x v#)])]
  [(csa#-subst (list e ...) x v#) (list (csa#-subst e x v#) ...)]
  [(csa#-subst (vector e ...) x v#) (vector (csa#-subst e x v#) ...)]
  [(csa#-subst (hash) x v#) (hash)]
  ;; [(csa#-subst (rcv (x) e) x v) (rcv (x) e)]
  ;; [(csa#-subst (rcv (x_h) e) x v) (rcv (x_h) (csa#-subst e x v))]
  ;; [(csa#-subst (rcv (x) e [(timeout n) e_timeout]) x v) (rcv (x) e [(timeout n) e_timeout])]
  ;; [(csa#-subst (rcv (x_h) e [(timeout n) e_timeout]) x v)
  ;;  (rcv (x_h) (csa#-subst e x v) [(timeout n) (csa#-subst e_timeout x v)])]
  )

(define-metafunction csa#
  csa#-subst/case-clause : [(t x ...) e#] x v# -> [(t x ...) e#]
  [(csa#-subst/case-clause [(t x_1 ... x x_2 ...) e#] x v#)
   [(t x_1 ... x x_2 ...) e#]]
  [(csa#-subst/case-clause [(t x_other ...) e#] x v#)
   [(t x_other ...) (csa#-subst e# x v#)]])


(module+ test
  (check-equal? (term (csa#-subst/case-clause [(Cons p) (begin p x)] p (* Nat)))
                (term [(Cons p) (begin p x)]))
  (check-equal? (term (csa#-subst/case-clause [(Cons p) (begin p x)] x (* Nat)))
                (term [(Cons p) (begin p (* Nat))])))

(module+ test
  (check-equal? (term (csa#-subst (variant Foo (* Nat)) a (* Nat))) (term (variant Foo (* Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; TODO: test these functions

(define (α-config concrete-config spec-initial-observables max-depth)
  (term (α-config/mf ,concrete-config ,spec-initial-observables ,max-depth)))

;; NOTE: currently only supports single-actor, no-externals configs
(define-metafunction csa#
  α-config/mf : K (a ...) natural -> K#
  [(α-config/mf ((αn) ; actors
                 () ; messages-in-transit
                 ((addr 0)) ; receptionists
                 () ; externals
                 )
                (a ...)
                natural_depth)
   ((α#n) () (SINGLE-ACTOR-ADDR) ())
   (where α#n (α-actor αn (a ...) natural_depth))])

;; NOTE: currently assumes address 0
(define-metafunction csa#
  α-actor : αn (a ...) natural_depth -> α#n
  [(α-actor ((addr 0) ((S ...) e)) (a ...) natural_depth)
   (SINGLE-ACTOR-ADDR (((α-S S (a ...) natural_depth) ...) (α-e e (a ...) natural_depth)))])

;; NOTE: does not support timeouts yet
(define-metafunction csa#
  α-S : S (a ...) natural_depth -> S#
  [(α-S (define-state (s [x τ] ...) (x_m) e) (a ...) natural_depth)
   (define-state (s [x τ] ...) (x_m) (α-e e (a ...) natural_depth))])

;; NOTE: does not yet support abstraction for addresses or spawns
;;
;; Abstracts the given expression to
;; the given depth, using the given list of addresses as the addresses to leave observable
(define-metafunction csa#
  α-e : e (a ...) natural_depth -> e#
  [(α-e natural _ _) (* Nat)]
  [(α-e string _ _) (* String)]
  [(α-e x _ _) x]
  ;; TODO: is there any way this will ever be used for anything but the initial addresses?
  ;; TODO: deal with the self-address here
  [(α-e (addr natural) (_ ... (addr natural) _ ...) _) (init-addr natural)]
  [(α-e a _ _) (* (Addr Nat))] ; TODO: fill in the real type here
  [(α-e (goto s e ...) (a ...) natural_depth) (goto s (α-e e (a ...) natural_depth) ...)]
  [(α-e (begin e ...) (a ...) natural_depth) (begin (α-e e (a ...) natural_depth) ...)]
  [(α-e (send e_1 e_2) (a ...) natural_depth)
   (send (α-e e_1 (a ...) natural_depth) (α-e e_2 (a ...) natural_depth))]
  [(α-e (let ([x e_binding] ...) e_body) (a ...) natural)
   (let ([x (α-e e_binding (a ...) natural)] ...) (α-e e_body (a ...) natural))]
  [(α-e (case e_val [(t x ...) e_clause] ...) (a ...) natural_depth)
   (case (α-e e_val (a ...) natural_depth) [(t x ...) (α-e e_clause (a ...) natural_depth)] ...)]
  [(α-e (primop e ...) (a ...) natural_depth) (primop (α-e e (a ...) natural_depth) ...)]
  ;; TODO: do something much better here - figure out how to limit the depth
  ;; [(α-e (tuple e ...) 0)
  ;;  ;; TODO: give the actual type here
  ;;  (* (Tuple))]
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
   (list (α-e e (a ...) ,(max 0 (sub1 (term natural_depth)))) ...)]
  [(α-e (vector e ...) (a ...) natural_depth)
   (vector (α-e e (a ...) ,(max 0 (sub1 (term natural_depth)))) ...)]
  [(α-e (hash) _ _) (hash)])

;; TODO: write tests for the variant/record case, because the crappy version I have here isn't good
;; enough

(module+ test
  (check-equal? (term (α-e (record [f1 1] [f2 2]) () 1))
                (term (record [f1 (* Nat)] [f2 (* Nat)])))
  (check-not-false
   (redex-match? csa#
                 (variant Foo (init-addr 1) (* (Addr τ)))
                 (term (α-e (variant Foo (addr 1) (addr 2)) ((addr 1)) 10)))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (csa#-actor-address the-actor)
  (redex-let csa# ([(a# _) the-actor])
             (term a#)))

(define (csa#-actor-current-state the-actor)
  (redex-let csa# ([(_ (_ (in-hole E# (goto s _ ...)))) the-actor])
             (term s)))

(define (csa#-config-only-actor prog-config)
  (term (config-only-actor/mf ,prog-config)))

(define-metafunction csa#
  config-only-actor/mf : K# -> α#n
  [(config-only-actor/mf (α# _ _ _))
   α#n
   (where (α#n) α#)])

;; ---------------------------------------------------------------------------------------------------
;; Boolean Logic

;; TODO: make these contracts tighter

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
