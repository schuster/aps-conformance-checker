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
  (S# (define-state (s x ...) (x) e#)
      ;; TODO: not dealing with timeouts yet...
      ;; (define-state (s x ...) (x) e# [(timeout Nat) e#])
      )
  ;; TODO: these probably should be sets of values, right?
  (v# a# ; TODO: replace this one with a special pattern
      (variant t v#)
      (* τ))
  (v#template
   ADDR-HOLE
   (variant t v#template)
   (* τ))
  (e# (spawn e# S ...)
      (goto s e# ...)
      (send e# e#)
      self
      (begin e# ... e#)
      (let ([x e#] ...) e#)
      (case e# [t x e#] ...)
      (variant t e#)
      (primop e# ...)
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
      (let ([x E#] [x e#] ...) e#)
      (case E# [t x e#] ...)
      (variant t E#)))

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
  [(generate-abstract-messages/mf (Union) _) ()]
  [(generate-abstract-messages/mf (Union [t τ] ...) 0) ((* (Union [t τ] ...)))]
  [(generate-abstract-messages/mf (Union [t_1 τ_1] [t_rest τ_rest] ...) natural_max-depth)
   ((variant t_1 v#template_1) ... v#template_rest ...)
   ;; TODO: do I need to do a (max 0) on natural_max-depth here?
   (where (v#template_1 ...) (generate-abstract-messages/mf τ_1 ,(max 0 (- (term natural_max-depth) 1))))
   (where (v#template_rest ...)
          (generate-abstract-messages/mf (Union [t_rest τ_rest] ...) natural_max-depth))]
  [(generate-abstract-messages/mf (minfixpt X τ) natural_max-depth)
   (generate-abstract-messages/mf (type-subst τ X (minfixpt X τ)) natural_max-depth)]
  ;; [(generate-abstract-messages/mf (Tuple τ ...) 0)
  ;;  ((* (Tuple τ ...)))]
  ;; [(generate-abstract-messages/mf (Tuple τ_1 τ_rest ...) natural_max-depth)
  ;;  ,(for/fold ([tuples-so-far null])
  ;;            ([sub-tuple (term (generate-abstract-messages/mf (Tuple τ_rest ...) natural_max-depth))])
  ;;    (append
  ;;     (for/list ([generated-v (term (generate-abstract-messages/mf τ_1 ,(- (term natural_max-depth) 1)))])
  ;;       (redex-let csa# ([(tuple v#_other ...) sub-tuple]
  ;;                        [v#_1 generated-v])
  ;;         (term (tuple v#_1 v#_other ...))))
  ;;     tuples-so-far))]
  ;; [(generate-abstract-messages/mf (Tuple) natural_max-depth)
  ;;  ((tuple))]
  [(generate-abstract-messages/mf (Addr τ) _) (ADDR-HOLE)])

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
   (term ())))

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
  [(fill-template/acc (variant t v#template_child) v#template natural_current s)
   ((variant t v#_child) natural_next)
   (where (v#_child natural_next) (fill-template/acc v#template_child v#template natural_current s))]
  ;; [(fill-template/acc (tuple v#template_child1 v#template_rest ...) v#template natural_current s)
  ;;  ((tuple v#_1 v#_rest ...) natural_next-rest)
  ;;  (where (v#_1 natural_next1) (fill-template/acc v#template_child1 v#template natural_current s))
  ;;  (where ((tuple v#_rest ...) natural_next-rest)
  ;;         (fill-template/acc (tuple v#template_rest ...) v#template natural_next1 s))]
  ;; [(fill-template/acc (tuple) v#template natural s)
  ;;  ((tuple) natural)]
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

(define-metafunction csa#
  fill-template/unobs : v#template -> v#
  [(fill-template/unobs ADDR-HOLE) (* (Addr Nat))] ;; TODO:  fill in the real address type here
  [(fill-template/unobs t) t]
  [(fill-template/unobs (variant t v#template_child ...))
   (variant t (fill-template/unobs v#template_child) ...)]
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
  (redex-let csa# ([(_ ((_ ... (define-state (s x_s ..._n) (x_m) e#) _ ...) (in-hole E# (goto s v# ..._n))))
                    (config-actor-by-address prog-config actor-address)])
             ;; TODO: deal with the case where x_m shadows an x_s
             ;; (printf "Expression to be run: ~s\n" (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...)))
             (define initial-config (inject/H# (term (csa#-subst-n e# [x_m ,message] [x_s v#] ...))))
             (define results (apply-reduction-relation* handler-step# initial-config))
             (unless (redex-match csa# (((in-hole E# (goto s v#_param ...)) ([a#ext v#_out] ...)) ...) results)
               (error 'csa#-eval-transition
                      "Abstract evaluation did not complete\nInitial config: ~s\nFinal configs:~s"
                      initial-config
                      results))
             results))

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

    (==> (case (* (Union _ ... [t τ] _ ...))
           [t x e#]
           _ ...)
         (csa#-subst e# x (* τ))
         CaseWildcardSuccess)
    (==> (case (* (Union [t_val τ_val] ...))
           ;; Only fail if there is at least one more clause; type safety guarantees that at least one
           ;; clause matches
           [t_1 x_1 e#_1]
           [t_2 x_2 e#_2]
           [t_rest x_rest e#_rest] ...)
         (case (* (Union [t_val τ_val] ...))
           [t_2 x_2 e#_2]
           [t_rest x_rest e#_rest] ...)
         CaseWildcardFailure)
    (==> (case (variant t v#)
           [t x e#]
           _ ...)
         (csa#-subst e# x v#)
         CaseVariantSuccess)
    (==> (case (variant t v#)
           [t_other x e#]
           [t_rest x_rest e#_rest] ...)
         (case (variant t v#)
           [t_rest x_rest e#_rest] ...)
         (side-condition (not (equal? (term t) (term t_other))))
         CaseVariantFailure)

    (==> (< (* Nat) (* Nat))
         (variant True (* Nat))
         LessThan1)
    (==> (< (* Nat) (* Nat))
         (variant False (* Nat))
         LessThan2)

    (==> (/ (* Nat) (* Nat))
         (* Nat)
         Div)

    (--> ((in-hole E# (send a# v#)) (any_outputs ...))
         ((in-hole E# v#)           (any_outputs ... [a# v#]))
         Send)

    ;; TODO: let

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
  ;; [(csa#-subst (let ([x_let e] ...) e_body) x v)
  ;;  (let ([x_let (csa#-subst e x v)] ...) e_body)
  ;;  (where (_ ... x _ ...) (x_let ...))] ; check that x is in the list of bound vars
  ;; [(csa#-subst (let ([x_let e] ...) e_body) x v)
  ;;  (let ([x_let (csa#-subst e x v)] ...) (csa#-subst e_body x v))]
  [(csa#-subst (case e# [t x_clause e#_clause] ...) x v#)
   (case (csa#-subst e# x v#) (csa#-subst/case-clause [t x_clause e#_clause] x v#) ...)]
  [(csa#-subst (variant t e#) x v#) (variant t (csa#-subst e# x v#))]
  [(csa#-subst (primop e# ...) x v#) (primop (csa#-subst e# x v#) ...)]
  ;; [(csa#-subst (rcv (x) e) x v) (rcv (x) e)]
  ;; [(csa#-subst (rcv (x_h) e) x v) (rcv (x_h) (csa#-subst e x v))]
  ;; [(csa#-subst (rcv (x) e [(timeout n) e_timeout]) x v) (rcv (x) e [(timeout n) e_timeout])]
  ;; [(csa#-subst (rcv (x_h) e [(timeout n) e_timeout]) x v)
  ;;  (rcv (x_h) (csa#-subst e x v) [(timeout n) (csa#-subst e_timeout x v)])]
  )

(define-metafunction csa#
  csa#-subst/case-clause : [t x e#] x v# -> [t x e#]
  [(csa#-subst/case-clause [t x e#] x v#)
   [t x e#]]
  [(csa#-subst/case-clause [t x_other e#] x v#)
   [t x_other (csa#-subst e# x v#)]])


(module+ test
  (check-equal? (term (csa#-subst/case-clause [Cons p (begin p x)] p (* Nat)))
                (term [Cons p (begin p x)]))
  (check-equal? (term (csa#-subst/case-clause [Cons p (begin p x)] x (* Nat)))
                (term [Cons p (begin p (* Nat))])))

(module+ test
  (check-equal? (term (csa#-subst (variant Foo (* Nat)) a (* Nat))) (term (variant Foo (* Nat)))))

;; ---------------------------------------------------------------------------------------------------
;; Abstraction

;; TODO: test these functions

(define (α-config concrete-config max-depth)
  (term (α-config/mf ,concrete-config ,max-depth)))

;; NOTE: currently only supports single-actor, no-externals configs
(define-metafunction csa#
  α-config/mf : K natural -> K#
  [(α-config/mf ((αn) ; actors
                 () ; messages-in-transit
                 ((addr 0)) ; receptionists
                 () ; externals
                 )
                natural_depth)
   ((α#n) () (SINGLE-ACTOR-ADDR) ())
   (where α#n (α-actor αn natural_depth))])

;; NOTE: currently assumes address 0
(define-metafunction csa#
  α-actor : αn natural_depth -> α#n
  [(α-actor ((addr 0) ((S ...) e)) natural_depth)
   (SINGLE-ACTOR-ADDR (((α-S S natural_depth) ...) (α-e e natural_depth)))])

;; NOTE: does not support timeouts yet
(define-metafunction csa#
  α-S : S natural_depth -> S#
  [(α-S (define-state (s x ...) (x_m)  e) natural_depth)
   (define-state (s x ...) (x_m) (α-e e natural_depth))])

;; NOTE: does not yet support abstraction for addresses or spawns
(define-metafunction csa#
  α-e : e natural_depth -> e#
  [(α-e natural _) (* Nat)]
  [(α-e x _) x]
  ;; TODO: is there any way this will ever be used for anything but the initial addresses?
  [(α-e (addr natural) _) (init-addr natural)]
  [(α-e (goto s e ...) natural_depth) (goto s (α-e e natural_depth) ...)]
  [(α-e (begin e ...) natural_depth) (begin (α-e e natural_depth) ...)]
  [(α-e (send e_1 e_2) natural_depth)
   (send (α-e e_1 natural_depth) (α-e e_2 natural_depth))]
  [(α-e (case e_val [t x e_clause] ...) natural_depth)
   (case (α-e e_val natural_depth) [t x (α-e e_clause natural_depth)] ...)]
  [(α-e (primop e ...) natural_depth) (primop (α-e e natural_depth) ...)]
  ;; TODO: do something much better here - figure out how to limit the depth
  ;; [(α-e (tuple e ...) 0)
  ;;  ;; TODO: give the actual type here
  ;;  (* (Tuple))]
  [(α-e (variant t e) natural_depth)
   ;; TODO: take out the "max" issue here
   (variant t (α-e e ,(max 0 (- (term natural_depth) 1))))])

;; TODO: write tests for the variant/record case, because the crappy version I have here isn't good
;; enough

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
