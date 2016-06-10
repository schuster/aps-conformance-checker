#lang racket

;; Defines the abstract APS configurations and helper functions

(provide
 aps#
 aps#-α-Σ
 subst-n/aps#
 aps#-current-transitions
 aps#-null-transition
 aps#-transition-observed?
 aps#-eval
 aps#-match
 aps#-matches-po?
 step-spec-with-goto
 aps#-spec-from-commitment-entry
 aps#-spec-from-fsm-and-commitments
 aps#-config-instances
 aps#-config-commitment-map
 aps#-transition-pattern
 aps#-transition-expression
 aps#-commitment-address
 aps#-commitment-pattern
 aps#-commitment-entry-address
 aps#-goto-state
 aps#-instance-state
 aps#-instance-arguments
 aps#-relevant-external-addrs)

;; ---------------------------------------------------------------------------------------------------

(require
 redex/reduction-semantics
 "aps.rkt"
 "csa-abstract.rkt")

(module+ test
  (require rackunit))

(define-union-language aps-eval-with-csa#
  aps-eval csa#)

(define-extended-language aps#
  aps-eval-with-csa#
  (Σ ((z ...) O))
  (z ((S-hat ...) e-hat σ))
  (σ a# null)
  (u .... a#) ; TODO: make this a#ext instead; allowing saves of spawned addresses is future work
  (v-hat a# a-hat)
  (O ((a#ext po ...) ...)))

;; TODO: change the language and conformance so that I don't have to do this little initial
;; abstraction
(define (aps#-α-Σ spec-config)
  ;; Doing a redex-let here just to add a codomain contract
  (redex-let aps# ([Σ (term (aps#-α-Σ/mf ,spec-config))])
             (term Σ)))

(define-metafunction aps#
  aps#-α-Σ/mf : any -> any
  [(aps#-α-Σ/mf (addr natural))
   (init-addr natural)]
  [(aps#-α-Σ/mf (any ...))
   ((aps#-α-Σ/mf any) ...)]
  [(aps#-α-Σ/mf any) any])

;; ---------------------------------------------------------------------------------------------------
;; Substitution

(define-metafunction aps#
  subst-n/aps# : e-hat (x v-hat) ... -> e-hat
  [(subst-n/aps# e-hat) e-hat]
  [(subst-n/aps# e-hat (x v-hat) any_rest ...)
   (subst-n/aps# (subst/aps# e-hat x v-hat) any_rest ...)])

;; TODO: write tests for this substitution

(define-metafunction aps#
  subst/aps# : e-hat x v-hat -> e-hat
  [(subst/aps# (goto s u ...) x v-hat)
   (goto s (subst/aps#/u u x v-hat) ...)]
  [(subst/aps# (with-outputs ([u po] ...) e-hat) x v-hat)
   ;; TODO: figure out if I need to substitute into the patterns, for spawned specs
   (with-outputs ([(subst/aps#/u u x v-hat) po] ...) (subst/aps# e-hat x v-hat))]
  ;; TODO: write the other clauses
  )

(define-metafunction aps#
  subst/aps#/u : u x v-hat -> u
  [(subst/aps#/u x x v-hat) v-hat]
  [(subst/aps#/u x_2 x v-hat) x_2]
  [(subst/aps#/u a# x v-hat) a#])

(define-metafunction aps#
  subst/aps#/po : po x v-hat -> po
  [(subst/aps#/po x x v-hat) v-hat]
  [(subst/aps#/po x_2 x v-hat) x_2]
  [(subst/aps#/po a x v-hat) a]
  [(subst/aps#/po a-hat x v-hat) a-hat]
  ;; TODO: do this for variants, records, and or
  [(subst/aps#/po * x v-hat) *])

;; ---------------------------------------------------------------------------------------------------
;; Evaluation

(define (aps#-current-transitions instance)
  (term (aps#-current-transitions/mf ,instance)))

;; TODO: deal with the case where the pattern variables shadow the state variables
(define-metafunction aps#
  aps#-current-transitions/mf : z -> ((ε -> e-hat) ...)
  [(aps#-current-transitions/mf ((_ ... (define-state (s x ...) (ε -> e-hat) ...) _ ...) (goto s v-hat ...) _))
   ((ε -> (subst-n/aps# e-hat (x v-hat) ...)) ...)])

(define (aps#-null-transition instance)
  (term (aps#-null-transition/mf ,instance)))

(define-metafunction aps#
  aps#-null-transition/mf : z -> (unobs -> (goto s v-hat ...))
  [(aps#-null-transition/mf ((_ ... (define-state (s x ...) _ ...) _ ...) (goto s v-hat ...) _))
   (unobs -> (goto s v-hat ...))])

(define (aps#-transition-observed? trans)
  (term (aps#-transition-observed?/mf ,trans)))

(define-metafunction aps#
  aps#-transition-observed?/mf : (ε -> e-hat) -> boolean
  [(aps#-transition-observed?/mf (p _ _)) #t]
  [(aps#-transition-observed?/mf _) #f])

(module+ test
  (check-false (aps#-transition-observed? (term [unobs -> (goto S x y)])))
  (check-true (aps#-transition-observed? (term [(variant Cons y) -> (goto S x y)])))
  (check-true (aps#-transition-observed? (term [* -> (goto S x y)]))))

(define (aps#-eval exp subst)
  (redex-let aps# ([(any_binding ...) subst])
    (term (aps#-eval/mf (subst-n/aps# ,exp any_binding ...)))))

(define-metafunction aps#
  aps#-eval/mf : e-hat -> [(goto s a#ext ...) ([a#ext po] ...)]
  [(aps#-eval/mf (goto s a#ext ...))
   [(goto s a#ext ...) ()]]
  [(aps#-eval/mf (with-outputs ([a#ext_1 po_1] any_rest ...) e-hat))
   [(goto s a#ext ...) ([a#ext_1 po_1] any_outputs ...)]
   ;; TODO: this is an example of a where clause I expect to always succeed. I should write a macro on
   ;; reduction-relation that enforces that
   (where [(goto s a#ext ...) (any_outputs ...)]
          (aps#-eval/mf (with-outputs (any_rest ...) e-hat)))]
  [(aps#-eval/mf (with-outputs () e-hat))
   (aps#-eval/mf e-hat)])

;; TODO: test the eval function

(define (step-spec-with-goto spec-instance goto-exp)
  (redex-let aps# ([((S-hat ...) _ σ) spec-instance])
             (term ((S-hat ...) ,goto-exp σ))))

;; ---------------------------------------------------------------------------------------------------
;; Pattern matching

(define (aps#-match val pat)
  (judgment-holds (aps#-match/j ,val ,pat ([x a#ext] ...))
                  ([x a#ext] ...)))

(define-judgment-form aps#
  #:mode (aps#-match/j I I O)
  #:contract (aps#-match/j v# p ((x v#) ...))

  [-------------------
   (aps#-match/j _ * ())]

  ;; TODO: make a version of this that only matches external addresses, for the APS matching
  [-------------------
   (aps#-match/j v# x ([x v#]))]

  [(aps#-match/j v# p ([x v#_binding] ...)) ...
   --------------
   (aps#-match/j (variant t v# ..._n) (variant t p ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j (* τ) p ([x v#_binding] ...)) ...
   --------------
   (aps#-match/j (* (Union _ ... [t τ ..._n] _ ...)) (variant t p ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j v# p ([x v#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (record [l v#] ..._n) (record [l p] ..._n) ([x v#_binding] ... ...))]

  [(aps#-match/j (* τ) p ([x v#_binding] ...)) ...
   ---------------------------------------------
   (aps#-match/j (* (Record [l τ] ..._n)) (record [l p] ..._n) ([x v#_binding] ... ...))])

;; TODO: rewrite these tests
;; (module+ test
;;   (check-equal? (aps#-match (term (* Nat)) (term *))
;;                 (list (term ())))
;;   (check-equal? (aps#-match (term (received-addr Always ADDR-HOLE 0 MOST-RECENT)) (term x))
;;                 (list (term ([x (received-addr Always ADDR-HOLE 0 MOST-RECENT)]))))
;;   (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a 'b)))
;;                 (list (term ())))
;;   ;; (displayln (redex-match csa# t (term 'a)))
;;   ;; (displayln (redex-match csa# v# (term 'a)))
;;   ;; (displayln (redex-match csa# x (term item)))
;;   ;; (displayln (build-derivations (aps#-match/j 'a item ())))
;;   (check-equal? (aps#-match (term 'a) (term item))
;;                 (list (term ([item 'a]))))
;;   (check-equal? (aps#-match (term (tuple 'a 'b)) (term (tuple 'a item)))
;;                 (list (term ([item 'b]))))
;;   (check-equal? (aps#-match (term (* (Tuple 'a 'b))) (term (tuple x 'b)))
;;                 (list (term ([x (* 'a)])))))

;; TODO: write tests for the above match

(define (aps#-matches-po? value pattern)
  (judgment-holds (aps#-matches-po?/j ,value ,pattern)))

(define-judgment-form aps#
  #:mode (aps#-matches-po?/j I I)
  #:contract (aps#-matches-po?/j v# po)

  [-----
   (aps#-matches-po?/j _ *)]

  ;; TODO: make this rule match not quite everything
  [----
   (aps#-matches-po?/j _ x)]

  ;; TODO: self
  [----
   (aps#-matches-po?/j t t)]
  [----
   (aps#-matches-po?/j (* t) t)]

  [(aps#-matches-po?/j v# po) ...
   ------
   (aps#-matches-po?/j (variant t v# ..._n) (variant t po ..._n))]

  [(aps#-matches-po?/j (* τ) po) ...
   -----
   (aps#-matches-po?/j (* (Union _ ... [t τ ..._n] _ ...)) (variant t po ..._n))]

  [(aps#-matches-po?/j v# po)
   ------------------------------------------------------------
   (aps#-matches-po?/j v# (or _ ... po _ ...))])

(module+ test
    ;; TODO: rewrite these tests
  ;; (check-true (judgment-holds (aps#-matches-po?/j 'a 'a)))
  ;; (check-true (aps#-matches-po? (term 'a) (term 'a)))
  ;; (check-true (aps#-matches-po? (term (* 'a)) (term 'a)))
  ;; (check-false (aps#-matches-po? (term (* 'a)) (term 'b)))

  ;; (check-true (aps#-matches-po? (term (* (Tuple 'a 'b))) (term (tuple 'a 'b))))
  ;; (check-false (aps#-matches-po? (term (* (Tuple 'a 'b))) (term (tuple 'a 'c))))
  ;; (check-true (aps#-matches-po? (term (tuple (* 'a))) (term (tuple 'a))))
  ;; (check-true (aps#-matches-po? (term (tuple (quote b) (* Nat)))
  ;;                               (term (tuple (quote b) *))))
  (check-true (aps#-matches-po? (term (variant A)) (term (or (variant A) (variant B)))))
  (check-true (aps#-matches-po? (term (variant B)) (term (or (variant A) (variant B)))))
  (check-false (aps#-matches-po? (term (variant C)) (term (or (variant A) (variant B))))))

;; TODO: add tests for the match predicate

;; ---------------------------------------------------------------------------------------------------
;; Constructors

(define (aps#-spec-from-fsm-and-commitments instance commitments)
  (redex-let* aps# ([z instance]
                    [O commitments]
                    [Σ (term ((z) O))])
              (term Σ)))

(module+ test)

(define (aps#-spec-from-commitment-entry entry)
  (redex-let aps# ([(a#ext po ...) entry])
             (term (() ((a#ext po ...))))))

(module+ test
  (check-equal?
   (aps#-spec-from-commitment-entry (term ((obs-ext 0) * (record [a *] [b *]))))
   (term (() (((obs-ext 0) * (record [a *] [b *])))))))

;; ---------------------------------------------------------------------------------------------------
;; Selectors

(define (aps#-config-instances config)
  (term (config-instances/mf ,config)))

(define-metafunction aps#
  config-instances/mf : Σ -> (z ...)
  [(config-instances/mf ((z ...) _)) (z ...)])

(define (aps#-config-commitment-map config)
  (term (config-commitment-map/mf ,config)))

(define-metafunction aps#
  config-commitment-map/mf : Σ -> O
  [(config-commitment-map/mf (_ O)) O])

;; TODO: test these

(define (aps#-transition-pattern transition)
  (redex-let aps# ([(ε -> _) transition])
    (term ε)))

(define (aps#-transition-expression transition)
  (redex-let aps# ([(_ -> e-hat) transition])
    (term e-hat)))

(module+ test
  ;; TODO: rewrite these tests
  ;; (define transition (term [(tuple a b) -> (with-outputs ([a *]) (goto S))]))

  ;; (check-equal? (aps#-transition-pattern transition) (term (tuple a b)))
  ;; (check-equal? (aps#-transition-expression transition) (term (with-outputs ([a *]) (goto S))))
  ;; (define transition2 (term [unobs -> (with-outputs ([x *]) (goto S2))]))
  ;; (check-equal? (aps#-transition-pattern transition2) (term unobs))
  )

(define (aps#-goto-state goto-exp)
  (redex-let aps# ([(goto s _ ...) goto-exp])
             (term s)))

(module+ test
  (check-equal? (aps#-goto-state (term (goto A))) (term A))
  (check-equal? (aps#-goto-state (term (goto B (SINGLE-ACTOR-ADDR SINGLE-ACTOR-ADDR)))) (term B)))

(define (aps#-commitment-address commitment)
  (term (commitment-address/mf ,commitment)))

(define-metafunction aps#
  commitment-address/mf : [a#ext po] -> a#ext
  [(commitment-address/mf [a#ext po]) a#ext])

(define (aps#-commitment-pattern commitment)
  (redex-let aps# ([[_ po] commitment])
    (term po)))

(module+ test
  (define commitment (term [(* (Addr Nat)) (variant Null *)]))
  (check-equal? (aps#-commitment-address commitment) (term (* (Addr Nat))))
  (check-equal? (aps#-commitment-pattern commitment) (term (variant Null *))))

(define (aps#-commitment-entry-address entry)
  (redex-let aps# ([(a#ext _ ...)  entry])
             (term a#ext)))

(define (aps#-instance-state z)
  (term (instance-state/mf ,z)))

(define-metafunction aps#
  instance-state/mf : z -> s
  [(instance-state/mf (_ (goto s _ ...) _)) s])

(define (aps#-instance-arguments z)
  (term (instance-arguments/mf ,z)))

(define-metafunction aps#
  instance-arguments/mf : z -> (a#ext ...)
  [(instance-arguments/mf (_ (goto _ u ...) _)) (u ...)])

(module+ test
  (check-equal?
   (aps#-instance-state (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                               (goto Always (* (Addr Nat)) (obs-ext 1))
                               null)))
   (term Always))

  (check-equal?
   (aps#-instance-arguments (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                                   (goto Always (* (Addr Nat)) (obs-ext 1))
                                   null)))
   (term ((* (Addr Nat)) (obs-ext 1)))))

(define (aps#-relevant-external-addrs Σ)
  (term (relevant-external-addrs/mf ,Σ)))

(define-metafunction aps#
  relevant-external-addrs/mf : Σ -> (a#ext ...)
  [(relevant-external-addrs/mf Σ)
   ,(remove-duplicates (term (any_args ... ... any_commitment-addr ...)))
   (where (any_z ...) (config-instances/mf Σ))
   (where ((any_args ...) ...) ((instance-arguments/mf any_z) ...))
   (where ((any_commitment-addr _ ...) ...) (config-commitment-map/mf Σ))])

(module+ test
  (check-equal?
   (aps#-relevant-external-addrs
    (redex-let* aps#
                ([z_1 (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                             (goto Always (obs-ext 1) (obs-ext 2))
                             null))]
                 [z_2 (term (((define-state (Always r1 r2) (* -> (goto Always r1 r2))))
                             (goto Always (obs-ext 1) (obs-ext 3))
                             null))]
                 [O (term (((obs-ext 1)) ((obs-ext 3)) ((obs-ext 4))))]
                 [Σ (term ((z_1 z_2) O))])
                (term Σ)))
   (term ((obs-ext 1) (obs-ext 2) (obs-ext 3) (obs-ext 4)))))
