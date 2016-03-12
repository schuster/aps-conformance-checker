#lang racket

;; Defines the desugaring from the surface syntax to the core syntax

(provide desugar-single-actor-program)

(require
 (only-in redex/reduction-semantics redex-let term)
 "csa.rkt")

;; TODO: consider using Nanopass for this transformation

;; Translates an actor definition from the surface syntax into the core language syntax
;;
;; TODO: add actor args
;; (define (desugar-actor actor-def address)
;;   (term (desugar-actor/mf ,actor-def ,address))
;;   )

;; (define-metafunction csa-eval
;;   ;; TODO: define some sort of Redex language that defines the surface-level programs
;;   desugar-actor/mf : any a -> αn
;;   [(desugar-actor/mf (define-actor (_) e S ...) a)
;;    (a ((S ...) e))])

;; (module+ test
;;   (require rackunit)

;;   (check-equal?
;;    (desugar-actor
;;     (term (define-actor (IgnoreAll)
;;             (goto Always)
;;             (define-state (Always) (m) (goto Always))))
;;     (term (addr 0)))
;;    (term ((addr 0)
;;           (((define-state (Always) (m) (goto Always)))
;;            (goto Always))))))

;; ---------------------------------------------------------------------------------------------------

(require nanopass)

(define (name? x)
  (and (symbol? x)
       (not (PrimOp? x))
       (not (PrimitiveType? x))))

(define (PrimOp? x) (not (not (member x (list '+ '-)))))

(define (PrimitiveType? x)
  (not (not (member x (list 'Nat)))))

(module+ test
  (check-not-false (PrimOp? '+))
  (check-false (name? '+))
  (check-false (PrimOp? 'x))
  (check-true (name? 'x)))

(define-language csa/surface
  (terminals
   (number (n))
   (boolean (b))
   (name (x f a s T))
   (PrimitiveType (pτ))
   )
  (Prog (P)
        (PI ... e))
  (ProgItem (PI)
            ad
            (define-type T τ))
  (ActorDef (ad)
    (define-actor τ (a x ...) (fd ...) e S ...))
  (StateDef (S)
    (define-state (s x  ...) (x2) e))
  (Exp (e body)
       n
       b
       x
       (goto s e ...)
       (send e1 e2)
       (spawn a e ...)
       (begin e1 e* ...)
       (f e ...)
       ;; (po e ...)
       (+ e ...)
       (- e ...)
       (let (lb ...) e2)
       (let* (lb ...) e2))
  (LetBinding (lb)
              [x e])
  (FuncDef (fd)
           (define-function (f x ...) e))
  (Type (τ)
        pτ
        T)
  (entry Prog))

;; TODO: how does Nanopass resolve ambiguity?

;; ---------------------------------------------------------------------------------------------------
;; Function inlining

(define-language csa/inlined-functions
  (extends csa/surface)
  (ActorDef (ad)
            (- (define-actor τ (a x ...) (fd ...) e S ...))
            (+ (define-actor τ (a x ...)          e S ...)))
  (Exp (e) (- (f e ...))))

(define-parser parse-csa/inlined-functions csa/inlined-functions)

(struct func-record (name formals body))

(define-pass inline-functions : csa/surface (P) -> csa/inlined-functions ()
  (definitions
    (define funcs null))
  (ActorDef : ActorDef (d) -> ActorDef ()
    [(define-actor ,τ (,a ,x1 ...) ((define-function (,f ,x2 ...) ,[body]) ,fd* ...)  ,e ,S ...)
     (set! funcs (cons (func-record f x2 body) funcs))
     (ActorDef
      (with-output-language (csa/surface ActorDef)
        `(define-actor ,τ (,a ,x1 ...) (,fd* ...) ,e ,S ...)))]
    [(define-actor ,τ (,a ,x ...) () ,[e] ,[S] ...)
     `(define-actor ,τ (,a ,x ...) ,e ,S ...)])
  (Exp : Exp (e) -> Exp ()
       ;; TODO: see tmp/expected-meta for why this breaks

    [(,f ,[e*] ...)
         (define (name-matches? rec) (eq? f (func-record-name rec)))
         (match (findf name-matches? funcs)
           [#f (error 'inline-functions "could not find match for function ~s\n") f]
           [(func-record _ (list formals ...) body)
            `(let ([,formals ,e*] ...) ,body)])]
        [(,po ,[e*] ...)
     (,po ,e* ...)])
  (StateDef : StateDef (S) -> StateDef ()
            [(define-state (,s ,x1 ...) (,x2) ,[e])
             `(define-state (,s ,x1 ...) (,x2) ,e)]))

(module+ test
  (require rackunit)

  (check-equal?
   (unparse-csa/inlined-functions
    (inline-functions
     (with-output-language (csa/surface Prog)
       `((define-actor Nat (A)
           ((define-function (foo x) (+ x 2))
            (define-function (bar x y) (- x y)))
           (foo (bar 3 4)))
         (spawn A)))))
   `((define-actor Nat (A)
       (let ([x
              (let ([x 3]
                    [y 4])
                (- x y))])
         (+ x 2)))
     (spawn A))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Types

(define-language csa/inlined-types
  (extends csa/inlined-functions)
  (ProgItem (PI)
            (- (define-type T τ)))
  (Type (τ) (- T)))

(define-parser parse-csa/inlined-types csa/inlined-types)

(define-pass inline-type-aliases : csa/inlined-functions (P) -> csa/inlined-types ()
  ;; TODO: figure out the best way to do this kind of fold, because the restriction that the return
  ;; type always has to be the same languae prevents me from doing a general Subst processor like I
  ;; want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define aliases-so-far (make-hash)))
  (Prog : Prog (P) -> Prog ()
        [((define-type ,T ,[τ]) ,PI ... ,e)
         ;; TODO: do something more defensive for hash overwrites
         (hash-set! aliases-so-far T τ)
         (Prog (with-output-language (csa/inlined-functions Prog) `(,PI ... ,e)))]
        ;; [(,[PI1^ aliases-so-far -> PI1] ,PI* ... ,e)
        ;;  (AppendItem (Prog (with-output-language (csa/inlined-functions Prog) `(,PI* ... ,e))
        ;;                    aliases-so-far)
        ;;              PI1)]
        ;; [(,[e0 aliases-so-far -> e]) `e]
        )
  (Type : Type (τ) -> Type ()
        [,T
         (hash-ref aliases-so-far T (lambda () (error ~s "Could not find alias for type ~s" T)))]))

(module+ test
  (check-equal?
   (unparse-csa/inlined-types
    (inline-type-aliases
     (parse-csa/inlined-functions
      `((define-type MyT Nat)
        (define-actor MyT (A)
          (goto S1))
        (spawn A)))))
   `((define-actor Nat (A)
       (goto S1))
     (spawn A))))

;; ---------------------------------------------------------------------------------------------------

(define-language csa/inlined-actors
  (extends csa/inlined-types)
  (Prog (P)
    (- (PI ... e))
    (+ e))
  (Exp (e)
       (- (spawn a e ...))
       (+ (spawn τ e S ...))))

(struct actor-record (type formals body state-defs))

(define-pass inline-actors : csa/inlined-functions (P) -> csa/inlined-actors ()
  ;; TODO: I think the return "type" is not checked, because I've seen things get through when I had ActorDef instead of Prog
  (Prog : Prog (P defs-so-far) -> Prog ()
        [((define-actor ,τ (,a ,x ...)  ,[Exp : e0 defs-so-far -> e] ,[StateDef : S0 defs-so-far -> S] ...) ,ad* ... ,e1)
         (Prog (with-output-language (csa/inlined-functions Prog) `(,ad* ... ,e1))
               ;; TODO: figure out if hash-set overwrites existing entries or not
               (hash-set defs-so-far a (actor-record τ x e S)))]
        [(,[Exp : e0 defs-so-far -> e]) e])
  (StateDef : StateDef (S defs-so-far) -> StateDef ()
    [(define-state (,s ,x ...) (,x2) ,[Exp : e0 defs-so-far -> e])
     `(define-state (,s ,x ...) (,x2) ,e)])
  ;; (MyExp2 : Exp (e) -> Exp ()
  ;;         [,spawn-exp `5]
  ;;         )
  (Exp : Exp (e defs-so-far) -> Exp ()
       [(spawn ,a ,[Exp : e0 defs-so-far -> e] ...)
        (match (hash-ref defs-so-far a)
          [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
          [(actor-record type formals body state-defs)
           ;; TODO: do I need to rename variables here at all?
           ;; `(spawn (goto S-Bad1))
           `(let ([,formals ,e] ...) (spawn ,type ,body ,state-defs ...))
           ])

        ;; ,spawn-exp
        ;; (SpawnExp spawn-exp defs-so-far)
        ]
       ;; [(goto ,s ,[e0 defs-so-far -> e] ...)
       ;;  `(goto ,s ,e)]
       ;; [(send ,[e1 defs-so-far -> e11] ,[e2 defs-so-far e22])
       ;;  `(send ,e1 ,e2)]
       ;; [(begin ,[e0 defs-so-far])]

       ;;        n
       ;; b
       ;; x
       ;; (goto s e ...)
       ;; (send e1 e2)
       ;; spawn-exp
       ;; (begin e1 e* ...)
       ;; (f e ...)
       ;; ;; (po e ...)
       ;; (+ e ...)
       ;; (- e ...)
       ;; (let (lb ...) e2)
       ;; (let* (lb ...) e2)

       )
  ;; (SpawnExp : SpawnExp (spawn-exp defs-so-far) -> SpawnExp ()
  ;;      [(spawn ,a ,[Exp : e0 defs-so-far -> e] ...)
  ;;       (match (hash-ref defs-so-far a)
  ;;         [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
  ;;         [(actor-record formals state-defs body)
  ;;          ;; TODO: do I need to rename variables here at all?
  ;;          ;; `(spawn (goto S-Bad1))
  ;;          `(let (;; [,formals ,e] ...
  ;;                 ) (spawn ,state-defs ... ,body))
  ;;          ])]
  ;;      [else "error in spawnexp"])

  ;; TODO: figure out why this processor is necessary at all
  ;; (SpawnExp2 : SpawnExp (spawn-exp) -> SpawnExp ()
  ;;            [(spawn ,a ,e ...)
  ;;             (error "this should never happen")

  ;;       ;; (match (findf (lambda (rec) (eq? a (actor-recod-name rec))) defs-so-far)
  ;;       ;;   [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
  ;;       ;;   [(actor-record formals state-defs body)
  ;;       ;;    ;; TODO: do I need to rename variables here at all?
  ;;       ;;    `(let ([,formals ,e] ...) (spawn ,state-defs ... ,body))])
  ;;            ]
  ;; )

  ;; BUG: (?): shouldn't this be the default init statement?
  (Prog P (hash)))

(module+ test
  (check-equal?
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-functions Prog)
       `((define-actor Nat (A x)
           (goto S1)
           (define-state (S1) (m)
             (goto S1)))
         (spawn A 5)))))
   `(let ([x 5])
      (spawn
       Nat
       (goto S1)
       (define-state (S1) (m) (goto S1)))))

  (check-equal?
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-functions Prog)
       `((define-actor Nat (A x)
           (goto S1)
           (define-state (S1) (m)
             (goto S1)))
         (define-actor Nat (B y)
           (goto S2)
           (define-state (S2) (m)
             (begin
               (spawn A 3)
               (goto S2))))
         (spawn B 5)))))
   `(let ([y 5])
      (spawn
       Nat
       (goto S2)
       (define-state (S2) (m)
         (begin
           (let ([x 3])
             (spawn
              Nat
              (goto S1)
              (define-state (S1) (m)
                (goto S1))))
           (goto S2)))))))

;; ---------------------------------------------------------------------------------------------------

(define-parser parse-actor-def-csa/surface csa/surface)

(define (desugar-single-actor-program single-actor-prog address)
  (define pass
    (compose
     unparse-csa/inlined-actors
     inline-actors
     inline-functions
     parse-actor-def-csa/surface))
  ;; TODO: deal with actor parameters and type
  (redex-let csa-eval ([(let () (spawn τ e S ...)) (pass single-actor-prog)])
    (term (,address ((S ...) e)))))
