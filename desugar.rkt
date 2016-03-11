#lang racket

;; Defines the desugaring from the surface syntax to the core syntax

;; (provide desugar-program)

(require
 ;; redex/reduction-semantics
 ;; "csa.rkt"
 )

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

;; (define desugar-program
;;   (compose )
;;   (unparse-csa/actors-inlined
;;    (desugar-pass
;;     (with-output-language (csa/surface ActorDef)
;;       `,a))))

;; (define desugar-program
;;   (compose
;;    unparse-csa/inlined-actors
;;    inline-actor-defs
;;    inline-functions
;;    parse-csa/surface))

;; ---------------------------------------------------------------------------------------------------

(require nanopass)

(define (name? x) (and (symbol? x) (not (PrimOp? x))))
(define (PrimOp? x) (not (not (member x (list '+ '-)))))

(check-not-false (PrimOp? '+))
(check-false (name? '+))
(check-false (PrimOp? 'x))
(check-true (name? 'x))

(define-language csa/surface
  (terminals
   (number (n))
   (boolean (b))
   (name (x f a s))
   ;; (PrimOp (po))
   )
  (Prog (P)
    (ad ... spawn-exp))
  (ActorDef (ad)
    (define-actor (a x ...) (fd ...) S ... e))
  (StateDef (S)
    (define-state (s x ...) (x2) e))
  (Exp (e body)
       n
       b
       x
       (goto s e ...)
       (send e1 e2)
       spawn-exp
       (begin e1 e* ...)
       (f e ...)
       ;; (po e ...)
       (+ e ...)
       (- e ...)
       (let (lb ...) e2)
       (let* (lb ...) e2))
  (SpawnExp (spawn-exp)
            (spawn a e ...))
  (LetBinding (lb)
              [x e])
  (FuncDef (fd)
           (define-function (f x ...) e))
  (entry Prog))

;; (define (parse-csa/surface prog)
;;   (with-output-language (csa/surface Prog)
;;     `,prog))

;; TODO: how does Nanopass resolve ambiguity?

;; (define-pass
;;   let*->let : L1 (P) -> L1
;;   (Exp (e) : Exp -> Exp
;;        [(let* () ,[e]) ,e]
;;        [(let* ([,x1 ,e1] [x* e*] ...))
;;         (let ([x1 e1]) (let* ([x* e*] ...)))
;;         ]
;;        )

;;   )

;; (module+ test
;;   (let*->let
;;    `(let* ([a 1] [b 2] [c 3]) (+ a b c)))
;;   `(let ([a 1])
;;      (let ([b 2])
;;        (let ([c 3])))))

;; ---------------------------------------------------------------------------------------------------
;; Function inlining

(define-language csa/inlined-funcs
  (extends csa/surface)
  (ActorDef (ad)
            (- (define-actor (a x ...) (fd ...) S ... e))
            (+ (define-actor (a x ...)          S ... e)))
  (Exp (e) (- (f e ...))))

(struct func-record (name formals body))

;; (define-pass inline-functions : csa/surface (actor-def) -> csa/inlined-funcs ()
;;   (definitions
;;     (define funcs null))
;;   (ActorDef : ActorDef (d) -> ActorDef ()
;;     [(define-actor (,a ,x1 ...) ((define-function (,f ,x2 ...) ,[body]) ,fd* ...) ,S ... ,e)
;;      (set! funcs (cons (func-record f x2 body) funcs))
;;      (ActorDef
;;       (with-output-language (csa/surface ActorDef)
;;         `(define-actor (,a ,x1 ...) (,fd* ...) ,S ... ,e)))]
;;     [(define-actor (,a ,x ...) () ,[S] ... ,[e])
;;      `(define-actor (,a ,x ...) ,S ... ,e)])
;;   (Exp : Exp (e) -> Exp ()
;;        ;; TODO: see tmp/expected-meta for why this breaks

;;     [(,f ,[e*] ...)
;;          (define (name-matches? rec) (eq? f (func-record-name rec)))
;;          (match (findf name-matches? funcs)
;;            [#f (error 'inline-functions "could not find match for function ~s\n") f]
;;            [(func-record _ (list formals ...) body)
;;             `(let ([,formals ,e*] ...) ,body)])]
;;         [(,po ,[e*] ...)
;;      (,po ,e* ...)])
;;   (StateDef : StateDef (S) -> StateDef ()
;;             [(define-state (,s ,x1 ...) (,x2) ,[e])
;;              `(define-state (,s ,x1 ...) (,x2) ,e)]))

(require rackunit)

;; (check-equal?
;;  (unparse-csa/inlined-funcs
;;   (inline-functions
;;    (with-output-language (csa/surface ActorDef)
;;      `(define-actor (A)
;;         (     (define-function (foo x) (+ x 2))
;;               (define-function (bar x y) (- x y)))
;;         (foo (bar 3 4))))))
;;  `(define-actor (A)
;;     (let ([x
;;            (let ([x 3]
;;                  [y 4])
;;              (- x y))])
;;       (+ x 2))))

;; ---------------------------------------------------------------------------------------------------

(define-language csa/inlined-actors
  (extends csa/inlined-funcs)
  (Prog (P)
    (- (ad ... spawn-exp))
    (+ spawn-exp))
  (SpawnExp (spawn-exp)
            (- (spawn a e ...))
            (+ (spawn e S ...))))

(struct actor-record (formals state-defs body))

(define-pass inline-actors : csa/inlined-funcs (P defs-so-far) -> csa/inlined-actors ()
  (Prog : Prog (P defs-so-far) -> ActorDef ()
        [((define-actor (,a ,x ...) ,[StateDef : S0 defs-so-far -> S] ... ,[Exp : e0 defs-so-far -> e]) ,ad* ... ,spawn-exp)
         (Prog (with-output-language (csa/inlined-funcs Prog) `(,ad* ... ,spawn-exp))
               ;; TODO: figure out if hash-set overwrites existing entries or not
               (hash-set defs-so-far a (actor-record x S e)))]
        [(,[SpawnExp : spawn-exp0 defs-so-far -> spawn-exp]) spawn-exp])
  (StateDef : StateDef (S defs-so-far) -> StateDef ()
    [(define-state (,s ,x ...) (,x2) ,[Exp : e0 defs-so-far -> e])
     `(define-state (,s ,x ...) (,x2) ,e)])
  (Exp : Exp (e defs-so-far) -> Exp ()
       [,spawn-exp
        (SpawnExp spawn-exp defs-so-far)]
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
  (SpawnExp : SpawnExp (spawn-exp defs-so-far) -> SpawnExp ()
       [(spawn ,a ,[Exp : e0 defs-so-far -> e] ...)
        (match (hash-ref defs-so-far a)
          [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
          [(actor-record formals state-defs body)
           ;; TODO: do I need to rename variables here at all?
           `(spawn (goto S-Bad))
           ;; `(let ([,formals ,e] ...) (spawn ,state-defs ... ,body))
           ])]
       [else "error in spawnexp"])
  ;; TODO: this one is just for debugging
  (SpawnExp2 : SpawnExp (spawn-exp) -> SpawnExp ()
             [(spawn ,a ,e ...)
              (displayln spawn-exp)
             `(spawn (goto S1))
        ;; (match (findf (lambda (rec) (eq? a (actor-recod-name rec))) defs-so-far)
        ;;   [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
        ;;   [(actor-record formals state-defs body)
        ;;    ;; TODO: do I need to rename variables here at all?
        ;;    `(let ([,formals ,e] ...) (spawn ,state-defs ... ,body))])
             ]
)
  (Prog P (hash))
  )

(check-equal?
 (unparse-csa/inlined-actors
  (inline-actors
   (with-output-language (csa/inlined-funcs Prog)
     `((define-actor (A x)
         (define-state (S1) (m) (goto S1))
         (goto S1))
       (spawn A 5)))
   (hash)))
 `(let ([x 5])
   (spawn
    (goto S1)
    (define-state (S1) (m) (goto S1)))))

 ;; (unparse-csa/inlined-funcs
 ;;  (inline-functions
 ;;   (with-output-language (csa/surface ActorDef)
