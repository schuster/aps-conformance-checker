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
   (name (x f a s T V))
   (PrimitiveType (pτ)))
  (Prog (P)
        (PI ... e))
  (ProgItem (PI)
            ad
            (define-function (f [x τ] ...) e)
            (define-type T τ)
            (define-record T [x τ] ...)
            (define-variant T (V [x τ] ...) ...))
  (ActorDef (ad)
    (define-actor τ (a [x τ2] ...) (fd ...) e S ...))
  (StateDef (S)
    (define-state (s [x τ]  ...) (x2) e))
  (Exp (e body)
       n
       b
       x
       (goto s e ...)
       (send e1 e2)
       (spawn a e ...)
       (begin e1 e* ...)
       (record [x e] ...)
       (: e x)
       (case e1 [(V x ...) e2] ...)
       (f e ...)
       ;; (po e ...)
       (+ e ...)
       (- e ...)
       (let (lb ...) e2)
       (let* (lb ...) e2))
  (LetBinding (lb)
              [x e])
  (FuncDef (fd)
           (define-function (f [x τ] ...) e))
  (Type (τ)
        pτ
        (Record [x τ] ...)
        (Union [V τ] ...)
        T)
  (entry Prog))

;; TODO: how does Nanopass resolve ambiguity?

;; TODO: put all the nominal stuff (at least program-level) into just one pass: it's basically all the
;; same, and would probably save boilerplate

;; ---------------------------------------------------------------------------------------------------
;; Variant desugaring

(define-language csa/desugared-variants
  (extends csa/surface)
  (ProgItem (PI)
            (- (define-variant T (V [x τ] ...) ...)))
  (Exp (e)
       (- (case e1 [(V x ...) e2] ...))
       (+ (case e1 [V x e2] ...))))

(define-parser parse-csa/desugared-variants csa/desugared-variants)

(define-pass desugar-variants : csa/surface (P) -> csa/desugared-variants ()
  (Prog : Prog (P items-to-add) -> Prog ()
        [((define-variant ,T (,V [,x ,[τ]] ...) ...) ,PI ... ,e)
         (define record-defs
           (map
            (lambda (name field-list types)
              (define x-as-f
                (build-list (length field-list)
                            (lambda (i) (string->symbol (string-append "f" (number->string (add1 i)))))))
              (with-output-language (csa/desugared-variants ProgItem)
                ;; TODO: field names must be different...
               `(define-record ,name [,x-as-f ,types] ...)))
            V x τ))
         (Prog (with-output-language (csa/surface Prog) `(,PI ... ,e))
               (append items-to-add
                       (append
                        record-defs
                        (list
                        (with-output-language (csa/desugared-variants ProgItem)
                          `(define-type ,T (Union [,V ,V] ...)))))
                       ))]
        [(,[PI1] ,PI* ... ,e)
         (Prog (with-output-language (csa/surface Prog) `(,PI* ... ,e))
               (append items-to-add (list PI1)))]
        [(,[e]) `(,items-to-add ... ,e)])
  (Exp : Exp (e) -> Exp ()
       [(case ,[e1] [(,V ,x ...) ,[e2]] ...)
        (define record-var (gensym))
        (define named-record-vars (build-list (length V) (lambda (i) record-var)))
        (define referenced-record-vars
          (for/list ([field-list x])
            (build-list
             (length field-list)
             (lambda (i) record-var))))
        (define field-name-lists
          (for/list ([field-list x])
            (build-list
             (length field-list)
             (lambda (i) (string->symbol (string-append "f" (number->string (add1 i))))))))
        ;; (for/list ([field-list x])
        ;;     (define record-var (gensym))
        ;;     (define-values (num field-names)
        ;;       (for/fold ([num 1]
        ;;                  [names-so-far null])
        ;;                 ([name field-list])
        ;;         (values (add1 num)
        ;;                 (append names-so-far
        ;;                         (list )))))
        ;;     (list field-names
        ;;           (build-list (length field-list) (lambda (i) record-var))
        ;;           record-var))
;;         (match-define (list generated-record-field-names referenced-record-vars named-record-vars)
;; )
        `(case ,e1
           [,V ,named-record-vars
               ;; TODO: would be nice if Nanopass did the Redex-style repetition of names so I didn't
               ;; rquire the above build-list calls, etc.
               (let ([,x (: ,referenced-record-vars ,field-name-lists)] ...) ,e2)] ...)])
  (Prog P null))

(module+ test
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (check-equal?
   (unparse-csa/desugared-variants
    (desugar-variants
     (with-output-language (csa/surface Prog)
       `((define-variant List (Null) (Cons [element Nat] [list List]))
         (case (Null)
           [(Null) 0]
           [(Cons element rest) element])))))
   `((define-record Null)
     (define-record Cons [f1 Nat] [f2 List])
     (define-type List (Union (Null Null) (Cons Cons)))
     (case (Null)
       [Null r (let () 0)]
       [Cons r
             (let ([element (: r f1)]
                   [rest (: r f2)])
               element)]))))

;; ---------------------------------------------------------------------------------------------------
;; Record type inlining

(define-language csa/inlined-records
  (extends csa/desugared-variants)
  (ProgItem (PI)
            (- (define-record T [x τ] ...))))

(define-parser parse-csa/inlined-records csa/inlined-records)

(define-pass inline-records : csa/desugared-variants (P) -> csa/inlined-records ()
  ;; TODO: I could really use something like syntax-parse's splicing forms so I could look at items
  ;; individually and splice them back in
  (Prog : Prog (P items-to-add) -> Prog ()
        [((define-record ,T [,x ,τ] ...) ,PI ... ,e)
         ;; TODO: would be nice if there were a shortcut syntax for saying "create something of the
         ;; source language type
         (Prog (with-output-language (csa/desugared-variants Prog) `(,PI ... ,e))
               (append items-to-add
                       (list ;; TODO: figure out why I need with-output-language here (maybe b/c I'm not parsing the entry point? or the entry point of this processor?
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-type ,T (Record [,x ,τ] ...)))
                        ;; TODO: figure out why I need with-output-language here
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-function (,T [,x ,τ] ...) (record [,x ,x] ...))))))]
        [(,[PI1] ,PI* ... ,e)
         (Prog (with-output-language (csa/desugared-variants Prog) `(,PI* ... ,e))
               (append items-to-add (list PI1)))]
        [(,[e]) `(,items-to-add ... ,e)])
  (Prog P null))

(module+ test
  (check-equal?
     (unparse-csa/inlined-records
   (inline-records
    (with-output-language (csa/desugared-variants Prog)
      `((define-record A [x Nat] [y Nat])
        (define-record B [z A])
        (B (A 5 4))))))

  `((define-type A (Record [x Nat] [y Nat]))
    (define-function (A [x Nat] [y Nat]) (record [x x] [y y]))
    (define-type B (Record [z A]))
    (define-function (B [z A]) (record [z z]))
    (B (A 5 4)))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Types

(define-language csa/inlined-types
  (extends csa/inlined-records)
  (ProgItem (PI)
            (- (define-type T τ)))
  (Type (τ) (- T)))

(define-parser parse-csa/inlined-types csa/inlined-types)

(define-pass inline-type-aliases : csa/inlined-records (P) -> csa/inlined-types ()
  ;; TODO: figure out the best way to do this kind of fold, because the restriction that the return
  ;; type always has to be the same languae prevents me from doing a general Subst processor like I
  ;; want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define aliases-so-far (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [((define-type ,T ,[τ]) ,PI ... ,e)
         ;; TODO: do something more defensive for hash overwrites
         (hash-set! aliases-so-far T τ)
         (Prog (with-output-language (csa/inlined-records Prog) `(,PI ... ,e))
               items-to-add)]
        [(,[PI1] ,PI* ... ,e)
         (Prog (with-output-language (csa/inlined-records Prog) `(,PI* ... ,e))
               (append items-to-add (list PI1)))]
        [(,[e])
         `(,items-to-add ... ,e)])
  (Type : Type (τ) -> Type ()
        [,T
         (hash-ref aliases-so-far T (lambda () (error ~s "Could not find alias for type ~s" T)))])
  (Prog P null))

(module+ test
  (check-equal?
   (unparse-csa/inlined-types
    (inline-type-aliases
     (parse-csa/inlined-records
      `((define-type MyT Nat)
        (define-actor MyT (A) ()
          (goto S1))
        (spawn A)))))
   `((define-actor Nat (A) ()
       (goto S1))
     (spawn A))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Program Functions

(define-language csa/inlined-program-functions
  (extends csa/inlined-types)
  (ProgItem (PI)
            (- (define-function (f [x τ] ...) e))))

(define-parser parse-csa/inlined-program-functions csa/inlined-program-functions)

(define-pass inline-program-functions : csa/inlined-types (P) -> csa/inlined-program-functions ()
  ;; TODO: figure out the best way to do this kind of fold, because the restriction that the return
  ;; type always has to be the same languae prevents me from doing a general Subst processor like I
  ;; want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define func-defs (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [((define-function (,f [,x ,τ] ...) ,[e]) ,PI ... ,body)
         (hash-set! func-defs f (func-record x e))
         (Prog (with-output-language (csa/inlined-types Prog) `(,PI ... ,body))
               items-to-add)]
        [(,[PI1] ,PI* ... ,e)
         (Prog (with-output-language (csa/inlined-types Prog) `(,PI* ... ,e))
               (append items-to-add (list PI1)))]
        [(,[e])
         `(,items-to-add ... ,e)])
  (Exp : Exp (e) -> Exp ()
       [(,f ,[e*] ...)
        (match-define (func-record formals body)
          (hash-ref func-defs f (lambda () (error 'inline-functions "could not find match for function in call ~s\n" e))))
        `(let ([,formals ,e*] ...) ,body)])

  (Prog P null))

(module+ test
  (check-equal?
   (unparse-csa/inlined-program-functions
    (inline-program-functions
     (parse-csa/inlined-types
      `((define-function (double [x Nat]) (+ x x))
        (double 5)))))
   `((let ([x 5]) (+ x x)))))

;; ---------------------------------------------------------------------------------------------------
;; Actor function inlining

(define-language csa/inlined-actor-functions
  (extends csa/inlined-program-functions)
  (ActorDef (ad)
            (- (define-actor τ (a [x τ2] ...) (fd ...) e S ...))
            (+ (define-actor τ (a [x τ2] ...)          e S ...)))
  (Exp (e) (- (f e ...))))

(define-parser parse-csa/inlined-actor-functions csa/inlined-actor-functions)

(struct func-record (formals body))

(define-pass inline-actor-functions : csa/inlined-program-functions (P) -> csa/inlined-actor-functions ()
  (definitions
    ;; TODO: clear this list every time we start a new actor
    (define funcs (make-hash)))
  (ActorDef : ActorDef (d) -> ActorDef ()
    [(define-actor ,τ (,a [,x1 ,τ1] ...) ((define-function (,f [,x2 ,[τ2]] ...) ,[body]) ,fd* ...)  ,e ,S ...)
     (hash-set! funcs f (func-record x2 body))
     (ActorDef
      (with-output-language (csa/inlined-program-functions ActorDef)
        `(define-actor ,τ (,a [,x1 ,τ1] ...) (,fd* ...) ,e ,S ...)))]
    [(define-actor ,[τ] (,a [,x ,[τ1]] ...) () ,[e] ,[S] ...)
     `(define-actor ,τ (,a [,x ,τ1] ...) ,e ,S ...)])
  (Exp : Exp (e) -> Exp ()
       ;; TODO: see tmp/expected-meta for why this breaks
       [(,f ,[e*] ...)
        (match-define (func-record formals body)
          (hash-ref funcs f (lambda () (error 'inline-actor-functions "could not find match for function in call ~s\n" e))))
        `(let ([,formals ,e*] ...) ,body)]
        [(,po ,[e*] ...)
         (,po ,e* ...)])
  ;; (StateDef : StateDef (S) -> StateDef ()
  ;;           [(define-state (,s ,x1 ...) (,x2) ,[e])
  ;;            `(define-state (,s ,x1 ...) (,x2) ,e)])
  )

(module+ test
  (require rackunit)

  (check-equal?
   (unparse-csa/inlined-actor-functions
    (inline-actor-functions
     (with-output-language (csa/inlined-program-functions Prog)
       `((define-actor Nat (A)
           ((define-function (foo [x Nat]) (+ x 2))
            (define-function (bar [x Nat] [y Nat]) (- x y)))
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
;; Inlined Actors

(define-language csa/inlined-actors
  (extends csa/inlined-actor-functions)
  (Prog (P)
    (- (PI ... e))
    (+ e))
  (ProgItem (P)
            (- ad))
  (Exp (e)
       (- (spawn a e ...))
       (+ (spawn τ e S ...))))

(struct actor-record (type formals body state-defs))

(define-pass inline-actors : csa/inlined-actor-functions (P) -> csa/inlined-actors ()
  ;; TODO: I think the return "type" is not checked, because I've seen things get through when I had ActorDef instead of Prog
  (Prog : Prog (P defs-so-far) -> Prog ()
        [(
          (define-actor ,[τ] (,a [,x ,[τ1]] ...)  ,[Exp : e0 defs-so-far -> e] ,[StateDef : S0 defs-so-far -> S] ...) ,PI* ... ,e1)
         (Prog (with-output-language (csa/inlined-actor-functions Prog) `(,PI* ... ,e1))
               ;; TODO: figure out if hash-set overwrites existing entries or not
               (hash-set defs-so-far a (actor-record τ x e S)))]
        [(,[Exp : e0 defs-so-far -> e]) e])
  (StateDef : StateDef (S defs-so-far) -> StateDef ()
    [(define-state (,s [,x ,[τ]] ...) (,x2) ,[Exp : e0 defs-so-far -> e])
     `(define-state (,s [,x ,τ] ...) (,x2) ,e)])
  ;; (MyExp2 : Exp (e) -> Exp ()
  ;;         [,spawn-exp `5]
  ;;         )
  (Exp : Exp (e defs-so-far) -> Exp ()
       [(spawn ,a ,[Exp : e0 defs-so-far -> e] ...)
        (match (hash-ref defs-so-far a #f)
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
     (with-output-language (csa/inlined-actor-functions Prog)
       `((define-actor Nat (A [x Nat])
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
     (with-output-language (csa/inlined-actor-functions Prog)
       `((define-actor Nat (A [x Nat])
           (goto S1)
           (define-state (S1) (m)
             (goto S1)))
         (define-actor Nat (B [y Nat])
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
     inline-actor-functions
     inline-program-functions
     inline-type-aliases
     inline-records
     desugar-variants
     parse-actor-def-csa/surface))
  ;; TODO: deal with actor parameters and type
  (redex-let csa-eval ([(let () (spawn τ e S ...)) (pass single-actor-prog)])
    (term (,address ((S ...) e)))))
