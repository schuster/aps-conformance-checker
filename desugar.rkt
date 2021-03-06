 #lang racket

;; Nanopass-based desugarer for the bigger language (desugars down to CSA)

(provide
 desugar)

;; ---------------------------------------------------------------------------------------------------

(require nanopass)

(module+ test
  (require rackunit))

(define (name? x)
  (and (symbol? x)
       (not (PrimitiveType? x))
       (not (eq? x 'timeout))))

(define (PrimitiveType? x)
  (not (not (member x (list 'Nat 'String)))))

(define (ProgramKeyword? x)
  (equal? x 'program))

(define (ElseKeyword? x)
  (equal? x 'else))

(define (ReceptionistsKeyword? x)
  (equal? x 'receptionists))

(define (ExternalsKeyword? x)
  (equal? x 'externals))

(define (LetActorsKeyword? x)
  (equal? x 'let-actors))

(define (Location? x)
  #t)

(define-language csa/surface
  (terminals
   (number (n))
   (boolean (b))
   (name (x f a s T V))
   (string (string))
   (PrimitiveType (pτ))
   ;; REFACTOR: figure out how to get rid of this
   (ProgramKeyword (program-kw))
   (ElseKeyword (else-kw))
   (ReceptionistsKeyword (receptionists-kw))
   (ExternalsKeyword (externals-kw))
   (LetActorsKeyword (let-actors-kw))
   (Location (l)))
  (Prog (P)
        (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                    PI ...
                    ;; NOTE: e should be a spawn expression
                    (let-actors-kw ([x3 e] ...) x4 ...)))
  (ProgItem (PI)
            ad
            fd
            cd
            (define-type T τ)
            (define-record T [x τ] ...)
            (define-variant T (V [x τ] ...) ...))
  (ActorDef (ad)
    (define-actor τ (a [x τ2] ...) (AI ...) e S ...))
  (StateDef (S)
            (define-state (s [x τ] ...) x2 e1 e* ...)
            (define-state/timeout (s [x τ] ...) x2 e1 e* ... tc))
  (TimeoutClause (tc) [timeout e2 e3 e4 ...])
  (ActorItem (AI)
    fd
    cd)
  (Exp (e body)
       n
       b
       string
       x
       (goto s e ...)
       (send e1 e2)
       ;; REFACTOR: have Nanopass compute the line number for each spawn
       (spawn l a e ...)
       (record [x e] ...)
       (variant V e ...)
       (: e x)
       (! e [x e2])
       (fold τ e)
       (unfold τ e)
       (case e1 [(V x ...) e2 e* ...] ...)
       ;; (po e ...)
       ;;
       ;; REFACTOR: find a way to generalize these to primops (ideal solution requires "tagless" fix
       ;; in Nanopass)
       (+ e1 e2)
       (- e1 e2)
       (mult e1 e2)
       (/ e1 e2)
       (arithmetic-shift e1 e2)
       (< e1 e2)
       (<= e1 e2)
       (> e1 e2)
       (>= e1 e2)
       (= e1 e2)
       (and e1 e2 ...)
       (or e1 e2 ...)
       (not e1)
       (if e1 e2 e3)
       (cond [e1 e2 e2* ...] ... [else-kw e3 e3* ...])
       (random e)
       (list e ...)
       (cons e1 e2)
       (list-as-variant e)
       (list-ref e1 e2)
       (remove e1 e2)
       (length e)
       (take e1 e2)
       (drop e1 e2)
       (list-copy e1 e2 e3)
       (append e1 e2)
       (dict [e1 e2] ...)
       (dict-ref e1 e2)
       (dict-keys e1)
       (dict-values e1)
       (dict-set e1 e2 e3)
       (dict-remove e1 e2)
       (dict-has-key? e1 e2)
       (dict-empty? e1)
       (printf e1 e* ...)
       (print-len e)
       (for/fold ([x1 e1]) ([x2 e2]) e3 e* ...)
       (for ([x1 e1]) e2 e* ...)
       (let ([x e] ...) e2 e* ...)
       (let* ([x e] ...) e2 e* ...)
       (addr n τ) ; only for giving the initial output addresses
       (f e ...))
  (FuncDef (fd)
           (define-function (f [x τ] ...) e1 e* ...))
  (ConstDef (cd)
            (define-constant x e)) ; NOTE: should really only be literals
  (Type (τ)
        pτ
        (rec T τ)
        T ; not really the right grammar, but Nanopass seems to require having at most one clause per
          ; constructor
        (Addr τ)
        (Record [x τ] ...)
        (Variant [V τ ...] ...)
        (List τ)
        (Dict τ1 τ2))
  (entry Prog))

;; ---------------------------------------------------------------------------------------------------
;; Function Call Wrapping

(define-language csa/wrapped-calls
  (extends csa/surface)
  (Exp (e)
       (- (f e ...))
       (+ (app f e ...))))

(define-parser parse-csa/wrapped-calls csa/wrapped-calls)

(define-pass wrap-function-calls : csa/surface (P) -> csa/wrapped-calls ()
  (Exp : Exp (e) -> Exp ()
       [(,f ,[e] ...) `(app ,f ,e ...)]))

(module+ test
  (test-equal? "Wrapped calls"
    (unparse-csa/wrapped-calls
     (wrap-function-calls
      (with-output-language (csa/surface Prog)
        `(program (receptionists) (externals) (let-actors ([a (f (g 1) 2)]) a)))))
    `(program (receptionists) (externals) (let-actors ([a (app f (app g 1) 2)]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Multi-body shrinking

(define-language csa/single-exp-bodies
  (extends csa/wrapped-calls)
  (StateDef (S)
            (- (define-state (s [x τ] ...) x2 e1 e* ...)
               (define-state/timeout (s [x τ] ...) x2 e1 e* ... tc))
            (+ (define-state (s [x τ] ...) x2 e)
               (define-state/timeout (s [x τ] ...) x2 e1 tc)))
  (TimeoutClause (tc)
                 (- [timeout e2 e3 e4 ...])
                 (+ [timeout e2 e3]))
  (FuncDef (fd)
           (- (define-function (f [x τ] ...) e1 e* ...))
           (+ (define-function (f [x τ] ...) e)))
  (Exp (e)
       (- (case e1 [(V x ...) e2 e* ...] ...)
          (let ([x e] ...) e2 e* ...)
          (let* ([x e] ...) e2 e* ...)
          (cond [e1 e2 e2* ...] ... [else-kw e3 e3* ...])
          (and e1 e2 ...)
          (or e1 e2 ...)
          (for/fold ([x1 e1]) ([x2 e2]) e3 e* ...)
          (for ([x1 e1]) e2 e* ...))
       (+ (case e1 [(V x ...) e2] ...)
          (let ([x e] ...) e2)
          (let* ([x e] ...) e2)
          (cond [e1 e2] ... [else-kw e3])
          (and e1 e2)
          (or e1 e2)
          (for/fold ([x1 e1]) ([x2 e2]) e3)
          (for ([x1 e1]) e2)
          (begin e1 e* ...))))

(define-parser parse-csa/single-exp-bodies csa/single-exp-bodies)

(define-pass wrap-multi-exp-bodies : csa/wrapped-calls (P) -> csa/single-exp-bodies ()
  (StateDef : StateDef (S) -> StateDef ()
            [(define-state (,s [,x ,[τ]] ...) ,x2 ,[e1] ,[e*] ...)
             `(define-state (,s [,x ,τ] ...) ,x2 (begin ,e1 ,e* ...))]
            [(define-state/timeout (,s [,x ,[τ]] ...) ,x2 ,[e1] ,[e*] ... ,[tc])
             `(define-state/timeout (,s [,x ,τ] ...) ,x2 (begin ,e1 ,e* ...) ,tc)])
  (TimeoutClause : TimeoutClause (tc) -> TimeoutClause ()
                 [(timeout ,[e2] ,[e3] ,[e4] ...)
                  `(timeout ,e2 (begin ,e3 ,e4 ...))])
  (FuncDef : FuncDef (fd) -> FuncDef ()
           [(define-function (,f [,x ,[τ]] ...) ,[e1] ,[e*] ...)
            `(define-function (,f [,x ,τ] ...) (begin ,e1 ,e* ...))])
  (Exp : Exp (e) -> Exp ()
       [(case ,[e1] [(,V ,x ...) ,[e2] ,[e*] ...] ...)
        `(case ,e1 [(,V ,x ...) (begin ,e2 ,e* ...)] ...)]
       [(let ([,x ,[e]] ...) ,[e2] ,[e*] ...)
        `(let ([,x ,e] ...) (begin ,e2 ,e* ...))]
       [(let* ([,x ,[e]] ...) ,[e2] ,[e*] ...)
        `(let* ([,x ,e] ...) (begin ,e2 ,e* ...))]
       [(cond [,[e1] ,[e2] ,[e2*] ...] ... [,else-kw ,[e3] ,[e3*] ...])
        `(cond [,e1 (begin ,e2 ,e2* ...)] ... [,else-kw (begin ,e3 ,e3* ...)])]
       [(and ,[e1] ,[e2]) `(and ,e1 ,e2)]
       [(and ,[e1] ,e2 ,e3 ...)
        `(and ,e1 ,(Exp (with-output-language (csa/wrapped-calls Exp) `(and ,e2 ,e3 ...))))]
       [(or ,[e1] ,[e2]) `(or ,e1 ,e2)]
       [(or ,[e1] ,e2 ,e3 ...)
        `(or ,e1 ,(Exp (with-output-language (csa/wrapped-calls Exp) `(or ,e2 ,e3 ...))))]
       [(for/fold ([,x1 ,[e1]]) ([,x2 ,[e2]]) ,[e3] ,[e*] ...)
        `(for/fold ([,x1 ,e1]) ([,x2 ,e2]) (begin ,e3 ,e* ...))]
       [(for ([,x1 ,[e1]]) ,[e2] ,[e*] ...)
        `(for ([,x1 ,e1]) (begin ,e2 ,e* ...))]))

(define-pass remove-extraneous-begins : csa/single-exp-bodies (P) -> csa/single-exp-bodies ()
  (Exp : Exp (e) -> Exp ()
       [(begin ,[e]) e]))

(module+ test
  (test-equal? "wrap-multi-exp-bodies/remove-extraneous-begins"
   (unparse-csa/single-exp-bodies
    (remove-extraneous-begins
     (wrap-multi-exp-bodies
      (with-output-language (csa/wrapped-calls Prog)
        `(program (receptionists) (externals)
          (define-function (f)
                  (case x
                    [(A) 1 2]
                    [(B) 7])
                  (let () 3 4))
          (let-actors ([a (let* () 5 6)]) a))))))
   `(program (receptionists) (externals)
     (define-function (f)
             (begin
               (case x
                 [(A) (begin 1 2)]
                 [(B) 7])
               (let () (begin 3 4))))
     (let-actors ([a (let* () (begin 5 6))]) a))))

;; ---------------------------------------------------------------------------------------------------
;; for -> for/fold

(define-language csa/desugared-for
  (extends csa/single-exp-bodies)
  (Exp (e)
       (- (for ([x1 e1]) e2))))

(define-parser parse-csa/desugared-for csa/desugared-for)

(define-pass desugar-for : csa/single-exp-bodies (P) -> csa/desugared-for ()
  (Exp : Exp (e) -> Exp ()
       [(for ([,x1 ,[e1]]) ,[e2])
        `(for/fold ([,(gensym 'for-var) 0]) ([,x1 ,e1])
           (begin ,e2 0))]))

(module+ test
  (require (prefix-in redex: redex/reduction-semantics))
  (redex:define-language L)

  (define desugared-code (unparse-csa/desugared-for
                 (desugar-for
                  (with-output-language (csa/single-exp-bodies Prog)
                    `(program (receptionists) (externals) (let-actors ([a (for ([i (list 1 2 3)]) i)]) a))))))
  (test-not-false "desugar for"
   (redex:redex-match L
                      (program (receptionists) (externals) (let-actors ([a (for/fold ([variable-not-otherwise-mentioned 0]) ([i (list 1 2 3)]) (begin i 0))]) a))
                      desugared-code)))

;; ---------------------------------------------------------------------------------------------------
;; Desugar cond

(define-language csa/desugared-cond
  (extends csa/desugared-for)
  (Exp (e)
       (- (cond [e1 e2] ... [else-kw e3]))))

(define-parser parse-csa/desugared-cond csa/desugared-cond)

(define-pass desugar-cond : csa/desugared-for (P) -> csa/desugared-cond ()
  (Exp : Exp (e) -> Exp ()
       [(cond [,else-kw ,[e]]) e]
       [(cond [,[e1] ,[e2]] [,e3 ,e4] ... [,else-kw ,e5])
        `(if ,e1
             ,e2
             ,(Exp (with-output-language (csa/desugared-for Exp)
                     `(cond [,e3 ,e4] ... [,else-kw ,e5]))))]))

(module+ test
  (test-equal? "desugar cond"
   (unparse-csa/desugared-cond
    (desugar-cond
     (with-output-language (csa/desugared-for Prog)
       `(program (receptionists) (externals)
         (let-actors
          ([a (cond
                [(< a b) 0]
                [(< b c) 1]
                [else 2])])
          a)))))
   `(program (receptionists) (externals) (let-actors ([a (if (< a b) 0 (if (< b c) 1 2))]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Desugar if

(define-language csa/desugared-if
  (extends csa/desugared-cond)
  (Exp (e)
       (- (if e1 e2 e3))))

(define-parser parse-csa/desugared-if csa/desugared-if)

(define-pass desugar-if : csa/desugared-cond (P) -> csa/desugared-if ()
  (Exp : Exp (e) -> Exp ()
       [(if ,[e1] ,[e2] ,[e3])
        `(case ,e1
           [(True) ,e2]
           [(False) ,e3])]))

(module+ test
  (test-equal? "desugar if"
   (unparse-csa/desugared-if
    (desugar-if
     (with-output-language (csa/desugared-cond Prog)
       `(program (receptionists) (externals) (let-actors ([a (if (< a b) 1 0)]) a)))))
   `(program (receptionists) (externals) (let-actors ([a (case (< a b) [(True) 1] [(False) 0])]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Desugar let*

(define-language csa/desugared-let*
  (extends csa/desugared-if)
  (Exp (e)
       (- (let* ([x e] ...) e2))))

(define-parser parse-csa/desugared-let* csa/desugared-let*)

(define-pass desugar-let* : csa/desugared-if (P) -> csa/desugared-let* ()
  (Exp : Exp (e) -> Exp ()
       [(let* ([,x ,[e]] [,x* ,e*] ...) ,body)
        `(let ([,x ,e])
           ,(Exp (with-output-language (csa/desugared-if Exp)
                   `(let* ([,x* ,e*] ...) ,body))))]
       [(let* () ,[e]) e]))

(module+ test
  (test-equal? "desugar let*"
    (unparse-csa/desugared-let*
     (desugar-let*
      (parse-csa/desugared-if
        `(program (receptionists) (externals)
                  (let-actors ([a (let* ([a 1]
                                         [b (+ a 2)]
                                         [c (+ a b)])
                                    (+ c 5))])
                              a)))))
    `(program (receptionists) (externals)
              (let-actors ([a (let ([a 1])
                                (let ([b (+ a 2)])
                                  (let ([c (+ a b)])
                                    (+ c 5))))])
                          a))))

;; ---------------------------------------------------------------------------------------------------
;; Variant desugaring

(define-language csa/desugared-variants
  (extends csa/desugared-let*)
  (ProgItem (PI)
            (- (define-variant T (V [x τ] ...) ...))))

(define-parser parse-csa/desugared-variants csa/desugared-variants)

(define-pass desugar-variants : csa/desugared-let* (P) -> csa/desugared-variants ()
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-variant ,T (,V [,x ,[τ]] ...) ...)
          ,PI ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (define constructor-defs
           (map
            (lambda (name field-list types)
              (with-output-language (csa/desugared-variants ProgItem)
                `(define-function (,name [,field-list ,types] ...) (variant ,name ,field-list ...))))
            V x τ))
         (Prog (with-output-language (csa/desugared-let* Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add
                       (append
                        constructor-defs
                        (list
                        (with-output-language (csa/desugared-variants ProgItem)
                          `(define-type ,T (Variant [,V ,τ ...] ...)))))))]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                      ,[PI1] ,PI* ...
                      (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/desugared-let* Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,let-actors-kw ([,x3 ,[e3]] ...) ,x4 ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                       ,items-to-add ...
                       (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))])
  (Prog P null))

(module+ test
  (test-equal? "desugar variants"
   (unparse-csa/desugared-variants
    (desugar-variants
     (with-output-language (csa/desugared-let* Prog)
       `(program (receptionists) (externals)
         (define-variant List (Null) (Cons [element Nat] [list List]))
         (let-actors
          ([a (case (app Null)
                [(Null) 0]
                [(Cons element rest) element])])
          a)))))
   `(program (receptionists) (externals)
     (define-function (Null) (variant Null))
     (define-function (Cons [element Nat] [list List]) (variant Cons element list))
     (define-type List (Variant (Null) (Cons Nat List)))
     (let-actors ([a (case (app Null)
                       [(Null) 0]
                       [(Cons element rest) element])])
                 a))))

;; ---------------------------------------------------------------------------------------------------
;; Record type inlining

(define-language csa/inlined-records
  (extends csa/desugared-variants)
  (ProgItem (PI)
            (- (define-record T [x τ] ...))))

(define-parser parse-csa/inlined-records csa/inlined-records)

(define-pass inline-records : csa/desugared-variants (P) -> csa/inlined-records ()
  ;; REFACTOR: I could really use something like syntax-parse's splicing forms so I could look at
  ;; items individually and splice them back in
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-record ,T [,x ,[τ]] ...)
          ,PI ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/desugared-variants Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add
                       (list
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-type ,T (Record [,x ,τ] ...)))
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-function (,T [,x ,τ] ...) (record [,x ,x] ...))))))]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw  [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/desugared-variants Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,let-actors-kw ([,x3 ,[e3]] ...) ,x4 ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))])
  (Prog P null))

(module+ test
  (test-equal? "inline records"
   (unparse-csa/inlined-records
    (inline-records
     (with-output-language (csa/desugared-variants Prog)
       `(program (receptionists) (externals)
         (define-record A [x Nat] [y Nat])
         (define-record B [z A])
         (let-actors ([a (app B (app A 5 4))]) a)))))

   `(program (receptionists) (externals)
     (define-type A (Record [x Nat] [y Nat]))
     (define-function (A [x Nat] [y Nat]) (record [x x] [y y]))
     (define-type B (Record [z A]))
     (define-function (B [z A]) (record [z z]))
     (let-actors ([a (app B (app A 5 4))]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Types

(define-language csa/inlined-types
  (extends csa/inlined-records)
  (ProgItem (PI)
            (- (define-type T τ))))

(define-parser parse-csa/inlined-types csa/inlined-types)

(define-pass inline-type-aliases : csa/inlined-records (P) -> csa/inlined-types ()
  ;; REFACTOR: figure out the best way to do this kind of fold, because the restriction that the
  ;; return type always has to be the same languae prevents me from doing a general Subst processor
  ;; like I want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define aliases-so-far (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-type ,T ,[τ])
          ,PI ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (hash-set! aliases-so-far T τ)
         (Prog (with-output-language (csa/inlined-records Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/inlined-records Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,let-actors-kw ([,x3 ,[e3]] ...) ,x4 ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))])
  (Type : Type (τ) -> Type ()
        [,T
         ;; Return this type by default, because it might be the name of a recursive type
         (hash-ref aliases-so-far T T)])
  (Prog P null))

(module+ test
  (test-equal? "inline types"
   (unparse-csa/inlined-types
    (inline-type-aliases
     (parse-csa/inlined-records
      `(program (receptionists) (externals)
        (define-type MyT Nat)
        (define-actor MyT (A) ()
          (goto S1))
        (let-actors ([a (spawn 1 A)]) a)))))
   `(program (receptionists) (externals)
     (define-actor Nat (A) ()
             (goto S1))
     (let-actors ([a (spawn 1 A)]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Program Functions

(define-language csa/inlined-program-definitions
  (extends csa/inlined-types)
  (ProgItem (PI)
            (- fd cd)))

(define-parser parse-csa/inlined-program-definitions csa/inlined-program-definitions)

(define-pass inline-program-definitions : csa/inlined-types (P) -> csa/inlined-program-definitions ()
  ;; REFACTOR: figure out the best way to do this kind of fold, because the restriction that the
  ;; return type always has to be the same languae prevents me from doing a general Subst processor
  ;; like I want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define func-defs (make-hash))
    (define const-defs (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-function (,f [,x ,τ] ...) ,[e])
          ,PI ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (hash-set! func-defs f (func-record x e))
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-constant ,x ,[e])
          ,PI ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (hash-set! const-defs x e)
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,let-actors-kw ([,x3 ,[e3]] ...) ,x4 ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))])
  (Exp : Exp (e) -> Exp ()
       [(app ,f ,[e*] ...)
        (match (hash-ref func-defs f #f)
          [#f
           `(app ,f ,e* ...)]
          [(func-record formals body)
           `(let ([,formals ,e*] ...) ,body)])]
       [,x
        (match (hash-ref const-defs x #f)
          [#f x]
          [e e])])

  (Prog P null))

(module+ test
  (test-equal? "inline program defs 1"
   (unparse-csa/inlined-program-definitions
    (inline-program-definitions
     (parse-csa/inlined-types
      `(program (receptionists) (externals)
        (define-function (double [x Nat]) (+ x x))
        (define-constant c 5)
        (let-actors ([a (app double c)]) a)))))
   `(program (receptionists) (externals) (let-actors ([a (let ([x 5]) (+ x x))]) a)))

  (test-equal? "inline program defs 2"
   (unparse-csa/inlined-program-definitions
    (inline-program-definitions
     (parse-csa/inlined-types
      `(program (receptionists) (externals)
        (define-function (double [x Nat]) (+ x x))
        (define-function (quadruple [x Nat]) (app double (app double x)))
        (let-actors ([a (app quadruple 5)]) a)))))
   `(program (receptionists) (externals)
      (let-actors ([a (let ([x 5])
                        (let ([x (let ([x x]) (+ x x))])
                          (+ x x)))])
                  a)))

  (test-equal? "inline program defs 3"
   (unparse-csa/inlined-program-definitions
    (inline-program-definitions
     (parse-csa/inlined-types
      `(program (receptionists) (externals)
        (define-actor Nat (A)
          ((define-function (double [x Nat]) (+ x x))
           (define-function (quadruple [x Nat]) (app double (app double x))))
          (app quadruple 5))
        (let-actors ([a (spawn 1 A)]) a)))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
             ((define-function (double [x Nat]) (+ x x))
              (define-function (quadruple [x Nat]) (app double (app double x))))
             (app quadruple 5))
     (let-actors ([a (spawn 1 A)]) a))))

;; ---------------------------------------------------------------------------------------------------
;; Actor func/const definition inlining

(define-language csa/inlined-actor-definitions
  (extends csa/inlined-program-definitions)
  (ActorDef (ad)
            (- (define-actor τ (a [x τ2] ...) (AI ...) e S ...))
            (+ (define-actor τ (a [x τ2] ...)          e S ...)))
  (Exp (e) (- (app f e ...))))

(define-parser parse-csa/inlined-actor-definitions csa/inlined-actor-definitions)

(struct func-record (formals body))

(define-pass inline-actor-definitions : csa/inlined-program-definitions (P) -> csa/inlined-actor-definitions ()
  (definitions
    (define funcs (make-hash))
    (define consts (make-hash)))
  (ActorDef : ActorDef (d) -> ActorDef ()
    [(define-actor ,τ (,a [,x1 ,τ1] ...) ((define-function (,f [,x2 ,τ2] ...) ,[body]) ,AI* ...) ,e ,S ...)
     (hash-set! funcs f (func-record x2 body))
     (ActorDef
      (with-output-language (csa/inlined-program-definitions ActorDef)
        `(define-actor ,τ (,a [,x1 ,τ1] ...) (,AI* ...) ,e ,S ...)))]
    [(define-actor ,τ (,a [,x1 ,τ1] ...) ((define-constant ,x ,[e]) ,AI* ...) ,body ,S ...)
     (hash-set! consts x e)
     (ActorDef
      (with-output-language (csa/inlined-program-definitions ActorDef)
        `(define-actor ,τ (,a [,x1 ,τ1] ...) (,AI* ...) ,body ,S ...)))]
    [(define-actor ,[τ] (,a [,x ,[τ1]] ...) () ,[e] ,[S] ...)
     (define result `(define-actor ,τ (,a [,x ,τ1] ...) ,e ,S ...))
     (hash-clear! funcs)
     (hash-clear! consts)
     result])
  (Exp : Exp (e) -> Exp ()
       [(app ,f ,[e*] ...)
        (match-define (func-record formals body)
          (hash-ref funcs f (lambda () (error 'inline-actor-definitions "could not find match for function in call ~s\n" e))))
        `(let ([,formals ,e*] ...) ,body)]
       [,x
        (match (hash-ref consts x #f)
          [#f x]
          [e e])]))

(module+ test
  (test-equal? "inline actor defs 1"
   (unparse-csa/inlined-actor-definitions
    (inline-actor-definitions
     (with-output-language (csa/inlined-program-definitions Prog)
       `(program (receptionists) (externals)
         (define-actor Nat (A)
                 ((define-constant z 2)
                  (define-constant w 4)
                  (define-function (foo [x Nat]) (+ x z))
                  (define-function (bar [x Nat] [y Nat]) (- x y)))

                 (app foo (app bar 3 w)))
         (let-actors ([a (spawn 1 A)]) a)))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
             (let ([x
                    (let ([x 3]
                          [y 4])
                      (- x y))])
               (+ x 2)))
     (let-actors ([a (spawn 1 A)]) a)))

  (test-equal? "inline actor defs 2"
   (unparse-csa/inlined-actor-definitions
    (inline-actor-definitions
     (parse-csa/inlined-program-definitions
      `(program (receptionists) (externals)
        (define-actor Nat (A)
                ((define-function (double [x Nat]) (+ x x))
                 (define-function (quadruple [x Nat]) (app double (app double x))))
                (app quadruple 5))
        (let-actors ([a (spawn 1 A)]) a)))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
       (let ([x 5])
         (let ([x (let ([x x]) (+ x x))]) (+ x x))))
     (let-actors ([a (spawn 1 A)]) a)))

  (test-exn "inline actor defs: don't reuse functions"
    (lambda (exn) #t)
    (lambda ()
      (unparse-csa/inlined-actor-definitions
       (inline-actor-definitions
        (parse-csa/inlined-program-definitions
         `(program (receptionists) (externals)
                   (define-actor Nat (A)
                     ((define-function (double [x Nat]) (+ x x)))
                     (app double 5))
                   (define-actor Nat (B)
                     ()
                     (app double 5))
                   (let-actors ([a (spawn 1 A)]
                                [b (spawn 2 B)]))))))))

  (test-equal? "inline actor defs: don't reuse constants"
   (unparse-csa/inlined-actor-definitions
    (inline-actor-definitions
     (parse-csa/inlined-program-definitions
      `(program (receptionists) (externals)
        (define-actor Nat (A)
          ((define-constant Y 5))
          Y)
        (define-actor Nat (B)
          ()
          Y)
        (let-actors ([a (spawn 1 A)]
                     [b (spawn 2 B)]))))))
   `(program (receptionists) (externals)
     (define-actor Nat (A) 5)
     (define-actor Nat (B) Y)
     (let-actors ([a (spawn 1 A)] [b (spawn 2 B)])))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Actors

(define-language csa/inlined-actors
  (extends csa/inlined-actor-definitions)
  (Prog (P)
    (- (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                   PI ...
                   (let-actors-kw ([x3 e] ...) x4 ...)))
    (+ (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                   (let-actors-kw ([x3 e] ...) x4 ...))))
  (ProgItem (P)
            (- ad))
  (Exp (e)
       (- (spawn l a e ...))
       (+ (spawn l τ e S ...))))

(struct actor-record (type formals formal-types body state-defs))

(define-pass inline-actors : csa/inlined-actor-definitions (P) -> csa/inlined-actors ()
  (Prog : Prog (P defs-so-far) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-actor ,[τ0] (,a [,x ,[τ]] ...)  ,[Exp : e0 defs-so-far -> e] ,[StateDef : S0 defs-so-far -> S] ...)
          ,PI* ...
          (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...))
         (Prog (with-output-language (csa/inlined-actor-definitions Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,let-actors-kw ([,x3 ,e3] ...) ,x4 ...)))
               (hash-set defs-so-far a (actor-record τ0 x τ e S)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,let-actors-kw ([,x3 ,[Exp : e0 defs-so-far -> e]] ...) ,x4 ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                       (,let-actors-kw ([,x3 ,e] ...) ,x4 ...))])
  (StateDef : StateDef (S defs-so-far) -> StateDef ()
    [(define-state (,s [,x ,[τ]] ...) ,x2 ,[Exp : e0 defs-so-far -> e])
     `(define-state (,s [,x ,τ] ...) ,x2 ,e)]
    [(define-state/timeout (,s [,x ,[τ]] ...) ,x2 ,[Exp : e0 defs-so-far -> e]
       ,[TimeoutClause : tc0 defs-so-far -> tc])
     `(define-state/timeout (,s [,x ,τ] ...) ,x2 ,e ,tc)])
  (TimeoutClause : TimeoutClause (tc defs-so-far) -> TimeoutClause ()
                 [(timeout ,[Exp : e1 defs-so-far -> e2]
                           ,[Exp : e3 defs-so-far -> e4])
                  `(timeout ,e2 ,e4)])
  (Exp : Exp (e defs-so-far) -> Exp ()
       [(spawn ,l ,a ,[Exp : e0 defs-so-far -> e] ...)
        (match (hash-ref defs-so-far a #f)
          [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
          [(actor-record type formals formal-types body state-defs)
           ;; `(spawn (goto S-Bad1))
           `(let ([,formals ,e] ...) (spawn ,l ,type ,body ,state-defs ...))
           ])])
  ;; BUG: (?): shouldn't this be the default init statement?
  (Prog P (hash)))

(module+ test
  (test-equal? "inline actors 1"
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-actor-definitions Prog)
       `(program (receptionists) (externals)
         (define-actor Nat (A [x Nat])
                 (goto S1)
                 (define-state (S1) m
                   (goto S1)))
         (let-actors ([a (spawn 1 A 5)]) a)))))
   `(program (receptionists) (externals)
             (let-actors ([a (let ([x 5])
                               (spawn
                                1
                                Nat
                                (goto S1)
                                (define-state (S1) m (goto S1))))]) a)))

  (test-equal? "inline actors 2"
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-actor-definitions Prog)
       `(program (receptionists) (externals)
         (define-actor Nat (A [x Nat])
                 (goto S1)
                 (define-state (S1) m
                   (goto S1)))
         (define-actor Nat (B [y Nat])
           (goto S2)
           (define-state (S2) m
             (begin
               (spawn 1 A 3)
               (goto S2))))
         (let-actors ([a (spawn 2 B 5)]) a)))))
   `(program (receptionists) (externals)
             (let-actors ([a (let ([y 5])
                               (spawn
                                2
                                Nat
                                (goto S2)
                                (define-state (S2) m
                                  (begin
                                    (let ([x 3])
                                      (spawn
                                       1
                                       Nat
                                       (goto S1)
                                       (define-state (S1) m
                                         (goto S1))))
                                    (goto S2)))))])
                         a)))

  (test-equal? "inline actors with externals"
    (unparse-csa/inlined-actors
     (inline-actors
      (with-output-language (csa/inlined-actor-definitions Prog)
        `(program (receptionists [rec1 (Record)]) (externals [ext1 Nat]) (let-actors ())))))
    `(program (receptionists [rec1 (Record)]) (externals [ext1 Nat]) (let-actors ()))))

;; ---------------------------------------------------------------------------------------------------
;; Fixed timeout syntax

;; Nanopass needs keywords at the beginning of each clause, so we do a non-Nanopass transform here to
;; fix the timeout syntax. Also separated define-state into two forms to avoid some sort of parsing
;; ambiguity error that I can't otherwise seem to fix.

(define (fix-timeout-syntax t)
  (match t
    [`(define-state/timeout ,exps ...)
     `(define-state ,@(map fix-timeout-syntax exps))]
    [`(timeout ,exp1 ,exps ...)
     `([timeout ,(fix-timeout-syntax exp1)] ,@(map fix-timeout-syntax exps))]
    [(list exps ...)
     (map fix-timeout-syntax exps)]
    [_ t]))

;; ---------------------------------------------------------------------------------------------------

(define-parser parse-actor-def-csa/surface csa/surface)

(define (valid-program? term)
  (with-handlers ([(lambda (ex) #t) (lambda (ex) #f)])
    (parse-actor-def-csa/surface term)
    #t))

(module+ test
  (test-false "Invalid program" (valid-program? '(foobar)))
  (test-true "Valid program" (valid-program? '(program (receptionists) (externals) (let-actors ())))))

(define/contract (desugar program)
  (-> valid-program? any/c)

  (define pass
    (compose
     fix-timeout-syntax
     unparse-csa/inlined-actors
     inline-actors
     inline-actor-definitions
     inline-program-definitions
     inline-type-aliases
     inline-records
     desugar-variants
     desugar-let*
     desugar-if
     desugar-cond
     desugar-for
     remove-extraneous-begins
     wrap-multi-exp-bodies
     wrap-function-calls
     parse-actor-def-csa/surface))
  (pass program))
