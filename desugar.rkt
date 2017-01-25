 #lang racket

;; Nanopass-based desugarer for the bigger language (desugars down to CSA)

;; TODO: report that it would be nice to have "input-language" as a variable for whatever language a
;; pass takes as input, rather than manually typing it each time (make it a "parameter", so it follows
;; dynamic scope?)

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

(define (ActorsKeyword? x)
  (equal? x 'actors))

(define (Location? x)
  #t)

(define-language csa/surface
  (terminals
   (number (n))
   (boolean (b))
   (name (x f a s T V))
   (string (string))
   (PrimitiveType (pτ))
   ;; TODO: figure out how to get rid of this
   (ProgramKeyword (program-kw))
   (ElseKeyword (else-kw))
   (ReceptionistsKeyword (receptionists-kw))
   (ExternalsKeyword (externals-kw))
   (ActorsKeyword (actors-kw))
   (Location (l)))
  (Prog (P)
        (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                    PI ...
                    ;; NOTE: e should be a spawn expression
                    (actors-kw [x3 e] ...)))
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
            (define-state (s [x τ] ...) (x2) e1 e* ...)
            (define-state/timeout (s [x τ] ...) (x2) e1 e* ... tc))
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
       ;; TODO: have Nanopass compute the line number for each spawn
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
       ;; TODO: find a way to generalize these to primops (ideal solution requires "tagless" fix in
       ;; Nanopass)
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
       (ceiling e)
       (list e ...)
       (cons e1 e2)
       (list-as-variant e)
       (list-ref e1 e2)
       (remove e1 e2)
       (length e)
       (vector e ...)
       (vector-length e)
       (vector-ref e1 e2)
       (vector-take e1 e2)
       (vector-drop e1 e2)
       (vector-copy e1 e2 e3)
       (vector-append e1 e2)
       (hash [e1 e2] ...)
       (hash-ref e1 e2)
       (hash-keys e1)
       (hash-values e1)
       (hash-set e1 e2 e3)
       (hash-remove e1 e2)
       (hash-has-key? e1 e2)
       (hash-empty? e1)
       (sort-numbers-descending e)
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
            (define-constant x e)) ; TODO: should really only be literals
  (Type (τ)
        pτ
        (minfixpt T τ)
        (Addr τ)
        (Record [x τ] ...)
        (Union [V τ ...] ...)
        (Listof τ)
        (Vectorof τ)
        (Hash τ1 τ2)
        T)
  (entry Prog))

;; TODO: how does Nanopass resolve ambiguity?

;; TODO: put all the nominal stuff (at least program-level) into just one pass: it's basically all the
;; same, and would probably save boilerplate

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
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (test-equal? "Wrapped calls"
    (unparse-csa/wrapped-calls
     (wrap-function-calls
      (with-output-language (csa/surface Prog)
        `(program (receptionists) (externals) (actors [a (f (g 1) 2)])))))
    `(program (receptionists) (externals) (actors [a (app f (app g 1) 2)]))))

;; ---------------------------------------------------------------------------------------------------
;; Multi-body shrinking

(define-language csa/single-exp-bodies
  (extends csa/wrapped-calls)
  (StateDef (S)
            (- (define-state (s [x τ] ...) (x2) e1 e* ...)
               (define-state/timeout (s [x τ] ...) (x2) e1 e* ... tc))
            (+ (define-state (s [x τ] ...) (x2) e)
               (define-state/timeout (s [x τ] ...) (x2) e1 tc)))
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
            [(define-state (,s [,x ,[τ]] ...) (,x2) ,[e1] ,[e*] ...)
             `(define-state (,s [,x ,τ] ...) (,x2) (begin ,e1 ,e* ...))]
            [(define-state/timeout (,s [,x ,[τ]] ...) (,x2) ,[e1] ,[e*] ... ,[tc])
             `(define-state/timeout (,s [,x ,τ] ...) (,x2) (begin ,e1 ,e* ...) ,tc)])
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
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
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
          (actors [a (let* () 5 6)]))))))
   `(program (receptionists) (externals)
     (define-function (f)
             (begin
               (case x
                 [(A) (begin 1 2)]
                 [(B) 7])
               (let () (begin 3 4))))
     (actors [a (let* () (begin 5 6))]))))

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

  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (define desugared-code (unparse-csa/desugared-for
                 (desugar-for
                  (with-output-language (csa/single-exp-bodies Prog)
                    `(program (receptionists) (externals) (actors [a (for ([i (list 1 2 3)]) i)]))))))
  (test-not-false "desugar for"
   (redex:redex-match L
                      (program (receptionists) (externals) (actors [a (for/fold ([variable-not-otherwise-mentioned 0]) ([i (list 1 2 3)]) (begin i 0))]))
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
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (test-equal? "desugar cond"
   (unparse-csa/desugared-cond
    (desugar-cond
     (with-output-language (csa/desugared-for Prog)
       `(program (receptionists) (externals)
         (actors
          [a (cond
               [(< a b) 0]
               [(< b c) 1]
               [else 2])])))))
   `(program (receptionists) (externals) (actors [a (if (< a b) 0 (if (< b c) 1 2))]))))

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
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (test-equal? "desugar if"
   (unparse-csa/desugared-if
    (desugar-if
     (with-output-language (csa/desugared-cond Prog)
       `(program (receptionists) (externals) (actors [a (if (< a b) 1 0)])))))
   `(program (receptionists) (externals) (actors [a (case (< a b) [(True) 1] [(False) 0])]))))

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
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (test-equal? "desugar let*"
   (unparse-csa/desugared-let*
    (desugar-let*
     (parse-csa/desugared-if
      `(program (receptionists) (externals)
        (actors [a (let* ([a 1]
                             [b (+ a 2)]
                             [c (+ a b)])
                        (+ c 5))])))))
   `(program (receptionists) (externals)
     (actors [a (let ([a 1])
                     (let ([b (+ a 2)])
                       (let ([c (+ a b)])
                         (+ c 5))))]))))

;; ---------------------------------------------------------------------------------------------------
;; Variant desugaring

(define-language csa/desugared-variants
  (extends csa/desugared-let*)
  (ProgItem (PI)
            (- (define-variant T (V [x τ] ...) ...))))

(define-parser parse-csa/desugared-variants csa/desugared-variants)

;; TODO: consider leaving the multi-arity variants in
(define-pass desugar-variants : csa/desugared-let* (P) -> csa/desugared-variants ()
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-variant ,T (,V [,x ,[τ]] ...) ...)
          ,PI ...
          (,actors-kw [,x3 ,e3] ...))
         (define constructor-defs
           (map
            (lambda (name field-list types)
              (with-output-language (csa/desugared-variants ProgItem)
                ;; TODO: field names must be different...
                `(define-function (,name [,field-list ,types] ...) (variant ,name ,field-list ...))))
            V x τ))
         (Prog (with-output-language (csa/desugared-let* Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add
                       (append
                        constructor-defs
                        (list
                        (with-output-language (csa/desugared-variants ProgItem)
                          `(define-type ,T (Union [,V ,τ ...] ...)))))))]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                      ,[PI1] ,PI* ...
                      (,actors-kw [,x3 ,e3] ...))
         (Prog (with-output-language (csa/desugared-let* Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
                      (,actors-kw [,x3 ,[e3]] ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                       ,items-to-add ...
                       (,actors-kw [,x3 ,e3] ...))])
  (Prog P null))

(module+ test
  ;; TODO: write an alpha-equivalence predicate, or reuse one from Redex
  (test-equal? "desugar variants"
   (unparse-csa/desugared-variants
    (desugar-variants
     (with-output-language (csa/desugared-let* Prog)
       `(program (receptionists) (externals)
         (define-variant List (Null) (Cons [element Nat] [list List]))
         (actors
          [a (case (app Null)
               [(Null) 0]
               [(Cons element rest) element])])))))
   `(program (receptionists) (externals)
     (define-function (Null) (variant Null))
     (define-function (Cons [element Nat] [list List]) (variant Cons element list))
     (define-type List (Union (Null) (Cons Nat List)))
     (actors [a (case (app Null)
                     [(Null) 0]
                     [(Cons element rest) element])]))))

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
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-record ,T [,x ,[τ]] ...)
          ,PI ...
          (,actors-kw [,x3 ,e3] ...))
         ;; TODO: would be nice if there were a shortcut syntax for saying "create something of the
         ;; source language type
         (Prog (with-output-language (csa/desugared-variants Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add
                       (list
                        ;; TODO: figure out why I need with-output-language here (maybe b/c I'm not
                        ;; parsing the entry point? or the entry point of this processor?
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-type ,T (Record [,x ,τ] ...)))
                        ;; TODO: figure out why I need with-output-language here
                        (with-output-language (csa/inlined-records ProgItem)
                          `(define-function (,T [,x ,τ] ...) (record [,x ,x] ...))))))]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw  [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,actors-kw [,x3 ,e3] ...))
         (Prog (with-output-language (csa/desugared-variants Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
          (,actors-kw [,x3 ,[e3]] ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,actors-kw [,x3 ,e3] ...))])
  (Prog P null))

(module+ test
  (test-equal? "inline records"
   (unparse-csa/inlined-records
    (inline-records
     (with-output-language (csa/desugared-variants Prog)
       `(program (receptionists) (externals)
         (define-record A [x Nat] [y Nat])
         (define-record B [z A])
         (actors [a (app B (app A 5 4))])))))

   `(program (receptionists) (externals)
     (define-type A (Record [x Nat] [y Nat]))
     (define-function (A [x Nat] [y Nat]) (record [x x] [y y]))
     (define-type B (Record [z A]))
     (define-function (B [z A]) (record [z z]))
     (actors [a (app B (app A 5 4))]))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Types

(define-language csa/inlined-types
  (extends csa/inlined-records)
  (ProgItem (PI)
            (- (define-type T τ))))

(define-parser parse-csa/inlined-types csa/inlined-types)

(define-pass inline-type-aliases : csa/inlined-records (P) -> csa/inlined-types ()
  ;; TODO: figure out the best way to do this kind of fold, because the restriction that the return
  ;; type always has to be the same languae prevents me from doing a general Subst processor like I
  ;; want to (but perhaps that's inefficient anyway, since it requires many passes)
  (definitions
    (define aliases-so-far (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-type ,T ,[τ])
          ,PI ...
          (,actors-kw [,x3 ,e3] ...))
         ;; TODO: do something more defensive for hash overwrites
         (hash-set! aliases-so-far T τ)
         (Prog (with-output-language (csa/inlined-records Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,actors-kw [,x3 ,e3] ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,actors-kw [,x3 ,e3] ...))
         (Prog (with-output-language (csa/inlined-records Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
          (,actors-kw [,x3 ,[e3]] ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,actors-kw [,x3 ,e3] ...))])
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
        (actors [a (spawn 1 A)])))))
   `(program (receptionists) (externals)
     (define-actor Nat (A) ()
             (goto S1))
     (actors [a (spawn 1 A)]))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Program Functions

(define-language csa/inlined-program-definitions
  (extends csa/inlined-types)
  (ProgItem (PI)
            (- fd cd)))

(define-parser parse-csa/inlined-program-definitions csa/inlined-program-definitions)

(define-pass inline-program-definitions : csa/inlined-types (P) -> csa/inlined-program-definitions ()
  ;; TODO: figure out the best way to do this kind of fold, because the restriction that the return
  ;; type always has to be the same languae prevents me from doing a general Subst processor like I
  ;; want to (but perhaps that's inefficient anyway, since it requires many passes)
  ;;
  ;; TODO: Figure out an easy way to preserve hygiene, since now I should do proper substitution
  (definitions
    (define func-defs (make-hash))
    (define const-defs (make-hash)))
  (Prog : Prog (P items-to-add) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-function (,f [,x ,τ] ...) ,[e])
          ,PI ...
          (,actors-kw [,x3 ,e3] ...))
         (hash-set! func-defs f (func-record x e))
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,actors-kw [,x3 ,e3] ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-constant ,x ,[e])
          ,PI ...
          (,actors-kw [,x3 ,e3] ...))
         (hash-set! const-defs x e)
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI ...
                   (,actors-kw [,x3 ,e3] ...)))
               items-to-add)]
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          ,[PI1] ,PI* ...
          (,actors-kw [,x3 ,e3] ...))
         (Prog (with-output-language (csa/inlined-types Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,actors-kw [,x3 ,e3] ...)))
               (append items-to-add (list PI1)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
          (,actors-kw [,x3 ,[e3]] ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           ,items-to-add ...
           (,actors-kw [,x3 ,e3] ...))])
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
        (actors [a (app double c)])))))
   `(program (receptionists) (externals) (actors [a (let ([x 5]) (+ x x))])))

  (test-equal? "inline program defs 2"
   (unparse-csa/inlined-program-definitions
    (inline-program-definitions
     (parse-csa/inlined-types
      `(program (receptionists) (externals)
        (define-function (double [x Nat]) (+ x x))
        (define-function (quadruple [x Nat]) (app double (app double x)))
        (actors [a (app quadruple 5)])))))
   `(program (receptionists) (externals)
     (actors [a
                   (let ([x 5])
                     (let ([x (let ([x x]) (+ x x))]) (+ x x)))])))

  (test-equal? "inline program defs 3"
   (unparse-csa/inlined-program-definitions
    (inline-program-definitions
     (parse-csa/inlined-types
      `(program (receptionists) (externals)
        (define-actor Nat (A)
          ((define-function (double [x Nat]) (+ x x))
           (define-function (quadruple [x Nat]) (app double (app double x))))
          (app quadruple 5))
        (actors [a (spawn 1 A)])))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
             ((define-function (double [x Nat]) (+ x x))
              (define-function (quadruple [x Nat]) (app double (app double x))))
             (app quadruple 5))
     (actors [a (spawn 1 A)]))))

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
    ;; TODO: clear this list every time we start a new actor
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
     `(define-actor ,τ (,a [,x ,τ1] ...) ,e ,S ...)])
  (Exp : Exp (e) -> Exp ()
       ;; TODO: see tmp/expected-meta for why this breaks
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
         (actors [a (spawn 1 A)])))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
             (let ([x
                    (let ([x 3]
                          [y 4])
                      (- x y))])
               (+ x 2)))
     (actors [a (spawn 1 A)])))

  (test-equal? "inline actor defs 2"
   (unparse-csa/inlined-actor-definitions
    (inline-actor-definitions
     (parse-csa/inlined-program-definitions
      `(program (receptionists) (externals)
        (define-actor Nat (A)
                ((define-function (double [x Nat]) (+ x x))
                 (define-function (quadruple [x Nat]) (app double (app double x))))
                (app quadruple 5))
        (actors [a (spawn 1 A)])))))
   `(program (receptionists) (externals)
     (define-actor Nat (A)
       (let ([x 5])
         (let ([x (let ([x x]) (+ x x))]) (+ x x))))
     (actors [a (spawn 1 A)]))))

;; ---------------------------------------------------------------------------------------------------
;; Inlined Actors

(define-language csa/inlined-actors
  (extends csa/inlined-actor-definitions)
  (Prog (P)
    (- (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                   PI ...
                   (actors-kw [x3 e] ...)))
    (+ (program-kw (receptionists-kw [x1 τ1] ...) (externals-kw [x2 τ2] ...)
                   (actors-kw [x3 e] ...))))
  (ProgItem (P)
            (- ad))
  (Exp (e)
       (- (spawn l a e ...))
       (+ (spawn l τ e S ...))))

(struct actor-record (type formals body state-defs))

(define-pass inline-actors : csa/inlined-actor-definitions (P) -> csa/inlined-actors ()
  ;; TODO: I think the return "type" is not checked, because I've seen things get through when I had ActorDef instead of Prog
  (Prog : Prog (P defs-so-far) -> Prog ()
        [(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
          (define-actor ,[τ0] (,a [,x ,[τ]] ...)  ,[Exp : e0 defs-so-far -> e] ,[StateDef : S0 defs-so-far -> S] ...)
          ,PI* ...
          (,actors-kw [,x3 ,e3] ...))
         (Prog (with-output-language (csa/inlined-actor-definitions Prog)
                 `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
                   ,PI* ...
                   (,actors-kw [,x3 ,e3] ...)))
               ;; TODO: figure out if hash-set overwrites existing entries or not
               (hash-set defs-so-far a (actor-record τ0 x e S)))]
        [(,program-kw (,receptionists-kw [,x1 ,[τ1]] ...) (,externals-kw [,x2 ,[τ2]] ...)
          (,actors-kw [,x3 ,[Exp : e0 defs-so-far -> e]] ...))
         `(,program-kw (,receptionists-kw [,x1 ,τ1] ...) (,externals-kw [,x2 ,τ2] ...)
           (,actors-kw [,x3 ,e] ...))])
  (StateDef : StateDef (S defs-so-far) -> StateDef ()
    [(define-state (,s [,x ,[τ]] ...) (,x2) ,[Exp : e0 defs-so-far -> e])
     `(define-state (,s [,x ,τ] ...) (,x2) ,e)]
    [(define-state/timeout (,s [,x ,[τ]] ...) (,x2) ,[Exp : e0 defs-so-far -> e]
       ,[TimeoutClause : tc0 defs-so-far -> tc])
     `(define-state/timeout (,s [,x ,τ] ...) (,x2) ,e ,tc)])
  (TimeoutClause : TimeoutClause (tc defs-so-far) -> TimeoutClause ()
                 [(timeout ,[Exp : e1 defs-so-far -> e2]
                           ,[Exp : e3 defs-so-far -> e4])
                  `(timeout ,e2 ,e4)])
  (Exp : Exp (e defs-so-far) -> Exp ()
       [(spawn ,l ,a ,[Exp : e0 defs-so-far -> e] ...)
        (match (hash-ref defs-so-far a #f)
          [#f (error 'inline-actors "Could not find match for actor ~s\n" a)]
          [(actor-record type formals body state-defs)
           ;; TODO: do I need to rename variables here at all?
           ;; `(spawn (goto S-Bad1))
           `(let ([,formals ,e] ...) (spawn ,l ,type ,body ,state-defs ...))
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
       ;; (let ([x e] ...) e2)
       ;; (let* ([x e] ...) e2)

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
  (test-equal? "inline actors 1"
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-actor-definitions Prog)
       `(program (receptionists) (externals)
         (define-actor Nat (A [x Nat])
                 (goto S1)
                 (define-state (S1) (m)
                   (goto S1)))
         (actors [a (spawn 1 A 5)])))))
   `(program (receptionists) (externals)
     (actors [a (let ([x 5])
                     (spawn
                      1
                      Nat
                      (goto S1)
                      (define-state (S1) (m) (goto S1))))])))

  (test-equal? "inline actors 2"
   (unparse-csa/inlined-actors
    (inline-actors
     (with-output-language (csa/inlined-actor-definitions Prog)
       `(program (receptionists) (externals)
         (define-actor Nat (A [x Nat])
                 (goto S1)
                 (define-state (S1) (m)
                   (goto S1)))
         (define-actor Nat (B [y Nat])
           (goto S2)
           (define-state (S2) (m)
             (begin
               (spawn 1 A 3)
               (goto S2))))
         (actors [a (spawn 2 B 5)])))))
   `(program (receptionists) (externals)
     (actors [a (let ([y 5])
                     (spawn
                      2
                      Nat
                      (goto S2)
                      (define-state (S2) (m)
                        (begin
                          (let ([x 3])
                            (spawn
                             1
                             Nat
                             (goto S1)
                             (define-state (S1) (m)
                               (goto S1))))
                          (goto S2)))))])))

  (test-equal? "inline actors with externals"
    (unparse-csa/inlined-actors
     (inline-actors
      (with-output-language (csa/inlined-actor-definitions Prog)
        `(program (receptionists [rec1 (Record)]) (externals [ext1 Nat]) (actors)))))
    `(program (receptionists [rec1 (Record)]) (externals [ext1 Nat]) (actors))))

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
  (test-true "Valid program" (valid-program? '(program (receptionists) (externals) (actors)))))

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
