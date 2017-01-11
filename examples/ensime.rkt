#lang racket

;; This program mimicks the structure of the "Project" actor from ensime-server
;; (https://github.com/ensime/ensime-server), which is a program for providing developers with tools
;; such as debuggers, documentation lookup, and auto-complete suggestions when writing Java or Scala
;; code.
;;
;; My version here simply stubs out the actual implementations for each of the RPC-like calls (which
;; largely involve no communication internally), focusing on the communication topology between the
;; Project actor and its children. The Project has 5 children (actors for the doc resolver, the
;; indexer, the debugger, the Java analyzer, and the Scala analyzer), and each incoming RPC is simply
;; dispatched to the appropriate actor.
;;
;; This example shows how my conformance checker can deal with simple RPC calls even when they involve
;; messages being routed through a static topology. This is also a good example of the kind of
;; benefits gained from the widening optimization.

(define ensime-program
  (quasiquote
(program (receptionists [project ProjectActorInput]) (externals)

(define-type Boolean (Union [True] [False]))

(define-variant ConnectionInfo
  (ConnectionInfo))

(define-variant ResolveResult
  (FalseResponse)
  (StringResponse [path String]))

(define-constant docs-lookup
  (hash ["begin" "http://www.racket-lang.org/"]))

(define-type DocResolverInput
  (Union (Resolve String (Addr ResolveResult))))

(define-actor DocResolverInput
  (DocResolver)
  ()
  (goto Always)
  (define-state (Always) (m)
    (case m
      [(Resolve pair sender)
       (case (hash-ref docs-lookup pair)
         [(Nothing)
          (send sender (FalseResponse))
          (goto Always)]
         [(Just path)
          (send sender (StringResponse path))
          (goto Always)])])))

(define-variant ImportSuggestions
  (ImportSuggestions [results (Listof String)]))

(define-variant SymbolSearchResults
  (SymbolSearchResults [results (Listof String)]))

(define-type IndexerInput
  (Union
   [PublicSymbolSearchReq (Listof String) Nat (Addr ImportSuggestions)]
   [TypeCompletionsReq String Nat (Addr SymbolSearchResults)]))

(define-actor IndexerInput
  (Indexer)
  ()
  (goto Always)
  (define-state (Always) (m)
    (case m
      [(PublicSymbolSearchReq keywords max-results sender)
       (send sender (ImportSuggestions (list "foo" "bar")))
       (goto Always)]
      [(TypeCompletionsReq query max-results sender)
       (send sender (SymbolSearchResults (list query)))
       (goto Always)])))

(define-variant BooleanResponse
  (TrueResponse)
  (FalseResponse))

(define-type DebugLocation Nat)
(define-variant DebugValue
  (DebugValue [value String]))

(define-constant debug-values (hash [1 "foo"] [2 "bar"]))

(define-type DebugActorInput
  (Union
   (DebugRunReq (Addr BooleanResponse))
   (DebugStopReq (Addr BooleanResponse))
   (DebugValueReq DebugLocation (Addr (Union [DebugValue String] [FalseResponse])))))

(define-actor DebugActorInput
  (DebugActor)
  ()
  (goto Always)
  (define-state (Always) (m)
    (case m
      [(DebugRunReq sender)
       (send sender (TrueResponse))
       (goto Always)]
      [(DebugStopReq sender)
       (send sender (TrueResponse))
       (goto Always)]
      [(DebugValueReq location sender)
       (case (hash-ref debug-values location)
         [(Nothing) (send sender (FalseResponse))]
         [(Just val) (send sender (DebugValue val))])
       (goto Always)])))

; stubbing out types for File and FileLocation
(define-variant FileType (Java) (Scala))
(define-record File [type FileType] [text (Hash Nat String)])
(define-type FileLocation Nat)
(define-variant MaybeDocSigPair
  (NoDocSigPair)
  (DocSigPair [path String]))

(define-type JavaAnalyzerInput
  (Union
   [DocUriAtPointReq File FileLocation (Addr MaybeDocSigPair)]
   [CompletionsReq File Nat Nat Boolean Boolean (Addr (Listof String))]))

(define-actor JavaAnalyzerInput
  (JavaAnalyzer)
  ()
  (goto Always)
  (define-state (Always) (m)
    (case m
      [(DocUriAtPointReq file loc sender)
       (case (hash-ref (: file text) loc)
         [(Nothing) (send sender (NoDocSigPair))]
         [(Just path) (send sender (DocSigPair path))])
       (goto Always)]
      [(CompletionsReq file point max-results case-sensitive? reload? sender)
       (send sender (list "a" "b" "c"))
       (goto Always)])))

(define-variant VoidResponse
  (VoidResponse))

(define-variant RefactorType
  (InlineLocal)
  (Rename))

(define-variant RefactorResult
  (RefactorFailure [procedure-id Nat] [reason String] [status String])
  (RefactorDiffEffect [procedure-id Nat] [refactor-type RefactorType] [diff String]))

(define-type AnalyzerInput
  (Union
   [TypecheckAllReq (Addr VoidResponse)]
   [CompletionsReq File Nat Nat Boolean Boolean (Addr (Listof String))]
   [RefactorReq Nat RefactorType Boolean (Addr RefactorResult)]))

(define-actor AnalyzerInput
  (Analyzer)
  ()
  (goto Always)
  (define-state (Always) (m)
    (case m
      [(TypecheckAllReq sender)
       (send sender (VoidResponse))
       (goto Always)]
      [(CompletionsReq file point max-results case-sensitive? reload? sender)
       (send sender (list "d" "e" "f"))
       (goto Always)]
      [(RefactorReq proc-id type interactive? sender)
       (case type
         [(InlineLocal)
          (send sender
                ; a numeric comparison here causes both branches to execute in abstract interpretation
                (if (= 1 1)
                    (RefactorFailure proc-id "fail" "fail")
                    (RefactorDiffEffect proc-id type "this is the new file")))
          (goto Always)]
         [(Rename)
          (send sender
                ; a numeric comparison here causes both branches to execute in abstract interpretation
                (if (= 1 2)
                    (RefactorFailure proc-id "fail" "fail")
                    (RefactorDiffEffect proc-id type "this is the new file")))
          (goto Always)])])))

(define-variant ProjectInput
  (ConnectionInfoReq [sender (Addr ConnectionInfo)])
  (Resolve [doc-sig-pair String] [sender (Addr ResolveResult)])
  (PublicSymbolSearchReq [keywords (Listof String)]
                         [max-results Nat]
                         [sender (Addr ImportSuggestions)])
  (TypeCompletionsReq [query String] [max-results Nat] [sender (Addr SymbolSearchResults)])
  (DebugRunReq [sender (Addr BooleanResponse)])
  (DebugStopReq [sender (Addr BooleanResponse)])
  (DebugValueReq [location DebugLocation]
                 [sender (Addr (Union [DebugValue String] [FalseResponse]))])
  (DocUriAtPointReq [file File] [point FileLocation] [sender (Addr MaybeDocSigPair)])
  (CompletionsReq [file File]
                  [point FileLocation]
                  [max-results Nat]
                  [case-sensitive? Boolean]
                  [reload? Boolean]
                  [sender (Addr (Listof String))])
  (TypecheckAllReq [sender (Addr VoidResponse)])
  (RefactorReq [proc-id Nat]
               [type RefactorType]
               [interactive? Boolean]
               [sender (Addr RefactorResult)]))

(define-actor ProjectInput
  (Project [docs (Addr DocResolverInput)]
           [indexer (Addr IndexerInput)]
           [debugger (Addr DebugActorInput)]
           [javac (Addr JavaAnalyzerInput)]
           [scalac (Addr AnalyzerInput)])
  ()
  (goto AwaitingConnectionInfoReq)
  (define-state (AwaitingConnectionInfoReq) (m)
    (case m
      [(ConnectionInfoReq sender)
       (send sender (ConnectionInfo))
       (goto HandleRequests)]
      [(Resolve p s) (goto AwaitingConnectionInfoReq)]
      [(PublicSymbolSearchReq k m s) (goto AwaitingConnectionInfoReq)]
      [(TypeCompletionsReq q m s) (goto AwaitingConnectionInfoReq)]
      [(DebugRunReq s) (goto AwaitingConnectionInfoReq)]
      [(DebugStopReq s) (goto AwaitingConnectionInfoReq)]
      [(DebugValueReq l s) (goto AwaitingConnectionInfoReq)]
      [(DocUriAtPointReq f p s) (goto AwaitingConnectionInfoReq)]
      [(CompletionsReq f p m c r s) (goto AwaitingConnectionInfoReq)]
      [(TypecheckAllReq s) (goto AwaitingConnectionInfoReq)]
      [(RefactorReq p t i s) (goto AwaitingConnectionInfoReq)]))
  (define-state (HandleRequests) (m)
    (case m
      [(ConnectionInfoReq sender)
       (send sender (ConnectionInfo))
       (goto HandleRequests)]
      [(Resolve p s)
       (send docs (Resolve p s))
       (goto HandleRequests)]
      [(PublicSymbolSearchReq k m s)
       (send indexer (PublicSymbolSearchReq k m s))
       (goto HandleRequests)]
      [(TypeCompletionsReq q m s)
       (send indexer (TypeCompletionsReq q m s))
       (goto HandleRequests)]
      [(DebugRunReq s)
       (send debugger (DebugRunReq s))
       (goto HandleRequests)]
      [(DebugStopReq s)
       (send debugger (DebugStopReq s))
       (goto HandleRequests)]
      [(DebugValueReq l s)
       (send debugger (DebugValueReq l s))
       (goto HandleRequests)]
      [(DocUriAtPointReq f p s)
       (send javac (DocUriAtPointReq f p s))
       (goto HandleRequests)]
      [(CompletionsReq f p m c r s)
       (case (: f type)
         [(Java) (send javac (CompletionsReq f p m c r s))]
         [(Scala) (send scalac (CompletionsReq f p m c r s))])
       (goto HandleRequests)]
      [(TypecheckAllReq s)
       (send scalac (TypecheckAllReq s))
       (goto HandleRequests)]
      [(RefactorReq p t i s)
       (send scalac (RefactorReq p t i s))
       (goto HandleRequests)])))

(actors [docs (spawn docs-loc DocResolver)]
        [indexer (spawn indexer-loc Indexer)]
        [debugger (spawn debugger-loc DebugActor)]
        [javac (spawn javac-loc JavaAnalyzer)]
        [scalac (spawn scala-loc Analyzer)]
        [project (spawn project-loc Project docs indexer debugger javac scalac)]))))

(module+ test
  (require
   racket/async-channel
   (only-in csa record variant :)
   csa/eval
   csa/testing
   rackunit
   asyncunit
   "../desugar.rkt"
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (define desugared-program (desugar ensime-program))
  (define (start-prog)
    (csa-run desugared-program))

  (test-case "No request gets a response before initialization"
    (define project (start-prog))
    (define dest (make-async-channel))
    (async-channel-put project (variant Resolve "begin" dest))
    (check-no-message dest)
    ;; TODO: check for all the other requests
    )

  (test-case "All methods get responses after initialization"
    (define project (start-prog))
    (define ci-dest (make-async-channel))
    (async-channel-put project (variant ConnectionInfoReq ci-dest))
    (check-unicast ci-dest (variant ConnectionInfo))

    ;; Check for responses on all messages
    (async-channel-put project (variant ConnectionInfoReq ci-dest))
    (check-unicast ci-dest (variant ConnectionInfo))
    ;; docs
    (define doc-dest (make-async-channel))
    (async-channel-put project (variant Resolve "begin" doc-dest))
    (check-unicast doc-dest (variant StringResponse "http://www.racket-lang.org/"))
    ;; indexer
    (define symbol-dest (make-async-channel))
    (async-channel-put project (variant PublicSymbolSearchReq (list "foo") 10 symbol-dest))
    (check-unicast symbol-dest (variant ImportSuggestions (list "foo" "bar")))
    (define completion-dest (make-async-channel))
    (async-channel-put project (variant TypeCompletionsReq "abc" 10 symbol-dest))
    (check-unicast symbol-dest (variant SymbolSearchResults (list "abc")))
    ;; debugger
    (define run-dest (make-async-channel))
    (async-channel-put project (variant DebugRunReq run-dest))
    (check-unicast run-dest (variant TrueResponse))
    (define value-dest (make-async-channel))
    (async-channel-put project (variant DebugValueReq 2 value-dest))
    (check-unicast value-dest (variant DebugValue "bar"))
    (define stop-dest (make-async-channel))
    (async-channel-put project (variant DebugStopReq stop-dest))
    (check-unicast stop-dest (variant TrueResponse))
    ;; javac
    (define javadoc-dest (make-async-channel))
    (define test-file (record [type (variant Java)] [text (hash 1 "a" 2 "b")]))
    (async-channel-put project (variant DocUriAtPointReq test-file 1 javadoc-dest))
    (check-unicast javadoc-dest (variant DocSigPair "a"))
    (async-channel-put project (variant DocUriAtPointReq test-file 3 javadoc-dest))
    (check-unicast javadoc-dest (variant NoDocSigPair))
    (define java-completions-dest (make-async-channel))
    (async-channel-put project (variant CompletionsReq
                                        test-file
                                        5
                                        10
                                        (variant False)
                                        (variant False)
                                        java-completions-dest))
    (check-unicast java-completions-dest (list "a" "b" "c"))
    ;; scalac
    (define typecheck-dest (make-async-channel))
    (async-channel-put project (variant TypecheckAllReq typecheck-dest))
    (check-unicast typecheck-dest (variant VoidResponse))
    (define scala-completions-dest (make-async-channel))
    (define scala-test-file (record [type (variant Scala)] [text (hash 3 "c" 4 "d")]))
    (async-channel-put project (variant CompletionsReq
                                        scala-test-file
                                        4
                                        10
                                        (variant False)
                                        (variant False)
                                        scala-completions-dest))
    (check-unicast scala-completions-dest (list "d" "e" "f"))
    (define refactor-dest (make-async-channel))
    (async-channel-put project (variant RefactorReq 1 (variant Rename) false refactor-dest))
    (check-unicast refactor-dest
                   (variant RefactorDiffEffect 1 (variant Rename) "this is the new file"))
    (define refactor-dest2 (make-async-channel))
    (async-channel-put project (variant RefactorReq 1 (variant InlineLocal) false refactor-dest2))
    (check-unicast refactor-dest2 (variant RefactorFailure 1 "fail" "fail"))))
