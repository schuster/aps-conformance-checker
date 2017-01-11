#lang racket

(define ensime-program
  (quasiquote
(program (receptionists [project ???]) (externals)

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
       (send sender (list "foo" "bar"))
       (goto Always)]
      [(TypeCompletionsReq query max-results sender)
       (send sender (list query))
       (goto Always)])))

(define-variant ProjectInput
  (ConnectionInfoReq [sender (Addr ConnectionInfo)])
  (Resolve [doc-sig-pair String] [sender (Addr ResolveResult)])
  (PublicSymbolSearchReq [keywords (Listof String)]
                         [max-results Nat]
                         [sender (Addr ImportSuggestions)])
  (TypeCompletionsReq [query String] [max-results Nat] [sender (Addr SymbolSearchResults)])
  )

(define-actor ProjectInput
  (Project [docs (Addr DocResolverInput)]
   ;; TODO: put all the other actors here
   )
  ()
  (goto AwaitingConnectionInfoReq)
  (define-state (AwaitingConnectionInfoReq) (m)
    (case m
      [(ConnectionInfoReq sender)
       (send sender (ConnectionInfo))
       (goto HandleRequests)]
      [(Resolve p s) (goto AwaitingConnectionInfoReq)]
      [(PublicSymbolSearchReq k m s) (goto AwaitingConnectionInfoReq)]
      [(TypeCompletionsReq q m s) (goto AwaitingConnectionInfoReq)]))
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
       (goto HandleRequests)]))
  )

(actors [docs (spawn docs DocResolver)]
        [project (spawn project Project docs)]))))

;; Messages to do:
;; * docs: resolve
;; * indexer: public symbol search, type complections req
;; * debugger: Run, Stop, Value(location)
;; * Javac: docUriAtPointReq, CompletionsReq
;; * Scalac: TypecheckAll, CompletionsReq, RefactorReq

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
    (define doc-dest (make-async-channel))
    (async-channel-put project (variant Resolve "begin" doc-dest))
    (check-unicast doc-dest (variant StringResponse "http://www.racket-lang.org/"))

    (define symbol-dest (make-async-channel))
    (async-channel-put project (variant PublicSymbolSearchReq (list "foo") 10 symbol-dest))
    (check-unicast symbol-dest (variant ImportSuggestions (list "foo" "bar")))
    (define completion-dest (make-async-channel))
    (async-channel-put project (variant TypeCompletionsReq "abc" 10 symbol-dest))
    (check-unicast symbol-dest (variant SymbolSearchResults (list "abc")))))

;; TODO: queue up messages during the ConnectionInfo phase: spec can be weak here, but at least say a
;; little bit of something AND be true to the real program
