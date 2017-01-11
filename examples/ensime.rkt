#lang racket

(define ensime-program
  (quasiquote
(program (receptionists [project ???]) (externals)

(define-variant ConnectionInfo
  (ConnectionInfo))

(define-variant ResolveResult
  (FalseResponse)
  (StringResponse [path String]))

(define-variant ProjectInput
  (ConnectionInfoReq [sender (Addr ConnectionInfo)])
  (Resolve [sender (Addr ResolveResult)]))

(define-actor ProjectInput
  (Project
   ;; TODO: put all the other actors here
   )
  ()
  (goto AwaitingConnectionInfoReq)
  (define-state (AwaitingConnectionInfoReq) (m)
    (case m
      [(ConnectionInfoReq sender)
       (send sender (ConnectionInfo))
       (goto HandleRequests)]
      [(Resolve s) (goto AwaitingConnectionInfoReq)])))

(actors [project (spawn project Project)]))))

;; Messages to do:
;; * docs: resolve
;; * indexer: public symbol search, type complections req
;; * debugger: Run, Stop, Value(location)
;; * Javac: docUriAtPointReq, CompletionsReq
;; * Scalac: TypecheckAll, CompletionsReq, RefactorReq


;; TODO: check that nothing gets a response pre-initialization

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
    (async-channel-put project (variant Resolve dest))
    (check-no-message dest)
    ;; TODO: check for all the other requests
    )

  ;; (test-case "All methods get responses after initialization")
  )
