#lang racket

(module+ test
  (require
   (for-syntax syntax/parse)
   (only-in csa record variant :)
   csa/eval
   csa/testing
   racket/async-channel
   asyncunit
   rackunit
   "../csa.rkt" ; for csa-valid-type?
   "../desugar.rkt"
   "../main.rkt"))

(define RESPONSE-WAIT-TIME-IN-MS 2000)

(define spray-can-definitions
  (quasiquote
   (

;; ---------------------------------------------------------------------------------------------------
;; TCP types

(define-type Byte Nat) ; fake bytes with natural numbers

(define-variant WriteResponse
  (CommandFailed)
  (WriteAck))

(define-variant TcpWriteOnlyCommand
  (Write (Vectorof Byte) (Addr WriteResponse)))

;; ---------------------------------------------------------------------------------------------------
;; HTTP types

(define-type HttpRequest (Vectorof Bytes))
(define-type HttpResponse (Vectorof Bytes))

;; ---------------------------------------------------------------------------------------------------
;; Application Layer Protocol

(define-record IncomingRequest
  [request HttpRequest]
  [response-dest (Addr HttpResponse)])

;; ---------------------------------------------------------------------------------------------------
;; Sink

;; just a simple actor to swallow TCP events
(define-actor WriteResponse
  (Sink)
  ()
  (goto Sink)
  (define-state (Sink) (m) (goto Sink)))

;; ---------------------------------------------------------------------------------------------------
;; RequestHandler: given a request, send to application layer and wait for their response (or
;; timeout). Also need to notify the HTTP connection actor when we're done so that if the listener is
;; trying to shut down, it can know when the request is complete.

(define-actor HttpResponse
  (RequestHandler [request HttpRequest]
                  [app-layer (Addr IncomingRequest)]
                  [tcp-connection (Addr TcpWriteOnlyCommand)])
  ()
  (let ()
    (send app-layer (IncomingRequest request self))
    (goto AwaitingAppResponse))
  (define-state/timeout (AwaitingAppResponse) (m)
    (send tcp-connection (Write m (spawn write-response Sink)))
    (goto Done)
    (timeout ,RESPONSE-WAIT-TIME-IN-MS
      ;; don't notify the application layer here: just assume they'll watch for the stop notification
      (goto Done)))
  (define-state (Done) (m) (goto Done))))))

;; ---------------------------------------------------------------------------------------------------
;; Programs

(define request-handler-only-program
  `(program (receptionists)
            (externals [app-layer (Addr IncomingRequest)] [tcp (Addr TcpWriteOnlyCommanpd)])
     ,@spray-can-definitions
     (define-actor Nat
       (Launcher [app-layer (Addr IncomingRequest)]
                 [tcp (Addr TcpWriteOnlyCommanpd)])
       ()
       (goto Init)
       (define-state/timeout (Init) (m) (goto Init)
         (timeout 0
           (spawn request-handler RequestHandler (vector 1 2 3) app-layer tcp)
           (goto Done)))
       (define-state (Done) (m) (goto Done)))
     (actors [launcher (spawn 1 Launcher app-layer tcp)])))

;; ---------------------------------------------------------------------------------------------------
;; Tests

(module+ test
  (define-syntax (define-test-variants stx)
    (syntax-parse stx
      [(_ (tag:id args:id ...) ...)
       #`(begin
           (define (tag args ...) (variant tag args ...)) ...)]))

  (define-test-variants
    (Write data handler)
    (IncomingRequest request response-dest)
    (FinishedRequest))

  (define desugared-request-handler-only-program (desugar request-handler-only-program))

  (test-case "Write response to TCP when application layer responds to request from RequestHandler"
    (define app-layer (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-request-handler-only-program app-layer tcp)
    (define handler
      (check-unicast-match app-layer (csa-record [request (vector 1 2 3)]
                                                 [response-dest handler])
                           #:result handler))
    (async-channel-put handler (vector 4 5 6))
    (check-unicast-match tcp (csa-variant Write (vector 4 5 6) _)))

  (test-case "RequestHandler times out if no response from application layer"
    (define app-layer (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-request-handler-only-program app-layer tcp)
    (check-unicast-match app-layer (csa-record [request (vector 1 2 3)] [response-dest _]))
    (check-no-message tcp #:timeout 2)))

