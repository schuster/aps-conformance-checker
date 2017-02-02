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
(define REGISTER-WAIT-TIME-IN-MS 2000)

(define spray-can-definitions
  (quasiquote
   (

;; ---------------------------------------------------------------------------------------------------
;; TCP types

(define-type Byte Nat) ; fake bytes with natural numbers

(define-type IpAddress Nat) ; fake IP addresses with Nats
  (define-record InetSocketAddress [ip IpAddress] [port Nat])
  (define-record SessionId
    [remote-address InetSocketAddress]
    [local-port Nat])

(define-type WriteResponse
  (Union
   (CommandFailed)
   (WriteAck)))

(define-type TcpWriteOnlyCommand
  (Union
   (Write (Vectorof Byte) (Addr WriteResponse))))

(define-type TcpSessionEvent
  (Union
   [ReceivedData (Vectorof Byte)]
   [Closed]
   [ConfirmedClosed]
   [Aborted]
   [PeerClosed]
   [ErrorClosed]))

(define-variant TcpSessionCommand
  (Register [handler (Addr TcpSessionEvent)])
  (Write [data (Vectorof Byte)] [handler (Addr WriteResponse)])
  (Close [close-handler (Addr (Union [CommandFailed] [Closed]))])
  (ConfirmedClose [close-handler (Addr (Union [CommandFailed] [ConfirmedClosed]))])
  (Abort [close-handler (Addr (Union [CommandFailed] [Aborted]))]))

;; ---------------------------------------------------------------------------------------------------
;; HTTP types

(define-type HttpRequest (Vectorof Bytes))
(define-type HttpResponse (Vectorof Bytes))

;; ---------------------------------------------------------------------------------------------------
;; Internal Types

(define-variant HttpServerConnectionInput
  ;; handles all TCP messages, plus HttpRegister
  [ReceivedData [bytes (Vectorof Byte)]]
  [Closed]
  [ConfirmedClosed]
  [Aborted]
  [PeerClosed]
  [ErrorClosed]
  [HttpRegister [handler (Addr IncomingRequest)]])

;; ---------------------------------------------------------------------------------------------------
;; Application Layer Protocol

(define-record IncomingRequest
  [request HttpRequest]
  [response-dest (Addr HttpResponse)])

(define-type HttpUnbindResponse
  (Union
   [HttpUnbound]
   ;; CommandFailed happens when we timeout waiting for TCP to unbind, but if TCP returns
   ;; CommandFailed, we still return HttpUnbound
   [CommandFailed]))

(define-variant HttpListenerCommand
  (HttpUnbind [commander (Addr HttpUnbindResponse)]))

(define-variant BindResponse
  (HttpBound [listener (Addr HttpListenerCommand)])
  (HttpCommandFailed))

(define-type HttpConnectionCommand
  (Union
   [HttpRegister (Addr IncomingRequest)]))

(define-variant HttpListenerEvent
  (HttpConnected [session-id SessionId] [connection (Addr HttpConnectionCommand)]))

(define-type HttpManagerCommands
  (Union
   [HttpBind (Addr BindResponse) ; commander, listener
             (Addr HttpListenerEvent)]))

;; ---------------------------------------------------------------------------------------------------
;; Sink

;; just a simple actor to swallow various TCP events
(define-actor (Union [CommandFailed]
                     [WriteAck]
                     [Closed]
                     [ConfirmedClosed]
                     [Aborted]
                     [PeerClosed]
                     [ErrorClosed])
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
  (define-state (Done) (m) (goto Done)))

;; ---------------------------------------------------------------------------------------------------
;; HttpServerConnection

(define-actor HttpServerConnectionInput
  (HttpServerConnection [session-id SessionId]
                        [app-listener (Addr HttpListenerEvent)]
                        [tcp-session (Addr TcpSessionCommand)])
  (
   ;; Finds the first prefix of the given data that ends in 0, if such a prefix exists.
   ;;
   ;; This fakes the idea of parsing an HTTP request from various received segments from the TCP
   ;; session.
   (define-function (find-request-tail [data (Vectorof Byte)])
     ;; returns (Union [FoundTail [prefix (Vectorof Byte)] [rest (Vectorof Byte)]] [TailNotFound])
     (let ([loop-result
            (for/fold ([result-so-far (variant LookingForTail (vector))])
                      ([byte data])
              (case result-so-far
                [(LookingForTail seen-bytes)
                 (if (= 0 byte)
                     (variant FoundTail seen-bytes (vector))
                     (variant LookingForTail (vector-append seen-bytes (vector byte))))]
                [(FoundTail prefix rest)
                 (variant FoundTail prefix (vector-append rest (vector byte)))]))])
       (case loop-result
         [(LookingForTail seen-bytes) (variant TailNotFound)]
         [(FoundTail prefix rest) (variant FoundTail prefix rest)]))))

  (let ()
    (send app-listener (HttpConnected session-id self))
    (goto AwaitingRegistration))

  (define-state/timeout (AwaitingRegistration) (m)
    (case m
      [(ReceivedData data)
       ;; this shouldn't happen here yet, because we haven't registered with TCP
       (goto AwaitingRegistration)]
      [(Closed) (goto Closed)]
      [(ConfirmedClosed) (goto Closed)]
      [(Aborted) (goto Closed)]
      [(PeerClosed) (goto Closed)]
      [(ErrorClosed) (goto Closed)]
      [(HttpRegister handler)
       (send tcp-session (Register self))
       (goto Running (vector) handler)])
    (timeout ,REGISTER-WAIT-TIME-IN-MS
      (send tcp-session (Close (spawn close-session Sink)))
      (goto Closed)))

  (define-state (Running [held-data (Vectorof Byte)] [handler (Addr IncomingRequest)]) (m)
    (case m
      [(ReceivedData data)
       (case (find-request-tail data)
         [(FoundTail tail rest)
          (spawn request-handler RequestHandler (vector-append held-data tail) handler tcp-session)
          (goto Running rest handler)]
         [(TailNotFound)
          (goto Running (vector-append held-data data) handler)])]
      [(Closed) (goto Closed)]
      [(ConfirmedClosed) (goto Closed)]
      [(Aborted) (goto Closed)]
      [(PeerClosed) (goto Closed)]
      [(ErrorClosed) (goto Closed)]
      [(HttpRegister handler)
       ;; just ignore extra registration messages
       (goto Running handler)]))

  (define-state (Closed) (m) (goto Closed)))

)))

;; ---------------------------------------------------------------------------------------------------
;; Programs

(define request-handler-only-program
  `(program (receptionists)
            (externals [app-layer IncomingRequest] [tcp TcpWriteOnlyCommanpd])
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

(define connection-program
  `(program (receptionists)
            (externals [app-listener HttpListenerEvent] [tcp-session TcpSessionCommand])
     ,@spray-can-definitions
     (define-actor Nat
       (Launcher [app-listener (Addr HttpListenerEvent)] [tcp-session (Addr TcpSessionCommand)])
       ()
       (goto Init)
       (define-state/timeout (Init) (m) (goto Init)
         (timeout 0
           (let ([session-id (SessionId (InetSocketAddress 1234 500) 80)])
             (spawn connection HttpServerConnection session-id app-listener tcp-session)
             (goto Done))))
       (define-state (Done) (m) (goto Done)))
     (actors [launcher (spawn 1 Launcher app-listener tcp-session)])))

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
    (FinishedRequest)
    (HttpRegister handler)
    (Register handler)
    (ReceivedData data)
    (Closed))

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
    (check-no-message tcp #:timeout 2))

  ;; HttpServerConnection tests

  (define desugared-connection-program (desugar connection-program))

  (test-case "ServerConection registers with TCP connection when application layer registers with ServerConnection"
    (define app-listener (make-async-channel))
    (define tcp-connection (make-async-channel))
    (csa-run desugared-connection-program app-listener tcp-connection)
    (define connection (check-unicast-match app-listener
                                            (csa-variant HttpConnected _ connection)
                                            #:result connection))
    (async-channel-put connection (HttpRegister (make-async-channel)))
    (check-unicast-match tcp-connection (csa-variant Register _)))

  (test-case "If app layer does not register, ServerConnection tells TCP to close"
    (define tcp-connection (make-async-channel))
    (csa-run desugared-connection-program (make-async-channel) tcp-connection)
    (sleep (/ REGISTER-WAIT-TIME-IN-MS 1000))
    (check-unicast-match tcp-connection (csa-variant Close _)))

  (define (run-connection-to-registered app-listener tcp-connection handler)
    (csa-run desugared-connection-program app-listener tcp-connection)
    (define connection (check-unicast-match app-listener
                                            (csa-variant HttpConnected _ connection)
                                            #:result connection))
    (async-channel-put connection (HttpRegister handler))
    (async-channel-get tcp-connection)
    connection)

  (test-case "ServerConnection creates request handler once all bytes for a packet are received"
    (define app-listener (make-async-channel))
    (define tcp-connection (make-async-channel))
    (define handler (make-async-channel))
    (define connection (run-connection-to-registered app-listener tcp-connection handler))
    (async-channel-put connection (ReceivedData (vector 1 2)))
    (async-channel-put connection (ReceivedData (vector 3 0)))
    (check-unicast-match handler (csa-record [request (vector 1 2 3)] [response-dest _])))

  (test-case "ServerConnection can create multiple request handlers"
    (define app-listener (make-async-channel))
    (define tcp-connection (make-async-channel))
    (define handler (make-async-channel))
    (define connection (run-connection-to-registered app-listener tcp-connection handler))
    (async-channel-put connection (ReceivedData (vector 1 0)))
    (sleep 0.5) ; make sure the first requet is handled first
    (async-channel-put connection (ReceivedData (vector 2 0)))
    (check-unicast-match handler (csa-record [request (vector 1)] [response-dest _]))
    (check-unicast-match handler (csa-record [request (vector 2)] [response-dest _])))

  (test-case "ServerConnection does not react to requests after TCP session closes"
    (define app-listener (make-async-channel))
    (define tcp-connection (make-async-channel))
    (define handler (make-async-channel))
    (define connection (run-connection-to-registered app-listener tcp-connection handler))
    (async-channel-put connection (ReceivedData (vector 1 0)))
    (check-unicast-match handler (csa-record [request (vector 1)] [response-dest _]))
    (async-channel-put connection (Closed))
    (async-channel-put connection (ReceivedData (vector 2 0)))
    (check-no-message handler))

  (test-case "ServerConnection might close before registration"
    (define app-listener (make-async-channel))
    (define tcp-connection (make-async-channel))
    (define handler (make-async-channel))
    (csa-run desugared-connection-program app-listener tcp-connection)
    (define connection (check-unicast-match app-listener
                                            (csa-variant HttpConnected _ connection)
                                            #:result connection))
    (async-channel-put connection (Closed))
    (sleep 0.5)
    (async-channel-put connection (HttpRegister handler))
    (check-no-message handler)))
