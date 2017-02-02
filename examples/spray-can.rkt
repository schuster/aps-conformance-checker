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
(define BIND-WAIT-TIME-IN-MS 2000)

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

(define-type BindStatus
  (Union [Bound] [CommandFailed]))
(define-function (Bound) (variant Bound))

(define-type ConnectionStatus
  (Union
   (CommandFailed)
   (Connected SessionId (Addr TcpSessionCommand))))
(define-function (Connected [session-id SessionId] [session (Addr TcpSessionCommand)])
  (variant Connected session-id session))

(define-variant TcpCommand
  ;; spray-can doesn't directly connect
  ;; (Connect [remote-address InetSocketAddress]
  ;;          [status-updates (Addr ConnectionStatus)])
  (Bind [port Nat] [bind-status (Addr BindStatus)] [bind-handler (Addr ConnectionStatus)]))

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

(define-variant HttpListenerInput
  (Bound)
  (CommandFailed)
  (Unbind [commander (Addr (Union [Unbound] [CommandFailed]))])
  (BindTimeout)
  (Connected [session-id SessionId] [session (Addr TcpSessionCommand)]))

(define-function (Unbound) (variant Unbound))

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
;; Timer

  (define-variant TimerCommand
    (Stop)
    (Start [timeout-in-milliseconds Nat]))

  (define-type ExpirationMessage
    (Union
     [BindTimeout]))

  (define-actor TimerCommand
    (Timer [expiration-message ExpirationMessage]
           [expiration-target (Addr ExpirationMessage)])
    ()
    (goto Stopped)
    (define-state (Stopped) (m)
      (case m
        [(Stop) (goto Stopped)]
        [(Start timeout-in-milliseconds)
         (goto Running timeout-in-milliseconds)]))
    (define-state/timeout (Running [timeout-in-milliseconds Nat]) (m)
      (case m
        [(Stop) (goto Stopped)]
        [(Start new-timeout-in-milliseconds)
         (goto Running new-timeout-in-milliseconds)])
      (timeout timeout-in-milliseconds
        (send expiration-target expiration-message)
        (goto Stopped))))

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

;; ---------------------------------------------------------------------------------------------------
;; HttpListener

(define-actor HttpListenerInput
  (HttpListener [port Nat]
                [bind-commander (Addr BindStatus)]
                [app-listener (Addr HttpListenerEvent)]
                [tcp (Addr TcpCommand)])
  ()
  (let ([bind-timer (spawn bind-timer Timer (BindTimeout) self)])
    (send tcp (Bind port self self))
    (send bind-timer (Start ,BIND-WAIT-TIME-IN-MS))
    (goto Binding bind-timer))
  (define-state (Binding [bind-timer (Addr TimerCommand)]) (m)
    (case m
      [(BindTimeout)
       (send bind-commander (CommandFailed))
       (goto Closed)]))
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

(define listener-program
  `(program (receptionists)
            (externals [bind-commander BindStatus]
                       [app-listener HttpListenerEvent]
                       [tcp TcpCommand])
     ,@spray-can-definitions
     (define-actor Nat
       (Launcher [bind-commander (Addr BindStatus) ]
                 [app-listener (Addr HttpListenerEvent)]
                 [tcp (Addr TcpCommand)])
       ()
       (goto Init)
       (define-state/timeout (Init) (m) (goto Init)
         (timeout 0
           (spawn listener HttpListener 80 bind-commander app-listener tcp)
           (goto Done)))
       (define-state (Done) (m) (goto Done)))
     (actors [launcher (spawn 1 Launcher bind-commander app-listener tcp)])))

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
    (Closed)
    (CommandFailed))

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
    (check-no-message handler))

  ;; HttpListener Tests

  (define desugared-listener-program (desugar listener-program))

  (test-case "HttpListener responds with CommandFailed if it times out while binding"
    (define bind-commander (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (sleep (/ BIND-WAIT-TIME-IN-MS 1000))
    (check-unicast bind-commander (CommandFailed)))

;; Tests:
;; * if get timeout while trying to bind, respond with CommandFailed
;; * if bound by TCP, send the app layer a Bound response with our address
;; * if new TCP connection, send it to the registered app layer (listener from Bind message)
;; * if get Unbind during Running, try to unbind: send back either succeed or fail
;; * if get Unbind while waiting to bind, abort the binding (send TCP.Unbind as soon as we get a Bound)
;; * if multiple actors try to unbind, send them each the response
;; * unbind while closed: ???

  )
