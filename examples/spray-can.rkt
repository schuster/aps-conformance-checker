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
(define UNBIND-WAIT-TIME-IN-MS 2000)

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

(define-type UnbindResponse
  (Union
   [Unbound]
   [CommandFailed]))

(define-variant TcpListenerCommand
  (Unbind [unbind-commander (Addr UnbindResponse)]))

(define-type BindStatus
  (Union [Bound (Addr TcpListenerCommand)]))
(define-function (Bound [listener (Addr TcpListenerCommand)]) (variant Bound listener))

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

(define-type HttpRequest (Vectorof Byte))
(define-type HttpResponse (Vectorof Byte))

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

(define-type HttpUnbindResponse
  (Union
   [HttpUnbound]
   [HttpCommandFailed]))
(define-function (HttpUnbound) (variant HttpUnbound))

(define-variant HttpListenerInput
  (Bound [listener (Addr TcpListenerCommand)])
  (CommandFailed)
  (HttpUnbind [commander (Addr HttpUnbindResponse)])
  (BindTimeout)
  (UnbindTimeout)
  (Connected [session-id SessionId] [session (Addr TcpSessionCommand)]))

;; ---------------------------------------------------------------------------------------------------
;; Application Layer Protocol

(define-record IncomingRequest
  [request HttpRequest]
  [response-dest (Addr HttpResponse)])

(define-variant HttpListenerCommand
  (HttpUnbind [commander (Addr HttpUnbindResponse)]))

(define-variant HttpBindResponse
  (HttpBound [listener (Addr HttpListenerCommand)])
  (HttpCommandFailed))

(define-type HttpConnectionCommand
  (Union
   [HttpRegister (Addr IncomingRequest)]))

(define-variant HttpListenerEvent
  (HttpConnected [session-id SessionId] [connection (Addr HttpConnectionCommand)]))

(define-variant HttpManagerCommand
  (HttpBind [port Nat] [commander (Addr HttpBindResponse)] [app-listener (Addr HttpListenerEvent)]))

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
     [BindTimeout]
     [UnbindTimeout]))

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
       (goto Running held-data handler)]))

  (define-state (Closed) (m) (goto Closed)))

;; ---------------------------------------------------------------------------------------------------
;; HttpListener

(define-actor HttpListenerInput
  (HttpListener [port Nat]
                [bind-commander (Addr BindStatus)]
                [app-listener (Addr HttpListenerEvent)]
                [tcp (Addr TcpCommand)])
  ((define-function (unbind [tcp-listener (Addr TcpListenerCommand)]
                            [unbind-commanders (Listof (Addr HttpUnbindResponse))])
     (send tcp (Unbind self))
     (let ([unbind-timer (spawn unbind-timer Timer (UnbindTimeout) self)])
       (send unbind-timer (Start ,UNBIND-WAIT-TIME-IN-MS))
       (goto Unbinding unbind-timer unbind-commanders))))

  ;; initialization
  (let ([bind-timer (spawn bind-timer Timer (BindTimeout) self)])
    (send tcp (Bind port self self))
    (send bind-timer (Start ,BIND-WAIT-TIME-IN-MS))
    (goto Binding bind-timer))

  (define-state (Binding [bind-timer (Addr TimerCommand)]) (m)
    (case m
      ;; From TCP
      [(CommandFailed)
       (send bind-commander (HttpCommandFailed))
       (send bind-timer (Stop))
       (goto Closed)]
      [(Bound tcp-listener)
       (send bind-commander (HttpBound self))
       (send bind-timer (Stop))
       (goto Connected tcp-listener)]
      [(Unbound)
       ;; shouldn't happen; ignore
       (goto Binding bind-timer)]
      [(Connected session-id session)
       ;; shouldn't happen here; ignore it
       (goto Binding bind-timer)]
      ;; From Timer
      [(BindTimeout)
       (send bind-commander (HttpCommandFailed))
       (goto Closed)]
      [(UnbindTimeout)
       ;; shouldn't happen
       (goto Binding bind-timer)]
      ;; From Application Layer
      [(HttpUnbind commander)
       ;; shouldn't happen here because client doesn't have our address yet, but for now I'm writing
       ;; it anyway
       (send bind-commander (HttpCommandFailed))
       (goto BindingAborted bind-timer (list commander))]))

  (define-state (BindingAborted [bind-timer (Addr TimerCommand)]
                                [commanders (Listof (Addr HttpUnbindResponse))]) (m)
    (case m
      ;; From TCP
      [(CommandFailed)
       (send bind-timer (Stop))
       (for/fold ([result 0])
                 ([commander commanders])
         (send commander (HttpUnbound))
         0)
       (goto Closed)]
      [(Bound tcp-listener)
       (send tcp-listener (Unbind self))
       (send bind-timer (Stop))
       (unbind tcp-listener commanders)]
      [(Unbound)
       ;; shouldn't happen; ignore
       (goto BindingAborted bind-timer commanders)]
      [(Connected session-id session)
       ;; shouldn't happen here; ignore it
       (goto BindingAborted bind-timer commanders)]
      ;; From Timer
      [(BindTimeout)
       (for/fold ([result 0])
                 ([commander commanders])
         (send commander (HttpUnbound))
         0)
       (goto Closed)]
      [(UnbindTimeout)
       ;; shouldn't happen here
       (goto BindingAborted bind-timer commanders)]
      ;; From Application Layer
      [(HttpUnbind commander)
       (goto BindingAborted bind-timer (cons commander commanders))]))

  (define-state (Unbinding [unbind-timer (Addr TimerCommand)]
                           [commanders (Listof (Addr HttpUnbindResponse))]) (m)
    (case m
      ;; From TCP
      [(CommandFailed)
       (send unbind-timer (Stop))
       (for/fold ([result 0])
                 ([commander commanders])
         (send commander (HttpUnbound))
         0)
       (goto Closed)]
      [(Bound tcp-listener)
       ;; shouldn't happen; ignore
       (goto Unbinding unbind-timer commanders)]
      [(Unbound)
       (send unbind-timer (Stop))
       (for/fold ([result 0])
                 ([commander commanders])
         (send commander (HttpUnbound))
         0)
       (goto Closed)]
      [(Connected session-id session)
       (goto Unbinding unbind-timer commanders)]
      ;; From Timer
      [(BindTimeout)
       (goto Unbinding unbind-timer commanders)]
      [(UnbindTimeout)
       (for/fold ([result 0])
                 ([commander commanders])
         (send commander (HttpCommandFailed))
         0)
       (goto Closed)]
      ;; From Application Layer
      [(HttpUnbind commander)
       (goto Unbinding unbind-timer (cons commander commanders))]))
  (define-state (Connected [tcp-listener (Addr TcpListenerCommand)]) (m)
    (case m
      ;; From TCP
      [(CommandFailed)
       ;; shouldn't happen; ignore
       (goto Connected tcp-listener)]
      [(Bound tcp-listener)
       ;; shouldn't happen; ignore
       (goto Connected tcp-listener)]
      [(Unbound)
       ;; shouldn't happen; ignore
       (goto Connected tcp-listener)]
      [(Connected session-id session)
       (spawn server-connection HttpServerConnection session-id app-listener session)
       (goto Connected tcp-listener)]
      ;; From Timer
      [(BindTimeout)
       ;; ignore
       (goto Connected tcp-listener)]
      [(UnbindTimeout)
       ;; ignore
       (goto Connected tcp-listener)]
      ;; From Application Layer
      [(HttpUnbind unbind-commander)
       (unbind tcp-listener (list unbind-commander))]))
  (define-state (Closed) (m)
    (case m
      ;; From TCP
      [(CommandFailed) (goto Closed)]
      [(Bound tcp-listener) (goto Closed)]
      [(Unbound) (goto Closed)]
      [(Connected session-id session) (goto Closed)]
      ;; From Timer
      [(BindTimeout) (goto Closed)]
      [(UnbindTimeout) (goto Closed)]
      ;; From Application Layer
      [(HttpUnbind unbind-commander)
       (send unbind-commander (HttpCommandFailed))
       (goto Closed)])))

;; ---------------------------------------------------------------------------------------------------
;; HttpManager

(define-actor HttpManagerCommand
  (HttpManager [tcp (Addr TcpCommand)])
  ()
  (goto Managing)
  (define-state (Managing) (m)
    (case m
      [(HttpBind port commander listener)
       (spawn listener HttpListener port commander listener tcp)
       (goto Managing)]))))))

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

(define manager-program
  `(program (receptionists [manager HttpManagerCommand])
            (externals [tcp TcpCommand])
     ,@spray-can-definitions
     (actors [manager (spawn manager HttpManager tcp)])))

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
    (CommandFailed)
    (HttpCommandFailed)
    (Connected session-id session)
    (HttpConnected seesion-id connection)
    (Bound listener)
    (Unbind commander)
    (HttpUnbind commander)
    (Unbound)
    (HttpUnbound)
    (HttpBind port commander listener))

  (define test-session-id (record [remote-address (record [ip 1234] [port 500])] [local-port 80]))

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
    (check-unicast bind-commander (HttpCommandFailed)))

  (test-case "HttpListener responds with CommandFailed if TCP says the bind failed"
    (define bind-commander (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (CommandFailed))
    (check-unicast bind-commander (HttpCommandFailed)))

  (test-case "HttpListener sends a bound response to listener after TCP gives Bound confirmation"
    (define bind-commander (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (Bound (make-async-channel)))
    (check-unicast-match bind-commander (csa-variant HttpBound _)))

  (define (start-and-bind-http-listener app-listener tcp)
    (define bind-commander (make-async-channel))
    (csa-run desugared-listener-program bind-commander app-listener tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (Bound (make-async-channel)))
    (async-channel-get bind-commander) ; eat the Bound
    listener)

  (test-case "HttpListener sends new TCP connection to app layer"
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (define listener (start-and-bind-http-listener app-listener tcp))
    (async-channel-put listener (Connected test-session-id (make-async-channel)))
    (check-unicast-match app-listener (csa-variant HttpConnected _ _)))

  (test-case "HttpListener tries to unbind during Connected, succeeds"
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (define listener (start-and-bind-http-listener app-listener tcp))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast-match tcp (csa-variant Unbind _))
    (async-channel-put listener (Unbound))
    (check-unicast unbind-commander (HttpUnbound)))

  (test-case "HttpListener tries to unbind during Connected, times out"
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (define listener (start-and-bind-http-listener app-listener tcp))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast-match tcp (csa-variant Unbind _))
    (sleep (/ UNBIND-WAIT-TIME-IN-MS 1000))
    (check-unicast unbind-commander (HttpCommandFailed)))

  (test-case "HttpListener tries to unbind during Connected, fails"
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (define listener (start-and-bind-http-listener app-listener tcp))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast-match tcp (csa-variant Unbind _))
    (async-channel-put listener (CommandFailed))
    (check-unicast unbind-commander (HttpUnbound)))

  (test-case "HttpListener aborts binding, succeeds"
    (define bind-commander (make-async-channel))
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast bind-commander (HttpCommandFailed))
    (define tcp-listener (make-async-channel))
    (async-channel-put listener (Bound tcp-listener))
    (check-unicast-match tcp-listener (csa-variant Unbind _))
    (async-channel-put listener (Unbound))
    (check-unicast unbind-commander (HttpUnbound)))

  (test-case "HttpListener aborts binding, unbind fails"
    (define bind-commander (make-async-channel))
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast bind-commander (HttpCommandFailed))
    (define tcp-listener (make-async-channel))
    (async-channel-put listener (Bound tcp-listener))
    (check-unicast-match tcp-listener (csa-variant Unbind _))
    (async-channel-put listener (CommandFailed))
    (check-unicast unbind-commander (HttpUnbound)))

  (test-case "HttpListener aborts binding, but original bind fails"
    (define bind-commander (make-async-channel))
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast bind-commander (HttpCommandFailed))
    (async-channel-put listener (CommandFailed))
    (check-unicast unbind-commander (HttpUnbound)))

  (test-case "HttpListener sends HttpUnbound to every Unbind commander"
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (define listener (start-and-bind-http-listener app-listener tcp))
    (define unbind-commander1 (make-async-channel))
    (define unbind-commander2 (make-async-channel))
    (define unbind-commander3 (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander1))
    (async-channel-put listener (HttpUnbind unbind-commander2))
    (async-channel-put listener (HttpUnbind unbind-commander3))
    (check-unicast-match tcp (csa-variant Unbind _))
    (async-channel-put listener (Unbound))
    (check-unicast unbind-commander1 (HttpUnbound))
    (check-unicast unbind-commander2 (HttpUnbound))
    (check-unicast unbind-commander3 (HttpUnbound)))

  (test-case "HttpListener responds to Unbind after it's closed"
    (define bind-commander (make-async-channel))
    (define app-listener (make-async-channel))
    (define tcp (make-async-channel))
    (csa-run desugared-listener-program bind-commander (make-async-channel) tcp)
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (CommandFailed)) ; listener should be closed now
    (define unbind-commander (make-async-channel))
    (async-channel-put listener (HttpUnbind unbind-commander))
    (check-unicast unbind-commander (HttpCommandFailed)))

  ;; HttpManager Tests

  (define desugared-manager-program (desugar manager-program))

  (test-case "HttpManager bind can fail; report failure to commander"
    (define tcp (make-async-channel))
    (define manager (csa-run desugared-manager-program tcp))
    (define bind-commander (make-async-channel))
    (async-channel-put manager (HttpBind 80 bind-commander (make-async-channel)))
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (CommandFailed))
    (check-unicast bind-commander (HttpCommandFailed)))

  (test-case "HttpManager responds with success when binding succeeds"
    (define tcp (make-async-channel))
    (define manager (csa-run desugared-manager-program tcp))
    (define bind-commander (make-async-channel))
    (async-channel-put manager (HttpBind 80 bind-commander (make-async-channel)))
    (define listener (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put listener (Bound (make-async-channel)))
    (check-unicast-match bind-commander (csa-variant HttpBound _)))

  (test-case "End-to-end HTTP test case"
    (define tcp (make-async-channel))
    (define manager (csa-run desugared-manager-program tcp))
    (define bind-commander (make-async-channel))
    (define app-listener (make-async-channel))
    ;; Bind to the port
    (async-channel-put manager (HttpBind 80 bind-commander app-listener))
    (define http-listener
      (check-unicast-match tcp (csa-variant Bind 80 _ listener) #:result listener))
    (async-channel-put http-listener (Bound (make-async-channel)))
    (check-unicast-match bind-commander (csa-variant HttpBound (== http-listener)))
    ;; Start a new TCP session
    (define tcp-session (make-async-channel))
    (async-channel-put http-listener (Connected test-session-id tcp-session))
    (define http-connection
      (check-unicast-match app-listener
                           (csa-variant HttpConnected (== test-session-id) connection)
                           #:result connection))
    ;; App layer registers with the session
    (define app-handler (make-async-channel))
    (async-channel-put http-connection (HttpRegister app-handler))
    (check-unicast-match tcp-session (csa-variant Register _))
    ;; Send in a new request from the wire
    (async-channel-put http-connection (ReceivedData (vector 1 2)))
    (async-channel-put http-connection (ReceivedData (vector 3 0)))
    (define http-handler
      (check-unicast-match app-handler
                           (csa-record [request (vector 1 2 3)] [response-dest handler])
                           #:result handler))
    (async-channel-put http-handler (vector 4 5 6))
    ;; HTTP server sends our response to TCP, hurray!
    (check-unicast-match tcp-session (csa-variant Write (vector 4 5 6) _))))
