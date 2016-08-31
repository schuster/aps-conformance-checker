#lang racket

;; A simple ping/pong service guarded by an authentication actor. Roughly based off of the server in
;; Scalas and Yoshida 2015, and slide 41 of this talk:
;; http://www.slideshare.net/rolandkuhn/project-galbma-actors-vs-types

;; To access the service, the user first sends a GetSession request to the service guard. The guard
;; then creates a new handshake actor to manage the authentication state machine, and that actor asks
;; the server to lookup the session indicated by the auth-token the user provided. If one is found,
;; the handshake actor immediately gives the user the address of the server, and the user can interact
;; with the service.

;; Otherwise, the lookup fails, and the handshake actor asks the user for their credentials. When
;; supplied, if incorrect, the user immediately gets a failure response and the authentication state
;; machine terminates. Otherwise, the handshake actor has the service create a new session and
;; auth-token, which are eventually returned to the user along with the server's address.

;; TODO: maybe make a second version of this protocol that locks up the requester (will require some
;; new tests to show the difference in the protocol)

(provide
 authN-program
 authN-specification)

;;---------------------------------------------------------------------------------------------------

(define authN-program
  (quasiquote

(program (receptionists [guard GetSessionType]) (externals)
  (define-variant SessionResponse
    (Pong))

  (define-variant SessionCommand
    (Ping [reply-to (Addr SessionResponse)]))

  (define-variant AuthenticateResult
    (ActiveNewSession [auth-token Nat] [service (Addr SessionCommand)])
    (FailedSession))

  (define-record Authenticate
    [username String]
    [password String]
    [reply-to (Addr AuthenticateResult)])

  (define-variant GetSessionResultInternal
    (SuccessInternal)
    (FailureInternal))

  (define-variant GetSessionInternalType
    (GetSessionInternal [auth-token Nat] [reply-to (Addr GetSessionResultInternal)]))

  (define-variant GetSessionResult
    (ActiveOldSession [service (Addr SessionCommand)])
    (NewSession [auth (Addr Authenticate)]))

  (define-variant GetSessionType
    (GetSession [auth-token Nat] [reply-to (Addr GetSessionResult)]))

  (define-variant CreateSessionResult
    (NewSessionInternal [auth-token Nat]))

  (define-variant CreateVariant
    (CreateSession [username String] [reply-to CreateSessionResult]))

  (define-type HandshakeWorkerInput
    (Union (SuccessInternal)
           (FailureInternal)
           (NewSessionInternal
            Nat ; auth-token
            )))

  (define-type ServerInput
    (Union
     (GetSessionInternal
      Nat ; auth-token
      (Addr GetSessionResultInternal) ; reply-to
      )
     (CreateSession
      String ; username
      (Addr CreateSessionResult) ; reply-to
      )
     (Ping
      (Addr SessionResponse) ; reply-to
      )))

;; ---------------------------------------------------------------------------------------------------

  (define-actor HandshakeWorkerInput
    (HandshakeWorker [auth-token Nat]
                     [client (Addr GetSessionResult)]
                     [server (Addr ServerInput)]
                     [password-table (Hash String String)])
    ()
    ;; init:
    (let ()
      ;; Hmm... this is a case where actors aren't a great choice, and you want something more
      ;; lightweight like sessions that more directly expresses the protocol/usage: just want to
      ;; send/receive exactly once, for several messages in this sequence
      (send server (GetSessionInternal auth-token self))
      (goto WaitingForMaybeSession))
    ;; TODO: try writing this in a different way where each stage gets a new actor, so as to avoid
    ;; lots of the "this should never happen" messages

    ;; IDEA: with some sort of linear type system, we could do a lightweight typestate-like thing that
    ;; allows us to ignore certain messages once they've been received (because we know the only
    ;; channel for them was already used). Doesn't work in presence of dropped messages, though.
    (define-state (WaitingForMaybeSession) (m)
      (case m
        [(SuccessInternal)
         (send client (ActiveOldSession server))
         (goto Done)]
        [(FailureInternal)
         (send client (NewSession self))
         (goto WaitingForCredentials)]
        ;; The rest of these shouldn't happen right now
        [(Authenticate u p r) (goto WaitingForMaybeSession)]
        [(NewSessionInternal auth-token) (goto WaitingForMaybeSession)]))
    (define-state (WaitingForCredentials) (m)
      (case m
        [(Authenticate username password reply-to)
         (case (hash-ref password-table username)
           [(Nothing)
            (send reply-to (FailedSession))
            (goto Done)]
           [(Just found-password)
            (cond
              [(= password found-password)
               (send server (CreateSession auth-token self))
               (goto WaitingForCredentials)]
              [else
               (send reply-to (FailedSession))
               (goto Done)])])]
        ;; These next three shouldn't happen at this point; ignore the message
        [(SuccessInternal) (goto WaitingForCredentials)]
        [(FailureInternal) (goto WaitingForCredentials)]
        [(NewSessionInternal auth-token) (goto WaitingForCredentials)]))
    (define-state (WaitingForServer) (m)
      (case m
        [(NewSessionInternal auth-token)
         (send client (ActiveNewSession auth-token server))
         (goto Done)]
        ;; None of these should happen right now
        [(SuccessInternal) (goto WaitingForServer)]
        [(FailureInternal) (goto WaitingForServer)]
        [(Authenticate u p r) (goto WaitingForServer)]))
    (define-state (Done) (m) (goto Done)))

  (define-actor GetSessionType
    (ServiceGuard [server (Addr ServerInput)] [password-table (Hash String String)])
    ()
    (goto Ready)
    (define-state (Ready) (m)
      (case m
        [(GetSession auth-token reply-to)
         (spawn 3 HandshakeWorker auth-token reply-to server password-table)
         (goto Ready)])))

  (define-actor ServerInput
    (Server)
    ()
    (goto Running (hash) 0)
    (define-state (Running [sessions (Hash Nat Nat)] [next-auth-token Nat]) (m)
      (case m
        [(GetSessionInternal auth-token reply-to)
         (cond
           [(hash-has-key? sessions auth-token)
            (send reply-to (FailureInternal))]
           [else (send reply-to (SuccessInternal))])
         (goto Running sessions next-auth-token)]
        [(CreateSession username reply-to)
         ;; In a real implementation, creating auth tokens would be more complicated, with very large
         ;; numbers, perhaps randomization, etc.
         (let ([auth-token next-auth-token]
               [next-auth-token (+ 1 next-auth-token)])
           (send reply-to (NewSessionInternal auth-token))
           (goto Running (hash-set sessions auth-token 1) next-auth-token))]
        [(Ping reply-to)
         (send reply-to (Pong))
         (goto Running sessions next-auth-token)])))

  ;; TODO: allow for hash literals with values in them
  (define-constant pw-table ;; (hash-set (hash-set (hash) "joe" "abc") "sally" "xyz")
    (hash))

  (actors [server (spawn 1 Server)]
          [guard (spawn 2 ServiceGuard server pw-table)]))))

;; ---------------------------------------------------------------------------------------------------
;; Specification

;; Spec says that:
;; * initial request gets response with authN thing.
;; * auth can fail or succeed, get response either way
;; * if succeed, returned address responds to pings

(define desugared-SessionResponse
  `(Union (Pong)))

(define desugared-SessionCommand
  `(Union (Ping (Addr ,desugared-SessionResponse))))

(define desugared-AuthenticateResult
  `(Union (ActiveNewSession Nat (Addr ,desugared-SessionCommand))
          (FailedSession)))

(define desugared-Authenticate
  `(Record [username String] [password String] [reply-to (Addr ,desugared-AuthenticateResult)]))

(define desugared-GetSessionResultInternal
  `(Union (SuccessInternal) (FailureInternal)))

(define desugared-GetSessionInternalType
  `(Union (GetSessionInternal Nat (Addr ,desugared-GetSessionResultInternal))))

(define desugared-GetSessionResultType
  `(Union (ActiveOldSession (Addr ,desugared-SessionCommand))
          (NewSession (Addr ,desugared-Authenticate))))

(define desugared-GetSessionType
  `(Union (GetSession Nat (Addr ,desugared-GetSessionResultType))))

(define desugared-CreateSessionResult
  `(Union (NewSessionInternal Nat)))

(define desugared-server-input-type
  `(Union
    (GetSessionInternal Nat (Addr ,desugared-GetSessionResultInternal))
    (CreateSession String desugared-CreateSessionResult)
    (Ping (Addr SessionResponse))))

(define spawn-server-specification
  (quasiquote
   (spawn-spec (goto ServerReady)
               (define-state (ServerReady)
                 [(variant Ping reply-to) ->
                  (with-outputs ([reply-to (variant Pong)]) (goto ServerReady))]))))

(define spawn-auth-specification
  (quasiquote
    (spawn-spec (goto WaitingForCredentials)
                (define-state (WaitingForCredentials)
                  [(record Authenticate [username *] [password *] [reply-to reply-to]) ->
                   (with-outputs ([reply-to (variant FailedSession)]) (goto Done))]
                  [(record Authenticate [username *] [password *] [reply-to reply-to]) ->
                   (with-outputs ([reply-to (variant ActiveNewSession * ,spawn-server-specification)])
                     (goto Done))])
                (define-state (Done)
                  [(record Authenticate [username *] [password *] [reply-to reply-to]) -> (goto Done)]))))

(define authN-specification
  (quasiquote
   (specification (receptionists [guard ,desugared-GetSessionType]) (externals)
     [guard ,desugared-GetSessionType] ; observed environment interface
     () ; unobserved environment interface
     (define-state (Ready)
       [(variant GetSession * reply-to) ->
        (with-outputs ([reply-to (variant ActiveOldSession ,spawn-server-specification
                                          )])
          (goto Ready))]
       [(variant GetSession * reply-to) ->
        (with-outputs ([reply-to (variant NewSession *;; ,spawn-auth-specification
                                             )])
          (goto Ready))]
       )
     (goto Ready))))

;; ---------------------------------------------------------------------------------------------------
;; Testing code

(module+ test
  (require
   rackunit
   "../desugar.rkt"
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (test-true "Valid type for server input"
    (redex-match? csa-eval τ desugared-server-input-type))

  (test-true "Authenticated session verification"
    (check-conformance (desugar authN-program) authN-specification)))

;; ---------------------------------------------------------------------------------------------------
;; Dynamic tests needed:

;; * create new session, with proper auth
;; * auth fails (bad password)
;; * auth fails (username doesn't exist)
;; * get existing session
;; * fresh auth token for each session
