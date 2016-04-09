#lang racket

;; I'm basing this off of slide 41 of this talk:
;; http://www.slideshare.net/rolandkuhn/project-galbma-actors-vs-types

;; To make this sensible, I'm assuming that each GetSession starts a new handshake session, so that
;; the front-end is always available for new GetSession requests (and therefore doesn't need, e.g., a
;; busy signal). Otherwise, if only a single actor is used for each, multiple authentication requests
;; can land at the same authentication actor without further information about which session they
;; refer to (assuming we don't update the requests with extra session info).

;; I think this method generally makes sense, because it's useful to have a separate actor to manage
;; each session's state machine, rather than awkwardly maintaining that information in a table.

;; TODO: maybe make a second version of this protocol that locks up the requester (will require some
;; new tests to show the difference in the protocol)

;; TODO: figure out whether to use session IDs (unclear how Kuhn's slides expect to work without ID:
;; match actor ID?). Maybe just use ints, with the understanding that someone without a session
;; provides the special session ID 0

(define-variant SessionResponse
  (Pong))

(define-variant SessionCommand
  (Ping [reply-to (Addr SessionResponse)]))

(define-variant AuthenticateResult
  (ActiveSession [session-id Nat] [service (Addr SessionCommand)])
  (FailedSession))

(define-record Authenticate
  [username String]
  [password String]
  [reply-to (Addr AuthenticateResult)])

(define-variant GetSessionResultInternal
  (SuccessInternal)
  (FailureInternal))

(define-variant GetSessionInternalType
  (GetSessionInternal [id Nat] [reply-to (Addr GetSessionResultInternal)]))

(define-variant GetSessionResult
  (ActiveSession [session-id Nat] [service (Addr SessionCommand)])
  (NewSession [auth (Addr Authenticate)]))

(define-variant GetSessionType
 (GetSession [id Nat] [reply-to (Addr GetSessionResult)]))

(define-variant CreateSessionResult
  (NewSessionInternal [session-id Nat]))

(define-variant CreateVariant
  (CreateSession [username String] [reply-to (CreateSessionResult)]))

(define-type HandshakeWorkerInput
  (Union (SuccessInternal)
         (FailureInternal)
         (NewSessionInternal [session-id Nat])))

(define-type ServerInput
  (Union
    (GetSessionInternal [id Nat] [reply-to (Addr GetSessionResultInternal)])
    (CreateSession [username String] [reply-to (CreateSessionResult)])
    (Ping [reply-to (Addr SessionResponse)])))

;; ---------------------------------------------------------------------------------------------------

(define-actor HandshakeWorkerInput
  (HandshakeWorker [session-id Nat]
                   [client (Addr GetSessionResult)]
                   [server (Addr ServerInput)]
                   [password-table (Hash String String)])
  ;; TODO: try writing this in a different way where each stage gets a new actor, so as to avoid lots
  ;; of the "this should never happen" messages

  ;; IDEA: with some sort of linear type system, we could do a lightweight typestate-like thing that
  ;; allows us to ignore certain messages once they've been received (because we know the only channel
  ;; for them was already used). Doesn't work in presence of dropped messages, though.
  (define-state (WaitingForMaybeSession) (m)
    (case m
      [(SuccessInternal)
       (send client (ActiveSession session-id client-service))
       (goto Done)]
      [(FailureInternal)
       (send client (NewSession self))
       (goto WaitingForCredentials)]
      ;; The rest of these shouldn't happen right now
      [(Authenticate u p r) (goto WaitingForMaybeSession)]
      [(NewSessionInternal id) (goto WaitingForMaybeSession)]))
  (define-state (WaitingForCredentials) (m)
    (case m
      [(Authenticate username password reply-to)
       (case (hash-ref password-table username)
         [(Nothing)
          (send reply-to (Failure))
          (goto Done)]
         [(Just found-password)
          (cond
            [(= password found-password)
             (send server (CreateSession session-id))
             (goto (WaitingForCredentials))]
            [else
             (send reply-to (Failure))
             (goto Done)])])]
      ;; These next three shouldn't happen at this point; ignore the message
      [(SuccessInternal) (goto WaitingForCredentials)]
      [(FailureInternal) (goto WaitingForCredentials)]
      [(NewSessionInternal session-id) (goto WaitingForCredentials)]))
  (define-state (WaitingForServer) (m)
    (case m
      [(NewSessionInternal session-id client-service)
       (send client (ActiveSession session-id client-service))
       (goto Done)]
      ;; None of these should happen right now
      [(SuccessInternal) (goto WaitingForServer)]
      [(FailureInternal) (goto WaitingForServer)]
      [(Authenticate u p r) (goto WaitingForServer)]))
  (define-state (Done) (m) (goto Done))
  ;; init:
  (begin
    ;; Hmm... this is a case where actors aren't a great choice, and you want something more
    ;; lightweight like sessions that more directly expresses the protocol/usage: just want to
    ;; send/receive exactly once, for several messages in this sequence
    (send server (GetSessionInternal session-id self))
    (goto WaitingForMaybeSession)))

(define-actor GetSessionType
  (ServiceGuard [server (Addr ServerInput)] [password-table (Hash String String)])
  (define-state (Ready) (m)
    (case m
      [(GetSession session-id reply-to)
       (spawn HandshakeWorker session-id reply-to server password-table)
       (goto Ready)]))
  (goto Ready))

(define-actor ServerInput
  (Server)
  (define-state (Running [sessions (Hash Nat Nat)] [next-session-id Nat]) (m)
    (case m
      [(GetSessionInternal id reply-to)
       (cond
         [(hash-has-key? sessions id)
          (send reply-to (FailureInternal))]
         [else (send reply-to (SuccessInternal))])
       (goto Running sessions next-session-id)]
      [(CreateSession username)
       (let ([id next-session-id]
             [next-session-id (+ 1 next-session-id)])
         (send reply-to (NewSessionInternal id))
         (goto Running (hash-set sessions id 1) next-session-id))]
      [(Ping reply-to)
       (send reply-to (Pong))
       (goto Running sessions next-session-id)]))
  (goto Running (hash) 0))

(let* ([empty-pw-table (hash)]
       [pw-table (hash-set (hash-set pw-table "joe" "abc") "sally" "xyz")]
       [server (spawn Server)])
  (spawn Guard server pw-table))
