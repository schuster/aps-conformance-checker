#lang racket

;; A simple IRC-like chat server implementation

;; Because address comparison is not allowed, we include the username in many messages that would
;; normally rely on the address for user identity. We assume for the sake of this example that the
;; user never tries to spoof someone eles.

(define chat-program (quote

(program (receptionists [auth AuthCommand]) (externals)
  (define-constant pw-table (hash ["joe" "abc"] ["sally" "xyz"]))
  (define-variant LogInResponse
    (AuthenticationFailed)
    (AuthenticationSucceeded [server (Addr ServerCommand)]))
  (define-variant AuthCommand
    (LogIn [username String] [password String] [callback (Addr LogInResponse)]))

  (define-actor AuthCommand
    Authenticator
    ()
    (goto Always)
    (define-state (Always) (m)
      (case m
        [(LogIn username password callback)
         (case (hash-ref pw-table username)
           [(Nothing)
            (send callback (AuthenticationFailed))
            (goto Always)]
           [(Just found-password)
            (cond
              [(= password found-password)
               (send callback (AuthenticationSucceeded server))]
              [else
               (send callback (AuthenticationFailed))])
            (goto Always)])])))

  (define-variant RoomEvent
    [(JoinedRoom (Addr (Union [Speak String])))]
    [(Message )])
  (define-variant ChatServerInput
    ;; TODO: join room, get room list, get room-done notification
    [JoinRoom [name String] [user (Addr RoomEvent)]]
    [GetRoomList [callback (Addr (Listof String))]])

  ;; room commands: speak, leave, get members

  ;; TODO: what about prefixing names onto messages? Without address comparison, this is hard

  ;; TODO: hmm, lack of "hash-keys" makes returning a room list tricky, but adding hash-keys would
  ;; change a *lot* of my abstract interpretation

  (define-variant ChatRoomInput
    (UserJoining [name String] [address (Addr RoomEvent)])
    (Speak [name String] [message String])
    (Leave [name String])
    (GetMembers [callback (Addr (Listof String))]))

  (define-actor ChatRoomInput
    (ChatRoom [name String] [server (Addr (Union (RoomClosed String)))])
    ()
    (goto Running (list))
    (define-state (Running [users (Hash String (Addr RoomEvent))]) (m)
      (case m
        [(UserJoining username user)
         (send user (JoinedRoom self))
         (goto Running (cons user users))]
        [(Speak message)
         (for/fold ([dummy 0])
                   ([user users])
           (send user (Message message))
           0)
         (goto Running users)]
        [(Leave username)
         (cond
           [(hash-has-key? users username)
            (cond
              [(hash-empty? users)
               (send server (RoomClosed name))
               (goto Done)]
              [else (goto Running (hash-remove users))])]
           [else (goto Running users)])]
        [(GetMembers callback)
         (send callback (hash-keys users))
         (goto Running users)]))
    (define-state (Done) (m) (goto Done)))

  (define-actor ChatServerInput
    (ChatServer)
    ()
    (goto Always (hash))
    (define-state (Always [rooms (Hash String (Addr RoomCommand))]) (m)
      (case m
        [(JoinRoom room-name user)
         (case (hash-ref rooms room-name)
           [(Nothing)
            (let ([new-room (spawn new-room Room name)])
              (send new-room (UserJoining user)))]
           [(Just room)
            (send new-room (UserJoining user))])]
        [(GetRoomList callback)
         (send callback (hash-keys rooms))
         (goto Always rooms)]
        [(RoomClosed room-name)
         (case (hash-ref rooms room-name)
           [(Nothing) (goto Always rooms)]
           [(Just r)
            (goto Always (hash-remove rooms room-name))])])))

  (actors  [server (spawn server ChatServer)]
           [auth (spawn auth Authenticator pw-table server)]))))

(module+ test
  (require
   racket/async-channel
   csa/eval
   rackunit
   asyncunit
   "../desugar.rkt"
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (define desugared-program (desugar chat-program)))
