#lang racket

;; A simple IRC-like chat server implementation

;; Because address comparison is not allowed, we include the username in many messages that would
;; normally rely on the address for user identity. We assume for the sake of this example that the
;; user never tries to spoof someone eles.

(define chat-program (quote

(program (receptionists [auth AuthCommand]) (externals)
  (define-constant pw-table (hash ["joe" "abc"] ["sally" "xyz"]))

  (define-type RoomCommand
    (Union
     (Speak String String)
     (Leave String)
     (GetMembers (Addr (Listof String)))))

  (define-variant RoomEvent
    (JoinedRoom [room (Addr RoomCommand)])
    (MemberLeft [username String])
    (MemberJoined [username String])
    (Message [username String] [message String]))

  (define-type ServerCommand
    (Union
     (JoinRoom String String (Addr RoomEvent))
     (GetRoomList (Addr (Listof String)))))

  (define-variant LogInResponse
    (AuthenticationFailed)
    (AuthenticationSucceeded [server (Addr ServerCommand)]))

  (define-variant AuthCommand
    (LogIn [username String] [password String] [callback (Addr LogInResponse)]))

  (define-variant ChatServerInput
    (JoinRoom [room-name String] [username String] [user (Addr RoomEvent)])
    (GetRoomList [callback (Addr (Listof String))])
    (RoomClosed [name String]))

  (define-variant ChatRoomInput
    (UserJoining [name String] [address (Addr RoomEvent)])
    (Speak [name String] [message String])
    (Leave [name String])
    (GetMembers [callback (Addr (Listof String))]))

  (define-actor AuthCommand
    (Authenticator [pw-table (Hash String String)] [server (Addr ServerCommand)])
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

  (define-actor ChatRoomInput
    (ChatRoom [name String] [server (Addr (Union (RoomClosed String)))])
    ()
    (goto Running (hash))
    (define-state (Running [users (Hash String (Addr RoomEvent))]) (m)
      (case m
        [(UserJoining username user)
         (send user (JoinedRoom self))
         (for/fold ([dummy 0])
                   ([other-user (hash-values users)])
           (send other-user (MemberJoined username))
           0)
         (goto Running (hash-set users username user))]
        [(Speak speaker-name message)
         (for/fold ([dummy 0])
                   ([user (hash-values users)])
           (send user (Message speaker-name message))
           0)
         (goto Running users)]
        [(Leave username)
         (cond
           [(hash-has-key? users username)
            (let ([remaining-users (hash-remove users username)])
              (cond
                [(hash-empty? remaining-users)
                 (send server (RoomClosed name))
                 (goto Done)]
                [else
                 (for/fold ([dummy 0])
                           ([remaining-user (hash-values remaining-users)])
                   (send remaining-user (MemberLeft username))
                   0)
                 (goto Running remaining-users)]))]
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
        [(JoinRoom room-name username user)
         (case (hash-ref rooms room-name)
           [(Nothing)
            (let ([new-room (spawn new-room ChatRoom name self)])
              (send new-room (UserJoining username user))
              (goto Always (hash-set rooms room-name new-room)))]
           [(Just room)
            (send new-room (UserJoining username user))
            (goto Always rooms)])]
        [(GetRoomList callback)
         (send callback (hash-keys rooms))
         (goto Always rooms)]
        [(RoomClosed room-name)
         (case (hash-ref rooms room-name)
           [(Nothing) (goto Always rooms)]
           [(Just r)
            (goto Always (hash-remove rooms room-name))])])))

  (actors [server (spawn server ChatServer)]
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
