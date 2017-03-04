#lang racket

;; A simple IRC-like chat server implementation

;; Because address comparison is not allowed, we include the username in many messages that would
;; normally rely on the address for user identity. We assume for the sake of this example that the
;; user never tries to spoof someone eles.

(provide
 chat-program
 chat-spec)

(require
 "../desugar.rkt")

(define chat-program (desugar (quote

(program (receptionists [auth AuthCommand]) (externals)
  (define-constant pw-table (hash ["joe" "abc"] ["sally" "xyz"] ["john" "def"]))

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
    (GetRoomList [callback (Addr (Listof String))]))

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
    (ChatRoom [name String])
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
              (for/fold ([dummy 0])
                        ([remaining-user (hash-values remaining-users)])
                (send remaining-user (MemberLeft username))
                0)
              (goto Running remaining-users))]
           [else (goto Running users)])]
        [(GetMembers callback)
         (send callback (hash-keys users))
         (goto Running users)])))

  (define-actor ChatServerInput
    (ChatServer)
    ()
    (goto Always (hash))
    (define-state (Always [rooms (Hash String (Addr RoomCommand))]) (m)
      (case m
        [(JoinRoom room-name username user)
         (case (hash-ref rooms room-name)
           [(Nothing)
            (let ([new-room (spawn new-room ChatRoom room-name)])
              (send new-room (UserJoining username user))
              (goto Always (hash-set rooms room-name new-room)))]
           [(Just room)
            (send room (UserJoining username user))
            (goto Always rooms)])]
        [(GetRoomList callback)
         (send callback (hash-keys rooms))
         (goto Always rooms)])))

  (actors [server (spawn server ChatServer)]
          [auth (spawn auth Authenticator pw-table server)])))))

(module+ test
  (require
   racket/async-channel
   (only-in csa record variant :)
   csa/eval
   csa/testing
   rackunit
   asyncunit
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (define (start-prog)
    (csa-run chat-program))

  (define (connect-to-server auth username password)
    (define auth-callback (make-async-channel))
    (async-channel-put auth (variant LogIn "joe" "abc" auth-callback))
    (match (async-channel-get auth-callback) [(csa-variant AuthenticationSucceeded server) server]))

  (define (join-room server room-name username)
    (define room-handler (make-async-channel))
    (async-channel-put server (variant JoinRoom room-name username room-handler))
    (match (async-channel-get room-handler)
      [(csa-variant JoinedRoom room) (list room room-handler)])))

(module+ test
  (test-case "User for auth does not exist"
    (define auth (start-prog))
    (define auth-callback (make-async-channel))
    (async-channel-put auth (variant LogIn "bob" "123" auth-callback))
    (check-unicast auth-callback (variant AuthenticationFailed)))

  (test-case "Wrong password"
    (define auth (start-prog))
    (define auth-callback (make-async-channel))
    (async-channel-put auth (variant LogIn "joe" "123" auth-callback))
    (check-unicast auth-callback (variant AuthenticationFailed)))

  (test-case "Right auth can log in, server responds to queries"
    (define auth (start-prog))
    (define auth-callback (make-async-channel))
    (async-channel-put auth (variant LogIn "joe" "abc" auth-callback))
    (define server(check-unicast-match auth-callback
                                       (csa-variant AuthenticationSucceeded server)
                                       #:result server))
    (define room-list-callback (make-async-channel))
    (async-channel-put server (variant GetRoomList room-list-callback))
    (check-unicast room-list-callback null))

  (test-case "Can join new room, new room is reflected in room list, message to room is echoed"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (define room-handler (make-async-channel))
    (async-channel-put server (variant JoinRoom "my-room" "joe" room-handler))
    (define room (check-unicast-match room-handler (csa-variant JoinedRoom room) #:result room))
    (define room-list-callback (make-async-channel))
    (async-channel-put server (variant GetRoomList room-list-callback))
    (check-unicast room-list-callback (list "my-room"))
    (async-channel-put room (variant Speak "joe" "hello"))
    (check-unicast room-handler (variant Message "joe" "hello")))

  (test-case "Notify others when a user joins and leaves a room"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (match-define (list room joe-room-handler) (join-room server "my-room" "joe"))
    (match-define (list _ sally-room-handler) (join-room server "my-room" "sally"))
    (check-unicast joe-room-handler (variant MemberJoined "sally"))
    (async-channel-put room (variant Leave "joe"))
    (check-unicast sally-room-handler (variant MemberLeft "joe")))

  (test-case "Do not receive messages after leaving room"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (match-define (list room joe-room-handler) (join-room server "my-room" "joe"))
    (match-define (list _ sally-room-handler) (join-room server "my-room" "sally"))
    (async-channel-put room (variant Leave "joe"))
    (async-channel-get sally-room-handler) ; swallow the "Joe left" notification
    (async-channel-put room (variant Speak "sally" "hello"))
    (check-unicast sally-room-handler (variant Message "sally" "hello"))
    (async-channel-get joe-room-handler) ; swallow the "Sally joined" notification
    (check-no-message joe-room-handler))

  (test-case "Sent message broadcast to all users in room"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (match-define (list room joe-room-handler) (join-room server "my-room" "joe"))
    (match-define (list _ sally-room-handler) (join-room server "my-room" "sally"))
    (match-define (list _ john-room-handler) (join-room server "my-room" "john"))
    ;; eat the join notifications
    (async-channel-get joe-room-handler)
    (async-channel-get joe-room-handler)
    (async-channel-get sally-room-handler)

    (async-channel-put room (variant Speak "joe" "hello"))
    (check-unicast joe-room-handler (variant Message "joe" "hello"))
    (check-unicast sally-room-handler (variant Message "joe" "hello"))
    (check-unicast john-room-handler (variant Message "joe" "hello")))

  (test-case "Room updates membership list as users join/leave"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (match-define (list room joe-room-handler) (join-room server "my-room" "joe"))
    (define member-callback (make-async-channel))
    (async-channel-put room (variant GetMembers member-callback))
    (check-unicast member-callback (list "joe"))
    (match-define (list _ sally-room-handler) (join-room server "my-room" "sally"))
    (match-define (list _ john-room-handler) (join-room server "my-room" "john"))
    (async-channel-put room (variant GetMembers member-callback))
    (check-unicast-match member-callback
                         new-members
                         #:result (check-equal? (list->set new-members) (set "joe" "sally" "john")))
    (async-channel-put room (variant Leave "joe"))
    (async-channel-put room (variant GetMembers member-callback))
    (check-unicast-match member-callback
                         new-members
                         #:result (check-equal? (list->set new-members) (set "sally" "john"))))

  (test-case "Messages are isolated within a single room"
    (define auth (start-prog))
    (define server (connect-to-server auth "joe" "abc"))
    (match-define (list room1 joe-room1-handler) (join-room server "room1" "joe"))
    (match-define (list _ sally-room1-handler) (join-room server "room1" "sally"))
    (match-define (list _ sally-room2-handler) (join-room server "room2" "sally"))
    (match-define (list _ john-room2-handler) (join-room server "room2" "john"))

    ;; swallow the various joined notifications
    (async-channel-get joe-room1-handler)
    (async-channel-get sally-room2-handler)

    ;; check the message recipients
    (async-channel-put room1 (variant Speak "joe" "hello"))
    (check-unicast joe-room1-handler (variant Message "joe" "hello"))
    (check-unicast sally-room1-handler (variant Message "joe" "hello"))
    (check-no-message sally-room2-handler)
    (check-no-message john-room2-handler)))

;; ---------------------------------------------------------------------------------------------------
;; Specification

(define desugared-room-command
  `(Union
    (Speak String String)
    (Leave String)
    (GetMembers (Addr (Listof String)))))

(define desugared-room-event
  `(Union
    (JoinedRoom (Addr ,desugared-room-command))
    (MemberLeft String)
    (MemberJoined String)
    (Message String String)))

(define desugared-server-command
  `(Union
    (JoinRoom String String (Addr ,desugared-room-event))
    (GetRoomList (Addr (Listof String)))))

(define desugared-login-response
  `(Union (AuthenticationFailed)
          (AuthenticationSucceeded (Addr ,desugared-server-command))))

(define desugared-auth-command
  `(Union (LogIn String String (Addr ,desugared-login-response))))

(define (room-spec-behavior handler)
  `((goto Running ,handler)
    ;; Because the observer could cause *any* member to leave, not just itself, the checker can't
    ;; prove that no messages will be sent to the handler after the Leave message is
    ;; sent.
    (define-state (Running room-handler)
      [(variant Speak * *) -> () (goto Running room-handler)]
      [(variant Leave *) -> () (goto Running room-handler)]
      [(variant GetMembers callback) -> ([obligation callback *]) (goto Running room-handler)]
      [unobs -> ([obligation room-handler (variant MemberLeft *)]) (goto Running room-handler)]
      [unobs -> ([obligation room-handler (variant MemberJoined *)]) (goto Running room-handler)]
      [unobs -> ([obligation room-handler (variant Message * *)]) (goto Running room-handler)])))

(define server-spec-behavior
  `((goto ServerAlways)
    (define-state (ServerAlways)
      [(variant GetRoomList callback) -> ([obligation callback *]) (goto ServerAlways)]
      [(variant JoinRoom * * handler) ->
       ([obligation handler (variant JoinedRoom (fork ,@(room-spec-behavior 'handler)))])
       (goto ServerAlways)])))

(define chat-spec
  `(specification (receptionists [auth ,desugared-auth-command]) (externals)
     ([auth ,desugared-auth-command])
     ([auth ,desugared-auth-command])
     (goto AuthAlways)
     (define-state (AuthAlways)
       [(variant LogIn * * callback) ->
        ([obligation callback (or (variant AuthenticationFailed)
                                  (variant AuthenticationSucceeded (fork ,@server-spec-behavior)))])
        (goto AuthAlways)])))

(module+ test
  ;; Specification conformance tests
  (check-true (redex-match? csa-eval τ desugared-room-command))
  (check-true (redex-match? csa-eval τ desugared-room-event))
  (check-true (redex-match? csa-eval τ desugared-server-command))
  (check-true (redex-match? csa-eval τ desugared-login-response))

  (test-true "Valid type for auth input"
    (redex-match? csa-eval τ desugared-auth-command))

  (test-true "Chat server conforms to its spec"
    (check-conformance chat-program chat-spec)))
