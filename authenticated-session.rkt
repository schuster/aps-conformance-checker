#lang racket

;; I'm basing this off of slide 41 of this talk:
;; http://www.slideshare.net/rolandkuhn/project-galbma-actors-vs-types

;; To make it interesting and at least partially match the Scalas and Yoshida paper, I'm going to
;; assume there are 3 actors: a front end that manages part of the handshake, a (single) server that
;; responds to commands and manages sessions, and an auth server. I could easily make multiple
;; versions of this, varying that pattern.

;; Main difference from the Scalas and Yoshida version is I skip the (seemingly unnecessary for
;; actors) GetAuthentication step (seems like just a bookkeeping step they need in order to start a
;; new session)

;; TODO: make a second version of this protocol that does *not* lock up the requester (will require
;; implementing the disjoint lemma)

;; TODO: write tests that show difference between the lock and no-lock versions

;; TODO: think about what happens if I allow the front-end to have multiple GetSessionInternal
;; requests in-flight at once. I think at that point verification will break down, because we'd be
;; managing an unbounded number of sessions in one place. We *could* do this by spawning a new worker
;; per request, though, because we don't need to update any state in the front-end (what if we did?
;; Would that be a problem?)

;; The front-end type
(define-variant GetSession
 (GetSession [id Nat] [reply-to (Addr GetSessionResult)]))

(define-variant GetSessionResult
  (ActiveSession [service (Addr SessionCommand)])
  (NewSession [auth (Addr Authenticate)]))

(define-variant SessionCommand
  (Ping [reply-to (Addr SessionResponse)]))

(define-variant SessionResponse
  (Pong))

(define-record Authenticate
  [username String]
  [password String]
  [reply-to (Addr AuthenticateResult)])

(define-variant AuthenticateResult
  (ActiveSession [service (Addr SessionCommand)])
  (FailedSession))

(define-variant GetSessionResultInternal
  (SuccessInternal [service (Addr SessionCommand)])
  (FailureInternal))

(CreateSession [username])
(NewSession [address (Addr Command)])

(define-variant )


;; The server
((Union
  (GetSession [id Nat] [reply-to (Addr GetSessionResult)])
  (SuccessInternal [service (Addr SessionCommand)])
  (FailureInternal))
 (define-state (Ready [auth ???] [server ???]) (m)
   ;; can get GetSession, Succ/Fail auth result, CreateSession, GetAuth
   (case m
     [(GetSession session-id reply-to)
      (send server (GetSessionInternal session-id self))
      (goto WaitingOnServer reply-to auth server)]
     ;; These next two shouldn't happen, so we ignore them
     [(SuccessInternal client-service) (goto Ready auth server)]
     [(FailureInternal) (goto Ready auth server)]))
 (define-state (WaitingOnServer [client (Addr GetSessionResult)]
                                [auth ???]
                                [server ???])
   (m)
   (case m
     [(GetSession session-id reply-to)
      ;; just ignore new requests right now by sending a Busy response
      (send reply-to (Busy))
      (goto WaitingOnServer client auth server)]
     [(SuccessInternal client-service)
      (send client (ActiveSession client-service))
      (goto Ready auth server)]
     [(FailureInternal)
      (send client (NewSession auth))
      (goto Ready auth server)]))
 (goto Ready auth server))



((Union
  (Authenticate [username String] [password String] [reply-to (Addr AuthenticateResult)]))

 ;; Authentication
 (define-state (Running [password-table (Hash String String)]
                        [service (Address ???)])
   (m)
   (case m
     
     [(Authenticate username password reply-to)
      (cond
        [(= (hash-ref password-table username) password)
         (send reply-to (ActiveSession service))]
        [else (send reply-to (FailedSession))])
      (goto Running password-table service)]))
 (define-state (WaitingForSession [password-table (Hash String String)]
                                  [service (Address ???)]
                                  [client (Address AuthenticationResult)])
   (m)
   (case m
     [(Authenticate username password reply-to)
      ;; Should never happen; just ignore it


      ;; NEXT: figure out how to deal with multiple requests floating around at once (might receive
      ;; another authenticate request here...

      
      ])
   ))

;; The app server
(define-state (Running [sessions (Hash Nat Nat)] [next-session-number Nat]) (m)
  (case m
    [(GetSessionInternal id reply-to)
     (cond
       [(hash-has-key? sessions id)
        (send reply-to (Failure))
        (goto Running sessions next-session-number)]
       [else
        (send reply-to (Success ))])
     ]
    [(CreateSession id)]
    [(Ping)])
  
  )

