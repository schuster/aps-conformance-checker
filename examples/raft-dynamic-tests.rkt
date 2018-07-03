#lang racket

;; Run-time tests for Raft, separated into a different file so we can take advantage of pre-comilation
;; (desugaring) for Raft itself.

(require "raft.rkt")

;; ---------------------------------------------------------------------------------------------------
;; Test infrastructure

(module+ test
  (require
   rackunit
   racket/async-channel
   asyncunit
   (only-in csa record variant :)
   csa/eval
   csa/testing)

  (define peer1-id 1)
  (define peer2-id 2)
  (define server-id 0)

  ;; Sleeps for one "tick", i.e. just long enough for the program to process whatever messages it
  ;; currently has and be in a consistent state for new messages from the outside world.
  (define (tick) (sleep 0.11))

  (define (Entry command term index client)
    (record [command command] [term term] [index index] [client client]))

  (define (RaftMember id address)
    (record [id id] [address address]))

  ;; a channel for output we don't care about
  (define junk-id 99)
  (define junk-channel (make-async-channel))
  (define junk-member (RaftMember junk-id junk-channel))

  ;;;; Helpers for constructing/initializing servers

  ;; Abstract the creation of a RaftActor here, for now
  (define (make-RaftActor)
    (make-RaftActor-with-outputs (make-async-channel) (make-async-channel)))

  (define (make-RaftActor-with-outputs timer-manager applications)
    (match-define-values (server _) (csa-run raft-actor-prog timer-manager applications))
    server)

  (define (make-initialized-follower)
    (define timer-manager (make-async-channel))
    (define applications (make-async-channel))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))

    (define server (make-RaftActor-with-outputs timer-manager applications))
    (define server-member (RaftMember server-id server))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    ;; consume message to timer manager on inital transition to Follower
    (define timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
    (list server peer1 peer2 timer-manager applications timeout-id))

  (define (make-peer1-follower-in-term term)
    (match-define (list server peer1 peer2 timer-manager applications timeout-id)
      (make-initialized-follower))
    (async-channel-put server (variant RequestVote term (RaftMember 1 peer1) 0 0))
    (check-unicast-match peer1 _)
    (define new-timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
    (list server peer1 peer2 timer-manager applications new-timeout-id))

  ;; Creates a candidate server for target-term, where target-term must be >= 1. Returns a list of the
  ;; server, peer1, peer2, timer-manager channel, applications channel, and next expected timeout ID
  (define (make-candidate-in-term target-term)
    (match-define (list server peer1 peer2 timer-manager applications timeout-id)
      (make-initialized-follower))
    (define peer1-client (make-async-channel))
    (define peer1-member (RaftMember peer1-id peer1))
    (when (> target-term 1)
      (async-channel-put server (variant AppendEntries (- target-term 1) 0 0 (list) 0 peer1-member peer1-client))
      (check-unicast-match peer1 _)
      ;; AppendEntries resets the timer, so have to grab a new timeout ID
      (set! timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id)))

    (async-channel-put server (variant Timeout timeout-id))
    ;; Consume the RequestVotes to each peer
    (check-unicast-match peer1 _)
    (check-unicast-match peer2 _)
    ;; Consume the timer request
    (define candidate-timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
    (list server peer1 peer2 peer1-client timer-manager applications candidate-timeout-id))

  (define (make-leader-in-term target-term)
    (match-define (list server peer1 peer2 peer1-client timer-manager applications candidate-timeout-id)
      (make-candidate-in-term target-term))
    (async-channel-put server (variant VoteCandidate target-term 1))
    ;; consume the two heartbeat messages, election cancellation, and the heartbeat timer initialization
    (check-unicast-match peer1 heartbeat-message)
    (check-unicast-match peer2 heartbeat-message)
    (check-unicast-match timer-manager (csa-variant CancelTimer "ElectionTimer"))
    (check-unicast-match timer-manager (csa-variant SetTimer "HeartbeatTimer" _ _ _ (csa-variant True)))
    (list server peer1 peer2 peer1-client timer-manager applications candidate-timeout-id))

  (define (get-next-election-timer-id timer-channel)
    (check-unicast-match timer-channel (csa-variant SetTimer "ElectionTimer" _ id _ _) #:result id)))

;; ---------------------------------------------------------------------------------------------------
;; Follower tests

(module+ test
  (test-case "Initial server does not respond to client message"
    (define server (make-RaftActor))
    (define client (make-async-channel))
    (async-channel-put server (variant ClientMessage client "testing"))
    (check-no-message client))

  (test-case "Follower votes and resets election deadline if candidate has later term"
    (match-define (list server peer1 _ timer-manager _ _) (make-initialized-follower))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant RequestVote 1 peer1-member 0 0))
    (check-unicast peer1 (variant VoteCandidate 1 server-id))
    (check-unicast-match timer-manager
                         (csa-variant SetTimer "ElectionTimer" election-timeouts _ _ (csa-variant False))))

  (test-case "Follower declines vote if candidate has earlier term"
    (match-define (list server peer1 peer2 _ _ _) (make-peer1-follower-in-term 2))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant RequestVote 1 peer2-member 1 1))
    (check-unicast peer2 (variant DeclineCandidate 2 server-id)))

  (test-case "Follower votes for at most one candidate per term"
    (match-define (list server _ _ _ _ _) (make-initialized-follower))
    (define candidate1 (make-async-channel))
    (define candidate1-member (RaftMember 3 candidate1))
    (async-channel-put server (variant RequestVote 1 candidate1-member 1 1))
    (check-unicast candidate1 (variant VoteCandidate 1 server-id))
    (define candidate2 (make-async-channel))
    (define candidate2-member (RaftMember 4 candidate2))
    (async-channel-put server (variant RequestVote 1 candidate2-member 1 1))
    (check-unicast candidate2 (variant DeclineCandidate 1 server-id)))

  (test-case "Follower can vote for same candidate multiple times in a term"
    (match-define (list server _ _ _ _ _) (make-initialized-follower))
    (define candidate (make-async-channel))
    (define candidate-member (RaftMember 3 candidate))
    (async-channel-put server (variant RequestVote 1 candidate-member 1 1))
    (check-unicast candidate (variant VoteCandidate 1 server-id))
    (async-channel-put server (variant RequestVote 1 candidate-member 1 1))
    (check-unicast candidate (variant VoteCandidate 1 server-id)))

  (test-case "Followers should check if candidate's log is up to date before granting vote"
    (match-define (list server peer1 peer2 _ timeouts _ timeout-id) (make-leader-in-term 1))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant ClientMessage junk-channel "a"))
    (check-unicast peer1 (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 junk-channel)) 0 server-member server))
    (check-unicast-match peer2 _) ; consume the other append entries
    ;; return to follower state
    (async-channel-put server (variant AppendEntries 2 0 0 (list) 0 peer2-member junk-channel))
    (check-unicast peer2 (variant AppendSuccessful 2 1 server-member))
    (async-channel-put server (variant RequestVote 3 peer1-member 0 0))
    (check-unicast peer1 (variant DeclineCandidate 3 server-id)))

  (test-case "Follower starts an election after timeout"
    (define timer-manager (make-async-channel))
    (define server (make-RaftActor-with-outputs timer-manager (make-async-channel)))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))

    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    ;; NOTE: I assume we async-channel-put a duration to the timer and the timer adds that onto the "now" time,
    ;; instead of the Raft actor getting the "now" time. For testing purposes, we don't want the actor
    ;; under test to have access to things like a clock
    (match-define (list election-timeouts timeout-id)
      (check-unicast-match timer-manager (csa-variant SetTimer "ElectionTimer" election-timeouts timeout-id _ (csa-variant False))
                           #:result (list election-timeouts timeout-id)))
    (async-channel-put election-timeouts (variant Timeout timeout-id))
    (check-unicast-match peer1 (csa-variant RequestVote 1 (== server-member) 0 0))
    (check-unicast-match peer2 (csa-variant RequestVote 1 (== server-member) 0 0))
    (check-unicast-match timer-manager (csa-variant SetTimer "ElectionTimer" _ _ _ (csa-variant False))))

  (test-case "Follower ignores VoteCandidate messages"
    (match-define (list server peer1 _ _ _ _) (make-peer1-follower-in-term 3))
        (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant VoteCandidate 1 peer1-id))
    (tick)
    (async-channel-put server (variant RequestVote 4 peer1-member 3 0))
    (check-unicast peer1 (variant VoteCandidate 4 server-id)))

  (test-case "Follower ignores DeclineCandidate messages"
    (match-define (list server peer1 _ _ _ _) (make-peer1-follower-in-term 3))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant DeclineCandidate 1 peer1-id))
    (tick)
    (async-channel-put server (variant RequestVote 4 peer1-member 3 0))
    (check-unicast peer1 (variant VoteCandidate 4 server-id)))

  (test-case "Follower ignores AppendRejected messages"
    (match-define (list server peer1 _ _ _ _) (make-peer1-follower-in-term 3))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant AppendRejected 1 0 peer1-member))
    (tick)
    (async-channel-put server (variant RequestVote 4 peer1-member 3 0))
    (check-unicast peer1 (variant VoteCandidate 4 server-id)))

  (test-case "Follower ignores AppendSuccessful messages"
    (match-define (list server peer1 _ _ _ _) (make-peer1-follower-in-term 3))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant AppendSuccessful 1 0 peer1-member))
    (tick)
    (async-channel-put server (variant RequestVote 4 peer1-member 3 0))
    (check-unicast peer1 (variant VoteCandidate 4 server-id)))

  (test-case "Follower responds to client with channel for leader"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define peer1-client (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (tick)
    ;; Async-Channel-Put a heartbeat to set the leader
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1-member peer1-client))
    (tick)
    (define client (make-async-channel))
    (async-channel-put server (variant ClientMessage client "a"))
    (check-unicast-match client (csa-variant LeaderIs (csa-variant JustLeader (== peer1-client)))))

  (test-case "Follower responds to heartbeat messaages"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (define client-response (make-async-channel))
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendSuccessful 1 0 server-member)))

  (test-case "Follower should commit each result as it gets new commit index from leader"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (define client-response (make-async-channel))
    (async-channel-put server (variant AppendEntries 1 0 0 (list (Entry "foo" 1 1 client-response)) 0 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendSuccessful 1 1 server-member))
    (async-channel-put server (variant AppendEntries 1 1 1 (list) 1 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendSuccessful 1 1 server-member))
    (check-unicast applications "foo"))

  (test-case "Follower can append and commit a command in one step"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (define client-response (make-async-channel))
    (async-channel-put server (variant AppendEntries 1 0 0 (list (Entry "foo" 1 1 client-response)) 1 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendSuccessful 1 1 server-member))
    (check-unicast applications "foo"))

  (test-case "Follower rejects entries from leaders from previous terms"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 junk-member junk-channel))
    (tick)
    (async-channel-put server (variant AppendEntries 2 0 0 (list) 0 junk-member junk-channel))
    (tick)
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendRejected 2 0 server-member)))

  (test-case "Follower rejects inconsistent updates"
    (define applications (make-async-channel))
    (define server (make-RaftActor-with-outputs (make-async-channel) applications))
    (define peer1 (make-async-channel))
    (define peer2 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant Config (record [members (list peer1-member peer2-member server-member)])))
    (async-channel-put server (variant AppendEntries 3 2 2 (list) 2 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendRejected 3 0 server-member)))

  (test-case "Follower does not update current term if leader is lagging"
    (match-define (list server peer1 peer2 _ _ _) (make-peer1-follower-in-term 3))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    ;; receive AppendEntries from older leader
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer2-member junk-channel))
    (check-unicast peer2 (variant AppendRejected 3 0 server-member))
    ;; check that term is still 3
    (async-channel-put server (variant RequestVote 2 peer2-member 0 0))
    (check-unicast peer2 (variant DeclineCandidate 3 server-id))))

;; ---------------------------------------------------------------------------------------------------
;; candidate tests

(module+ test
  (test-case "Candidate becomes leader on receiving majority of votes"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 2))
    (define server-member (RaftMember server-id server))
    (async-channel-put server (variant VoteCandidate 2 peer1-id))
    (define heartbeat-message
      (variant AppendEntries 2 0 0 (list) 0 server-member server))
    (check-unicast peer1 heartbeat-message)
    (check-unicast peer2 heartbeat-message))

  (test-case "Extra decline vote does not affect election result"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 2))
    (define server-member (RaftMember server-id server))
    (async-channel-put server (variant DeclineCandidate 2 peer2-id))
    (async-channel-put server (variant VoteCandidate 2 peer1-id))
    (define heartbeat-message
      (variant AppendEntries 2 0 0 (list) 0 server-member server))
    (check-unicast peer1 heartbeat-message)
    (check-unicast peer2 heartbeat-message))

  (test-case "Extra AppendEntries responses do not affect election result"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 2))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant AppendRejected 1 0 peer1-member))
    (async-channel-put server (variant AppendSuccessful 1 1 peer1-member))
    (async-channel-put server (variant VoteCandidate 2 peer1-id))
    (define heartbeat-message
      (variant AppendEntries 2 0 0 (list) 0 server-member server))
    (check-unicast peer1 heartbeat-message)
    (check-unicast peer2 heartbeat-message))

  (test-case "Candidate does not win election with votes from old term"
    (match-define (list server peer1 _ _ _ _ _) (make-candidate-in-term 2))
    (async-channel-put server (variant VoteCandidate 1 peer1-id))
    (check-no-message peer1))

  (test-case "Candidate does not win election with multiple votes from same server"
    (define timer-manager (make-async-channel))
    (define server (make-RaftActor-with-outputs timer-manager junk-channel))
    (define peer1 (make-async-channel))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant Config (record [members (list server-member
                                                                     peer1-member
                                                                     (RaftMember 6 junk-channel)
                                                                     (RaftMember 7 junk-channel)
                                                                     (RaftMember 8 junk-channel))])))
    (define timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
    (async-channel-put server (variant Timeout timeout-id))
    (check-unicast-match peer1 (csa-variant RequestVote 1 _ _ _))
    (async-channel-put server (variant VoteCandidate 1 peer1-id))
    (async-channel-put server (variant VoteCandidate 1 peer1-id))
    (check-no-message peer1))

  (test-case "Candidate rejects votes from previous terms"
    (match-define (list server peer1 _ _ _ _ _) (make-candidate-in-term 2))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant RequestVote 1 peer1-member 0 0))
    (check-unicast peer1 (variant DeclineCandidate 2 server-id)))

  (test-case "Candidate rejects votes from current term"
    (match-define (list server peer1 _ _ _ _ _) (make-candidate-in-term 2))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant RequestVote 2 peer1-member 0 0))
    (check-unicast peer1 (variant DeclineCandidate 2 server-id)))

  (test-case "Candidate reverts to follower and grants vote on receiving RequestVotes from newer candidate"
    (match-define (list server peer1 _ _ _ _ _) (make-candidate-in-term 2))
    (define peer1-member (RaftMember peer1-id peer1))
    (async-channel-put server (variant RequestVote 3 peer1-member 0 0))
    (check-unicast peer1 (variant VoteCandidate 3 server-id))
    (tick)
    (async-channel-put server (variant RequestVote 3 peer1-member 0 0))
    (check-unicast peer1 (variant VoteCandidate 3 server-id)))

  (test-case "Candidate reverts to follower on receiving AppendEntries from leader with equal/later term"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 2))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant AppendEntries 3 0 0 (list) 0 peer1-member junk-channel))
    (check-unicast-match peer1 _)
    ;; Test for follower state by seeing if the server grants its vote
    (async-channel-put server (variant RequestVote 4 peer2-member 0 0))
    (check-unicast peer2 (variant VoteCandidate 4 server-id)))

  (test-case "Candidate starts new election after a timeout"
    (match-define (list server peer1 peer2 _ timer-manager _ timeout-id) (make-candidate-in-term 1))
    (define server-member (RaftMember server-id server))
    (async-channel-put server (variant Timeout timeout-id))
    (check-unicast peer1 (variant RequestVote 2 server-member 0 0))
    (check-unicast peer2 (variant RequestVote 2 server-member 0 0))
    (check-unicast-match timer-manager (csa-variant SetTimer _ _ _ _ _)))

  (test-case "Candidate replies to client messages with unknown leader"
    (match-define (list server _ _ _ _ _ _) (make-candidate-in-term 1))
    (define client-response (make-async-channel))
    (async-channel-put server (variant ClientMessage client-response "a"))
    (check-unicast client-response (variant LeaderIs (variant NoLeader))))

  (test-case "DeclineVote for current term does not affect rest of the election"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 1))
    (define server-member (RaftMember server-id server))
    (async-channel-put server (variant DeclineCandidate 1 peer2-id))
    (tick)
    (async-channel-put server (variant VoteCandidate 1 peer1-id))
    (define heartbeat-message
      (variant AppendEntries 1 0 0 (list) 0 server-member server))
    (check-unicast peer1 heartbeat-message)
    (check-unicast peer2 heartbeat-message))

  (test-case "AppendEntries from an earlier leader does not change the state"
    (match-define (list server peer1 peer2 _ _ _ _) (make-candidate-in-term 2))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1-member junk-channel))
    (check-unicast peer1 (variant AppendRejected 2 0 server-member))
    ;; Test for follower state by seeing if the server grants its vote
    (async-channel-put server (variant RequestVote 2 peer2-member 0 0))
    (check-unicast peer2 (variant DeclineCandidate 2 server-id)))

  (test-case "Candidates should check if candidate's log is up to date before granting vote"
    (match-define (list server peer1 peer2 _ timer _ _) (make-leader-in-term 1))
    (define server-member (RaftMember server-id server))
    (define peer1-member (RaftMember peer1-id peer1))
    (define peer2-member (RaftMember peer2-id peer2))
    (check-no-message timer)
    (async-channel-put server  (variant ClientMessage junk-channel "a"))
    (check-unicast peer1 (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 junk-channel)) 0 server-member server))
    (check-no-message timer)
    ;; return to Follower
    (async-channel-put server (variant AppendEntries 2 0 0 (list) 0 peer2-member junk-channel))
    (check-unicast-match peer2 _)
    (check-unicast-match timer _) ; consume the heartbeat cancellation
    (check-unicast-match timer _) ; consume the election reset from step-down
    (define timeout-id (get-next-election-timer-id timer)) ; this is the AppendEntries election reset
    ;; timeout and go to Candidate
    (async-channel-put server (variant Timeout timeout-id))
    (check-unicast peer1 (variant RequestVote 3 server-member 1 1))
    (async-channel-put server (variant RequestVote 4 peer1-member 0 0))
    (check-unicast peer1 (variant DeclineCandidate 4 server-id))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Leader tests

;; (module+ test
;;   (test-case "Leader periodically sends heartbeat"
;;     (match-define (list server peer1 peer2 _ _ _ _) (make-leader-in-term 2))
;;     (async-channel-put server (variant SendHeartbeatTimeouts 1)) ; timeout ID doesn't matter here
;;     (define heartbeat
;;       (variant AppendEntries 2 0 0 (list) 0 server server))
;;     (check-unicast peer1 heartbeat)
;;     (check-unicast peer2 heartbeat))

;;   (test-case "Leader commits entry when replicated to majority of cluster and replies to client"
;;     (match-define (list server peer1 peer2 _ _ applications _) (make-leader-in-term 1))
;;     (define client (make-async-channel))
;;     (async-channel-put server (variant ClientMessage client "a"))
;;     (define append-message
;;       (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 client)) 0 server server))
;;     (check-unicast peer1 append-message)
;;     (check-unicast peer2 append-message)
;;     (async-channel-put server (variant AppendSuccessful 1 1 peer1))
;;     (check-unicast client (variant CommitSuccess "a"))
;;     (check-unicast applications "a"))

;;   (test-case "Leader does not commit previous term messages until replicating a message of its own"
;;     ;; 1. someone else is leader and sends a message
;;     (define client1 (make-async-channel))
;;     (match-define (list server peer1 peer2 timer-manager applications _) (make-peer1-follower-in-term 1))
;;     (async-channel-put server (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 client1)) 0 peer1 junk-channel))
;;     (check-unicast-match peer1 (csa-variant AppendSuccessful _ _ _))
;;     (define timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
;;     ;; 2. timeout and become leader
;;     (async-channel-put server (variant Timeout timeout-id))
;;     (check-unicast peer1 (variant RequestVote 2 server 1 1))
;;     (async-channel-put server (variant VoteCandidate 2 peer1))
;;     ;; 3. async-channel-put heartbeat, check for no commit
;;     (check-unicast peer1 (variant AppendEntries 2 1 1 (list) 0 server server))
;;     (check-no-message applications)
;;     ;; 4. async-channel-put new response (client), check for commit of both after
;;     (define client2 (make-async-channel))
;;     (async-channel-put server (variant ClientMessage client2 "b"))
;;     (check-unicast peer1 (variant AppendEntries 2 1 1 (list (Entry "b" 2 2 client2)) 0 server server))
;;     (async-channel-put server (variant AppendSuccessful 2 2 peer1))
;;     (check-unicast applications "a")
;;     (check-unicast applications "b"))

;;   (test-case "Leader steps down on receiving RequestVote for later term"
;;     (match-define (list server peer1 peer2 _ _ _ _) (make-leader-in-term 1))
;;     (async-channel-put server (variant RequestVote 2 peer1 0 0))
;;     (check-unicast peer1 (variant VoteCandidate 2 server))
;;     (async-channel-put server (variant RequestVote 3 peer2 0 0))
;;     (check-unicast peer2 (variant VoteCandidate 3 server)))

;;   (test-case "Leader responds with current term to RequestVote for earlier term"
;;     (match-define (list server peer1 _ _ _ _ _) (make-leader-in-term 2))
;;     (async-channel-put server (variant RequestVote 1 peer1 0 0))
;;     (check-unicast peer1 (variant DeclineCandidate 2 server)))

;;   (test-case "Leader steps down on receiving AppendEntries for later term"
;;     (match-define (list server peer1 peer2 _ _ _ _) (make-leader-in-term 1))
;;     (async-channel-put server (variant AppendEntries 2 0 0 (list) 0 peer1 junk-channel))
;;     (check-unicast peer1 (variant AppendSuccessful 2 0 server))
;;     (async-channel-put server (variant RequestVote 3 peer2 0 0))
;;     (check-unicast peer2 (variant VoteCandidate 3 server)))

;;   ;; OLD test: would send back entries instead of an AppendRejected, which does not follow the
;;   ;; protocol
;;   ;; (test-case "Leader responds with current term to AppendEntries for earlier term"
;;   ;;   (match-define (list server peer1 _ _ _ _ _) (make-leader-in-term 2))
;;   ;;   (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1 junk-channel))
;;   ;;   (check-unicast peer1 (variant AppendEntries 2 0 0 (list) 0 server server)))

;;   (test-case "Leader responds with current term to AppendEntries for earlier term"
;;     (match-define (list server peer1 _ _ _ _ _) (make-leader-in-term 2))
;;     (async-channel-put server (variant AppendEntries 1 0 0 (list) 0 peer1 junk-channel))
;;     (check-unicast peer1 (variant AppendRejected 2 0 server)))

;;   (test-case "Leader ignores incoming votes"
;;     (match-define (list server peer1 peer2 _ _ _ _) (make-leader-in-term 1))
;;     (async-channel-put server (variant VoteCandidate 1 peer1))
;;     (async-channel-put server (variant DeclineCandidate 1 peer2))
;;     (tick)

;;     (define client (make-async-channel))
;;     (async-channel-put server (variant ClientMessage client "a"))
;;     (define append-message
;;       (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 client)) 0 server server))
;;     (check-unicast peer1 append-message)
;;     (check-unicast peer2 append-message))

;;   (test-case "Leader responds to rejected append with a previous log entry"
;;     ;; 1. As a follower, receive 5 entries
;;     (match-define (list server peer1 peer2 timer-manager _ _) (make-peer1-follower-in-term 1))
;;     (define entries (list (Entry "a" 1 1 junk-channel)
;;                                       (Entry "b" 1 2 junk-channel)
;;                                       (Entry "c" 1 3 junk-channel)
;;                                       (Entry "d" 1 4 junk-channel)
;;                                       (Entry "e" 1 5 junk-channel)))
;;     (async-channel-put server
;;           (variant AppendEntries 1 0 0 entries 0 peer1 junk-channel))
;;     ;; 2. Timeout and become leader
;;     (define timeout-id (check-unicast-match timer-manager (csa-variant SetTimer _ _ id _ _) #:result id))
;;     (async-channel-put server (variant Timeout timeout-id))
;;     (check-unicast peer2 (variant RequestVote 2 server 1 5))
;;     (async-channel-put server (variant VoteCandidate 2 peer1))
;;     (check-unicast-match peer2 (csa-variant AppendEntries _ _ _ _ _ _ _)) ; initial heartbeat
;;     ;; 3. Receive a client message and broadcast AppendEntries at log index 6
;;     (async-channel-put server (variant ClientMessage junk-channel "f"))
;;     (check-unicast peer2 (variant AppendEntries 2 1 5 (list (Entry "f" 2 6 junk-channel)) 0 server server))
;;     ;; 4. Receive rejection, async-channel-put AppendEntries to peer2 with indices 1-5
;;     (async-channel-put server (variant AppendRejected 2 0 peer2))
;;     (check-unicast peer2 (variant AppendEntries 2 0 0 entries 0 server server)))

;;   (test-case "Leaders should check if candidate's log is up to date before granting vote"
;;     (match-define (list server peer1 peer2 _ timeouts _ timeout-id) (make-leader-in-term 1))
;;     (async-channel-put server  (variant ClientMessage junk-channel "a"))
;;     (check-unicast peer1 (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 junk-channel)) 0 server server))
;;     (async-channel-put server (variant RequestVote 2 peer1 0 0))
;;     (check-unicast peer1 (variant DeclineCandidate 2 server)))

;;   (test-case "Leader steps down after RequestVote with newer term but older log"
;;     (match-define (list server peer1 peer2 _ timeouts _ timeout-id) (make-leader-in-term 1))
;;     (async-channel-put server  (variant ClientMessage junk-channel "a"))
;;     (check-unicast peer1 (variant AppendEntries 1 0 0 (list (Entry "a" 1 1 junk-channel)) 0 server server))
;;     (async-channel-put server (variant RequestVote 2 peer1 0 0))
;;     (check-unicast peer1 (variant DeclineCandidate 2 server))
;;     (define client (make-async-channel))
;;     (async-channel-put server  (variant ClientMessage client "a"))
;;     (check-unicast client (variant LeaderIs (variant NoLeader)))))
