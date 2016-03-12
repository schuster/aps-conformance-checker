#lang racket

;; A full test of the Raft port to CSA, verified against its spec

(require
 rackunit
 redex/reduction-semantics
 "aps.rkt"
 "csa.rkt"
 "desugar.rkt"
 "main.rkt")

;; TODO: put this in a common place so it isn't repeated across files
(define single-agent-concrete-addr (term (addr 0)))

;; 0. Define the spec
(define raft-spec
  (term
   (((define-state (Init)
       [* -> (goto Init)])
     ;; (define-state (Follower)
     ;;   [(RequestVote _ candidate _ _) -> ]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     ;; (define-state (Candidate)
     ;;   [(RequestVote _ candidate _ _) -> ???]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     ;; (define-state (Leader)
     ;;   [(RequestVote _ candidate _ _) -> ???]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     )
    (goto Init)
    ,single-agent-concrete-addr)))

(check-not-false (redex-match aps-eval z raft-spec))

;; 1. Define Raft in the basic syntax
(define raft-actor-surface-def
  ;; Client message contains a command (string) to print when applying to the state machine, and a
;; channel to send to to confirm the application
;; (define-variant-type ClientMessage
;;   (ClientMessage [client (Channel ClientResponse)] [cmd String]))

;; (define-variant-type ClientResponse
;;   (LeaderIs [leader MaybeLeader])
;;   (CommitSuccess [cmd String]))

;; (define-variant-type MaybeLeader
;;   (NoLeader)
;;   (JustLeader [leader (Channel ClientMessage)]))

;; (define-record-type ClusterConfiguration
;;   [members (Listof (Channel RaftMessage))]
;;   ;; ignoring other config fields for now, since I'm not implementing configuration changes
;;   )

;; (define-record-type Entry
;;   [command String]
;;   [term Nat]
;;   [index Nat]
;;   [client (Channel String)])

;; (define-variant-type RaftMessage
;;   (RequestVote
;;    [term Nat]
;;    [candidate (Channel RaftMessage)]
;;    [last-log-term Nat]
;;    [last-log-index Nat])
;;   (VoteCandidate
;;    [term Nat]
;;    [follower (Channel RaftMessage)])
;;   (DeclineCandidate
;;    [term Term]
;;    [follower (Channel RaftMessage)])
;;   (AppendEntries
;;    [term Nat]
;;    [prev-log-term Nat]
;;    [prev-log-index Nat]
;;    [entries (Vectorof Entry)]
;;    [leader-commit-id Nat]
;;    [leader (Channel RaftMessage)]
;;    [leader-client (Channel ClientMessage)])
;;   ;; A note on last-index: In the paper, this is the optimization at the bottom of p. 7 that allows
;;   ;; for quicker recovery of a node that has fallen behind in its log. In RaftScope, they call this
;;   ;; "matchIndex", which indicates the lat index in the log (or 0 for AppendRejected). In akka-raft,
;;   ;; this is always the last index of the log (for both success and failure)
;;   (AppendRejected
;;    [term Nat]
;;    [last-index Nat]
;;    [member (Channel RaftMessage)])
;;   (AppendSuccessful
;;    [term Nat]
;;    [last-index Nat]
;;    [member (Channel RaftMessage)]))

;; (define-variant-type MaybePeer
;;   (NoPeer)
;;   (JustPeer [peer (Channel RaftMessage)]))

;; (define-record-type StateMetadata
;;   [current-term Nat]
;;   [votes (Hash Nat (Channel RaftMessage))]
;;   [last-used-timeout-id Nat])

;; (define-record-type ElectionMeta
;;   [current-term Nat]
;;   [votes-received (Hash (Channel RaftMessage) Bool)]
;;   [votes (Hash Nat (Channel RaftMessage))]
;;   [last-used-timeout-id Nat])

;; (define-record-type LeaderMeta
;;   [current-term Nat]
;;   [last-used-timeout-id Nat])

;; (define-variant-type TimerMessage
;;   (SetTimer [timer-name String] [target (Channel)] [id Nat] [duration Duration] [repeat? Boolean])
;;   (CancelTimer [timer-name String]))

;; (define-record-type AppendResult
;;   [message RaftMessage]
;;   [log ReplicatedLog])

;; (define-record-type ReplicatedLog
;;   [entries (Vectorof Entry)]
;;   [committed-index Int])

  (term
   (define-actor Nat (RaftActor)
     ;; (in: [client-messages ClientMessage]
     ;;      [peer-messages RaftMessage]
     ;;      [configs ClusterConfiguration]
     ;;      [timeouts Nat]
     ;;      [begin-election-alerts]
     ;;      [elected-as-leader]
     ;;      [send-heartbeat-timeouts Nat])
     ;; (out: [timer-manager TimerMessage]
     ;;       [application String]) ; the server sends a command here when it is applied

     () ; the functions go here
     (goto Init)

     (define-state (Init) (m)
       (goto Init)

       ;; [configs (config)
       ;;          (let ([metadata (reset-election-deadline/follower timer-manager timeouts (initial-metadata))])
       ;;            (next-state (Follower (NoLeader)
       ;;                                  metadata
       ;;                                  (replicated-log-empty)
       ;;                                  config)))]
       )

     ;; (define-state (Follower [recently-contacted-by-leader MaybeLeader]
     ;;                         [metadata StateMetadata]
     ;;                         [replicated-log ReplicatedLog]
     ;;                         [config ClusterConfiguration])
     ;;   [client-messages (m)
     ;;                    (case m
     ;;                      [ClientMessage (client command)
     ;;                                     (send client (LeaderIs recently-contacted-by-leader))
     ;;                                     (next-state (Follower recently-contacted-by-leader metadata replicated-log config))])]
     ;;   [peer-messages (m)
     ;;                  (case m
     ;;                    [RequestVote (term candidate last-term last-index)
     ;;                                 (cond
     ;;                                   [(grant-vote?/follower metadata replicated-log term candidate last-term last-index)
     ;;                                    (send candidate (VoteCandidate term peer-messages))
     ;;                                    ;; NOTE: akka-raft did not update the term here, which I think is a bug
     ;;                                    (let ([metadata (reset-election-deadline/follower timer-manager timeouts metadata)])
     ;;                                      (next-state (Follower recently-contacted-by-leader
     ;;                                                            (! (with-vote metadata term candidate) [current-term term])
     ;;                                                            replicated-log
     ;;                                                            config)))]
     ;;                                   [else
     ;;                                    (let ([metadata (! metadata [current-term (max term (: metadata current-term))])])
     ;;                                      (send candidate (DeclineCandidate (: metadata current-term) peer-messages))
     ;;                                      ;; TODO: change this to goto-this-state, once I reimplement/find that
     ;;                                      (next-state (Follower recently-contacted-by-leader metadata replicated-log config)))])]
     ;;                    [VoteCandidate (t f)
     ;;                                   (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;                    [DeclineCandidate (t f)
     ;;                                      (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;                    [AppendEntries (term prev-term prev-index entries leader-commit-id leader leader-client)
     ;;                                   (let ([recently-contacted-by-leader (JustLeader leader-client)])
     ;;                                     (append-entries term
     ;;                                                     prev-term
     ;;                                                     prev-index
     ;;                                                     entries
     ;;                                                     leader-commit-id
     ;;                                                     leader
     ;;                                                     metadata
     ;;                                                     replicated-log
     ;;                                                     config
     ;;                                                     recently-contacted-by-leader))]
     ;;                    [AppendRejected (t l m)
     ;;                                    (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;                    [AppendSuccessful (t l m)
     ;;                                      (next-state (Follower recently-contacted-by-leader metadata replicated-log config))])]
     ;;   [configs (c) (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;   [timeouts (id)
     ;;             (cond
     ;;               [(= id (: metadata last-used-timeout-id))
     ;;                (begin-election timer-manager timeouts metadata replicated-log config begin-election-alerts)]
     ;;               [else (next-state (Follower recently-contacted-by-leader metadata replicated-log config))])]
     ;;   [begin-election-alerts ()
     ;;                          (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;   [elected-as-leader ()
     ;;                      (next-state (Follower recently-contacted-by-leader metadata replicated-log config))]
     ;;   [send-heartbeat-timeouts (id)
     ;;                            (next-state (Follower recently-contacted-by-leader metadata replicated-log config))])

     ;; (define-state (Candidate [m ElectionMeta]
     ;;                          [replicated-log ReplicatedLog]
     ;;                          [config ClusterConfiguration])
     ;;   [client-messages (m)
     ;;                    (case m
     ;;                      [ClientMessage (client command)
     ;;                                     (send client (LeaderIs (NoLeader)))
     ;;                                     (next-state (Candidate m replicated-log config))])]
     ;;   [peer-messages (msg)
     ;;                  (case msg
     ;;                    [RequestVote (term candidate last-log-term last-log-index)
     ;;                                 (cond
     ;;                                   [(grant-vote?/candidate m replicated-log term candidate last-log-term last-log-index)
     ;;                                    (send candidate (VoteCandidate term peer-messages))
     ;;                                    ;; TODO: this seems wrong that we stay in candidate instead of
     ;;                                    ;; going to Follower. Some test should probably break this
     ;;                                    (next-state (Candidate (with-vote-for m term candidate) replicated-log config))]
     ;;                                   [else
     ;;                                    (let ([m (! m [current-term (max term (: m current-term))])])
     ;;                                      (send candidate (DeclineCandidate (: m current-term) peer-messages))
     ;;                                      (next-state (Candidate m replicated-log config)))])]
     ;;                    [VoteCandidate (term follower)
     ;;                                   (cond
     ;;                                     [(= term (: m current-term))
     ;;                                      (let ([including-this-vote (inc-vote m follower)])
     ;;                                        (cond
     ;;                                          [(has-majority including-this-vote config)
     ;;                                           (send elected-as-leader)
     ;;                                           (cancel-election-deadline timer-manager)
     ;;                                           ;; NOTE: have to just make up fake temporary values for the log index maps, for now
     ;;                                           (next-state (Leader (for-leader m) (hash) (hash) replicated-log config))]
     ;;                                          [else
     ;;                                           (next-state (Candidate including-this-vote replicated-log config))]))]
     ;;                                     [else (next-state (Candidate m replicated-log config))])]
     ;;                    [DeclineCandidate (term server) (next-state (Candidate m replicated-log config))]
     ;;                    [AppendEntries (term
     ;;                                    prev-log-term
     ;;                                    prev-log-index
     ;;                                    entries
     ;;                                    leader-commit-id
     ;;                                    leader
     ;;                                    leader-client)
     ;;                                   (let ([leader-is-ahead (>= term (: m current-term))])
     ;;                                     (cond
     ;;                                       [leader-is-ahead
     ;;                                        (send peer-messages msg)
     ;;                                        (let ([m (reset-election-deadline/candidate timer-manager timeouts m)])
     ;;                                          (next-state (Follower (Just leader-client)
     ;;                                                                (for-follower/candidate m)
     ;;                                                                replicated-log
     ;;                                                                config)))]
     ;;                                       [else
     ;;                                        ;; BUG: original code left out the response
     ;;                                        (send leader
     ;;                                              (AppendRejected (: m current-term)
     ;;                                                              (replicated-log-last-index replicated-log)
     ;;                                                              peer-messages))
     ;;                                        (next-state (Candidate m replicated-log config))]))]
     ;;                    [AppendSuccessful (t i member) (next-state (Candidate m replicated-log config))]
     ;;                    [AppendRejected (t i member) (next-state (Candidate m replicated-log config))])]
     ;;   [timeouts (id)
     ;;             (cond
     ;;               [(= id (: m last-used-timeout-id))
     ;;                (send begin-election-alerts)
     ;;                (next-state (Candidate (for-new-election/candidate m) replicated-log config))]
     ;;               [else (next-state (Candidate m replicated-log config))])]
     ;;   [begin-election-alerts ()
     ;;                          (let ([request (RequestVote (: m current-term)
     ;;                                                      peer-messages
     ;;                                                      (replicated-log-last-term replicated-log)
     ;;                                                      (replicated-log-last-index replicated-log))])
     ;;                            (for ([member (members-except-self config peer-messages)])
     ;;                              (send member request))
     ;;                            (let* ([m (reset-election-deadline/candidate timer-manager timeouts m)]
     ;;                                   [including-this-vote (inc-vote m peer-messages)]) ; this is the self vote
     ;;                              (next-state (Candidate (with-vote-for including-this-vote (: m current-term) peer-messages)
     ;;                                                     replicated-log config))))]
     ;;   [elected-as-leader () (next-state (Candidate m replicated-log config))]
     ;;   [send-heartbeat-timeouts (id) (next-state (Candidate m replicated-log config))])

     ;; (define-state (Leader [m LeaderMeta]
     ;;                       [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                       [match-index (Hash (Channel RaftMessage) Nat)]
     ;;                       [replicated-log ReplicatedLog]
     ;;                       [config ClusterConfiguration])
     ;;   [client-messages (msg)
     ;;                    (case msg
     ;;                      [ClientMessage (client command)
     ;;                                     (let* ([entry (Entry command
     ;;                                                          (: m current-term) (replicated-log-next-index replicated-log)
     ;;                                                          client)]
     ;;                                            [replicated-log (replicated-log+ replicated-log entry)]
     ;;                                            [match-index (hash-set match-index peer-messages (: entry index))])
     ;;                                       (replicate-log m next-index replicated-log config)
     ;;                                       (next-state (Leader m next-index match-index replicated-log config)))])]
     ;;   [peer-messages (msg)
     ;;                  (case msg
     ;;                    [RequestVote (term candidate last-log-term last-log-index)
     ;;                                 (cond
     ;;                                   [(grant-vote?/leader m replicated-log term candidate last-log-term last-log-index)
     ;;                                    (send candidate (VoteCandidate term peer-messages))
     ;;                                    (stop-heartbeat)
     ;;                                    (step-down m replicated-log config)]
     ;;                                   [(> term (: m current-term))
     ;;                                    (let ([m (! m [current-term term])])
     ;;                                      (send candidate (DeclineCandidate term peer-messages))
     ;;                                      (step-down m replicated-log config))]
     ;;                                   [else
     ;;                                    (send candidate (DeclineCandidate (: m current-term) peer-messages))
     ;;                                    (next-state (Leader m next-index match-index replicated-log config))])]
     ;;                    [VoteCandidate (t s) (next-state (Leader m next-index match-index replicated-log config))]
     ;;                    [DeclineCandidate (t s) (next-state (Leader m next-index match-index replicated-log config))]
     ;;                    [AppendEntries (term
     ;;                                    prev-log-term
     ;;                                    prev-log-index
     ;;                                    entries
     ;;                                    leader-commit-id
     ;;                                    leader
     ;;                                    leader-client)
     ;;                                   (cond
     ;;                                     [(> term (: m current-term))
     ;;                                      (stop-heartbeat)
     ;;                                      (send peer-messages msg)
     ;;                                      (step-down m replicated-log config)]
     ;;                                     [else
     ;;                                      (send-entries leader
     ;;                                                    m
     ;;                                                    replicated-log
     ;;                                                    next-index
     ;;                                                    (: replicated-log committed-index)
     ;;                                                    peer-messages
     ;;                                                    client-messages)
     ;;                                      (next-state (Leader m next-index match-index replicated-log config))])]
     ;;                    [AppendRejected (term last-index member)
     ;;                                    (register-append-rejected term
     ;;                                                              last-index
     ;;                                                              member
     ;;                                                              m
     ;;                                                              next-index
     ;;                                                              match-index
     ;;                                                              replicated-log
     ;;                                                              config)]
     ;;                    [AppendSuccessful (term last-index member)
     ;;                                      (register-append-successful term
     ;;                                                                  last-index
     ;;                                                                  member
     ;;                                                                  m
     ;;                                                                  next-index
     ;;                                                                  match-index
     ;;                                                                  replicated-log
     ;;                                                                  config)])]
     ;;   [configs (c) (next-state (Leader m next-index match-index replicated-log config))]
     ;;   [timeouts (id) (next-state (Leader m next-index match-index replicated-log config))]
     ;;   [begin-election-alerts () (next-state (Leader m next-index match-index replicated-log config))]
     ;;   [elected-as-leader ()
     ;;                      (let ([next-index (log-index-map-initialize (: config members)
     ;;                                                                  (+ (replicated-log-last-index replicated-log) 1))]
     ;;                            [match-index (log-index-map-initialize (: config members) 0)])
     ;;                        (start-heartbeat m next-index replicated-log config)
     ;;                        (next-state (Leader m next-index match-index replicated-log config)))]
     ;;   [send-heartbeat-timeouts (id)
     ;;                            (send-heartbeat m next-index replicated-log config)
     ;;                            (next-state (Leader m next-index match-index replicated-log config))])

     ;; ;; Only called from Follower state on receiving an election timeout
     ;; (define (begin-election [timer (Channel TimerMessage)]
     ;;                         [election-timeout-target (Channel Nat)]
     ;;                         [metadata StateMetadata]
     ;;                         [replicated-log ReplicatedLog]
     ;;                         [config ClusterConfiguration]
     ;;                         [begin-election-alerts (Channel)])
     ;;   ;; unlike akka-raft, we assume the config is full, because we don't deal with dynamic
     ;;   ;; configuration changes
     ;;   ;;
     ;;   ;; BUG: this reset should not happen, because the begin-election-alerts handler will do a reset
     ;;   ;; for us
     ;;   ;(let ([metadata (reset-election-deadline/follower timer election-timeout-target metadata)])
     ;;   ;; these next two lines are from the onTransition code. The duplicate call to
     ;;   ;; reset-election-deadline is a bug from the original akka-raft code
     ;;   (send begin-election-alerts)
     ;;   ;BUG: (let ([metadata (reset-election-deadline timer election-timeout-target metadata)])
     ;;   (next-state (Candidate (for-new-election/follower metadata) replicated-log config))
     ;;   ;)
     ;;   ;)
     ;;   )

     ;; ;; TODO: consider making AppendEntries into a record to remove these long param lists and better
     ;; ;; match akka-raft
     ;; (define (append-entries [term Nat]
     ;;                         [prev-log-term Nat]
     ;;                         [prev-log-index Nat]
     ;;                         [entries (Vectorof Entry)]
     ;;                         [leader-commit-id Nat]
     ;;                         [leader (Channel RaftMessage)]
     ;;                         [m StateMetadata]
     ;;                         [replicated-log ReplicatedLog]
     ;;                         [config ClusterConfiguration]
     ;;                         [recently-contacted-by-leader MaybeLeader])
     ;;   (cond
     ;;     [(leader-is-lagging term m)
     ;;      (send leader (AppendRejected (: m current-term)
     ;;                                   (replicated-log-last-index replicated-log)
     ;;                                   peer-messages))
     ;;      ;; akka-raft does not respond to heartbeats in this case, but I think it should
     ;;      ;; (cond
     ;;      ;;   [(not (is-heartbeat entries))
     ;;      ;;    (send leader (AppendRejected (: m current-term)
     ;;      ;;                                 (replicated-log-last-index replicated-log)))]
     ;;      ;;   [else (void)])
     ;;      (next-state (Follower recently-contacted-by-leader m replicated-log config))]
     ;;     [(not (replicated-log-consistent-update replicated-log prev-log-term prev-log-index))
     ;;      (let ([meta-with-updated-term (! m [current-term term])])
     ;;        (send leader (AppendRejected (: meta-with-updated-term current-term)
     ;;                                     (replicated-log-last-index replicated-log)
     ;;                                     peer-messages))
     ;;        (accept-heartbeat meta-with-updated-term replicated-log config recently-contacted-by-leader))]
     ;;     ;; akka-raft does not do the append/commit logic for heartbeats, even though it should
     ;;     ;; [(is-heartbeat entries)
     ;;     ;;  (accept-heartbeat m replicated-log config)]
     ;;     [else
     ;;      (let ([meta-with-updated-term (! m [current-term term])])
     ;;        (define append-result (append replicated-log prev-log-index entries meta-with-updated-term))
     ;;        (send leader (: append-result message))
     ;;        (let  ([replicated-log (commit-until-index (: append-result log) leader-commit-id false)])
     ;;          (accept-heartbeat meta-with-updated-term
     ;;                            replicated-log
     ;;                            config
     ;;                            recently-contacted-by-leader)))]))

     ;; ;; appends the entries to the log and returns the success message to send
     ;; (define (append [replicated-log ReplicatedLog]
     ;;                 [prev-log-index Nat]
     ;;                 [entries (Vectorof Entry)]
     ;;                 [m StateMetadata])
     ;;   (cond
     ;;     [(is-heartbeat entries)
     ;;      (AppendResult (AppendSuccessful (: m current-term)
     ;;                                      (replicated-log-last-index replicated-log)
     ;;                                      peer-messages)
     ;;                    replicated-log)]
     ;;     [else
     ;;      ;; NOTE: this num-entries-to-keep calculation is too naive if we do log compaction
     ;;      (let ([num-entries-to-keep prev-log-index])
     ;;        (let ([replicated-log (replicated-log-append replicated-log entries num-entries-to-keep)])
     ;;          (AppendResult (AppendSuccessful (replicated-log-last-term replicated-log)
     ;;                                          (replicated-log-last-index replicated-log)
     ;;                                          peer-messages)
     ;;                        replicated-log)))]))

     ;; ;; NOTE: only works for follower, but fortunately only used there
     ;; (define (accept-heartbeat [m StateMetadata]
     ;;                           [replicated-log ReplicatedLog]
     ;;                           [config ClusterConfiguration]
     ;;                           [recently-contacted-by-leader MaybeLeader])
     ;;   (let ([m (reset-election-deadline/follower timer-manager timeouts m)])
     ;;     (next-state (Follower recently-contacted-by-leader m replicated-log config))))

     ;; (define (commit-until-index [replicated-log ReplicatedLog]
     ;;                             [last-index-to-commit Nat]
     ;;                             [notify-client? Bool])
     ;;   (let ([entries (replicated-log-between replicated-log
     ;;                                          (: replicated-log committed-index)
     ;;                                          last-index-to-commit)])
     ;;     (for/fold ([rep-log replicated-log])
     ;;               ([entry entries])
     ;;       (send application (: entry command))
     ;;       (cond [notify-client? (send (: entry client) (: entry command))] [else void])
     ;;       (replicated-log-commit rep-log (: entry index)))))

     ;; (define heartbeat-timer-name "HeartbeatTimer")
     ;; (define heartbeat-interval 50)
     ;; (define (start-heartbeat [m LeaderMeta] [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                          [replicated-log ReplicatedLog]
     ;;                          [config ClusterConfiguration])
     ;;   (send-heartbeat m next-index replicated-log config)
     ;;   (send timer-manager
     ;;         (SetTimer heartbeat-timer-name send-heartbeat-timeouts 1 heartbeat-interval true)))

     ;; (define (stop-heartbeat)
     ;;   (send timer-manager (CancelTimer heartbeat-timer-name)))

     ;; (define (send-heartbeat [m LeaderMeta]
     ;;                         [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                         [replicated-log ReplicatedLog]
     ;;                         [config ClusterConfiguration])
     ;;   (replicate-log m next-index replicated-log config))

     ;; (define (replicate-log [m LeaderMeta]
     ;;                        [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                        [replicated-log ReplicatedLog]
     ;;                        [config ClusterConfiguration])
     ;;   (for ([member (members-except-self config peer-messages)])
     ;;     (send member (AppendEntries-apply (: m current-term)
     ;;                                       replicated-log
     ;;                                       (log-index-map-value-for next-index member)
     ;;                                       (: replicated-log committed-index)
     ;;                                       peer-messages
     ;;                                       client-messages))))

     ;; (define (send-entries [follower (Channel RaftMessage)]
     ;;                       [m LeaderMeta]
     ;;                       [replicated-log ReplicatedLog]
     ;;                       [next-index Nat]
     ;;                       [leader-commit-id Nat]
     ;;                       [leader (Channel RaftMessage)]
     ;;                       [leader-client (Channel ClientMessage)])
     ;;   (send follower (AppendEntries-apply (: m current-term)
     ;;                                       replicated-log
     ;;                                       (log-index-map-value-for next-index follower)
     ;;                                       (: replicated-log committed-index)
     ;;                                       peer-messages
     ;;                                       client-messages)))

     ;; ;; TODO: define messages like this alongside handlers in a state, so we don't have to repeat state
     ;; ;; fields so much
     ;; (define (register-append-successful [follower-term Nat]
     ;;                                     [follower-index Nat]
     ;;                                     [member (Channel RaftMessage)]
     ;;                                     [m LeaderMeta]
     ;;                                     [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                                     [match-index (Hash (Channel RaftMessage) Nat)]
     ;;                                     [replicated-log ReplicatedLog]
     ;;                                     [config ClusterConfiguration])
     ;;   ;; TODO: why don't both indices use put-if-greater?
     ;;   (let* ([next-index (hash-set next-index member follower-index)]
     ;;          [match-index (log-index-map-put-if-greater match-index
     ;;                                                     member
     ;;                                                     (log-index-map-value-for next-index member))]
     ;;          [replicated-log (maybe-commit-entry match-index replicated-log config)])
     ;;     (next-state (Leader m next-index match-index replicated-log config))))

     ;; (define (register-append-rejected [follower-term Nat]
     ;;                                   [follower-index Nat]
     ;;                                   [member (Channel RaftMessage)]
     ;;                                   [m LeaderMeta]
     ;;                                   [next-index (Hash (Channel RaftMessage) Nat)]
     ;;                                   [match-index (Hash (Channel RaftMessage) Nat)]
     ;;                                   [replicated-log ReplicatedLog]
     ;;                                   [config ClusterConfiguration])
     ;;   (let ([next-index (log-index-map-put-if-smaller next-index member (+ 1 follower-index))])
     ;;     (send-entries member
     ;;                   m
     ;;                   replicated-log
     ;;                   next-index
     ;;                   (: replicated-log committed-index)
     ;;                   peer-messages
     ;;                   client-messages)
     ;;     (next-state (Leader m next-index match-index replicated-log config))))

     ;; (define (maybe-commit-entry [match-index (Hash (Channel RaftMessage) Nat)]
     ;;                             [replicated-log ReplicatedLog]
     ;;                             [config ClusterConfiguration])
     ;;   (let ([index-on-majority (log-index-map-consensus-for-index match-index config)])
     ;;     (let ([will-commit (> index-on-majority (: replicated-log committed-index))])
     ;;       (cond
     ;;         [will-commit (commit-until-index replicated-log index-on-majority true)]
     ;;         [else replicated-log]))))

     ;; (define (step-down [m LeaderMeta] [replicated-log ReplicatedLog] [config ClusterConfiguration])
     ;;   (let ([m (reset-election-deadline/leader timer-manager timeouts m)])
     ;;     (next-state (Follower (NoLeader) (for-follower/leader m) replicated-log config))))
     ))

;; ---------------------------------------------------------------------------------------------------
;; State metadata helpers

;; (define (grant-vote?/follower [metadata StateMetadata]
;;                               [log ReplicatedLog]
;;                               [term Nat]
;;                               [candidate (Channel RaftMessage)]
;;                               [last-log-term Nat]
;;                               [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
;;        (case (hash-ref (: metadata votes) term)
;;          [Nothing () true]
;;          [Just (c) (= candidate c)])))

;; (define (grant-vote?/candidate [metadata StateMetadata]
;;                                [log ReplicatedLog]
;;                                [term Nat]
;;                                [candidate (Channel RaftMessage)]
;;                                [last-log-term Nat]
;;                                [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
;;        (case (hash-ref (: metadata votes) term)
;;          [Nothing () true]
;;          [Just (c) (= candidate c)])))

;; (define (grant-vote?/leader [metadata StateMetadata]
;;                             [log ReplicatedLog]
;;                             [term Nat]
;;                             [candidate (Channel RaftMessage)]
;;                             [last-log-term Nat]
;;                             [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)))

;; (define (candidate-at-least-as-up-to-date? [log ReplicatedLog]
;;                                            [candidate-log-term Nat]
;;                                            [candidate-log-index Nat])
;;   (let ([my-last-log-term (replicated-log-last-term log)])
;;     (or (> candidate-log-term my-last-log-term)
;;         (and (= candidate-log-term my-last-log-term)
;;              (>= candidate-log-index (replicated-log-last-index log))))))

;; (define (with-vote [metadata StateMetadata] [term Nat] [candidate (Channel RaftMessage)])
;;   (! metadata [votes (hash-set (: metadata votes) term candidate)]))

;; (define (initial-metadata)
;;   (StateMetadata 0 (hash) 0))

;; (define (for-follower/candidate [metadata ElectionMeta])
;;   (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

;; (define (for-follower/leader [metadata LeaderMeta])
;;   (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

;; (define (for-leader [metadata ElectionMeta])
;;   (LeaderMeta (: metadata current-term) (: metadata last-used-timeout-id)))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Election

;; ;; All times are in milliseconds
;; (define election-timeout-min 0)
;; (define election-timeout-max 100)
;; (define election-timer-name "ElectionTimer")

;; ;; Resets the timer for the election deadline and returns the metadata with the new expected next
;; ;; timeout ID
;; (define (reset-election-deadline/follower [timer (Channel TimerMessage)]
;;                                           [target (Channel Nat)]
;;                                           [m StateMetadata])
;;   (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
;;         [next-id (+ 1 (: m last-used-timeout-id))])
;;     (send timer (SetTimer election-timer-name target next-id deadline false))
;;     (! m [last-used-timeout-id next-id])))

;; (define (reset-election-deadline/candidate [timer (Channel TimerMessage)]
;;                                            [target (Channel Nat)]
;;                                            [m ElectionMeta])
;;   (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
;;         [next-id (+ 1 (: m last-used-timeout-id))])
;;     (send timer (SetTimer election-timer-name target next-id deadline false))
;;     (! m [last-used-timeout-id next-id])))

;; (define (reset-election-deadline/leader [timer (Channel TimerMessage)]
;;                                         [target (Channel Nat)]
;;                                         [m LeaderMeta])
;;   (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
;;         [next-id (+ 1 (: m last-used-timeout-id))])
;;     (send timer (SetTimer election-timer-name target next-id deadline false))
;;     (! m [last-used-timeout-id next-id])))

;; (define (cancel-election-deadline [timer (Channel TimerMessage)])
;;   (send timer (CancelTimer election-timer-name)))

;; ;; Because this language does not have traits, I separate forNewElection into two functions
;; (define (for-new-election/follower [m StateMetadata])
;;   (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; (define (for-new-election/candidate [m StateMetadata])
;;   (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; ;; this effectively duplicates the logic of withVote, but it follows the akka-raft code
;; (define (with-vote-for [m ElectionMeta] [term Nat] [candidate (Channel RaftMessage)])
;;   (! m [votes (hash-set (: m votes) term candidate)]))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Terms

;; (define (next [term Nat])
;;   (+ 1 term))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Config helpers

;; (define (members-except-self [config ClusterConfiguration] [self (Channel RaftMessage)])
;;   (for/fold ([result null])
;;             ([member (: config members)])
;;     (if (not (= member self)) (cons member result) result)))

;; (define (inc-vote [m ElectionMeta] [follower (Channel RaftMessage)])
;;   (! m [votes-received (hash-set (: m votes-received) follower true)]))

;; (define (has-majority [m ElectionMeta] [config ClusterConfiguration])
;;   ;; TODO: figure out what the type for division is here (or maybe rewrite to not use division)
;;   (let ([total-votes-received
;;          (for/fold ([total 0])
;;                    ([member (: config members)])
;;            (+ total (if (hash-has-key? (: m votes-received) member) 1 0)))])
;;     (> total-votes-received (/ (length (: config members)) 2))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Misc.

;; (define (leader-is-lagging [append-entries-term Nat] [m StateMetadata])
;;   (< append-entries-term (: m current-term)))

;; (define (is-heartbeat [append-entries-entries (Vectorof Entry)])
;;   (= 0 (vector-length append-entries-entries)))

;; (define (AppendEntries-apply [term Nat]
;;                              [replicated-log ReplicatedLog]
;;                              [from-index Nat]
;;                              [leader-commit-id Nat]
;;                              [leader (Channel RaftMessage)]
;;                              [leader-client (Channel ClientMessage)])
;;   (let ([entries (replicated-log-entries-batch-from replicated-log from-index)])
;;     (cond
;;       [(> (vector-length entries) 0)
;;        (let ([head (vector-ref entries 0)])
;;          (AppendEntries term
;;                         (replicated-log-term-at replicated-log (entry-prev-index head))
;;                         (entry-prev-index head)
;;                         entries
;;                         leader-commit-id
;;                         leader
;;                         leader-client))]
;;       [else (AppendEntries term
;;                            (replicated-log-term-at replicated-log (- from-index 1))
;;                            (- from-index 1)
;;                            entries
;;                            leader-commit-id
;;                            leader
;;                            leader-client)])))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Replicated log

;; (define (replicated-log-empty)
;;   (ReplicatedLog (vector) 0))

;; (define (replicated-log+ [replicated-log ReplicatedLog] [entry Entry])
;;   (replicated-log-append replicated-log (vector entry) (vector-length (: replicated-log entries))))

;; ;; Takes the first *take* entries from the log and appends *entries* onto it, returning the new log
;; (define (replicated-log-append [log ReplicatedLog] [entries-to-append (Vectorof Entry)] [take Nat])
;;   (! log [entries (vector-append (vector-take (: log entries) take) entries-to-append)]))

;; (define (replicated-log-commit [replicated-log ReplicatedLog] [n Int])
;;   (! replicated-log [commit-index n]))

;; ;; Returns the log entries from from-index (exclusive) to to-index (inclusive) (these are *semantic*
;; ;; indices)
;; (define (replicated-log-between [replicated-log ReplicatedLog] [from-index Int] [to-index Int])
;;   ;; NOTE: this naive conversion from semantic to implementation indices won't work under log
;;   ;; compaction
;;   (let ([vector-from-index (- from-index 1)]
;;         [vector-to-index   (- to-index   1)])
;;       (vector-slice (: replicated-log entries) (+ 1 vector-from-index) (+ 1 vector-to-index))))

;; (define (replicated-log-last-index [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 0]
;;       [else (: (vector-ref entries (- (vector-length entries) 1)) index)])))

;; (define (replicated-log-last-term [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 0]
;;       [else (: (vector-ref entries (- (vector-length entries) 1)) term)])))

;; ;; NOTE: this differs from the akka-raft version, which is broken
;; (define (replicated-log-next-index [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 1]
;;       [else (+ (: (vector-ref entries (- (vector-length entries) 1)) index) 1)])))

;; ;; Returns true if the leader's previous log is consistent with ours (i.e. the term of the previous
;; ;; index matches the term at that index in our log)
;; (define (replicated-log-consistent-update [replicated-log Replicated-Log]
;;                                           [prev-log-term Nat]
;;                                           [prev-log-index Nat])
;;   (= (replicated-log-term-at replicated-log prev-log-index) prev-log-term))

;; (define-variant-type FindTermResult (NoTerm) (FoundTerm [term Nat]))
;; (define (replicated-log-term-at [replicated-log ReplicatedLog] [index Nat])
;;   (cond
;;     [(<= index 0) 0]
;;     [else
;;      ;; Note: this code is uglier than it would be if we used more general list-traversal functions
;;      (let ([fold-result
;;                  (for/fold ([result (NoTerm)])
;;                            ([entry (: replicated-log entries)])
;;                    (case result
;;                      [NoTerm ()
;;                              (cond
;;                                [(= (: entry index) index) (FoundTerm (: entry term))]
;;                                [else (NoTerm)])]
;;                      [FoundTerm (t) result]))])
;;        (case fold-result
;;          [FoundTerm (t) t]
;;          [NoTerm ()
;;                  ;; If no term was found, just return 0, although this should really be a fatal error
;;                  0]))]))

;; ;; Returns a vector of entries from the log, starting at the from-including index and including either
;; ;; all entries with the same term or a total of 5 entries, whichever is less. We assume from-including
;; ;; is no less than 1 and no more than 1 + the last index in the log.
;; (define (replicated-log-entries-batch-from [replicated-log ReplicatedLog] [from-including Nat])
;;   (let* ([how-many 5] ; this is the default parameter in akka-raft
;;          [first-impl-index 0]
;;          [first-semantic-index
;;           (if (= (vector-length (: replicated-log entries)) 0)
;;               1
;;               (: (vector-ref (: replicated-log entries) 0) index))]
;;          [semantic->impl-offset (- first-impl-index first-semantic-index)]
;;          [from-including-impl (+ from-including semantic->impl-offset)]
;;          [to-send (vector-slice (: replicated-log entries)
;;                                 from-including-impl
;;                                 (+ from-including-impl how-many))])
;;     (cond
;;       [(> (vector-length to-send) 0)
;;        (let* ([head (vector-ref to-send 0)]
;;               [batch-term (: head term)])
;;          ;; this for/fold implements the takeWhile
;;          (for/fold ([result (vector)])
;;                    ([entry to-send])
;;            (cond
;;              [(= (: entry term) batch-term) (vector-append result (vector entry))]
;;              [else result])))]
;;       [else (vector)])))

;; (define (min [a Nat] [b Nat])
;;   (cond [(< a b) a] [else b]))

;; (define (entry-prev-index [entry Entry])
;;   (- (: entry index) 1))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; LogIndexMap

;; (define (log-index-map-initialize [members (Listof (Channel RaftMessage))] [initialize-with Nat])
;;   (for/fold ([map (hash)])
;;             ([member members])
;;     (hash-set map member initialize-with)))

;; (define (log-index-map-value-for [map (Hash (Channel RaftMessage) Nat)]
;;                                  [member (Channel RaftMessage)])
;;   (case (hash-ref map member)
;;     [Nothing ()
;;       ;; akka-raft would update the map here, but we should never have to because we don't change the
;;       ;; config
;;       0]
;;     [Just (value) value]))

;; (define (log-index-map-put-if-greater [map (Hash (Channel RaftMessage) Nat)]
;;                                       [member (Channel RaftMessage)]
;;                                       [value Nat])
;;   (let ([old-value (log-index-map-value-for map member)])
;;     (cond
;;       [(< old-value value) (hash-set map member value)]
;;       [else map])))

;; (define (log-index-map-put-if-smaller [map (Hash (Channel RaftMessage) Nat)]
;;                                       [member (Channel RaftMessage)]
;;                                       [value Nat])
;;   (let ([old-value (log-index-map-value-for map member)])
;;     (cond
;;       [(> old-value value) (hash-set map member value)]
;;       [else map])))

;; ;; NOTE: because the akka-raft version of this is completely wrong, I'm writing my own
;; ;; Returns the greatest index that a majority of entries in the map agree on
;; (define (log-index-map-consensus-for-index [map (Hash (Channel RaftMessage) Nat)]
;;                                            [config ClusterConfiguration])
;;   (let ([all-indices
;;          (for/fold ([indices-so-far null])
;;                    ([member (: config members)])
;;            (case (hash-ref map member)
;;              [Nothing () indices-so-far] ; NOTE: this should never happen
;;              [Just (index) (cons index indices-so-far)]))])
;;     (list-ref (sort-numbers-descending all-indices)
;;               (- (ceiling (/ (length (: config members)) 2)) 1))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Vector and list helpers

;; ;; Works like Scala's list slice (i.e. returns empty list instead of returning errors)
;; (define (vector-slice [v (Vectorof Entries)] [from-index Int] [to-index Int])
;;   (vector-copy v
;;                (min from-index (vector-length v))
;;                (min to-index   (vector-length v))))

  )

;; TODO: write a test that checks the Raft program's grammar (later: and type-checks it)

;; 2. Desugar that into the actor definition the verifier needs/translate it into the structural
;; version, using arbitrary addresses for each initial output address
(define desugared-raft-actor (desugar-actor raft-actor-surface-def single-agent-concrete-addr))

(check-not-false (redex-match csa-eval αn desugared-raft-actor))
(check-not-false (redex-match aps-eval z raft-spec))

;; 3. Move the actor definition into a config, with addresses assigned appropriately
(define raft-config (make-single-agent-config desugared-raft-actor))

;; 4. Run the verifier
(check-true (analyze raft-config
                     raft-spec
                     (term (Union)) (term (Union))
                     (hash 'Init 'Init
                           'Follower 'Follower
                           'Candidate 'Candidate
                           'Leader 'Leader)))
