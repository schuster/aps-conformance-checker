#lang racket

;; A full test of the Raft port to CSA, verified against its spec

;; TODO: refactor this program to use records like those in akka-raft

(require
 rackunit
 redex/reduction-semantics
 "aps.rkt"
 "csa.rkt"
 "desugar.rkt"
 "main.rkt")

;; TODO: put this in a common place so it isn't repeated across files
(define single-agent-concrete-addr (term (addr 0)))

;; TODO: write a check that alerts for any underscores in the spec (b/c those are invalid)
(define raft-spec
  (term
   (((define-state (Init)
       [unobs -> (goto Running)]
       [(variant PeerMessage *) -> (goto Init)])
     (define-state (Running)
       ;; TODO: consider removing the "PeerMessage" part of the type, just to make things more
       ;; concise, esp. for sending back *out*
       [(variant PeerMessage (variant RequestVote * candidate * *)) ->
        (with-outputs ([candidate (variant PeerMessage (or (variant VoteCandidate * *)
                                                           (variant DeclineCandidate * *)))])
          (goto Running))]
       [(variant PeerMessage (variant VoteCandidate * *)) -> (goto Running)]
       [(variant PeerMessage (variant DeclineCandidate * *)) -> (goto Running)]
       [(variant PeerMessage (variant AppendEntries * * * * * leader *)) ->
        (with-outputs ([leader (variant PeerMessage (or (variant AppendRejected * * *)
                                                        (variant AppendSuccessful * * *)))])
          (goto Running))]
       ;; TODO: break these out into separate states so that the append retry can only happen when in the leader state (and otherwise the leader must fall back to being a follower)
       [(variant PeerMessage (variant AppendRejected * * *)) -> (goto Running)]
       [(variant PeerMessage (variant AppendRejected * * member)) ->
        ;; TODO: should I require that the self address is in this response?
        (with-outputs ([member (variant PeerMessage (variant AppendEntries * * * * * * *))])
          (goto Running))]
       [(variant PeerMessage (variant AppendSuccessful * * *)) -> (goto Running)]))
    ;; TODO: switch the order of the init exp and the states
    (goto Init)
    ,single-agent-concrete-addr)))

(define raft-actor-surface-prog

  (term
   ((define-type Unit (Record))
    (define-type Duration Nat) ; number of seconds
    ;; TODO: move these into the core language
    (define-variant Boolean (True) (False))
    ;; TODO: use these constants
    (define-constant true (variant True))
    (define-constant false (variant False))
    ;; TODO: actually define Int
    (define-type Int Nat)

    ;; ---------------------------------------------------------------------------------------------------
    ;; Standard Library Functions and Other Definitions

    (define-function (max [a Nat] [b Nat])
      (if (> a b) a b))
    (define-function (min [a Nat] [b Nat])
      (if (< a b) a b))

    (define-variant MaybeHashResult
      (Nothing)
      (Just [val Nat])) ; TODO: come up with an accurate type

    ;; ---------------------------------------------------------------------------------------------------
    ;; Vector and list helpers

    ;; Works like Scala's list slice (i.e. returns empty list instead of returning errors)
    ;; TODO: give an accurate type here
    (define-function (vector-slice [v (Vectorof Nat)] [from-index Int] [to-index Int])
      (vector-copy v
                   (min from-index (vector-length v))
                   (min to-index   (vector-length v))))

    ;; ---------------------------------------------------------------------------------------------------

    (define-record ClusterConfiguration
      ;; TODO:
      [members (Listof (Addr Nat ;; RaftMessage
                             ))
               ]
      ;; ignoring other config fields for now, since I'm not implementing configuration changes
      )

    (define-variant ClientResponse
      ;; TODO: allow this recursive type
      (LeaderIs [leader Nat ;;MaybeLeader
                        ])
      (CommitSuccess [cmd String]))

    ;; Client message contains a command (string) to print when applying to the state machine, and a
    ;; channel to send to to confirm the application
    (define-variant ClientMessage
      (ClientMessage [client (Addr ClientResponse)] [cmd String]))

    (define-variant MaybeLeader
      (NoLeader)
      ;; TODO: allow this type
      (JustLeader [leader (Addr ClientMessage)]))

(define-record Entry
  [command String]
  [term Nat]
  [index Nat]
  [client (Addr String)])

(define-variant RaftMessage
  (RequestVote
   [term Nat]
   [candidate (Addr Nat ;; TODO: RaftMessage
                    )]
   [last-log-term Nat]
   [last-log-index Nat])
  (VoteCandidate
   [term Nat]
   ;; TODO:
   [follower (Addr Nat ;; RaftMessage
                   )])
  (DeclineCandidate
   [term Nat]
   [follower (Addr Nat ;; TODO: RaftMessage
                   )])
  (AppendEntries
   [term Nat]
   [prev-log-term Nat]
   [prev-log-index Nat]
   [entries (Vectorof Entry)]
   [leader-commit-id Nat]
   [leader (Addr Nat ; TODO: RaftMessage
                 )]
   [leader-client (Addr ClientMessage)])
  ;; A note on last-index: In the paper, this is the optimization at the bottom of p. 7 that allows
  ;; for quicker recovery of a node that has fallen behind in its log. In RaftScope, they call this
  ;; "matchIndex", which indicates the lat index in the log (or 0 for AppendRejected). In akka-raft,
  ;; this is always the last index of the log (for both success and failure)
  (AppendRejected
   [term Nat]
   [last-index Nat]
   ;; TODO:
   [member (Addr Nat ;; RaftMessage
                 )])
  (AppendSuccessful
   [term Nat]
   [last-index Nat]
   ;; TODO:
   [member (Addr Nat ;; RaftMessage
                 )]))

(define-variant RaftActorMessage
  (Config [config ClusterConfiguration])
  (ClientMessage [client (Addr ClientResponse)] [cmd String])
  (PeerMessage [m RaftMessage])
  (ElectedAsLeader)
  (BeginElectionAlerts)
  (SendHeartbeatTimeouts [id Nat]))

(define-variant MaybePeer
  (NoPeer)
  (JustPeer [peer (Addr RaftMessage)]))

(define-record StateMetadata
  [current-term Nat]
  [votes (Hash Nat (Addr RaftMessage))]
  [last-used-timeout-id Nat])

(define-record ElectionMeta
  [current-term Nat]
  [votes-received (Hash (Addr RaftMessage) Boolean)]
  [votes (Hash Nat (Addr RaftMessage))]
  [last-used-timeout-id Nat])

(define-record LeaderMeta
  [current-term Nat]
  [last-used-timeout-id Nat])

(define-variant TimerMessage
  (SetTimer [timer-name String] [target (Addr (Union (Timeout Nat)))] [id Nat] [duration Duration] [repeat? Boolean])
  (CancelTimer [timer-name String]))

(define-record ReplicatedLog
  [entries (Vectorof Entry)]
  [committed-index Int])

(define-record AppendResult
  [message RaftMessage]
  [log ReplicatedLog])

    ;;;; Program-level Functions

;; ---------------------------------------------------------------------------------------------------
;; Replicated log

(define-function (replicated-log-empty)
  (ReplicatedLog (vector) 0))

;; Takes the first *take* entries from the log and appends *entries* onto it, returning the new log
(define-function (replicated-log-append [log ReplicatedLog] [entries-to-append (Vectorof Entry)] [take Nat])
  (! log [entries (vector-append (vector-take (: log entries) take) entries-to-append)]))

(define-function (replicated-log+ [replicated-log ReplicatedLog] [entry Entry])
  (replicated-log-append replicated-log (vector entry) (vector-length (: replicated-log entries))))

(define-function (replicated-log-commit [replicated-log ReplicatedLog] [n Int])
  (! replicated-log [commit-index n]))

;; ;; Returns the log entries from from-index (exclusive) to to-index (inclusive) (these are *semantic*
;; ;; indices)
(define-function (replicated-log-between [replicated-log ReplicatedLog] [from-index Int] [to-index Int])
  ;; NOTE: this naive conversion from semantic to implementation indices won't work under log
  ;; compaction
  (let ([vector-from-index (- from-index 1)]
        [vector-to-index   (- to-index   1)])
      (vector-slice (: replicated-log entries) (+ 1 vector-from-index) (+ 1 vector-to-index))))

(define-function (replicated-log-last-index [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (vector-length entries)) 0]
      [else (: (vector-ref entries (- (vector-length entries) 1)) index)])))

(define-function (replicated-log-last-term [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (vector-length entries)) 0]
      [else (: (vector-ref entries (- (vector-length entries) 1)) term)])))

;; ;; NOTE: this differs from the akka-raft version, which is broken
(define-function (replicated-log-next-index [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (vector-length entries)) 1]
      [else (+ (: (vector-ref entries (- (vector-length entries) 1)) index) 1)])))

(define-variant FindTermResult (NoTerm) (FoundTerm [term Nat]))
(define-function (replicated-log-term-at [replicated-log ReplicatedLog] [index Nat])
  (cond
    [(<= index 0) 0]
    [else
     ;; Note: this code is uglier than it would be if we used more general list-traversal functions
     (let ([fold-result
            (NoTerm) ; TODO: remove this line
            ;; TODO:
                 ;; (for/fold ([result (NoTerm)])
                 ;;           ([entry (: replicated-log entries)])
                 ;;   (case result
                 ;;     [(NoTerm)
                 ;;             (cond
                 ;;               [(= (: entry index) index) (FoundTerm (: entry term))]
                 ;;               [else (NoTerm)])]
                 ;;     [(FoundTerm t) result]))
                 ])
       (case fold-result
         [(FoundTerm t) t]
         [(NoTerm)
                 ;; If no term was found, just return 0, although this should really be a fatal error
          0]))]))

;; Returns true if the leader's previous log is consistent with ours (i.e. the term of the previous
;; index matches the term at that index in our log)
(define-function (replicated-log-consistent-update [replicated-log ReplicatedLog]
                                          [prev-log-term Nat]
                                          [prev-log-index Nat])
  (= (replicated-log-term-at replicated-log prev-log-index) prev-log-term))

;; Returns a vector of entries from the log, starting at the from-including index and including either
;; all entries with the same term or a total of 5 entries, whichever is less. We assume from-including
;; is no less than 1 and no more than 1 + the last index in the log.
(define-function (replicated-log-entries-batch-from [replicated-log ReplicatedLog] [from-including Nat])
  (let* ([how-many 5] ; this is the default parameter in akka-raft
         [first-impl-index 0]
         [first-semantic-index
          (if (= (vector-length (: replicated-log entries)) 0)
              1
              (: (vector-ref (: replicated-log entries) 0) index))]
         [semantic->impl-offset (- first-impl-index first-semantic-index)]
         [from-including-impl (+ from-including semantic->impl-offset)]
         [to-send (vector-slice (: replicated-log entries)
                                from-including-impl
                                (+ from-including-impl how-many))])
    (cond
      [(> (vector-length to-send) 0)
       (let* ([head (vector-ref to-send 0)]
              [batch-term (: head term)])
         ;; TODO:
         ;; this for/fold implements the takeWhile
         ;; (for/fold ([result (vector)])
         ;;           ([entry to-send])
         ;;   (cond
         ;;     [(= (: entry term) batch-term) (vector-append result (vector entry))]
         ;;     [else result]))
         (vector) ;; TODO: remove this line
         )]
      [else (vector)])))

(define-function (entry-prev-index [entry Entry])
  (- (: entry index) 1))

;; ---------------------------------------------------------------------------------------------------
;; State metadata helpers

(define-function (candidate-at-least-as-up-to-date? [log ReplicatedLog]
                                           [candidate-log-term Nat]
                                           [candidate-log-index Nat])
  (let ([my-last-log-term (replicated-log-last-term log)])
    (or (> candidate-log-term my-last-log-term)
        (and (= candidate-log-term my-last-log-term)
             (>= candidate-log-index (replicated-log-last-index log))))))


(define-function (grant-vote?/follower [metadata StateMetadata]
                              [log ReplicatedLog]
                              [term Nat]
                              [candidate (Addr RaftMessage)]
                              [last-log-term Nat]
                              [last-log-index Nat])
  (and (>= term (: metadata current-term))
       (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
       (case (hash-ref (: metadata votes) term)
         [(Nothing) true]
         [(Just c) (= candidate c)])))

(define-function (grant-vote?/candidate [metadata StateMetadata]
                               [log ReplicatedLog]
                               [term Nat]
                               [candidate (Addr RaftMessage)]
                               [last-log-term Nat]
                               [last-log-index Nat])
  (and (>= term (: metadata current-term))
       (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
       (case (hash-ref (: metadata votes) term)
         [(Nothing) true]
         [(Just c) (= candidate c)])))

(define-function (grant-vote?/leader [metadata StateMetadata]
                            [log ReplicatedLog]
                            [term Nat]
                            [candidate (Addr RaftMessage)]
                            [last-log-term Nat]
                            [last-log-index Nat])
  (and (>= term (: metadata current-term))
       (candidate-at-least-as-up-to-date? log last-log-term last-log-index)))

(define-function (with-vote [metadata StateMetadata] [term Nat] [candidate (Addr RaftMessage)])
  (! metadata [votes (hash-set (: metadata votes) term candidate)]))

(define-function (initial-metadata)
  (StateMetadata 0 (hash) 0))

(define-function (for-follower/candidate [metadata ElectionMeta])
  (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

(define-function (for-follower/leader [metadata LeaderMeta])
  (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

(define-function (for-leader [metadata ElectionMeta])
  (LeaderMeta (: metadata current-term) (: metadata last-used-timeout-id)))

;; ---------------------------------------------------------------------------------------------------
;; Terms

(define-function (next [term Nat])
  (+ 1 term))

;; ---------------------------------------------------------------------------------------------------
;; Election

;; All times are in milliseconds
;; TODO: define these as constants in the program
(define-constant election-timeout-min 0)
(define-constant election-timeout-max 100)
(define-constant election-timer-name "ElectionTimer")

;; Resets the timer for the election deadline and returns the metadata with the new expected next
;; timeout ID
(define-function (reset-election-deadline/follower [timer (Addr TimerMessage)]
                                                   [target (Addr Nat)]
                                                   [m StateMetadata])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline false))
    (! m [last-used-timeout-id next-id])))

(define-function (reset-election-deadline/candidate [timer (Addr TimerMessage)]
                                           [target (Addr Nat)]
                                           [m ElectionMeta])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline false))
    (! m [last-used-timeout-id next-id])))

(define-function (reset-election-deadline/leader [timer (Addr TimerMessage)]
                                        [target (Addr Nat)]
                                        [m LeaderMeta])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline false))
    (! m [last-used-timeout-id next-id])))

(define-function (cancel-election-deadline [timer (Addr TimerMessage)])
  (send timer (CancelTimer election-timer-name)))

;; ;; Because this language does not have traits, I separate forNewElection into two functions
(define-function (for-new-election/follower [m StateMetadata])
  (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

(define-function (for-new-election/candidate [m StateMetadata])
  (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; ;; this effectively duplicates the logic of withVote, but it follows the akka-raft code
(define-function (with-vote-for [m ElectionMeta] [term Nat] [candidate (Addr RaftMessage)])
  (! m [votes (hash-set (: m votes) term candidate)]))

;; ---------------------------------------------------------------------------------------------------
;; Config helpers

(define-function (members-except-self [config ClusterConfiguration] [self (Addr RaftMessage)])
  ;; TODO:
  ;; (for/fold ([result (list)])
  ;;           ([member (: config members)])
  ;;   (if (not (= member self)) (cons member result) result))
  (list) ;; TODO: remove this line
  )

(define-function (inc-vote [m ElectionMeta] [follower (Addr RaftMessage)])
  (! m [votes-received (hash-set (: m votes-received) follower true)]))

(define-function (has-majority [m ElectionMeta] [config ClusterConfiguration])
  ;; TODO: figure out what the type for division is here (or maybe rewrite to not use division)
  (let ([total-votes-received
         ;; TODO:
         ;; (for/fold ([total 0])
         ;;           ([member (: config members)])
         ;;   (+ total (if (hash-has-key? (: m votes-received) member) 1 0)))
         0 ;; TODO: remove this line
         ])
    (> total-votes-received (/ (length (: config members)) 2))))

;; ---------------------------------------------------------------------------------------------------
;; LogIndexMap

;; (define-function (log-index-map-initialize [members (Listof (Addr RaftMessage))] [initialize-with Nat])
;;   (for/fold ([map (hash)])
;;             ([member members])
;;     (hash-set map member initialize-with)))

(define-function (log-index-map-value-for [map (Hash (Addr RaftMessage) Nat)]
                                 [member (Addr RaftMessage)])
  (case (hash-ref map member)
    [(Nothing)
      ;; akka-raft would update the map here, but we should never have to because we don't change the
      ;; config
      0]
    [(Just value) value]))

(define-function (log-index-map-put-if-greater [map (Hash (Addr RaftMessage) Nat)]
                                               [member (Addr RaftMessage)]
                                               [value Nat])
  (let ([old-value (log-index-map-value-for map member)])
    (cond
      [(< old-value value) (hash-set map member value)]
      [else map])))

(define-function (log-index-map-put-if-smaller [map (Hash (Addr RaftMessage) Nat)]
                                      [member (Addr RaftMessage)]
                                      [value Nat])
  (let ([old-value (log-index-map-value-for map member)])
    (cond
      [(> old-value value) (hash-set map member value)]
      [else map])))

;; ;; NOTE: because the akka-raft version of this is completely wrong, I'm writing my own
;; ;; Returns the greatest index that a majority of entries in the map agree on
(define-function (log-index-map-consensus-for-index [map (Hash (Addr RaftMessage) Nat)]
                                                    [config ClusterConfiguration])
  (let ([all-indices
         (list) ;; TODO: remove this line
                     ;; TODO:
         ;; (for/fold ([indices-so-far (list)])
         ;;           ([member (: config members)])
         ;;   (case (hash-ref map member)
         ;;     [(Nothing) indices-so-far] ; NOTE: this should never happen
         ;;     [(Just index) (cons index indices-so-far)]))
         ])
    (list-ref (sort-numbers-descending all-indices)
              (- (ceiling (/ (length (: config members)) 2)) 1))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Misc.

(define-function (leader-is-lagging [append-entries-term Nat] [m StateMetadata])
  (< append-entries-term (: m current-term)))

(define-function (is-heartbeat [append-entries-entries (Vectorof Entry)])
  (= 0 (vector-length append-entries-entries)))

(define-function (AppendEntries-apply [term Nat]
                             [replicated-log ReplicatedLog]
                             [from-index Nat]
                             [leader-commit-id Nat]
                             [leader (Addr (Union (PeerMessage RaftMessage)))]
                             [leader-client (Addr (Union (ClientMessage ClientMessage)))])
  (let ([entries (replicated-log-entries-batch-from replicated-log from-index)])
    (cond
      [(> (vector-length entries) 0)
       (let ([head (vector-ref entries 0)])
         (AppendEntries term
                        (replicated-log-term-at replicated-log (entry-prev-index head))
                        (entry-prev-index head)
                        entries
                        leader-commit-id
                        leader
                        leader-client))]
      [else (AppendEntries term
                           (replicated-log-term-at replicated-log (- from-index 1))
                           (- from-index 1)
                           entries
                           leader-commit-id
                           leader
                           leader-client)])))

(define-actor RaftActorMessage (RaftActor [timer-manager (Addr TimerMessage)]
                                          [application (Addr String)])
      ;; (in: [client-messages ClientMessage]
      ;;      [peer-messages RaftMessage]
      ;;      [configs ClusterConfiguration]
      ;;      [timeouts Nat]
      ;;      [begin-election-alerts]
      ;;      [elected-as-leader]
      ;;      [send-heartbeat-timeouts Nat])
      ;; (out: [timer-manager TimerMessage]
      ;;       [application String]) ; the server sends a command here when it is applied

      ; the functions go here
      (
      ;; ;; Only called from Follower state on receiving an election timeout
      (define-function (begin-election [timer (Addr TimerMessage)]
                              [election-timeout-target (Addr Nat)]
                              [metadata StateMetadata]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration]
                              [begin-election-alerts (Addr (Union (BeginElectionAlerts)))])
        ;; unlike akka-raft, we assume the config is full, because we don't deal with dynamic
        ;; configuration changes
        ;;
        ;; BUG: this reset should not happen, because the begin-election-alerts handler will do a reset
        ;; for us
        ;(let ([metadata (reset-election-deadline/follower timer election-timeout-target metadata)])
        ;; these next two lines are from the onTransition code. The duplicate call to
        ;; reset-election-deadline is a bug from the original akka-raft code
        ;; TODO: deal with self-sends
        (send self (BeginElectionAlerts))
        ;BUG: (let ([metadata (reset-election-deadline timer election-timeout-target metadata)])
        (goto Candidate (for-new-election/follower metadata) replicated-log config)
        ;)
        ;)
        )

      ;; NOTE: only works for follower, but fortunately only used there
      (define-function (accept-heartbeat [m StateMetadata]
                                         [replicated-log ReplicatedLog]
                                         [config ClusterConfiguration]
                                         [recently-contacted-by-leader MaybeLeader])
        (let ([m (reset-election-deadline/follower timer-manager self m)])
          (goto Follower recently-contacted-by-leader m replicated-log config)))

      ;; appends the entries to the log and returns the success message to send
      (define-function (append [replicated-log ReplicatedLog]
                               [prev-log-index Nat]
                               [entries (Vectorof Entry)]
                               [m StateMetadata])
        (cond
          [(is-heartbeat entries)
           (AppendResult (AppendSuccessful (: m current-term)
                                           (replicated-log-last-index replicated-log)
                                           self)
                         replicated-log)]
          [else
           ;; NOTE: this num-entries-to-keep calculation is too naive if we do log compaction
           (let ([num-entries-to-keep prev-log-index])
             (let ([replicated-log (replicated-log-append replicated-log entries num-entries-to-keep)])
               (AppendResult (AppendSuccessful (replicated-log-last-term replicated-log)
                                               (replicated-log-last-index replicated-log)
                                               self)
                             replicated-log)))]))

      (define-function (commit-until-index [replicated-log ReplicatedLog]
                                           [last-index-to-commit Nat]
                                           [notify-client? Boolean])
        (let ([entries (replicated-log-between replicated-log
                                               (: replicated-log committed-index)
                                               last-index-to-commit)])
          ;; TODO: 
          ;; (for/fold ([rep-log replicated-log])
          ;;           ([entry entries])
          ;;   (send application (: entry command))
          ;;   (cond [notify-client? (send (: entry client) (: entry command))] [else void])
          ;;   (replicated-log-commit rep-log (: entry index)))
          replicated-log ; TODO: remove this line
          ))

      ;; TODO: consider making AppendEntries into a record to remove these long param lists and better
      ;; match akka-raft
      (define-function (append-entries [term Nat]
                              [prev-log-term Nat]
                              [prev-log-index Nat]
                              [entries (Vectorof Entry)]
                              [leader-commit-id Nat]
                              [leader (Addr RaftMessage)]
                              [m StateMetadata]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration]
                              [recently-contacted-by-leader MaybeLeader])
        (cond
          [(leader-is-lagging term m)
           (send leader (PeerMessage (AppendRejected (: m current-term)
                                                     (replicated-log-last-index replicated-log)
                                                     self)))
           ;; BUG: akka-raft does not respond to heartbeats in this case, but I think it should
           ;; (cond
           ;;   [(not (is-heartbeat entries))
           ;;    (send leader (AppendRejected (: m current-term)
           ;;                                 (replicated-log-last-index replicated-log)))]
           ;;   [else (void)])
           (goto Follower recently-contacted-by-leader m replicated-log config)]
          [(not (replicated-log-consistent-update replicated-log prev-log-term prev-log-index))
           (let ([meta-with-updated-term (! m [current-term term])])
             (send leader (PeerMessage (AppendRejected (: meta-with-updated-term current-term)
                                                       (replicated-log-last-index replicated-log)
                                                       self)))
             (accept-heartbeat meta-with-updated-term replicated-log config recently-contacted-by-leader))]
          ;; akka-raft does not do the append/commit logic for heartbeats, even though it should
          ;; [(is-heartbeat entries)
          ;;  (accept-heartbeat m replicated-log config)]
          [else
           (let* ([meta-with-updated-term (! m [current-term term])]
                  [append-result (append replicated-log prev-log-index entries meta-with-updated-term)])
             (send leader (PeerMessage (: append-result message)))
             (let  ([replicated-log (commit-until-index (: append-result log) leader-commit-id false)])
               (accept-heartbeat meta-with-updated-term
                                 replicated-log
                                 config
                                 recently-contacted-by-leader)))]))

      (define-function (replicate-log [m LeaderMeta]
                             [next-index (Hash (Addr RaftMessage) Nat)]
                             [replicated-log ReplicatedLog]
                             [config ClusterConfiguration])
        0 ;; TODO: add this for loop back in
        ;; (for ([member (members-except-self config self)])
        ;;   (send member (AppendEntries-apply (: m current-term)
        ;;                                     replicated-log
        ;;                                     (log-index-map-value-for next-index member)
        ;;                                     (: replicated-log committed-index)
        ;;                                     self
        ;;                                     self)))
        )

      (define-function (send-heartbeat [m LeaderMeta]
                              [next-index (Hash (Addr RaftMessage) Nat)]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration])
        (replicate-log m next-index replicated-log config))

      (define-constant heartbeat-timer-name "HeartbeatTimer")
      (define-constant heartbeat-interval 50)
      (define-function (start-heartbeat [m LeaderMeta] [next-index (Hash (Addr RaftMessage) Nat)]
                               [replicated-log ReplicatedLog]
                               [config ClusterConfiguration])
        (send-heartbeat m next-index replicated-log config)
        (send timer-manager
              (SetTimer heartbeat-timer-name self 1 heartbeat-interval true)))

      (define-function (stop-heartbeat)
        (send timer-manager (CancelTimer heartbeat-timer-name)))

      (define-function (send-entries [follower (Addr RaftMessage)]
                            [m LeaderMeta]
                            [replicated-log ReplicatedLog]
                            [next-index Nat]
                            [leader-commit-id Nat]
                            [leader (Addr RaftMessage)]
                            [leader-client (Addr ClientMessage)])
        (send follower
              (PeerMessage
               (AppendEntries-apply (: m current-term)
                                    replicated-log
                                    (log-index-map-value-for next-index follower)
                                    (: replicated-log committed-index)
                                    self
                                    self))))

       (define-function (maybe-commit-entry [match-index (Hash (Addr RaftMessage) Nat)]
                                            [replicated-log ReplicatedLog]
                                            [config ClusterConfiguration])
         (let ([index-on-majority (log-index-map-consensus-for-index match-index config)])
          (let ([will-commit (> index-on-majority (: replicated-log committed-index))])
            (cond
              [will-commit (commit-until-index replicated-log index-on-majority true)]
              [else replicated-log]))))

      ;; TODO: define messages like this alongside handlers in a state, so we don't have to repeat state
      ;; fields so much
      (define-function (register-append-successful [follower-term Nat]
                                          [follower-index Nat]
                                          [member (Addr RaftMessage)]
                                          [m LeaderMeta]
                                          [next-index (Hash (Addr RaftMessage) Nat)]
                                          [match-index (Hash (Addr RaftMessage) Nat)]
                                          [replicated-log ReplicatedLog]
                                          [config ClusterConfiguration])
        ;; TODO: why don't both indices use put-if-greater?
        (let* ([next-index (hash-set next-index member follower-index)]
               [match-index (log-index-map-put-if-greater match-index
                                                          member
                                                          (log-index-map-value-for next-index member))]
               [replicated-log (maybe-commit-entry match-index replicated-log config)])
          (goto Leader m next-index match-index replicated-log config)))

      (define-function (register-append-rejected [follower-term Nat]
                                        [follower-index Nat]
                                        [member (Addr RaftMessage)]
                                        [m LeaderMeta]
                                        [next-index (Hash (Addr RaftMessage) Nat)]
                                        [match-index (Hash (Addr RaftMessage) Nat)]
                                        [replicated-log ReplicatedLog]
                                        [config ClusterConfiguration])
        (let ([next-index (log-index-map-put-if-smaller next-index member (+ 1 follower-index))])
          (send-entries member
                        m
                        replicated-log
                        next-index
                        (: replicated-log committed-index)
                        self
                        self)
          (goto Leader m next-index match-index replicated-log config)))

      (define-function (step-down [m LeaderMeta] [replicated-log ReplicatedLog] [config ClusterConfiguration])
        (let ([m (reset-election-deadline/leader timer-manager self m)])
          (goto Follower (NoLeader) (for-follower/leader m) replicated-log config))))

      ;; ---------------------------------------------------------------------------------------------------
      ;; Behavior

      (goto Init)

      ;; ---------------------------------------------------------------------------------------------------
      ;; States

      (define-state (Init) (m)
        (case m
          [(Config config)
           ;; TODO:
            (let ([metadata (reset-election-deadline/follower timer-manager self (initial-metadata))])
              (goto Follower
                    (NoLeader)
                    metadata
                    (replicated-log-empty)
                    config))]
          [(ClientMessage client cmd) (goto Init)]
          [(PeerMessage r) (goto Init)]
          [(Timeout id) (goto Init)]
          [(SendHeartbeatTimeouts id) (goto Init)]))

      (define-state (Follower [recently-contacted-by-leader MaybeLeader]
                              [metadata StateMetadata]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration]) (m)
        (case m

        [(ClientMessage client command)
                       (send client (LeaderIs recently-contacted-by-leader))
                       (goto Follower recently-contacted-by-leader metadata replicated-log config)]
        [(PeerMessage m)
                       (case m
                         [(RequestVote term candidate last-term last-index)
                                      (cond
                                        [(grant-vote?/follower metadata replicated-log term candidate last-term last-index)
                                         (send candidate (PeerMessage (VoteCandidate term self)))
                                         ;; NOTE: akka-raft did not update the term here, which I think is a bug
                                         (let ([metadata (reset-election-deadline/follower timer-manager self metadata)])
                                           (goto Follower recently-contacted-by-leader
                                                                 (! (with-vote metadata term candidate) [current-term term])
                                                                 replicated-log
                                                                 config))]
                                        [else
                                         (let ([metadata (! metadata [current-term (max term (: metadata current-term))])])
                                           (send candidate (PeerMessage (DeclineCandidate (: metadata current-term) self)))
                                           (goto Follower recently-contacted-by-leader metadata replicated-log config))])]
                         [(VoteCandidate t f)
                                        (goto Follower recently-contacted-by-leader metadata replicated-log config)]
                         [(DeclineCandidate t f)
                                           (goto Follower recently-contacted-by-leader metadata replicated-log config)]
                         [(AppendEntries term prev-term prev-index entries leader-commit-id leader leader-client)
                                        (let ([recently-contacted-by-leader (JustLeader leader-client)])
                                          (append-entries term
                                                          prev-term
                                                          prev-index
                                                          entries
                                                          leader-commit-id
                                                          leader
                                                          metadata
                                                          replicated-log
                                                          config
                                                          recently-contacted-by-leader))]
                         [(AppendRejected t l m)
                                         (goto Follower recently-contacted-by-leader metadata replicated-log config)]
                         [(AppendSuccessful t l m)
                                           (goto Follower recently-contacted-by-leader metadata replicated-log config)])]
      [(Config c) (goto Follower recently-contacted-by-leader metadata replicated-log config)]
        [(Timeout id)
                  (cond
                    [(= id (: metadata last-used-timeout-id))
                     (begin-election timer-manager self metadata replicated-log config self)]
                    [else (goto Follower recently-contacted-by-leader metadata replicated-log config)])]
      ;;   [(begin-election-alerts )
      ;;                          (goto Follower recently-contacted-by-leader metadata replicated-log config)]
      ;;   [(elected-as-leader)
      ;;                      (goto Follower recently-contacted-by-leader metadata replicated-log config)]
        [(SendHeartbeatTimeouts id)
         (goto Follower recently-contacted-by-leader metadata replicated-log config)]))
      (define-state (Candidate [m ElectionMeta]
                               [replicated-log ReplicatedLog]
                               [config ClusterConfiguration]) (message)
                                                           (printf "became candidate\n")
        (case message
        [(ClientMessage client command)
                       (send client (LeaderIs (NoLeader)))
                       (goto Candidate m replicated-log config)]
        [(PeerMessage msg)
                       (case msg
                         [(RequestVote term candidate last-log-term last-log-index)
                                      (cond
                                        [(grant-vote?/candidate m replicated-log term candidate last-log-term last-log-index)
                                         (send candidate (PeerMessage (VoteCandidate term self)))
                                         ;; TODO: this seems wrong that we stay in candidate instead of
                                         ;; going to Follower. Some test should probably break this
                                         (goto Candidate (with-vote-for m term candidate) replicated-log config)]
                                        [else
                                         (let ([m (! m [current-term (max term (: m current-term))])])
                                           (send candidate (PeerMessage (DeclineCandidate (: m current-term) self)))
                                           (goto Candidate m replicated-log config))])]
                         [(VoteCandidate term follower)
                                        (cond
                                          [(= term (: m current-term))
                                           (let ([including-this-vote (inc-vote m follower)])
                                             (cond
                                               [(has-majority including-this-vote config)
                                                ;; TODO:
                                                ;; (send self (ElectedAsLeader))
                                                (cancel-election-deadline timer-manager)
                                                ;; NOTE: have to just make up fake temporary values for the log index maps, for now
                                                (goto Leader (for-leader m) (hash) (hash) replicated-log config)]
                                               [else
                                                (goto Candidate including-this-vote replicated-log config)]))]
                                          [else (goto Candidate m replicated-log config)])]
                         [(DeclineCandidate term server) (goto Candidate m replicated-log config)]
                         [(AppendEntries term
                                         prev-log-term
                                         prev-log-index
                                         entries
                                         leader-commit-id
                                         leader
                                         leader-client)
                                        (let ([leader-is-ahead (>= term (: m current-term))])
                                          (cond
                                            [leader-is-ahead
                                             ;; TODO: instead of doing the call to append-entries and
                                             ;; the let, just do this self-send and Follower goto
                                             ;; (send self msg)
                                             ;; (let ([m (reset-election-deadline/candidate timer-manager self m)])
                                             ;;   (goto Follower (Just leader-client)
                                             ;;                         (for-follower/candidate m)
                                             ;;                         replicated-log
                                             ;;                         config))
                                             ;; TODO: remove this code; replace with above
                                             (let ([recently-contacted-by-leader (JustLeader leader-client)])
                                               (append-entries term
                                                               prev-log-term
                                                               prev-log-index
                                                               entries
                                                               leader-commit-id
                                                               leader
                                                               (for-follower/candidate m)
                                                               replicated-log
                                                               config
                                                               recently-contacted-by-leader))
                                             ]
                                            [else
                                             ;; BUG: original code left out the response
                                             (send leader
                                                   (PeerMessage
                                                    (AppendRejected (: m current-term)
                                                                    (replicated-log-last-index replicated-log)
                                                                    self)))
                                             (goto Candidate m replicated-log config)]))]
                         [(AppendSuccessful t i member) (goto Candidate m replicated-log config)]
                         [(AppendRejected t i member) (goto Candidate m replicated-log config)]
                         )]
        [(Config c) (goto Candidate m replicated-log config)]
        [(Timeout id)
                  (cond
                    [(= id (: m last-used-timeout-id))
                     ;; TODO: deal with self-sends
                     (send self (BeginElectionAlerts))
                     (goto Candidate (for-new-election/candidate m) replicated-log config)]
                    [else (goto Candidate m replicated-log config)])]
      ;;   [(begin-election-alerts)
      ;;                          (let ([request (RequestVote (: m current-term)
      ;;                                                      self
      ;;                                                      (replicated-log-last-term replicated-log)
      ;;                                                      (replicated-log-last-index replicated-log))])
      ;;                            (for ([member (members-except-self config self)])
      ;;                              (send member request))
      ;;                            (let* ([m (reset-election-deadline/candidate timer-manager self m)]
      ;;                                   [including-this-vote (inc-vote m self)]) ; this is the self vote
      ;;                              (goto Candidate (with-vote-for including-this-vote (: m current-term) self)
      ;;                                                     replicated-log config)))]
      ;;   [(elected-as-leader) (goto Candidate m replicated-log config)]
        [(SendHeartbeatTimeouts id) (goto Candidate m replicated-log config)]))

      (define-state (Leader [m LeaderMeta]
                            [next-index (Hash (Addr RaftMessage) Nat)]
                            [match-index (Hash (Addr RaftMessage) Nat)]
                            [replicated-log ReplicatedLog]
                            [config ClusterConfiguration]) (message)
                            (printf "became leader\n")
        (case message
        [(ClientMessage client command)
         (let* ([entry (Entry command
                              (: m current-term) (replicated-log-next-index replicated-log)
                              client)]
                [replicated-log (replicated-log+ replicated-log entry)]
                [match-index (hash-set match-index self (: entry index))])
           (replicate-log m next-index replicated-log config)
           (goto Leader m next-index match-index replicated-log config))]
        [(PeerMessage msg)
                       (case msg
                         [(RequestVote term candidate last-log-term last-log-index)
                                      (cond
                                        [(grant-vote?/leader m replicated-log term candidate last-log-term last-log-index)
                                         (send candidate (PeerMessage (VoteCandidate term self)))
                                         (stop-heartbeat)
                                         (step-down m replicated-log config)]
                                        [(> term (: m current-term))
                                         (let ([m (! m [current-term term])])
                                           (send candidate (PeerMessage (DeclineCandidate term self)))
                                           (step-down m replicated-log config))]
                                        [else
                                         (send candidate (PeerMessage (DeclineCandidate (: m current-term) self)))
                                         (goto Leader m next-index match-index replicated-log config)])]
                         [(VoteCandidate t s) (goto Leader m next-index match-index replicated-log config)]
                         [(DeclineCandidate t s) (goto Leader m next-index match-index replicated-log config)]
                         [(AppendEntries term
                                         prev-log-term
                                         prev-log-index
                                         entries
                                         leader-commit-id
                                         leader
                                         leader-client)
                                        (cond
                                          [(> term (: m current-term))
                                           (stop-heartbeat)
                                           ;; TODO: do this self-send and step-down instead of the
                                           ;; code below that copies the Follower code
                                           ;;
                                           ;; (send self msg)
                                           ;; (step-down m replicated-log config)
                                           ;; TODO: remove this entire let block
                                           (let ([m (reset-election-deadline/leader timer-manager self m)])
                                             (let ([recently-contacted-by-leader (JustLeader leader-client)])
                                               (append-entries term
                                                               prev-log-term
                                                               prev-log-index
                                                               entries
                                                               leader-commit-id
                                                               leader
                                                               (for-follower/leader m)
                                                               replicated-log
                                                               config
                                                               recently-contacted-by-leader)))]
                                          [else
                                           ;; NOTE: this send is my own code, not the akka-raft code
                                           (send leader (PeerMessage (AppendRejected (: m current-term)
                                                                                     (replicated-log-last-index replicated-log)
                                                                                     self)))
                                           ;; BUG: this is where akka-raft sends entries back instead
                                           ;; of the rejection response
                                           ;;
                                           ;; (send-entries leader
                                           ;;               m
                                           ;;               replicated-log
                                           ;;               next-index
                                           ;;               (: replicated-log committed-index)
                                           ;;               self
                                           ;;               self)
                                           (goto Leader m next-index match-index replicated-log config)])]
                         [(AppendRejected term last-index member)
                                         (register-append-rejected term
                                                                   last-index
                                                                   member
                                                                   m
                                                                   next-index
                                                                   match-index
                                                                   replicated-log
                                                                   config)]
                         [(AppendSuccessful term last-index member)
                                           (register-append-successful term
                                                                       last-index
                                                                       member
                                                                       m
                                                                       next-index
                                                                       match-index
                                                                       replicated-log
                                                                       config)])]
      [(Config c) (goto Leader m next-index match-index replicated-log config)]
        [(Timeout id) (goto Leader m next-index match-index replicated-log config)]
      ;;   [(begin-election-alerts) (goto Leader m next-index match-index replicated-log config)]
      ;;   [(elected-as-leader)
      ;;                      (let ([next-index (log-index-map-initialize (: config members)
      ;;                                                                  (+ (replicated-log-last-index replicated-log) 1))]
      ;;                            [match-index (log-index-map-initialize (: config members) 0)])
      ;;                        (start-heartbeat m next-index replicated-log config)
      ;;                        (goto Leader m next-index match-index replicated-log config))]
        [(SendHeartbeatTimeouts id)
         (send-heartbeat m next-index replicated-log config)
         (goto Leader m next-index match-index replicated-log config)])))
;; TODO: think of a way to not have to give concrete addresses here
    (spawn RaftActor (addr 2) (addr 3)))))

;; TODO: write a test that checks the Raft program's grammar (later: and type-checks it)

;; 2. Desugar that into the actor definition the verifier needs/translate it into the structural
;; version, using arbitrary addresses for each initial output address
(define desugared-raft-program (desugar-single-actor-program raft-actor-surface-prog))
(define desugared-raft-actor
  (single-agent-prog->config desugared-raft-program single-agent-concrete-addr))

(check-not-false (redex-match csa-eval e desugared-raft-program))
(check-not-false (redex-match csa-eval αn desugared-raft-actor))
(check-not-false (redex-match aps-eval z raft-spec))

;; 3. Move the actor definition into a config, with addresses assigned appropriately
(define raft-config (make-single-agent-config desugared-raft-actor))

(define cluster-config-variant
  ;; TODO:
  (term (Config (Record [members (Listof (Addr Nat ;; RaftMessage
                             ))]))))

(define desugared-raft-message-type
  `(Union
    (RequestVote Nat
                 (Addr Nat) ;; TODO: add the minfixpt here
                 Nat
                 Nat)
    (VoteCandidate Nat (Addr Nat))
    (DeclineCandidate Nat (Addr Nat)) ;; TODO: add the minfixpt here
    (AppendEntries
     Nat
     Nat
     Nat
     (Vectorof (Record [command String] [term Nat] [index Nat] [client (Addr String)]))
     Nat
     (Addr Nat) ; TODO: add the minfixpt here
     (Addr Nat)) ; TODO: add a real representation of the ClientMessage type here
    (AppendRejected Nat Nat (Addr Nat)) ; TODO: add the minfixpt here
    (AppendSuccessful Nat Nat (Addr Nat)))   ; TODO: add the minfixpt here
  )
;; 4. Run the verifier
(check-true (analyze raft-config
                     raft-spec
                     (term (Union (PeerMessage ,desugared-raft-message-type)))
                     (term (Union ,cluster-config-variant
                                  (ClientMessage (Addr Nat) ; TODO: add the real type here
                                                 String)
                                  (Timeout Nat)
                                  (SendHeartbeatTimeouts Nat)))
                     (hash 'Init 'Init
                           'Follower 'Running
                           'Candidate 'Running
                           'Leader 'Running)))
