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
       [unobs -> (goto Running)])
     (define-state (Running)
       ;; [(RequestVote _ candidate _ _) -> ]
       ;; [(VoteCandidate _ _) -> ???]
       ;; [(DeclineCandidate _ _) -> ???]
       ;; [(AppendEntries _ _ _ _ _ leader _) -> ???]
       ;; [(AppendRejected _ _ _) -> ???]
       ;; [(AppendSuccessful _ _ _) -> ???]
       ))
    ;; TODO: switch the order of the init exp adn the states
    (goto Init)
    ,single-agent-concrete-addr)))

(check-not-false (redex-match aps-eval z raft-spec))

;; 1. Define Raft in the basic syntax
(define raft-actor-surface-prog

  (term
   (
    (define-type Unit (Record))
    (define-type Duration Nat) ; number of seconds
    (define-variant Boolean (True) (False))
    ;; TODO: actually define Int
    (define-type Int Nat)

    ;; ---------------------------------------------------------------------------------------------------
    ;; Fake Vector and Hash Definitions

    (define-function (vector) (variant DummyVector))
    (define-function (hash) (variant DummyHash))

    ;; ---------------------------------------------------------------------------------------------------


    (define-record ClusterConfiguration
      ;; TODO:
      [members Nat ;; (Listof (Addr RaftMessage))
               ]
      ;; ignoring other config fields for now, since I'm not implementing configuration changes
      )

    (define-variant RaftActorMessage
      (Config [config ClusterConfiguration]))

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
   ;; TODO: allow for fixpoint types
   ;; [candidate (Addr RaftMessage)]
   [last-log-term Nat]
   [last-log-index Nat])
  (VoteCandidate
   [term Nat]
   ;; [follower (Addr RaftMessage)]
   )
  (DeclineCandidate
   [term Nat]
   ;; [follower (Addr RaftMessage)]
   )
  (AppendEntries
   [term Nat]
   [prev-log-term Nat]
   [prev-log-index Nat]
   ;; [entries (Vectorof Entry)]
   [leader-commit-id Nat]
   ;; [leader (Addr RaftMessage)]
   ;; [leader-client (Addr ClientMessage)]
   )
  ;; A note on last-index: In the paper, this is the optimization at the bottom of p. 7 that allows
  ;; for quicker recovery of a node that has fallen behind in its log. In RaftScope, they call this
  ;; "matchIndex", which indicates the lat index in the log (or 0 for AppendRejected). In akka-raft,
  ;; this is always the last index of the log (for both success and failure)
  (AppendRejected
   [term Nat]
   [last-index Nat]
   ;; [member (Addr RaftMessage)]
   )
  (AppendSuccessful
   [term Nat]
   [last-index Nat]
   ;; [member (Addr RaftMessage)]
   ))

;; (define-variant MaybePeer
;;   (NoPeer)
;;   (JustPeer [peer (Addr RaftMessage)]))

(define-record StateMetadata
  [current-term Nat]
  [votes (Hash Nat (Addr RaftMessage))]
  [last-used-timeout-id Nat])

;; (define-record ElectionMeta
;;   [current-term Nat]
;;   [votes-received (Hash (Addr RaftMessage) Bool)]
;;   [votes (Hash Nat (Addr RaftMessage))]
;;   [last-used-timeout-id Nat])

;; (define-record LeaderMeta
;;   [current-term Nat]
;;   [last-used-timeout-id Nat])

(define-variant TimerMessage
  (SetTimer [timer-name String] [target (Addr Unit)] [id Nat] [duration Duration] [repeat? Boolean])
  (CancelTimer [timer-name String]))

;; (define-record AppendResult
;;   [message RaftMessage]
;;   [log ReplicatedLog])

(define-record ReplicatedLog
  [entries (Vectorof Entry)]
  [committed-index Int])

    ;;;; Program-level Functions
    ;; ---------------------------------------------------------------------------------------------------
;; State metadata helpers

;; (define-function (grant-vote?/follower [metadata StateMetadata]
;;                               [log ReplicatedLog]
;;                               [term Nat]
;;                               [candidate (Addr RaftMessage)]
;;                               [last-log-term Nat]
;;                               [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
;;        (case (hash-ref (: metadata votes) term)
;;          [Nothing () (True)]
;;          [Just (c) (= candidate c)])))

;; (define-function (grant-vote?/candidate [metadata StateMetadata]
;;                                [log ReplicatedLog]
;;                                [term Nat]
;;                                [candidate (Addr RaftMessage)]
;;                                [last-log-term Nat]
;;                                [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)
;;        (case (hash-ref (: metadata votes) term)
;;          [Nothing () (True)]
;;          [Just (c) (= candidate c)])))

;; (define-function (grant-vote?/leader [metadata StateMetadata]
;;                             [log ReplicatedLog]
;;                             [term Nat]
;;                             [candidate (Addr RaftMessage)]
;;                             [last-log-term Nat]
;;                             [last-log-index Nat])
;;   (and (>= term (: metadata current-term))
;;        (candidate-at-least-as-up-to-date? log last-log-term last-log-index)))

;; (define-function (candidate-at-least-as-up-to-date? [log ReplicatedLog]
;;                                            [candidate-log-term Nat]
;;                                            [candidate-log-index Nat])
;;   (let ([my-last-log-term (replicated-log-last-term log)])
;;     (or (> candidate-log-term my-last-log-term)
;;         (and (= candidate-log-term my-last-log-term)
;;              (>= candidate-log-index (replicated-log-last-index log))))))

;; (define-function (with-vote [metadata StateMetadata] [term Nat] [candidate (Addr RaftMessage)])
;;   (! metadata [votes (hash-set (: metadata votes) term candidate)]))

(define-function (initial-metadata)
  (StateMetadata 0 (hash) 0))

;; (define-function (for-follower/candidate [metadata ElectionMeta])
;;   (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

;; (define-function (for-follower/leader [metadata LeaderMeta])
;;   (StateMetadata (: metadata current-term) (hash) (: metadata last-used-timeout-id)))

;; (define-function (for-leader [metadata ElectionMeta])
;;   (LeaderMeta (: metadata current-term) (: metadata last-used-timeout-id)))

;; ---------------------------------------------------------------------------------------------------
;; Election

;; ;; All times are in milliseconds
;; TODO: define these as constants in the program
(define-constant election-timeout-min 0)
(define-constant election-timeout-max 100)
(define-constant election-timer-name "ElectionTimer")

;; ;; Resets the timer for the election deadline and returns the metadata with the new expected next
;; ;; timeout ID
(define-function (reset-election-deadline/follower [timer (Addr TimerMessage)]
                                                   [target (Addr Nat)]
                                                   [m StateMetadata])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline (False)))
    (! m [last-used-timeout-id next-id])))

;; (define-function (reset-election-deadline/candidate [timer (Addr TimerMessage)]
;;                                            [target (Addr Nat)]
;;                                            [m ElectionMeta])
;;   (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
;;         [next-id (+ 1 (: m last-used-timeout-id))])
;;     (send timer (SetTimer election-timer-name target next-id deadline (False)))
;;     (! m [last-used-timeout-id next-id])))

;; (define-function (reset-election-deadline/leader [timer (Addr TimerMessage)]
;;                                         [target (Addr Nat)]
;;                                         [m LeaderMeta])
;;   (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
;;         [next-id (+ 1 (: m last-used-timeout-id))])
;;     (send timer (SetTimer election-timer-name target next-id deadline (False)))
;;     (! m [last-used-timeout-id next-id])))

;; (define-function (cancel-election-deadline [timer (Addr TimerMessage)])
;;   (send timer (CancelTimer election-timer-name)))

;; ;; Because this language does not have traits, I separate forNewElection into two functions
;; (define-function (for-new-election/follower [m StateMetadata])
;;   (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; (define-function (for-new-election/candidate [m StateMetadata])
;;   (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; ;; this effectively duplicates the logic of withVote, but it follows the akka-raft code
;; (define-function (with-vote-for [m ElectionMeta] [term Nat] [candidate (Addr RaftMessage)])
;;   (! m [votes (hash-set (: m votes) term candidate)]))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Terms

;; (define-function (next [term Nat])
;;   (+ 1 term))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Config helpers

;; (define-function (members-except-self [config ClusterConfiguration] [self (Addr RaftMessage)])
;;   (for/fold ([result null])
;;             ([member (: config members)])
;;     (if (not (= member self)) (cons member result) result)))

;; (define-function (inc-vote [m ElectionMeta] [follower (Addr RaftMessage)])
;;   (! m [votes-received (hash-set (: m votes-received) follower (True))]))

;; (define-function (has-majority [m ElectionMeta] [config ClusterConfiguration])
;;   ;; TODO: figure out what the type for division is here (or maybe rewrite to not use division)
;;   (let ([total-votes-received
;;          (for/fold ([total 0])
;;                    ([member (: config members)])
;;            (+ total (if (hash-has-key? (: m votes-received) member) 1 0)))])
;;     (> total-votes-received (/ (length (: config members)) 2))))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; Misc.

;; (define-function (leader-is-lagging [append-entries-term Nat] [m StateMetadata])
;;   (< append-entries-term (: m current-term)))

;; (define-function (is-heartbeat [append-entries-entries (Vectorof Entry)])
;;   (= 0 (vector-length append-entries-entries)))

;; (define-function (AppendEntries-apply [term Nat]
;;                              [replicated-log ReplicatedLog]
;;                              [from-index Nat]
;;                              [leader-commit-id Nat]
;;                              [leader (Addr RaftMessage)]
;;                              [leader-client (Addr ClientMessage)])
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

(define-function (replicated-log-empty)
  (ReplicatedLog (vector) 0))

;; (define-function (replicated-log+ [replicated-log ReplicatedLog] [entry Entry])
;;   (replicated-log-append replicated-log (vector entry) (vector-length (: replicated-log entries))))

;; ;; Takes the first *take* entries from the log and appends *entries* onto it, returning the new log
;; (define-function (replicated-log-append [log ReplicatedLog] [entries-to-append (Vectorof Entry)] [take Nat])
;;   (! log [entries (vector-append (vector-take (: log entries) take) entries-to-append)]))

;; (define-function (replicated-log-commit [replicated-log ReplicatedLog] [n Int])
;;   (! replicated-log [commit-index n]))

;; ;; Returns the log entries from from-index (exclusive) to to-index (inclusive) (these are *semantic*
;; ;; indices)
;; (define-function (replicated-log-between [replicated-log ReplicatedLog] [from-index Int] [to-index Int])
;;   ;; NOTE: this naive conversion from semantic to implementation indices won't work under log
;;   ;; compaction
;;   (let ([vector-from-index (- from-index 1)]
;;         [vector-to-index   (- to-index   1)])
;;       (vector-slice (: replicated-log entries) (+ 1 vector-from-index) (+ 1 vector-to-index))))

;; (define-function (replicated-log-last-index [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 0]
;;       [else (: (vector-ref entries (- (vector-length entries) 1)) index)])))

;; (define-function (replicated-log-last-term [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 0]
;;       [else (: (vector-ref entries (- (vector-length entries) 1)) term)])))

;; ;; NOTE: this differs from the akka-raft version, which is broken
;; (define-function (replicated-log-next-index [replicated-log ReplicatedLog])
;;   (let ([entries (: replicated-log entries)])
;;     (cond
;;       [(= 0 (vector-length entries)) 1]
;;       [else (+ (: (vector-ref entries (- (vector-length entries) 1)) index) 1)])))

;; ;; Returns (True) if the leader's previous log is consistent with ours (i.e. the term of the previous
;; ;; index matches the term at that index in our log)
;; (define-function (replicated-log-consistent-update [replicated-log Replicated-Log]
;;                                           [prev-log-term Nat]
;;                                           [prev-log-index Nat])
;;   (= (replicated-log-term-at replicated-log prev-log-index) prev-log-term))

;; (define-variant FindTermResult (NoTerm) (FoundTerm [term Nat]))
;; (define-function (replicated-log-term-at [replicated-log ReplicatedLog] [index Nat])
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
;; (define-function (replicated-log-entries-batch-from [replicated-log ReplicatedLog] [from-including Nat])
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

;; (define-function (min [a Nat] [b Nat])
;;   (cond [(< a b) a] [else b]))

;; (define-function (entry-prev-index [entry Entry])
;;   (- (: entry index) 1))

;; ;; ---------------------------------------------------------------------------------------------------
;; ;; LogIndexMap

;; (define-function (log-index-map-initialize [members (Listof (Addr RaftMessage))] [initialize-with Nat])
;;   (for/fold ([map (hash)])
;;             ([member members])
;;     (hash-set map member initialize-with)))

;; (define-function (log-index-map-value-for [map (Hash (Addr RaftMessage) Nat)]
;;                                  [member (Addr RaftMessage)])
;;   (case (hash-ref map member)
;;     [Nothing ()
;;       ;; akka-raft would update the map here, but we should never have to because we don't change the
;;       ;; config
;;       0]
;;     [Just (value) value]))

;; (define-function (log-index-map-put-if-greater [map (Hash (Addr RaftMessage) Nat)]
;;                                       [member (Addr RaftMessage)]
;;                                       [value Nat])
;;   (let ([old-value (log-index-map-value-for map member)])
;;     (cond
;;       [(< old-value value) (hash-set map member value)]
;;       [else map])))

;; (define-function (log-index-map-put-if-smaller [map (Hash (Addr RaftMessage) Nat)]
;;                                       [member (Addr RaftMessage)]
;;                                       [value Nat])
;;   (let ([old-value (log-index-map-value-for map member)])
;;     (cond
;;       [(> old-value value) (hash-set map member value)]
;;       [else map])))

;; ;; NOTE: because the akka-raft version of this is completely wrong, I'm writing my own
;; ;; Returns the greatest index that a majority of entries in the map agree on
;; (define-function (log-index-map-consensus-for-index [map (Hash (Addr RaftMessage) Nat)]
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
;; (define-function (vector-slice [v (Vectorof Entries)] [from-index Int] [to-index Int])
;;   (vector-copy v
;;                (min from-index (vector-length v))
;;                (min to-index   (vector-length v))))




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
      ;; (define-function (begin-election [timer (Addr TimerMessage)]
      ;;                         [election-timeout-target (Addr Nat)]
      ;;                         [metadata StateMetadata]
      ;;                         [replicated-log ReplicatedLog]
      ;;                         [config ClusterConfiguration]
      ;;                         [begin-election-alerts (Addr)])
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
      ;;   (goto (Candidate (for-new-election/follower metadata) replicated-log config))
      ;;   ;)
      ;;   ;)
      ;;   )

      ;; ;; TODO: consider making AppendEntries into a record to remove these long param lists and better
      ;; ;; match akka-raft
      ;; (define-function (append-entries [term Nat]
      ;;                         [prev-log-term Nat]
      ;;                         [prev-log-index Nat]
      ;;                         [entries (Vectorof Entry)]
      ;;                         [leader-commit-id Nat]
      ;;                         [leader (Addr RaftMessage)]
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
      ;;      (goto (Follower recently-contacted-by-leader m replicated-log config))]
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
      ;;        (let  ([replicated-log (commit-until-index (: append-result log) leader-commit-id (False))])
      ;;          (accept-heartbeat meta-with-updated-term
      ;;                            replicated-log
      ;;                            config
      ;;                            recently-contacted-by-leader)))]))

      ;; ;; appends the entries to the log and returns the success message to send
      ;; (define-function (append [replicated-log ReplicatedLog]
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
      ;; (define-function (accept-heartbeat [m StateMetadata]
      ;;                           [replicated-log ReplicatedLog]
      ;;                           [config ClusterConfiguration]
      ;;                           [recently-contacted-by-leader MaybeLeader])
      ;;   (let ([m (reset-election-deadline/follower timer-manager timeouts m)])
      ;;     (goto (Follower recently-contacted-by-leader m replicated-log config))))

      ;; (define-function (commit-until-index [replicated-log ReplicatedLog]
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

      ;; (define-constant heartbeat-timer-name "HeartbeatTimer")
      ;; (define-constant heartbeat-interval 50)
      ;; (define-function (start-heartbeat [m LeaderMeta] [next-index (Hash (Addr RaftMessage) Nat)]
      ;;                          [replicated-log ReplicatedLog]
      ;;                          [config ClusterConfiguration])
      ;;   (send-heartbeat m next-index replicated-log config)
      ;;   (send timer-manager
      ;;         (SetTimer heartbeat-timer-name send-heartbeat-timeouts 1 heartbeat-interval (True))))

      ;; (define-function (stop-heartbeat)
      ;;   (send timer-manager (CancelTimer heartbeat-timer-name)))

      ;; (define-function (send-heartbeat [m LeaderMeta]
      ;;                         [next-index (Hash (Addr RaftMessage) Nat)]
      ;;                         [replicated-log ReplicatedLog]
      ;;                         [config ClusterConfiguration])
      ;;   (replicate-log m next-index replicated-log config))

      ;; (define-function (replicate-log [m LeaderMeta]
      ;;                        [next-index (Hash (Addr RaftMessage) Nat)]
      ;;                        [replicated-log ReplicatedLog]
      ;;                        [config ClusterConfiguration])
      ;;   (for ([member (members-except-self config peer-messages)])
      ;;     (send member (AppendEntries-apply (: m current-term)
      ;;                                       replicated-log
      ;;                                       (log-index-map-value-for next-index member)
      ;;                                       (: replicated-log committed-index)
      ;;                                       peer-messages
      ;;                                       client-messages))))

      ;; (define-function (send-entries [follower (Addr RaftMessage)]
      ;;                       [m LeaderMeta]
      ;;                       [replicated-log ReplicatedLog]
      ;;                       [next-index Nat]
      ;;                       [leader-commit-id Nat]
      ;;                       [leader (Addr RaftMessage)]
      ;;                       [leader-client (Addr ClientMessage)])
      ;;   (send follower (AppendEntries-apply (: m current-term)
      ;;                                       replicated-log
      ;;                                       (log-index-map-value-for next-index follower)
      ;;                                       (: replicated-log committed-index)
      ;;                                       peer-messages
      ;;                                       client-messages)))

      ;; ;; TODO: define messages like this alongside handlers in a state, so we don't have to repeat state
      ;; ;; fields so much
      ;; (define-function (register-append-successful [follower-term Nat]
      ;;                                     [follower-index Nat]
      ;;                                     [member (Addr RaftMessage)]
      ;;                                     [m LeaderMeta]
      ;;                                     [next-index (Hash (Addr RaftMessage) Nat)]
      ;;                                     [match-index (Hash (Addr RaftMessage) Nat)]
      ;;                                     [replicated-log ReplicatedLog]
      ;;                                     [config ClusterConfiguration])
      ;;   ;; TODO: why don't both indices use put-if-greater?
      ;;   (let* ([next-index (hash-set next-index member follower-index)]
      ;;          [match-index (log-index-map-put-if-greater match-index
      ;;                                                     member
      ;;                                                     (log-index-map-value-for next-index member))]
      ;;          [replicated-log (maybe-commit-entry match-index replicated-log config)])
      ;;     (goto (Leader m next-index match-index replicated-log config))))

      ;; (define-function (register-append-rejected [follower-term Nat]
      ;;                                   [follower-index Nat]
      ;;                                   [member (Addr RaftMessage)]
      ;;                                   [m LeaderMeta]
      ;;                                   [next-index (Hash (Addr RaftMessage) Nat)]
      ;;                                   [match-index (Hash (Addr RaftMessage) Nat)]
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
      ;;     (goto (Leader m next-index match-index replicated-log config))))

      ;; (define-function (maybe-commit-entry [match-index (Hash (Addr RaftMessage) Nat)]
      ;;                             [replicated-log ReplicatedLog]
      ;;                             [config ClusterConfiguration])
      ;;   (let ([index-on-majority (log-index-map-consensus-for-index match-index config)])
      ;;     (let ([will-commit (> index-on-majority (: replicated-log committed-index))])
      ;;       (cond
      ;;         [will-commit (commit-until-index replicated-log index-on-majority (True))]
      ;;         [else replicated-log]))))

      ;; (define-function (step-down [m LeaderMeta] [replicated-log ReplicatedLog] [config ClusterConfiguration])
      ;;   (let ([m (reset-election-deadline/leader timer-manager timeouts m)])
      ;;     (goto (Follower (NoLeader) (for-follower/leader m) replicated-log config))))
       )
      (goto Init)

      (define-state (Init) (m)
        (case m
          [(Config config)
           ;; TODO:
            (let ([metadata (reset-election-deadline/follower timer-manager self (initial-metadata))])
              (goto Follower
                    (NoLeader)
                    metadata
                    (replicated-log-empty)
                    config))])
)

      (define-state (Follower [recently-contacted-by-leader MaybeLeader]
                              [metadata StateMetadata]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration]) (m)
                              (goto Follower recently-contacted-by-leader metadata replicated-log config)
      ;;   [client-messages (m)
      ;;                    (case m
      ;;                      [ClientMessage (client command)
      ;;                                     (send client (LeaderIs recently-contacted-by-leader))
      ;;                                     (goto (Follower recently-contacted-by-leader metadata replicated-log config))])]
      ;;   [peer-messages (m)
      ;;                  (case m
      ;;                    [RequestVote (term candidate last-term last-index)
      ;;                                 (cond
      ;;                                   [(grant-vote?/follower metadata replicated-log term candidate last-term last-index)
      ;;                                    (send candidate (VoteCandidate term peer-messages))
      ;;                                    ;; NOTE: akka-raft did not update the term here, which I think is a bug
      ;;                                    (let ([metadata (reset-election-deadline/follower timer-manager timeouts metadata)])
      ;;                                      (goto (Follower recently-contacted-by-leader
      ;;                                                            (! (with-vote metadata term candidate) [current-term term])
      ;;                                                            replicated-log
      ;;                                                            config)))]
      ;;                                   [else
      ;;                                    (let ([metadata (! metadata [current-term (max term (: metadata current-term))])])
      ;;                                      (send candidate (DeclineCandidate (: metadata current-term) peer-messages))
      ;;                                      ;; TODO: change this to goto-this-state, once I reimplement/find that
      ;;                                      (goto (Follower recently-contacted-by-leader metadata replicated-log config)))])]
      ;;                    [VoteCandidate (t f)
      ;;                                   (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
      ;;                    [DeclineCandidate (t f)
      ;;                                      (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
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
      ;;                                    (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
      ;;                    [AppendSuccessful (t l m)
      ;;                                      (goto (Follower recently-contacted-by-leader metadata replicated-log config))])]
      ;;   [configs (c) (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
      ;;   [timeouts (id)
      ;;             (cond
      ;;               [(= id (: metadata last-used-timeout-id))
      ;;                (begin-election timer-manager timeouts metadata replicated-log config begin-election-alerts)]
      ;;               [else (goto (Follower recently-contacted-by-leader metadata replicated-log config))])]
      ;;   [begin-election-alerts ()
      ;;                          (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
      ;;   [elected-as-leader ()
      ;;                      (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
      ;;   [send-heartbeat-timeouts (id)
      ;;                            (goto (Follower recently-contacted-by-leader metadata replicated-log config))]
 )
      (define-state (Candidate [m Nat ;; ElectionMeta
                                  ]
                               [replicated-log Nat ;; ReplicatedLog
                                               ]
                               [config ClusterConfiguration]) (m)
                               (goto Candidate)
      ;;   [client-messages (m)
      ;;                    (case m
      ;;                      [ClientMessage (client command)
      ;;                                     (send client (LeaderIs (NoLeader)))
      ;;                                     (goto (Candidate m replicated-log config))])]
      ;;   [peer-messages (msg)
      ;;                  (case msg
      ;;                    [RequestVote (term candidate last-log-term last-log-index)
      ;;                                 (cond
      ;;                                   [(grant-vote?/candidate m replicated-log term candidate last-log-term last-log-index)
      ;;                                    (send candidate (VoteCandidate term peer-messages))
      ;;                                    ;; TODO: this seems wrong that we stay in candidate instead of
      ;;                                    ;; going to Follower. Some test should probably break this
      ;;                                    (goto (Candidate (with-vote-for m term candidate) replicated-log config))]
      ;;                                   [else
      ;;                                    (let ([m (! m [current-term (max term (: m current-term))])])
      ;;                                      (send candidate (DeclineCandidate (: m current-term) peer-messages))
      ;;                                      (goto (Candidate m replicated-log config)))])]
      ;;                    [VoteCandidate (term follower)
      ;;                                   (cond
      ;;                                     [(= term (: m current-term))
      ;;                                      (let ([including-this-vote (inc-vote m follower)])
      ;;                                        (cond
      ;;                                          [(has-majority including-this-vote config)
      ;;                                           (send elected-as-leader)
      ;;                                           (cancel-election-deadline timer-manager)
      ;;                                           ;; NOTE: have to just make up fake temporary values for the log index maps, for now
      ;;                                           (goto (Leader (for-leader m) (hash) (hash) replicated-log config))]
      ;;                                          [else
      ;;                                           (goto (Candidate including-this-vote replicated-log config))]))]
      ;;                                     [else (goto (Candidate m replicated-log config))])]
      ;;                    [DeclineCandidate (term server) (goto (Candidate m replicated-log config))]
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
      ;;                                          (goto (Follower (Just leader-client)
      ;;                                                                (for-follower/candidate m)
      ;;                                                                replicated-log
      ;;                                                                config)))]
      ;;                                       [else
      ;;                                        ;; BUG: original code left out the response
      ;;                                        (send leader
      ;;                                              (AppendRejected (: m current-term)
      ;;                                                              (replicated-log-last-index replicated-log)
      ;;                                                              peer-messages))
      ;;                                        (goto (Candidate m replicated-log config))]))]
      ;;                    [AppendSuccessful (t i member) (goto (Candidate m replicated-log config))]
      ;;                    [AppendRejected (t i member) (goto (Candidate m replicated-log config))])]
      ;;   [timeouts (id)
      ;;             (cond
      ;;               [(= id (: m last-used-timeout-id))
      ;;                (send begin-election-alerts)
      ;;                (goto (Candidate (for-new-election/candidate m) replicated-log config))]
      ;;               [else (goto (Candidate m replicated-log config))])]
      ;;   [begin-election-alerts ()
      ;;                          (let ([request (RequestVote (: m current-term)
      ;;                                                      peer-messages
      ;;                                                      (replicated-log-last-term replicated-log)
      ;;                                                      (replicated-log-last-index replicated-log))])
      ;;                            (for ([member (members-except-self config peer-messages)])
      ;;                              (send member request))
      ;;                            (let* ([m (reset-election-deadline/candidate timer-manager timeouts m)]
      ;;                                   [including-this-vote (inc-vote m peer-messages)]) ; this is the self vote
      ;;                              (goto (Candidate (with-vote-for including-this-vote (: m current-term) peer-messages)
      ;;                                                     replicated-log config))))]
      ;;   [elected-as-leader () (goto (Candidate m replicated-log config))]
      ;;   [send-heartbeat-timeouts (id) (goto (Candidate m replicated-log config))]
                               )
      ;; TODO:
      (define-state (Leader [m Nat ;;LeaderMeta
                               ]
                            [next-index Nat ;; (Hash (Addr RaftMessage) Nat)
                                        ]
                            [match-index Nat;; (Hash (Addr RaftMessage) Nat)
                                         ]
                            [replicated-log Nat ;; ReplicatedLog
                                            ]
                            [config ClusterConfiguration]) (m)
                            (goto Leader)
      ;;   [client-messages (msg)
      ;;                    (case msg
      ;;                      [ClientMessage (client command)
      ;;                                     (let* ([entry (Entry command
      ;;                                                          (: m current-term) (replicated-log-next-index replicated-log)
      ;;                                                          client)]
      ;;                                            [replicated-log (replicated-log+ replicated-log entry)]
      ;;                                            [match-index (hash-set match-index peer-messages (: entry index))])
      ;;                                       (replicate-log m next-index replicated-log config)
      ;;                                       (goto (Leader m next-index match-index replicated-log config)))])]
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
      ;;                                    (goto (Leader m next-index match-index replicated-log config))])]
      ;;                    [VoteCandidate (t s) (goto (Leader m next-index match-index replicated-log config))]
      ;;                    [DeclineCandidate (t s) (goto (Leader m next-index match-index replicated-log config))]
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
      ;;                                      (goto (Leader m next-index match-index replicated-log config))])]
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
      ;;   [configs (c) (goto (Leader m next-index match-index replicated-log config))]
      ;;   [timeouts (id) (goto (Leader m next-index match-index replicated-log config))]
      ;;   [begin-election-alerts () (goto (Leader m next-index match-index replicated-log config))]
      ;;   [elected-as-leader ()
      ;;                      (let ([next-index (log-index-map-initialize (: config members)
      ;;                                                                  (+ (replicated-log-last-index replicated-log) 1))]
      ;;                            [match-index (log-index-map-initialize (: config members) 0)])
      ;;                        (start-heartbeat m next-index replicated-log config)
      ;;                        (goto (Leader m next-index match-index replicated-log config)))]
      ;;   [send-heartbeat-timeouts (id)
      ;;                            (send-heartbeat m next-index replicated-log config)
      ;;                            (goto (Leader m next-index match-index replicated-log config))]
                            ))
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
  (term (Config (Record [f1 (Record [members Nat])]))))

;; 4. Run the verifier
(check-true (analyze raft-config
                     raft-spec
                     (term (Union)) (term (Union ,cluster-config-variant))
                     (hash 'Init 'Init
                           'Follower 'Running
                           'Candidate 'Running
                           'Leader 'Running)))
