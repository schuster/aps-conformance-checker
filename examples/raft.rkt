#lang racket

;; A full test of the Raft port to CSA, verified against its spec

(provide
 raft-actor-prog
 raft-spec)

;; TODO: refactor this program to use records like those in akka-raft

(require
 redex/reduction-semantics
 "../desugar.rkt")

(define desugared-client-response-type
  `(Union [LeaderIs
           (Union [NoLeader]
                  [JustLeader (Addr (Union [ClientMessage (Addr ResponseType) String]))])]
          [CommitSuccess String]))

(define desugared-entry-type
  `(Record [command String]
           [term Nat]
           [index Nat]
           [client (Addr ,desugared-client-response-type)]))

(define desugared-raft-message-address-type
  `(minfixpt RaftMsgAddress
     (Addr
      (Union
       (RequestVote
        Nat
        RaftMsgAddress
        Nat
        Nat)

       (VoteCandidate
        Nat
        RaftMsgAddress)

       (DeclineCandidate
        Nat
        RaftMsgAddress)

       (AppendEntries
        Nat
        Nat
        Nat
        (List ,desugared-entry-type)
        Nat
        RaftMsgAddress
        (Addr (Union (ClientMessage (Addr ,desugared-client-response-type) String))))

       (AppendRejected
        Nat
        Nat
        RaftMsgAddress)

       (AppendSuccessful
        Nat
        Nat
        RaftMsgAddress)))))

(define desugared-raft-message-type
  `(Union
    (RequestVote
     Nat
     ,desugared-raft-message-address-type
     Nat
     Nat)

    (VoteCandidate
     Nat
     ,desugared-raft-message-address-type)

    (DeclineCandidate
     Nat
     ,desugared-raft-message-address-type)

    (AppendEntries
     Nat
     Nat
     Nat
     (List ,desugared-entry-type)
     Nat
     ,desugared-raft-message-address-type
     (Addr (Union (ClientMessage (Addr ,desugared-client-response-type) String))))

    (AppendRejected
     Nat
     Nat
     ,desugared-raft-message-address-type)

    (AppendSuccessful
     Nat
     Nat
     ,desugared-raft-message-address-type)))

(define cluster-config-variant
  (term (Config (Record [members (List ,desugared-raft-message-address-type)]))))

(define unobserved-interface-type
  (term
   (Union ,cluster-config-variant
          (ClientMessage (Addr ,desugared-client-response-type) String)
          (Timeout Nat)
          (SendHeartbeatTimeouts Nat))))

(define full-raft-actor-type
  (term
   (Union

    (RequestVote
     Nat
     ,desugared-raft-message-address-type
     Nat
     Nat)

    (VoteCandidate
     Nat
     ,desugared-raft-message-address-type)

    (DeclineCandidate
     Nat
     ,desugared-raft-message-address-type)

    (AppendEntries
     Nat
     Nat
     Nat
     (List ,desugared-entry-type)
     Nat
     ,desugared-raft-message-address-type
     (Addr (Union (ClientMessage (Addr ,desugared-client-response-type) String))))

    (AppendRejected
     Nat
     Nat
     ,desugared-raft-message-address-type)

    (AppendSuccessful
     Nat
     Nat
     ,desugared-raft-message-address-type)

    ,cluster-config-variant
    (ClientMessage (Addr ,desugared-client-response-type) String)
    (Timeout Nat)
    (SendHeartbeatTimeouts Nat))))

;; TODO: write a check that alerts for any underscores in the spec (b/c those are invalid)
(define raft-spec
  (term
   (specification (receptionists [raft-server ,desugared-raft-message-type] [raft-server-unobs ,unobserved-interface-type])
                  (externals)
     (mon-receptionist raft-server)
     (goto Init)
     (define-state (Init)
       [free -> () (goto Running)]
       [(variant RequestVote * candidate * *) -> () (goto Init)]
       [(variant RequestVote * candidate * *) -> () (goto Init)]
       [(variant VoteCandidate * *) -> () (goto Init)]
       [(variant DeclineCandidate * *) -> () (goto Init)]
       [(variant AppendEntries * * * * * leader *) -> () (goto Init)]
       [(variant AppendRejected * * member) -> () (goto Init)]
       [(variant AppendSuccessful * * *) -> () (goto Init)])
     (define-state (Running)
       [(variant RequestVote * candidate * *) ->
        ([obligation candidate (variant VoteCandidate * *)])
        (goto Running)]
       [(variant RequestVote * candidate * *) ->
        ([obligation candidate (variant DeclineCandidate * *)])
        (goto Running)]
       [(variant VoteCandidate * *) -> () (goto Running)]
       [(variant DeclineCandidate * *) -> () (goto Running)]
       [(variant AppendEntries * * * * * leader *) ->
        ([obligation leader (variant AppendRejected * * *)])
        (goto Running)]
       [(variant AppendEntries * * * * * leader *) ->
        ([obligation leader (variant AppendSuccessful * * *)])
        (goto Running)]
       ;; TODO: break these out into separate states so that the append retry can only happen when in
       ;; the leader state (and otherwise the leader must fall back to being a follower)
       [(variant AppendRejected * * member) -> () (goto Running)]
       ;; APS PROTOCOL BUG: to replicate, comment out this case that sends an AppendEntries back (I
       ;; left this case out the first time around)
       [(variant AppendRejected * * member) ->
        ;; TODO: should I require that the self address is in this response?
        ([obligation member (variant AppendEntries * * * * * * *)])
        (goto Running)]
       [(variant AppendSuccessful * * *) -> () (goto Running)]))))

(define raft-actor-prog (desugar (term
(program
 (receptionists [raft-server ,desugared-raft-message-type] [raft-server-unobs ,unobserved-interface-type])
 (externals [timer-manager TimerMessage] [application String])

(define-type Unit (Record))
(define-type Duration Nat) ; number of seconds
;; TODO: move these into the core language
(define-variant Boolean (True) (False))
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

;; Client message contains a command (string) to print when applying to the state machine, and a
;; channel to send to to confirm the application

(define-type ClientResponse ,desugared-client-response-type)

(define-type ClientMessage
  (Union (ClientMessage (Addr ClientResponse) String)))

;; Defining just to get the constructors
(define-variant ClientMessageBranches
  (ClientMessage [client (Addr ClientResponse)] [cmd String]))

(define-variant MaybeLeader
  (NoLeader)
  (JustLeader [leader (Addr ClientMessage)]))

;; Defining this only for the variant constructors
(define-variant ClientResponseBranches
  (LeaderIs [leader MaybeLeader])
  (CommitSuccess [cmd String]))

(define-record Entry
  [command String]
  [term Nat]
  ;; NOTE: indices start at 1 so that a committed index of 0 means nothing has been committed
  [index Nat]
  [client (Addr ClientResponse)])

;; Defined only to get the variant constructors
(define-variant RaftMessageBranches
  (RequestVote
   [term Nat]
   [candidate ,desugared-raft-message-address-type]
   [last-log-term Nat]
   [last-log-index Nat])
  (VoteCandidate
   [term Nat]
   [follower ,desugared-raft-message-address-type])
  (DeclineCandidate
   [term Nat]
   [follower ,desugared-raft-message-address-type])
  (AppendEntries
   [term Nat]
   [prev-log-term Nat]
   [prev-log-index Nat]
   [entries (List Entry)]
   [leader-commit-id Nat]
   [leader ,desugared-raft-message-address-type]
   [leader-client (Addr ClientMessage)])
  ;; A note on last-index: In the paper, this is the optimization at the bottom of p. 7 that allows
  ;; for quicker recovery of a node that has fallen behind in its log. In RaftScope, they call this
  ;; "matchIndex", which indicates the lat index in the log (or 0 for AppendRejected). In akka-raft,
  ;; this is always the last index of the log (for both success and failure)
  (AppendRejected
   [term Nat]
   [last-index Nat]
   [member ,desugared-raft-message-address-type])
  (AppendSuccessful
   [term Nat]
   [last-index Nat]
   [member ,desugared-raft-message-address-type]))

(define-record ClusterConfiguration
  [members (List ,desugared-raft-message-address-type)]
  ;; ignoring other config fields for now, since I'm not implementing configuration changes
  )

;; including this only to define some of the other variants of RaftActorMessage
(define-variant RaftActorMessageOtherBranches
  (Config [config ClusterConfiguration])
  ;; ClientMessage has already been defined as a variant above
  (SendHeartbeatTimeouts [id Nat]))

(define-type RaftActorMessage
  (Union
   (Config ClusterConfiguration)
   (ClientMessage (Addr ClientResponse) String)
   (RequestVote
    Nat
    ,desugared-raft-message-address-type
    Nat
    Nat)
   (VoteCandidate
    Nat
    ,desugared-raft-message-address-type)
   (DeclineCandidate
    Nat
    ,desugared-raft-message-address-type)
   (AppendEntries
    Nat
    Nat
    Nat
    (List ,desugared-entry-type)
    Nat
    ,desugared-raft-message-address-type
    (Addr (Union (ClientMessage (Addr ,desugared-client-response-type) String))))
   (AppendRejected
    Nat
    Nat
    ,desugared-raft-message-address-type)
   (AppendSuccessful
    Nat
    Nat
    ,desugared-raft-message-address-type)
   (SendHeartbeatTimeouts Nat)))

(define-variant MaybePeer
  (NoPeer)
  (JustPeer [peer ,desugared-raft-message-address-type]))

(define-record StateMetadata
  [current-term Nat]
  [votes (Hash Nat ,desugared-raft-message-address-type)]
  [last-used-timeout-id Nat])

(define-record ElectionMeta
  [current-term Nat]
  [votes-received (Hash ,desugared-raft-message-address-type Boolean)]
  [votes (Hash Nat ,desugared-raft-message-address-type)]
  [last-used-timeout-id Nat])

(define-record LeaderMeta
  [current-term Nat]
  [last-used-timeout-id Nat])

(define-variant TimerMessage
  (SetTimer [timer-name String]
            [target (Addr (Union (Timeout Nat)))]
            [id Nat]
            [duration Duration]
            [repeat? Boolean])
  (CancelTimer [timer-name String]))

(define-record ReplicatedLog
  [entries (List Entry)]
  [committed-index Int])

(define-record AppendResult
  [message RaftMessage]
  [log ReplicatedLog])

;; ---------------------------------------------------------------------------------------------------
;; List helpers

;; Works like Scala's list slice (i.e. returns empty list instead of returning errors)
;;
;; from-index is inclusive, to-index is exclusive
(define-function (list-slice [v (List Entry)] [from-index Int] [to-index Int])
  (list-copy v
             (min from-index (length v))
             (min to-index   (length v))))

    ;;;; Program-level Functions

;; ---------------------------------------------------------------------------------------------------
;; Replicated log

(define-function (replicated-log-empty)
  (ReplicatedLog (list) 0))

;; Takes the first *take* entries from the log and appends *entries* onto it, returning the new log
(define-function (replicated-log-append [log ReplicatedLog]
                                        [entries-to-append (List Entry)]
                                        [to-take Nat])
  (ReplicatedLog
   (append (take (: log entries) to-take) entries-to-append)
   (: log committed-index)))

(define-function (replicated-log+ [replicated-log ReplicatedLog] [entry Entry])
  (replicated-log-append replicated-log (list entry) (length (: replicated-log entries))))

(define-function (replicated-log-commit [replicated-log ReplicatedLog] [n Int])
  (ReplicatedLog (: replicated-log entries) n))

;; Returns the log entries from from-index (exclusive) to to-index (inclusive) (these are *semantic*
;; indices)
(define-function (replicated-log-between [replicated-log ReplicatedLog]
                                         [from-index Int]
                                         [to-index Int])
  ;; NOTE: this naive conversion from semantic to implementation indices won't work under log
  ;; compaction
  ;;
  ;; NOTE: have to be careful here because CSA cannot represent negative numbers; subtraction instead
  ;; goes down to 0
  (let ([inclusive-impl-from-index from-index]
        [exclusive-impl-to-index   to-index])
      (list-slice (: replicated-log entries) inclusive-impl-from-index exclusive-impl-to-index)))

(define-function (replicated-log-last-index [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (length entries)) 0]
      [else (: (list-ref entries (- (length entries) 1)) index)])))

(define-function (replicated-log-last-term [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (length entries)) 0]
      [else (: (list-ref entries (- (length entries) 1)) term)])))

;; ;; NOTE: this differs from the akka-raft version, which is broken
(define-function (replicated-log-next-index [replicated-log ReplicatedLog])
  (let ([entries (: replicated-log entries)])
    (cond
      [(= 0 (length entries)) 1]
      [else (+ (: (list-ref entries (- (length entries) 1)) index) 1)])))

(define-variant FindTermResult (NoTerm) (FoundTerm [term Nat]))
(define-function (replicated-log-term-at [replicated-log ReplicatedLog] [index Nat])
  (cond
    [(<= index 0) 0]
    [else
     ;; Note: this code is uglier than it would be if we used more general list-traversal functions
     (let ([fold-result
            (for/fold ([result (NoTerm)])
                      ([entry (: replicated-log entries)])
              (case result
                [(NoTerm)
                 (cond
                   [(= (: entry index) index) (FoundTerm (: entry term))]
                   [else (NoTerm)])]
                [(FoundTerm t) result]))])
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

;; Returns a list of entries from the log, starting at the from-including index and including either
;; all entries with the same term or a total of 5 entries, whichever is less. We assume from-including
;; is no less than 1 and no more than 1 + the last index in the log.
(define-function (replicated-log-entries-batch-from [replicated-log ReplicatedLog]
                                                    [from-including Nat])
  (let* ([how-many 5] ; this is the default parameter in akka-raft
         [first-impl-index 0]
         [first-semantic-index
          (if (= (length (: replicated-log entries)) 0)
              1
              (: (list-ref (: replicated-log entries) 0) index))]
         ;; CSA can't represent negative numbers, so we have to reverse the direction of the offset
         [impl->semantic-offset (- first-semantic-index first-impl-index)]
         [from-including-impl (- from-including impl->semantic-offset)]
         [to-send (list-slice (: replicated-log entries)
                                from-including-impl
                                (+ from-including-impl how-many))])
    (cond
      [(> (length to-send) 0)
       (let* ([head (list-ref to-send 0)]
              [batch-term (: head term)])
         ;; this for/fold implements the takeWhile
         (for/fold ([result (list)])
                   ([entry to-send])
           (cond
             [(= (: entry term) batch-term) (append result (list entry))]
             [else result])))]
      [else (list)])))

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
                              [candidate ,desugared-raft-message-address-type]
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
                               [candidate ,desugared-raft-message-address-type]
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
                            [candidate ,desugared-raft-message-address-type]
                            [last-log-term Nat]
                            [last-log-index Nat])
  (and (>= term (: metadata current-term))
       (candidate-at-least-as-up-to-date? log last-log-term last-log-index)))

(define-function (with-vote [metadata StateMetadata] [term Nat] [candidate ,desugared-raft-message-address-type])
  (StateMetadata
   (: metadata current-term)
   (hash-set (: metadata votes) term candidate)
   (: metadata last-used-timeout-id)))

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
    (StateMetadata (: m current-term) (: m votes) next-id)))

(define-function (reset-election-deadline/candidate [timer (Addr TimerMessage)]
                                           [target (Addr Nat)]
                                           [m ElectionMeta])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline false))
    (ElectionMeta (: m current-term) (: m votes-received) (: m votes) next-id)))

(define-function (reset-election-deadline/leader [timer (Addr TimerMessage)]
                                        [target (Addr Nat)]
                                        [m LeaderMeta])
  (let ([deadline (+ election-timeout-min (random (- election-timeout-max election-timeout-min)))]
        [next-id (+ 1 (: m last-used-timeout-id))])
    (send timer (SetTimer election-timer-name target next-id deadline false))
    (LeaderMeta (: m current-term) next-id)))

(define-function (cancel-election-deadline [timer (Addr TimerMessage)])
  (send timer (CancelTimer election-timer-name)))

;; ;; Because this language does not have traits, I separate forNewElection into two functions
(define-function (for-new-election/follower [m StateMetadata])
  (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

(define-function (for-new-election/candidate [m StateMetadata])
  (ElectionMeta (next (: m current-term)) (hash) (: m votes) (: m last-used-timeout-id)))

;; ;; this effectively duplicates the logic of withVote, but it follows the akka-raft code
(define-function (with-vote-for [m ElectionMeta] [term Nat] [candidate ,desugared-raft-message-address-type])
  (ElectionMeta (: m current-term)
                (: m votes-received)
                (hash-set (: m votes) term candidate)
                (: m last-used-timeout-id)))

;; ---------------------------------------------------------------------------------------------------
;; Config helpers

(define-function (members-except-self [config ClusterConfiguration] [self ,desugared-raft-message-address-type])
  (for/fold ([result (list)])
            ([member (: config members)])
    (if (not (= member self)) (cons member result) result)))

(define-function (inc-vote [m ElectionMeta] [follower ,desugared-raft-message-address-type])
  (ElectionMeta (: m current-term)
                (hash-set (: m votes-received) follower true)
                (: m votes)
                (: m last-used-timeout-id)))

(define-function (has-majority [m ElectionMeta] [config ClusterConfiguration])
  (let ([total-votes-received
         (for/fold ([total 0])
                   ([member (: config members)])
           (+ total (if (hash-has-key? (: m votes-received) member) 1 0)))])
    (> total-votes-received (/ (length (: config members)) 2))))

;; ---------------------------------------------------------------------------------------------------
;; LogIndexMap

(define-function (log-index-map-initialize [members (List ,desugared-raft-message-address-type)]
                                           [initialize-with Nat])
  (for/fold ([map (hash)])
            ([member members])
    (hash-set map member initialize-with)))

(define-function (log-index-map-value-for [map (Hash ,desugared-raft-message-address-type Nat)]
                                 [member ,desugared-raft-message-address-type])
  (case (hash-ref map member)
    [(Nothing)
      ;; akka-raft would update the map here, but we should never have to because we don't change the
      ;; config
      0]
    [(Just value) value]))

(define-function (log-index-map-put-if-greater [map (Hash ,desugared-raft-message-address-type Nat)]
                                               [member ,desugared-raft-message-address-type]
                                               [value Nat])
  (let ([old-value (log-index-map-value-for map member)])
    (cond
      [(< old-value value) (hash-set map member value)]
      [else map])))

(define-function (log-index-map-put-if-smaller [map (Hash ,desugared-raft-message-address-type Nat)]
                                      [member ,desugared-raft-message-address-type]
                                      [value Nat])
  (let ([old-value (log-index-map-value-for map member)])
    (cond
      [(> old-value value) (hash-set map member value)]
      [else map])))

;; Helper for sort-numbers-descending
(define-function (insert-sorted-descending [sorted-nums (List Nat)] [num Nat])
  (let ([others-inserted-result
         (for/fold ([result (record [inserted? false] [accumulated (list)])])
                   ([sorted-num sorted-nums])
           (if (and (> num sorted-num) (not (: result inserted?)))
               (record [inserted? true]
                       [accumulated (append (: result accumulated) (list num sorted-num))])
               (record [inserted? (: result inserted?)]
                       [accumulated (append (: result accumulated) (list sorted-num))])))])
    (if (: others-inserted-result inserted?)
        (: others-inserted-result accumulated)
        (append (: others-inserted-result accumulated) (list num)))))

;; Simple insertion sort
(define-function (sort-numbers-descending [nums (List Nat)])
  (for/fold ([sorted-so-far (list)])
            ([num nums])
    (insert-sorted-descending sorted-so-far num)))

;; ;; NOTE: because the akka-raft version of this is completely wrong, I'm writing my own
;; ;; Returns the greatest index that a majority of entries in the map agree on
(define-function (log-index-map-consensus-for-index [map (Hash ,desugared-raft-message-address-type Nat)]
                                                    [config ClusterConfiguration])
  (let ([all-indices
         (for/fold ([indices-so-far (list)])
                   ([member (: config members)])
           (case (hash-ref map member)
             [(Nothing) indices-so-far] ; NOTE: this should never happen
             [(Just index) (cons index indices-so-far)]))])
    (list-ref (sort-numbers-descending all-indices)
              (/ (length (: config members)) 2))))

;; ---------------------------------------------------------------------------------------------------
;; Misc.

(define-function (leader-is-lagging [append-entries-term Nat] [m StateMetadata])
  (< append-entries-term (: m current-term)))

(define-function (is-heartbeat [append-entries-entries (List Entry)])
  (= 0 (length append-entries-entries)))

(define-function (AppendEntries-apply [term Nat]
                             [replicated-log ReplicatedLog]
                             [from-index Nat]
                             [leader-commit-id Nat]
                             [leader ,desugared-raft-message-address-type]
                             [leader-client (Addr (Union (ClientMessage ClientMessage)))])
  (let ([entries (replicated-log-entries-batch-from replicated-log from-index)])
    (cond
      [(> (length entries) 0)
       (let ([head (list-ref entries 0)])
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

;;---------------------------------------------------------------------------------------------------
;; The main actor

(define-actor RaftActorMessage (RaftActor [timer-manager (Addr TimerMessage)]
                                          [application (Addr String)])

 ;; the functions go here
 (
  ;; Replaces the handling of the BeginElection self-send message in akka-raft
  (define-function (begin-election [m StateMetadata]
                                   [replicated-log ReplicatedLog]
                                   [config ClusterConfiguration])
    ;; unlike akka-raft, we assume the config is full, because we don't deal with dynamic
    ;; configuration changes
    (let ([request (RequestVote (: m current-term)
                                (fold ,desugared-raft-message-address-type self)
                                (replicated-log-last-term replicated-log)
                                (replicated-log-last-index replicated-log))])
      (for ([member (members-except-self config (fold ,desugared-raft-message-address-type self))])
        (send (unfold ,desugared-raft-message-address-type member) request))
      (let* ([m (reset-election-deadline/candidate timer-manager self m)]
             [including-this-vote (inc-vote m (fold ,desugared-raft-message-address-type self))]) ; this is the self vote
        (goto Candidate
              (with-vote-for including-this-vote (: m current-term) (fold ,desugared-raft-message-address-type self))
              replicated-log
              config))))

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
                           [entries (List Entry)]
                           [m StateMetadata])
    (cond
      [(is-heartbeat entries)
       (AppendResult (AppendSuccessful (: m current-term)
                                       (replicated-log-last-index replicated-log)
                                       (fold ,desugared-raft-message-address-type self))
                     replicated-log)]
      [else
       ;; NOTE: this num-entries-to-keep calculation is too naive if we do log compaction
       (let ([num-entries-to-keep prev-log-index])
         (let ([replicated-log (replicated-log-append replicated-log
                                                      entries
                                                      num-entries-to-keep)])
           (AppendResult (AppendSuccessful (replicated-log-last-term replicated-log)
                                           (replicated-log-last-index replicated-log)
                                           (fold ,desugared-raft-message-address-type self))
                         replicated-log)))]))

  (define-function (commit-until-index [replicated-log ReplicatedLog]
                                       [last-index-to-commit Nat]
                                       [notify-client? Boolean])
    (let ([entries (replicated-log-between replicated-log
                                           (: replicated-log committed-index)
                                           last-index-to-commit)])
      (for/fold ([rep-log replicated-log])
                ([entry entries])
        (send application (: entry command))
        (cond
          [notify-client?
           (send (: entry client) (CommitSuccess (: entry command)))]
          [else 0])
        (replicated-log-commit rep-log (: entry index)))))

  ;; TODO: consider making AppendEntries into a record to remove these long param lists and better
  ;; match akka-raft
  (define-function (append-entries [term Nat]
                                   [prev-log-term Nat]
                                   [prev-log-index Nat]
                                   [entries (List Entry)]
                                   [leader-commit-id Nat]
                                   [leader ,desugared-raft-message-address-type]
                                   [m StateMetadata]
                                   [replicated-log ReplicatedLog]
                                   [config ClusterConfiguration]
                                   [recently-contacted-by-leader MaybeLeader])
    (cond
      [(leader-is-lagging term m)
       ;; MY FIX:
       (send (unfold ,desugared-raft-message-address-type leader)
             (AppendRejected (: m current-term)
                             (replicated-log-last-index replicated-log)
                             (fold ,desugared-raft-message-address-type self)))
       ;; APS PROTOCOL BUG: akka-raft does not respond to heartbeats in this case, but I think it
       ;; should. To replicate, comment out the above send and uncomment the following cond expression
       ;; (cond
       ;;   [(not (is-heartbeat entries))
       ;;    (send (unfold ,desugared-raft-message-address-type leader)
       ;;          (AppendRejected (: m current-term)
       ;;                          (replicated-log-last-index replicated-log)
       ;;                          (fold ,desugared-raft-message-address-type self)))]
       ;;   [else 0])
       (goto Follower recently-contacted-by-leader m replicated-log config)]
      [(not (replicated-log-consistent-update replicated-log prev-log-term prev-log-index))
       (let ([meta-with-updated-term (StateMetadata term (: m votes) (: m last-used-timeout-id))])
         (send (unfold ,desugared-raft-message-address-type leader)
               (AppendRejected (: meta-with-updated-term current-term)
                               (replicated-log-last-index replicated-log)
                               (fold ,desugared-raft-message-address-type self)))
         (accept-heartbeat meta-with-updated-term
                           replicated-log
                           config
                           recently-contacted-by-leader))]
      ;; APS PROTOCOL BUG: akka-raft does not do the append/commit logic for heartbeats, even though
      ;; it should. To replicate, uncomment this cond clause
      ;; [(is-heartbeat entries)
      ;;  (accept-heartbeat m replicated-log config recently-contacted-by-leader)]
      [else
       (let* ([meta-with-updated-term (StateMetadata term (: m votes) (: m last-used-timeout-id))]
              [append-result (append replicated-log prev-log-index entries meta-with-updated-term)])
         (send (unfold ,desugared-raft-message-address-type leader) (: append-result message))
         (let  ([replicated-log (commit-until-index (: append-result log) leader-commit-id false)])
           (accept-heartbeat meta-with-updated-term
                             replicated-log
                             config
                             recently-contacted-by-leader)))]))

  (define-function (replicate-log [m LeaderMeta]
                                  [next-index (Hash ,desugared-raft-message-address-type Nat)]
                                  [replicated-log ReplicatedLog]
                                  [config ClusterConfiguration])
    (for ([member (members-except-self config (fold ,desugared-raft-message-address-type self))])
      (send (unfold ,desugared-raft-message-address-type member)
            (AppendEntries-apply (: m current-term)
                                 replicated-log
                                 (log-index-map-value-for next-index member)
                                 (: replicated-log committed-index)
                                 (fold ,desugared-raft-message-address-type self)
                                 self))))

  (define-function (send-heartbeat [m LeaderMeta]
                                   [next-index (Hash ,desugared-raft-message-address-type Nat)]
                                   [replicated-log ReplicatedLog]
                                   [config ClusterConfiguration])
    (replicate-log m next-index replicated-log config))

  (define-constant heartbeat-timer-name "HeartbeatTimer")
  (define-constant heartbeat-interval 50)
  (define-function (start-heartbeat [m LeaderMeta] [next-index (Hash ,desugared-raft-message-address-type Nat)]
                                    [replicated-log ReplicatedLog]
                                    [config ClusterConfiguration])
    (send-heartbeat m next-index replicated-log config)
    (send timer-manager
          (SetTimer heartbeat-timer-name self 1 heartbeat-interval true)))

  (define-function (stop-heartbeat)
    (send timer-manager (CancelTimer heartbeat-timer-name)))

  (define-function (send-entries [follower ,desugared-raft-message-address-type]
                                 [m LeaderMeta]
                                 [replicated-log ReplicatedLog]
                                 [next-index Nat]
                                 [leader-commit-id Nat]
                                 [leader ,desugared-raft-message-address-type]
                                 [leader-client (Addr ClientMessage)])
    (send (unfold ,desugared-raft-message-address-type follower)
          (AppendEntries-apply (: m current-term)
                               replicated-log
                               (log-index-map-value-for next-index follower)
                               (: replicated-log committed-index)
                               (fold ,desugared-raft-message-address-type self)
                               self)))

  (define-function (maybe-commit-entry [match-index (Hash ,desugared-raft-message-address-type Nat)]
                                       [replicated-log ReplicatedLog]
                                       [config ClusterConfiguration])
    (let ([index-on-majority (log-index-map-consensus-for-index match-index config)])
      (let ([will-commit (> index-on-majority (: replicated-log committed-index))])
        (cond
          [will-commit (commit-until-index replicated-log index-on-majority true)]
          [else replicated-log]))))

  (define-function (register-append-successful [follower-term Nat]
                                               [follower-index Nat]
                                               [member ,desugared-raft-message-address-type]
                                               [m LeaderMeta]
                                               [next-index (Hash ,desugared-raft-message-address-type Nat)]
                                               [match-index (Hash ,desugared-raft-message-address-type Nat)]
                                               [replicated-log ReplicatedLog]
                                               [config ClusterConfiguration])
    ;; NOTE: (maybe akka-raft bug): why don't both indices use put-if-greater?
    (let* ([next-index (hash-set next-index member follower-index)]
           [match-index (log-index-map-put-if-greater match-index
                                                      member
                                                      (log-index-map-value-for next-index member))]
           [replicated-log (maybe-commit-entry match-index replicated-log config)])
      (goto Leader m next-index match-index replicated-log config)))

  (define-function (register-append-rejected [follower-term Nat]
                                             [follower-index Nat]
                                             [member ,desugared-raft-message-address-type]
                                             [m LeaderMeta]
                                             [next-index (Hash ,desugared-raft-message-address-type Nat)]
                                             [match-index (Hash ,desugared-raft-message-address-type Nat)]
                                             [replicated-log ReplicatedLog]
                                             [config ClusterConfiguration])
    (let ([next-index (log-index-map-put-if-smaller next-index member (+ 1 follower-index))])
      (send-entries member
                    m
                    replicated-log
                    next-index
                    (: replicated-log committed-index)
                    (fold ,desugared-raft-message-address-type self)
                    self)
      (goto Leader m next-index match-index replicated-log config)))

  (define-function (step-down [m LeaderMeta]
                              [replicated-log ReplicatedLog]
                              [config ClusterConfiguration])
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
      (let ([metadata (reset-election-deadline/follower timer-manager self (initial-metadata))])
        (goto Follower
              (NoLeader)
              metadata
              (replicated-log-empty)
              config))]
     [(ClientMessage client cmd) (goto Init)]
     [(RequestVote t c lt li) (goto Init)]
     [(VoteCandidate t f) (goto Init)]
     [(DeclineCandidate t f) (goto Init)]
     [(AppendEntries t pt prev-index entries lci l lc) (goto Init)]
     [(AppendRejected t l m) (goto Init)]
     [(AppendSuccessful t l m) (goto Init)]
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
     [(RequestVote term candidate last-term last-index)
      (cond
        [(grant-vote?/follower metadata replicated-log term candidate last-term last-index)
         (send (unfold ,desugared-raft-message-address-type candidate)
               (VoteCandidate term (fold ,desugared-raft-message-address-type self)))
         ;; NOTE: akka-raft did not update the term here, which I think is a bug
         (let ([metadata (reset-election-deadline/follower timer-manager self metadata)])
           (goto Follower recently-contacted-by-leader
                 (let ([meta-with-vote (with-vote metadata term candidate)])
                   (StateMetadata term
                                  (: meta-with-vote votes)
                                  (: meta-with-vote last-used-timeout-id)))
                 replicated-log
                 config))]
        [else
         (let ([metadata (StateMetadata (max term (: metadata current-term))
                                        (: metadata votes)
                                        (: metadata last-used-timeout-id))])
           (send (unfold ,desugared-raft-message-address-type candidate)
                 (DeclineCandidate (: metadata current-term) (fold ,desugared-raft-message-address-type self)))
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
      (goto Follower recently-contacted-by-leader metadata replicated-log config)]
     [(Config c) (goto Follower recently-contacted-by-leader metadata replicated-log config)]
     [(Timeout id)
      (cond
        [(= id (: metadata last-used-timeout-id))
         ;; This code replaces the beginElection function from akka-raft
         ;; NOTE: we assume the config is non-empty
         (begin-election (for-new-election/follower metadata) replicated-log config)]
        [else (goto Follower recently-contacted-by-leader metadata replicated-log config)])]
     [(SendHeartbeatTimeouts id)
      (goto Follower recently-contacted-by-leader metadata replicated-log config)]))

 (define-state (Candidate [m ElectionMeta]
                          [replicated-log ReplicatedLog]
                          [config ClusterConfiguration]) (message)
   (case message
     [(ClientMessage client command)
      (send client (LeaderIs (NoLeader)))
      (goto Candidate m replicated-log config)]
     [(RequestVote term candidate last-log-term last-log-index)
      (cond
        [(grant-vote?/candidate m replicated-log term candidate last-log-term last-log-index)
         (send (unfold ,desugared-raft-message-address-type candidate)
               (VoteCandidate term (fold ,desugared-raft-message-address-type self)))
         ;; TODO: (maybe akka-raft bug): this seems wrong that we stay in candidate instead of
         ;; going to Follower. Some test should probably break this
         (goto Candidate (with-vote-for m term candidate) replicated-log config)]
        [else
         (let ([m (ElectionMeta (max term (: m current-term))
                                (: m votes-received)
                                (: m votes)
                                (: m last-used-timeout-id))])
           (send (unfold ,desugared-raft-message-address-type candidate)
                 (DeclineCandidate (: m current-term) (fold ,desugared-raft-message-address-type self)))
           (goto Candidate m replicated-log config))])]
     [(VoteCandidate term follower)
      (cond
        [(= term (: m current-term))
         (let ([including-this-vote (inc-vote m follower)])
           (cond
             [(has-majority including-this-vote config)
              ;; NOTE: instead of doing the below self-send and going to Leader, I instead inline
              ;; the ElectedAsLeader handling here
              ;;
              ;; (send self (ElectedAsLeader))
              ;; (cancel-election-deadline timer-manager)
              ;; (next-state (Leader (for-leader m) (hash) (hash) replicated-log config))
              (cancel-election-deadline timer-manager)
              ;; NOTE: because we don't have mutation, I'm just inlining the code for
              ;; initializeLeaderState here
              (let ([members (: config members)])
                (let ([next-index
                       ;; TODO: is the +1 here a correction for an akka-raft bug? (and same for the
                       ;; lack of a -1 for match-index below)
                       (log-index-map-initialize members
                                                 (+ (replicated-log-last-index replicated-log) 1))]
                      [match-index (log-index-map-initialize (: config members) 0)])
                  (start-heartbeat m next-index replicated-log config)
                  (goto Leader (LeaderMeta (: m current-term) (: m last-used-timeout-id))
                        next-index
                        match-index
                        replicated-log
                        config)))]
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
                             recently-contacted-by-leader))]
          [else
           ;; APS PROTOCOL BUG: original code left out this response. To replicate, uncomment this
           ;; send
           (send (unfold ,desugared-raft-message-address-type leader)
                 (AppendRejected (: m current-term)
                                 (replicated-log-last-index replicated-log)
                                 (fold ,desugared-raft-message-address-type self)))
           (goto Candidate m replicated-log config)]))]
     [(AppendSuccessful t i member) (goto Candidate m replicated-log config)]
     [(AppendRejected t i member) (goto Candidate m replicated-log config)]
     [(Config c) (goto Candidate m replicated-log config)]
     [(Timeout id)
      (cond
        [(= id (: m last-used-timeout-id))
         ;; NOTE: starting an election here directly instead of doing a self-send as akka-raft does
         ;; Old code:
         ;; (send self (BeginElectionAlerts))
         ;; (goto Candidate (for-new-election/candidate m) replicated-log config)
         (let ([m (for-new-election/candidate m)])
           (begin-election m replicated-log config))]
        [else (goto Candidate m replicated-log config)])]
     [(SendHeartbeatTimeouts id) (goto Candidate m replicated-log config)]))

 (define-state (Leader [m LeaderMeta]
                       [next-index (Hash ,desugared-raft-message-address-type Nat)]
                       [match-index (Hash ,desugared-raft-message-address-type Nat)]
                       [replicated-log ReplicatedLog]
                       [config ClusterConfiguration]) (message)
   (case message
     [(ClientMessage client command)
      (let* ([entry (Entry command
                           (: m current-term) (replicated-log-next-index replicated-log)
                           client)]
             [replicated-log (replicated-log+ replicated-log entry)]
             [match-index (hash-set match-index (fold ,desugared-raft-message-address-type self) (: entry index))])
        (replicate-log m next-index replicated-log config)
        (goto Leader m next-index match-index replicated-log config))]
     [(RequestVote term candidate last-log-term last-log-index)
      (cond
        [(grant-vote?/leader m replicated-log term candidate last-log-term last-log-index)
         (send (unfold ,desugared-raft-message-address-type candidate)
               (VoteCandidate term (fold ,desugared-raft-message-address-type self)))
         (stop-heartbeat)
         (step-down m replicated-log config)]
        [(> term (: m current-term))
         (let ([m (LeaderMeta term (: m last-used-timeout-id))])
           (send (unfold ,desugared-raft-message-address-type candidate)
                 (DeclineCandidate term (fold ,desugared-raft-message-address-type self)))
           (step-down m replicated-log config))]
        [else
         (send (unfold ,desugared-raft-message-address-type candidate)
               (DeclineCandidate (: m current-term) (fold ,desugared-raft-message-address-type self)))
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
         ;; MY FIX:
         (send (unfold ,desugared-raft-message-address-type leader)
               (AppendRejected (: m current-term)
                               (replicated-log-last-index replicated-log)
                               (fold ,desugared-raft-message-address-type self)))
         ;; APS PROTOCOL BUG: this is where akka-raft sends entries back instead of the rejection
         ;; response. To replicate, comment out the above send and uncomment the below send-entries
         ;;
         ;; (send-entries leader
         ;;               m
         ;;               replicated-log
         ;;               next-index
         ;;               (: replicated-log committed-index)
         ;;               (fold ,desugared-raft-message-address-type self)
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
                                  config)]
     [(Config c) (goto Leader m next-index match-index replicated-log config)]
     [(Timeout id) (goto Leader m next-index match-index replicated-log config)]
     [(SendHeartbeatTimeouts id)
      (send-heartbeat m next-index replicated-log config)
      (goto Leader m next-index match-index replicated-log config)])))

;; ---------------------------------------------------------------------------------------------------
;; The main program expression

(let-actors ([raft-server (spawn 1 RaftActor timer-manager application)])
            raft-server raft-server)))))

;; ---------------------------------------------------------------------------------------------------
;; Conformance check

(module+ test
  (require
   rackunit
   "../csa.rkt" ; for csa-valid-type?
   "../main.rkt")

  (test-true "Client response type" (csa-valid-type? desugared-client-response-type))
  (test-true "Raft message type" (csa-valid-type? desugared-raft-message-type))
  (test-true "Full Raft actor type" (csa-valid-type? full-raft-actor-type))

  (test-true "Raft verification"
    (check-conformance raft-actor-prog raft-spec)))
