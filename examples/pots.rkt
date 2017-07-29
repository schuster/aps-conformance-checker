#lang racket

;; An implementation of the POTS system often used as an Erlang tutorial, found here:
;; https://github.com/uwiger/pots

;; Difference's from Ulf's version:
;; * all messages other than number analysis are send-and-forget
;; * any response to a request is assumed to be for the most recent request (i.e. no "Ref"s)

;; Notes on the protocol:
;; * regardless of who started the call, the side that hangs up first sends Disconnect to the LIM
;; * "A" side is the calling side, "B" side is the called side
;; * we use an extra identifier for connecting through the lim, rather than the actor address, so that
;;   we can exactly specify our use of the address

(provide
 pots-program
 pots-spec)

;; ---------------------------------------------------------------------------------------------------

(require
 "../desugar.rkt")

(define desugared-seizer-peer-address
  `(Addr
    (Union
     [Seized]
     [Rejected]
     [Answered]
     [Cleared])))

(define desugared-seizable-peer-message
  `(Union
    [Seize (Record [id Nat] [address ,desugared-seizer-peer-address])]
    [Answered]
    [Cleared]))

(define desugared-seizable-peer-address
  `(Addr ,desugared-seizable-peer-message))

(define desugared-lim-message-type
  `(Union
    [StartTone (Union [Dial] [Fault] [Ring] [Busy])]
    [StopTone]
    [StartRing]
    [StopRing]))

(define desugared-analyzer-message-type
  `(Union
    [AnalysisRequest
     (List Nat)
     (Addr (Union
            [Invalid]
            [Valid (Record [id Nat]
                           [address ,desugared-seizable-peer-address])]
            [GetMoreDigits]))]))

(define desugared-controller-message-type
  `(Union
    ;; hardware messages
    [OnHook]
    [OffHook]
    [Digit Nat]
    ;; analyzer messages
    [Invalid]
    [Valid (Record [id Nat] [address ,desugared-seizable-peer-address])]
    [GetMoreDigits]
    [Seize (Record [id Nat] [address ,desugared-seizer-peer-address])]
    [Seized]
    [Rejected]
    [Answered]
    [Cleared]))

(define pots-program (desugar
`(program
 (receptionists [controller ControllerMessage])
 (externals [lim LimMessage] [analyzer AnalyzerMessage])

(define-record SeizablePeer
  [id Nat]
  [address ,desugared-seizable-peer-address])

(define-record SeizerPeer
  [id Nat]
  [address ,desugared-seizer-peer-address])

(define-record Peer
  [id Nat]
  [address (Addr (Union [Answered] [Cleared]))])

(define-variant ControllerMessage
  ;; hardware messages
  [OnHook]
  [OffHook]
  [Digit [digit Nat]]
  ;; analyzer messages
  [Invalid]
  [Valid [peer SeizablePeer]]
  [GetMoreDigits]
  [Seize [peer SeizerPeer]]
  [Seized]
  [Rejected]
  [Answered]
  [Cleared])

(define-variant Tone
  (Dial)
  (Fault)
  (Ring)
  (Busy))

(define-variant LimMessage
  (Connect [peer-id Nat])
  (Disconnect [peer-id Nat])
  (StartTone [tone Tone])
  (StopTone)
  (StartRing)
  (StopRing))

(define-function (Seize [peer SeizerPeer]) (variant Seize peer))
(define-function (Seized) (variant Seized))
(define-function (Rejected) (variant Rejected))
(define-function (Answered) (variant Answered))
(define-function (Cleared) (variant Cleared))

(define-type AnalyzerResult
  (Union
   (Invalid)
   (Valid SeizablePeer)
   (GetMoreDigits)))

(define-variant AnalyzerMessage
  (AnalysisRequest [digits (List Nat)] [response-dest (Addr AnalyzerResult)]))

(define-variant HaveTone?
  (HaveTone)
  (NoTone))

(define-actor ControllerMessage (PotsController [my-id Nat]
                                                [lim (Addr LimMessage)]
                                                [analyzer (Addr AnalyzerMessage)])
  () ; no actor-specific functions

  (goto Idle)

  (define-state (Idle) (m)
    (case m
      [(OffHook)
       (send lim (StartTone (Dial)))
       (goto GettingFirstDigit)]
      [(Seize peer)
       ;; TODO: need an unfold here
       (send (: peer address) (Seized))
       (send lim (StartRing))
       (goto RingingBSide peer)]
      ;; ignore other peer messages
      [(Seized) (goto Idle)]
      [(Rejected) (goto Idle)]
      [(Answered) (goto Idle)]
      [(Cleared) (goto Idle)]
      ;; Ignore other messages
      [(OnHook) (goto Idle)]
      [(Digit n) (goto Idle)]
      [(Invalid) (goto Idle)]
      [(Valid a) (goto Idle)]
      [(GetMoreDigits) (goto Idle)]))

  (define-state (GettingFirstDigit) (m)
    (case m
      [(OnHook)
       (send lim (StopTone))
       (goto Idle)]
      [(Digit n)
       (let ([digits (list n)])
         (send lim (StopTone))
         (send analyzer (AnalysisRequest digits self))
         (goto WaitOnAnalysis digits))]
      [(Seize peer)
       (send (: peer address) (Rejected))
       (goto GettingFirstDigit)]
      ;; ignore other peer messages
      [(Seized) (goto GettingFirstDigit)]
      [(Rejected) (goto GettingFirstDigit)]
      [(Answered) (goto GettingFirstDigit)]
      [(Cleared) (goto GettingFirstDigit)]
      ;; ignore other messages
      [(OffHook) (goto GettingFirstDigit)]
      [(Invalid) (goto GettingFirstDigit)]
      [(Valid a) (goto GettingFirstDigit)]
      [(GetMoreDigits) (goto GettingFirstDigit)]))

  (define-state (GettingNumber [number (List Nat)]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(Digit n)
       (let ([digits (cons n number)])
         (send analyzer (AnalysisRequest digits self))
         (goto WaitOnAnalysis digits))]
      [(Seize peer)
       (send (: peer address) (Rejected))
       (goto GettingNumber number)]
      ;; ignore other peer messages
      [(Seized) (goto GettingNumber number)]
      [(Rejected) (goto GettingNumber number)]
      [(Answered) (goto GettingNumber number)]
      [(Cleared) (goto GettingNumber number)]
      ;; ignore other messages
      [(OffHook) (goto GettingNumber number)]
      [(Invalid) (goto GettingNumber number)]
      [(Valid a) (goto GettingNumber number)]
      [(GetMoreDigits) (goto GettingNumber number)]))

  (define-state (WaitOnAnalysis [number (List Nat)]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(Seize peer)
       (send (: peer address) (Rejected))
       (goto WaitOnAnalysis number)]
      ;; ignore other peer messages
      [(Seized) (goto WaitOnAnalysis number)]
      [(Rejected) (goto WaitOnAnalysis number)]
      [(Answered) (goto WaitOnAnalysis number)]
      [(Cleared) (goto WaitOnAnalysis number)]
      [(Invalid)
       (send lim (StartTone (Fault)))
       (goto WaitOnHook (HaveTone))]
      [(Valid peer)
       (send (: peer address) (Seize (Peer my-id self)))
       (goto MakeCallToB peer)]
      [(GetMoreDigits) (goto GettingNumber number)]
      ;; ignore other messages
      ;;
      ;; Note: because we don't have selective receive, we throw away any numbers dialed while
      ;; waiting on the analysis. Ideally we would save them in some sort of stack instead
      [(OffHook) (goto WaitOnAnalysis number)]
      [(Digit n) (goto WaitOnAnalysis number)]))

  ;; Called "calling_B" in Ulf's version
  (define-state (MakeCallToB [peer Peer]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(Seize new-peer)
       (send (: new-peer address) (Rejected))
       (goto MakeCallToB peer)]
      [(Seized)
       (send lim (StartTone (Ring)))
       (goto RingingASide peer)]
      [(Rejected)
       (send lim (StartTone (Busy)))
       (goto WaitOnHook (HaveTone))]
      ;; ignore the Cleared message; shouldn't happen here
      [(Cleared)
       (goto MakeCallToB peer)]
      [(Answered)
       (goto MakeCallToB peer)]
      ;; ignore other messages
      [(OffHook) (goto MakeCallToB peer)]
      [(Digit n) (goto MakeCallToB peer)]
      [(Invalid) (goto MakeCallToB peer)]
      [(Valid a) (goto MakeCallToB peer)]
      [(GetMoreDigits) (goto MakeCallToB peer)]))

  ;; the other phone is ringing
  (define-state (RingingASide [peer Peer]) (m)
    (case m
      [(Seize new-peer)
       (send (: new-peer address) (Rejected))
       (goto RingingASide peer)]
      [(Answered)
       (send lim (StopTone))
       (send lim (Connect (: peer id)))
       (goto Speech peer)]
      ;; ignore other peer messages
      [(Seized) (goto RingingASide peer)]
      [(Rejected) (goto RingingASide peer)]
      [(Cleared) (goto RingingASide peer)]
      [(OnHook)
       (send (: peer address) (Cleared))
       (send lim (StopTone))
       (goto Idle)]
      ;; ignore other messages
      [(OffHook) (goto RingingASide peer)]
      [(Digit n) (goto RingingASide peer)]
      [(Invalid) (goto RingingASide peer)]
      [(Valid a) (goto RingingASide peer)]
      [(GetMoreDigits) (goto RingingASide peer)]))

  ;; this phone is ringing
  (define-state (RingingBSide [peer Peer]) (m)
    (case m
      [(Seize new-peer)
       (send (: new-peer address) (Rejected))
       (goto RingingBSide peer)]
      [(Cleared)
       (send lim (StopRing))
       (goto Idle)]
      ;; ignore other peer messages
      [(Seized) (goto RingingBSide peer)]
      [(Rejected) (goto RingingBSide peer)]
      [(Answered) (goto RingingBSide peer)]
      [(OffHook)
       (send lim (StopRing))
       (send (: peer address) (Answered))
       (goto Speech peer)]
      ;; ignore other messages
      [(OnHook) (goto RingingBSide peer)]
      [(Digit n) (goto RingingBSide peer)]
      [(Invalid) (goto RingingBSide peer)]
      [(Valid a) (goto RingingBSide peer)]
      [(GetMoreDigits) (goto RingingBSide peer)]))

  (define-state (Speech [peer Peer]) (m)
    (case m
      [(Seize new-peer)
       (send (: new-peer address) (Rejected))
       (goto Speech peer)]
      [(Cleared) (goto WaitOnHook (NoTone))]
      ;; ignore other peer messages
      [(Seized) (goto Speech peer)]
      [(Rejected) (goto Speech peer)]
      [(Answered) (goto Speech peer)]
      [(OnHook)
       (send lim (Disconnect (: peer id)))
       (send (: peer address) (Cleared))
       (goto Idle)]
      ;; ignore other messages
      [(OffHook) (goto Speech peer)]
      [(Digit n) (goto Speech peer)]
      [(Invalid) (goto Speech peer)]
      [(Valid a) (goto Speech peer)]
      [(GetMoreDigits) (goto Speech peer)]))

  (define-state (WaitOnHook [have-tone? HaveTone?]) (m)
    (case m
      [(Seize new-peer)
       (send (: new-peer address) (Rejected))
       (goto WaitOnHook have-tone?)]
      ;; ignore other peer messages
      [(Seized) (goto WaitOnHook have-tone?)]
      [(Rejected) (goto WaitOnHook have-tone?)]
      [(Answered) (goto WaitOnHook have-tone?)]
      [(Cleared) (goto WaitOnHook have-tone?)]
      [(OnHook)
       (case have-tone?
         [(HaveTone)
          (send lim (StopTone))
          (goto Idle)]
         [(NoTone) (goto Idle)])]
      ;; ignore other messages
      [(OffHook) (goto WaitOnHook have-tone?)]
      [(Digit n) (goto WaitOnHook have-tone?)]
      [(Invalid) (goto WaitOnHook have-tone?)]
      [(Valid a) (goto WaitOnHook have-tone?)]
      [(GetMoreDigits) (goto WaitOnHook have-tone?)])))

(actors [controller (spawn 1 PotsController 1 lim analyzer)]))))

;; ---------------------------------------------------------------------------------------------------
;; Specifications

;; Specification from POV of another phone
(define pots-spec
  `(specification (receptionists [controller ,desugared-controller-message-type])
                  (externals [lim ,desugared-lim-message-type]
                             [analyzer ,desugared-analyzer-message-type])
     (obs-rec controller ,desugared-seizable-peer-message ,desugared-controller-message-type)
     (goto Idle)

     (define-state (Idle)
       [(variant Seize (record [id *] [address peer])) ->
        ([obligation peer (variant Seized)])
        (goto Ringing peer)]
       [(variant Seize (record [id *] [address peer])) ->
        ([obligation peer (variant Rejected)])
        (goto Idle)]
       [(variant Seized) -> () (goto Idle)]
       [(variant Rejected) -> () (goto Idle)]
       [(variant Answered) -> () (goto Idle)]
       [(variant Cleared) -> () (goto Idle)])

     (define-state (Ringing peer)
       ; can answer, can react to a Cleared, can respond to Seized
       [free ->
        ([obligation peer (variant Answered)])
        (goto InCall peer)]
       [(variant Seize (record [id *] [address other-peer])) ->
        ([obligation other-peer (variant Rejected)])
        (goto Ringing peer)]
       [(variant Cleared) -> () (goto Idle)]
       ;; An unobserved actor could *also* send us Cleared, which still causes us to go to Idle
       [free -> () (goto Idle)]
       [(variant Seized) -> () (goto Ringing peer)]
       [(variant Rejected) -> () (goto Ringing peer)]
       [(variant Answered) -> () (goto Ringing peer)])

     (define-state (InCall peer)
       [free -> ([obligation peer (variant Cleared)]) (goto Idle)]
       [(variant Seize (record [id *] [address other-peer])) ->
        ([obligation other-peer (variant Rejected)])
        (goto InCall peer)]
       [(variant Cleared) -> () (goto Idle)]
       ;; An unobserved actor could *also* send us Cleared, which still causes us to go to Idle,
       ;; without us sending a Cleared message back
       [free -> () (goto Idle)]
       ;; ignore all others
       [(variant Seized) -> () (goto InCall peer)]
       [(variant Rejected) -> () (goto InCall peer)]
       [(variant Answered) -> () (goto InCall peer)])))

(module+ test
  (require
   rackunit
   "../csa.rkt" ; for csa-valid-type?
   "../desugar.rkt"
   "../main.rkt")

  (test-true "Controller message type" (csa-valid-type? desugared-controller-message-type))

  (test-true "POTS controller conforms to controller-POV spec"
    (check-conformance pots-program pots-spec)))

(module+ test
  ;; Dynamic tests
  (require
   racket/async-channel
   asyncunit
   (only-in csa record variant :)
   csa/eval
   csa/testing)

  (test-case "Basic call test"
    (define lim (make-async-channel))
    (define analyzer (make-async-channel))
    (define controller (csa-run pots-program lim analyzer))
    ;; pick up the phone
    (async-channel-put controller (variant OffHook))
    ;; wait for dial tone
    (check-unicast lim (variant StartTone (variant Dial)))
    ;; dial a 1
    (async-channel-put controller (variant Digit 1))
    ;; dial tone should stop
    (check-unicast lim (variant StopTone))
    ;; wait for analyzer request
    (check-unicast-match analyzer (csa-variant AnalysisRequest (list 1) _))
    ;; analyzer requires more digits
    (async-channel-put controller (variant GetMoreDigits))
    ;; dial a 2
    (async-channel-put controller (variant Digit 2))
    ;; wait for analyzer request
    (check-unicast-match analyzer (csa-variant AnalysisRequest (list 2 1) _))
    ;; analyzer accepts the number
    (define peer (make-async-channel))
    (async-channel-put controller (variant Valid (record [id 500] [address peer])))
    ;; wait for seize to peer
    (check-unicast-match
     peer
     (csa-variant Seize _))
    ;; peer is seized, starts ringing
    (async-channel-put controller (variant Seized))
    (check-unicast lim (variant StartTone (variant Ring)))
    ;; peer answers, controller should connect
    (async-channel-put controller (variant Answered))
    (check-unicast lim (variant StopTone))
    (check-unicast lim (variant Connect 500))
    ;; we hang up, wait for Disconnect/Cleared
    (async-channel-put controller (variant OnHook))
    (check-unicast lim (variant Disconnect 500))
    (check-unicast peer (variant Cleared))))
