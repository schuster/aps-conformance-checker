#lang racket

;; An implementation of the POTS system often used as an Erlang tutorial, found here:
;; https://github.com/uwiger/pots

;; Difference's from Ulf's version:
;; * all messages other than number analysis are send-and-forget
;; * any response to a request is assumed to be for the most recent request (i.e. no "Ref"s)

;; Notes on the protocol:
;; * regardless of who started the call, the side that hangs up first sends Disconnect to the LIM
;; * "A" side is the calling side, "B" side is the called side

;; ---------------------------------------------------------------------------------------------------

(define desugared-peer-message-type
  `(minfixpt PeerMessageType
             (Union
              [Seize (Addr (Union [PeerMessage PeerMessageType]))]
              [Seized]
              [Rejected]
              [Answered]
              [Cleared])))

(define desugared-lim-message-type
  `(Union
    [StartTone (Union [Dial] [Fault] [Ring] [Busy])]
    [StopTone]
    [StartRing]
    [StopRing]))

(define desugared-list-of-digits-type
  `(minfixpt TheList
             (Union (NoDigits)
                    (Cons Nat TheList))))

(define desugared-analyzer-result-type
  `(Union [Invalid]
          [Valid (Addr (Union [PeerMessage ,desugared-peer-message-type]))]
          [GetMoreDigits]))

(define desugared-analyzer-message-type
  `(Union
    [AnalysisRequest ,desugared-list-of-digits-type
                     (Addr ,desugared-analyzer-result-type)]))

(define desugared-controller-message-type
  `(Union
    ;; hardware messages
    [OnHook]
    [OffHook]
    [Digit Nat]
    ;; analyzer messages
    [Invalid]
    [Valid (Addr (Union [PeerMessage ,desugared-peer-message-type]))]
    [GetMoreDigits]
    ;; peer messages (have to add a tag around these because of the recursive type
    [PeerMessage ,desugared-peer-message-type]))

(define pots-program
`(program
 (receptionists [controller ControllerMessage])
 (externals [lim LimMessage] [analyzer AnalyzerMessage])

(define-variant Tone
  (Dial)
  (Fault)
  (Ring)
  (Busy))

(define-variant LimMessage
  ; the Connect/Disconnect messages' usage of the peer address is not specified in any source I've
  ; found, so we leave it as an empty union address here
  (Connect [peer (Addr (Union))])
  (Disconnect [peer (Addr (Union))])
  (StartTone [tone Tone])
  (StopTone)
  (StartRing)
  (StopRing))

;; recursive variants aren't supported in the sugared language right now
(define-type PeerMessage ,desugared-peer-message-type)
(define-type PeerMessageAddress (Addr (Union [PeerMessage PeerMessage])))
(define-function (Seize [peer PeerMessageAddress]) (variant Seize peer))
(define-function (Seized) (variant Seized))
(define-function (Rejected) (variant Rejected))
(define-function (Answered) (variant Answered))
(define-function (Cleared) (variant Cleared))

;; Recursive types require a lot of extra annotations/folding, so we abstract that into one function
;; here
(define-function (send-peer [peer PeerMessageAddress] [message PeerMessage])
  (send peer (variant PeerMessage (fold PeerMessage message))))

(define-type ListOfDigits
  (minfixpt TheList
            (Union (NoDigits)
                   (Cons Nat TheList))))
(define-function (NoDigits)
  (variant NoDigits))

(define-function (Cons [n Nat] [l ListOfDigits])
  (variant Cons l))

(define-variant AnalyzerResult
  (Invalid)
  (Valid [peer PeerMessageAddress])
  (GetMoreDigits))

(define-variant AnalyzerMessage
  (AnalysisRequest [digits ListOfDigits] [response-dest (Addr AnalyzerResult)]))

(define-type ControllerMessage
  (Union
   ;; hardware messages
   [OnHook]
   [OffHook]
   [Digit Nat]
   ;; analyzer messages
   [Invalid]
   [Valid PeerMessageAddress]
   [GetMoreDigits]
   ;; peer messages (have to add a tag around these because of the recursive type
   [PeerMessage PeerMessage]))

(define-variant HaveTone?
  (HaveTone)
  (NoTone))

(define-actor ControllerMessage (PotsController [lim (Addr LimMessage)] [analyzer (Addr AnalyzerMessage)])
  () ; no actor-specific functions

  (goto Idle)

  (define-state (Idle) (m)
    (case m
      [(OffHook)
       (send lim (StartTone (Dial)))
       (goto GettingFirstDigit)]
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize peer)
          (send-peer peer (Seized))
          (send lim (StartRing))
          (goto RingingBSide peer)]
         ;; ignore other peer messages
         [(Seized) (goto Idle)]
         [(Rejected) (goto Idle)]
         [(Answered) (goto Idle)]
         [(Cleared) (goto Idle)])]
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
       (let ([digits (fold ListOfDigits (Cons n (fold ListOfDigits (NoDigits))))])
         (send lim (StopTone))
         (send analyzer (AnalysisRequest digits self))
         (goto WaitOnAnalysis digits))]
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize peer)
          (send-peer peer (Rejected))
          (goto GettingFirstDigit)]
         ;; ignore other peer messages
         [(Seized) (goto GettingFirstDigit)]
         [(Rejected) (goto GettingFirstDigit)]
         [(Answered) (goto GettingFirstDigit)]
         [(Cleared) (goto GettingFirstDigit)])]
      ;; ignore other messages
      [(OffHook) (goto GettingFirstDigit)]
      [(Invalid) (goto GettingFirstDigit)]
      [(Valid a) (goto GettingFirstDigit)]
      [(GetMoreDigits) (goto GettingFirstDigit)]))

  (define-state (GettingNumber [number ListOfDigits]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(Digit n)
       (let ([digits (fold ListOfDigits (Cons n number))])
         (send analyzer (AnalysisRequest digits self))
         (goto WaitOnAnalysis digits))]
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize peer)
          (send-peer peer (Rejected))
          (goto GettingNumber number)]
         ;; ignore other peer messages
         [(Seized) (goto GettingNumber number)]
         [(Rejected) (goto GettingNumber number)]
         [(Answered) (goto GettingNumber number)]
         [(Cleared) (goto GettingNumber number)])]
      ;; ignore other messages
      [(OffHook) (goto GettingNumber number)]
      [(Invalid) (goto GettingNumber number)]
      [(Valid a) (goto GettingNumber number)]
      [(GetMoreDigits) (goto GettingNumber number)]))

  (define-state (WaitOnAnalysis [number ListOfDigits]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize peer)
          (send-peer peer (Rejected))
          (goto WaitOnAnalysis lim analyzer number)]
         ;; ignore other peer messages
         [(Seized) (goto WaitOnAnalysis number)]
         [(Rejected) (goto WaitOnAnalysis number)]
         [(Answered) (goto WaitOnAnalysis number)]
         [(Cleared) (goto WaitOnAnalysis number)])]
      [(Invalid)
       (send lim (StartTone (Fault)))
       (goto WaitOnHook (HaveTone))]
      [(Valid peer)
       (send-peer peer (Seize self))
       (goto MakeCallToB peer)]
      [(GetMoreDigits) (goto GettingNumber number)]
      ;; ignore other messages
      ;;
      ;; Note: because we don't have selective receive, we throw away any numbers dialed while
      ;; waiting on the analysis. Ideally we would save them in some sort of stack instead
      [(OffHook) (goto WaitOnAnalysis number)]
      [(Digit n) (goto WaitOnAnalysis number)]))

  ;; Called "calling_B" in Ulf's version
  (define-state (MakeCallToB [peer PeerMessageAddress]) (m)
    (case m
      [(OnHook) (goto Idle)]
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize new-peer)
          (send-peer new-peer (Rejected))
          (goto MakeCallToB peer)]
         [(Seized)
          (send lim (StartTone (Ring)))
          (goto RingingASide peer)]
         [(Rejected)
          (send lim (StartTone (Busy)))
          (goto WaitOnHook (HaveTone))]
         ;; ignore the Cleared message; shouldn't happen here
         [(Cleared)
          (goto MakeCallToB peer)])]
      ;; ignore other messages
      [(OffHook) (goto MakeCallToB peer)]
      [(Digit n) (goto MakeCallToB peer)]
      [(Invalid) (goto MakeCallToB peer)]
      [(Valid a) (goto MakeCallToB peer)]
      [(GetMoreDigits) (goto MakeCallToB peer)]))

  ;; the other phone is ringing
  (define-state (RingingASide [peer PeerMessageAddress]) (m)
    (case m
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize new-peer)
          (send-peer new-peer Rejected)
          (goto RingingASide peer)]
         [(Answered)
          (send lim (StopTone))
          (send lim (Connect peer))
          (goto Speech peer)]
         ;; ignore other peer messages
         [(Seized) (goto RingingASide peer)]
         [(Rejected) (goto RingingASide peer)]
         [(Cleared) (goto RingingASide peer)])]
      [(OnHook)
       (send-peer peer (Cleared))
       (send lim (StopTone))
       (goto Idle)]
      ;; ignore other messages
      [(OffHook) (goto RingingASide peer)]
      [(Digit n) (goto RingingASide peer)]
      [(Invalid) (goto RingingASide peer)]
      [(Valid a) (goto RingingASide peer)]
      [(GetMoreDigits) (goto RingingASide peer)]))

  ;; this phone is ringing
  (define-state (RingingBSide [peer PeerMessageAddress]) (m)
    (case m
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize new-peer)
          (send-peer new-peer (Rejected))
          (goto RingingBSide peer)]
         [(Cleared)
          (send lim (StopRing))
          (goto Idle)]
         ;; ignore other peer messages
         [(Seized) (goto RingingBSide peer)]
         [(Rejected) (goto RingingBSide peer)]
         [(Answered) (goto RingingBSide peer)])]
      [(OffHook)
       (send lim (StopRing))
       (send-peer peer (Answered))
       (goto Speech peer)]
      ;; ignore other messages
      [(OnHook) (goto RingingBSide peer)]
      [(Digit n) (goto RingingBSide peer)]
      [(Invalid) (goto RingingBSide peer)]
      [(Valid a) (goto RingingBSide peer)]
      [(GetMoreDigits) (goto RingingBSide peer)]))

  (define-state (Speech [peer PeerMessageAddress]) (m)
    (case m
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize new-peer)
          (send-peer new-peer (Rejected))
          (goto Speech peer)]
         [(Cleared) (goto WaitOnHook (NoTone))]
         ;; ignore other peer messages
         [(Seized) (goto Speech peer)]
         [(Rejected) (goto Speech peer)]
         [(Answered) (goto Speech peer)])]
      [(OnHook)
       (send lim (Disconnect peer))
       (send-peer peer (Cleared))
       (goto Idle)]
      ;; ignore other messages
      [(OffHook) (goto Speech peer)]
      [(Digit n) (goto Speech peer)]
      [(Invalid) (goto Speech peer)]
      [(Valid a) (goto Speech peer)]
      [(GetMoreDigits) (goto Speech peer)]))

  (define-state (WaitOnHook [have-tone? HaveTone?]) (m)
    (case m
      [(PeerMessage p)
       (case (unfold PeerMessage p)
         [(Seize new-peer)
          (send-peer new-peer (Rejected))
          (goto WaitOnHook have-tone?)]
         ;; ignore other peer messages
         [(Seized) (goto WaitOnHook have-tone?)]
         [(Rejected) (goto WaitOnHook have-tone?)]
         [(Answered) (goto WaitOnHook have-tone?)]
         [(Cleared) (goto WaitOnHook have-tone?)])]
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

(actors [controller (spawn 1 PotsController lim analyzer)])))

;; ---------------------------------------------------------------------------------------------------
;; Specifications

;; Specification from POV of another phone
(define pots-spec
  ;; TODO: list all peer messages here
  `(specification (receptionists [controller ,desugared-controller-message-type])
                  (externals [lim ,desugared-lim-message-type]
                             [analyzer ,desugared-analyzer-message-type])
     [controller (Union [PeerMessage ,desugared-peer-message-type])]
     ([controller ,desugared-controller-message-type])
     (goto Idle)

     (define-state (Idle)
       [(variant Seize peer) ->
        ([obligation peer (variant Seized)])
        (goto Ringing peer)]
       [(variant Seize peer) ->
        ([obligation peer (variant Rejected)])
        (goto Idle)]
       [(variant Cleared) -> () (goto Idle)])

     (define-state (Ringing peer)
       ; can answer, can respond to a Cleared, can respond to Seized
       [unobs ->
        ([obligation peer (variant Answered)])
        (goto InCall peer)]
       [(variant Seize other-peer) ->
        ([obligation other-peer (variant Rejected)])
        (goto Ringing peer)]
       [(variant Cleared) -> () (goto Idle)])

     (define-state (InCall peer)
       [unobs -> ([obligation peer (variant Cleared)]) (goto Idle)]
       [(variant Seize other-peer) ->
        ([obligation other-peer (variant Rejected)])
        (goto InCall peer)]
       [(variant Cleared) -> () (goto Idle)])
     ))

(module+ test
  (require
   rackunit
   "../csa.rkt" ; for csa-valid-type?
   "../desugar.rkt"
   "../main.rkt")

  (test-true "Peer message type" (csa-valid-type? desugared-peer-message-type))
  (test-true "Controller message type" (csa-valid-type? desugared-controller-message-type))

  (test-true "POTS controller conforms to controller-POV spec"
    (check-conformance (desugar pots-program) pots-spec)))
