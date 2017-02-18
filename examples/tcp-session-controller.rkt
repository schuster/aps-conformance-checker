#lang racket

;; An alternative implementation of a TCP session, using variants for packet flags rather than natural
;; numbers, allowing for conformance checking of actually interesting specs on the network side.
;;
;; This actor presumes a different design for the TCP session, where a session is split into three
;; actors:
;;
;; * a session controller that manages the state of the session
;;
;; * a receive buffer that does an initial filtering on received packets and only sends to the
;; controller the next packet in the sequence, along with all packets before our SEQ has been ACKed
;; (so that we know when to consider the connection established). This buffer is also responsible for
;; sending all ACKs and informing the send buffer what has been ACKed so far. The buffer tailors
;; segments so that only unseen segment text is sent to the session controller (as described at the
;; top of p. 70 in RFC 793).
;;
;; * a send buffer that handles sending packets across the network, retransmissions, flow control, and
;; congestion control.
;;
;; Separating the send and receive buffers into separate actors makes it feasible to check the session
;; controller for conformance to the classical FSM specification for TCP, because we don't have to
;; reason about how the buffers ensure that messages are processed in order by sequence number.
;;
;; The assumed protocol for the receive buffer is that it first sends all acceptable packets to the
;; controller, because it doesn't yet know what the valid order for packets is. Once the receive
;; buffer receives a packet with an ACK for our SYN, it holds off on forwarding more packets until the
;; session controller tells it to resume, allowing the controller to await registration from the
;; application layer without having to enqueue more received packets internally. This requires a
;; slight breach of separation of concerns, in that the receive buffer requires some knowledge of the
;; conditions that trigger the AwaitingUserRegistration state, but this seems to be inevitable if we
;; want to avoid any internal queueing or duplication of the receive buffer's ordering logic in the
;; session controller.

(define DEFAULT-WINDOW-SIZE 29200)
(define MAXIMUM-SEGMENT-SIZE-IN-BYTES 536)
(define wait-time-in-milliseconds 2000)
(define max-retries 3)
;; NOTE: real MSL value is 2 minutes
(define max-segment-lifetime (* 1000 2)) ; defined in milliseconds
(define user-response-wait-time 3000)
(define register-timeout 5000) ; in milliseconds (5 seconds is the Akka default)
(define timeout-fudge-factor 500) ; in milliseconds

(define remote-ip 500) ; we're faking IPs with natural numbers, so the actual number doesn't matter
(define remote-port 80)
(define local-port 55555)
(define local-iss 100)
(define remote-iss 1024)
(define fin-seq 200)

(define tcp-definitions
  (quasiquote
(

;;---------------------------------------------------------------------------------------------------
;; Math

  (define-function (max [a Nat] [b Nat])
    (if (> a b) a b))

  (define-function (min [a Nat] [b Nat])
    (if (< a b) a b))

;;---------------------------------------------------------------------------------------------------
;; TCP Packets

  (define-type Byte Nat) ; fake bytes with natural numbers

  (define-type IpAddress Nat) ; fake IP addresses with Nats
  (define-record InetSocketAddress [ip IpAddress] [port Nat])
  (define-record SessionId
    [remote-address InetSocketAddress]
    [local-port Nat])

  (define-variant Ack? [Ack] [NoAck])
  (define-variant Rst? [Rst] [NoRst])
  (define-variant Syn? [Syn] [NoSyn])
  (define-variant Fin? [Fin] [NoFin])

  (define-record TcpPacket
    [source-port Nat]
    [destination-port Nat]
    [seq Nat]
    [ack Nat]
    [ack-flag Ack?]
    [rst Rst?]
    [syn Syn?]
    [fin Fin?]
    [window Nat]
    [payload (Vectorof Byte)])

  (define-function (packet-ack? [packet TcpPacket])
    (case (: packet ack-flag)
      [(Ack) (variant True)]
      [(NoAck) (variant False)]))

  (define-function (packet-rst? [packet TcpPacket])
    (case (: packet rst)
      [(Rst) (variant True)]
      [(NoRst) (variant False)]))

  (define-function (packet-syn? [packet TcpPacket])
    (case (: packet syn)
      [(Syn) (variant True)]
      [(NoSyn) (variant False)]))

  (define-function (packet-fin? [packet TcpPacket])
    (case (: packet fin)
      [(Fin) (variant True)]
      [(NoFin) (variant False)]))

  (define-variant MaybeFinSeq
    [NoFinSeq]
    [FinSeq [num Nat]])

;; ---------------------------------------------------------------------------------------------------
;; Timer

  (define-variant TimerCommand
    (Stop)
    (Start [timeout-in-milliseconds Nat]))

  (define-type ExpirationMessage
    (Union
     [RegisterTimeout]
     [TimeWaitTimeout]))

  (define-actor TimerCommand
    (Timer [expiration-message ExpirationMessage]
           [expiration-target (Addr ExpirationMessage)])
    ()
    (goto Stopped)
    (define-state (Stopped) (m)
      (case m
        [(Stop) (goto Stopped)]
        [(Start timeout-in-milliseconds)
         (goto Running timeout-in-milliseconds)]))
    (define-state/timeout (Running [timeout-in-milliseconds Nat]) (m)
      (case m
        [(Stop) (goto Stopped)]
        [(Start new-timeout-in-milliseconds)
         (goto Running new-timeout-in-milliseconds)])
      (timeout timeout-in-milliseconds
        (send expiration-target expiration-message)
        (goto Stopped))))

;; ---------------------------------------------------------------------------------------------------
;; Some types for TCP

  (define-variant TcpSessionEvent
    [ReceivedData [bytes (Vectorof Byte)]]
    [Closed]
    [ConfirmedClosed]
    [Aborted]
    [PeerClosed]
    [ErrorClosed])

;; ---------------------------------------------------------------------------------------------------
;; Sink

  ;; just a simple actor to swallow messages to the user when we're closing before the user registered
  ;; a handler
  (define-actor TcpSessionEvent
    (Sink)
    ()
    (goto Sink)
    (define-state (Sink) (m) (goto Sink)))

;; ---------------------------------------------------------------------------------------------------
;; TCP

  (define-function (SessionCloseNotification [id SessionId])
    (variant SessionCloseNotification id))

  (define-type WriteResponse
    (Union (CommandFailed) ; CommandFailed defined below
           (WriteAck)))
  (define-function (WriteAck) (variant WriteAck))

  (define-type TcpSessionCommand
    (Union
     (Register (Addr TcpSessionEvent))
     (Write (Vectorof Byte) (Addr WriteResponse))
     (Close (Addr (Union [CommandFailed] [Closed])))
     (ConfirmedClose (Addr (Union [CommandFailed] [ConfirmedClosed])))
     (Abort (Addr (Union [CommandFailed] [Aborted])))))

  (define-variant ConnectionStatus
    (CommandFailed)
    (Connected [session-id SessionId] [session (Addr TcpSessionCommand)]))

  (define-variant Open
    (ActiveOpen)
    (PassiveOpen [remote-seq Nat]))

  (define-type CloseType
    (Union
     [PeerClose]
     [Close (Addr TcpSessionEvent)]
     [ConfirmedClose (Addr TcpSessionEvent)]))
  (define-function (PeerClose) (variant PeerClose))

  (define-variant ClosingState
    (SentFin) ; FIN-WAIT-1
    (WaitingOnPeerFin) ; FIN-WAIT-2
    (SentThenReceivedFin) ; CLOSING
    (WaitingOnPeerAck) ; LAST-ACK
    )

  (define-variant ReceiveBufferCommand
    (Resume))

  (define-variant SendBufferCommand
    (SendSyn)
    (SendRst)
    (SendText [data (Vectorof Byte)])
    (SendFin))

  (define-variant TcpSessionInput
    (OrderedTcpPacket [packet TcpPacket])
    (Register [handler (Addr TcpSessionEvent)])
    (Write [data (Vectorof Byte)] [handler (Addr WriteResponse)])
    (Close [close-handler (Addr (Union [CommandFailed] [Closed]))])
    (ConfirmedClose [close-handler (Addr (Union [CommandFailed] [ConfirmedClosed]))])
    (Abort [close-handler (Addr (Union [CommandFailed] [Aborted]))])
    (InternalAbort) ; e.g. if the Send Buffer retransmit timeout happens too many times
    (TheFinSeq [seq Nat])
    ;; timeouts
    (RegisterTimeout)
    (TimeWaitTimeout))

  ;;; The TCP session actor

  (define-actor TcpSessionInput
    (TcpSession [id SessionId]
                [iss Nat]
                [open Open]
                [receive-buffer (Addr ReceiveBufferCommand)]
                [send-buffer (Addr SendBufferCommand)]
                [status-updates (Addr ConnectionStatus)]
                [close-notifications (Addr (Union [SessionCloseNotification SessionId]))]
                ;; REFACTOR: make these things constants instead
                [wait-time-in-milliseconds Nat]
                [max-retries Nat]
                [max-segment-lifetime-in-ms Nat]
                [user-response-wait-time Nat])
    ((define-function (halt-with-notification)
       (send close-notifications (SessionCloseNotification id))
       (goto Closed))

     (define-function (finish-connecting)
       (send status-updates (Connected id self))
       (let ([reg-timer (spawn reg-timer-EVICT Timer (RegisterTimeout) self)])
         (send reg-timer (Start ,register-timeout))
         (goto AwaitingRegistration reg-timer)))

     ;; Transitions to time-wait, starting a timer on the way in
     (define-function (goto-TimeWait [octet-stream (Addr TcpSessionEvent)])
       (let ([timer (spawn time-wait-timer-EVICT Timer (TimeWaitTimeout) self)])
         (send timer (Start (mult 2 max-segment-lifetime-in-ms)))
         (goto TimeWait octet-stream timer)))

     ;; Does the necessary handling for segment text on the next in-order packet
     (define-function (process-segment-text [segment TcpPacket]
                                            [receive-data? (Union (True) (False))]
                                            [octet-stream (Addr TcpSessionEvent)])
       (let ([unseen-payload (: segment payload)])
         (cond
           [(and (> (vector-length unseen-payload) 0) receive-data?)
            (send octet-stream (ReceivedData unseen-payload))
            0]
           [else 0])))

     (define-function (abort-connection)
       (send send-buffer (SendRst)))

     (define-function (start-close [close-type CloseType]
                                   [closing-state ClosingState]
                                   [octet-stream (Addr TcpSessionEvent)])
       (send send-buffer (SendFin))
       (goto Closing close-type closing-state (NoFinSeq) octet-stream)))

    ;; initialization
    (goto SynSent)

    (define-state (SynSent) (m)
      (case m
        [(OrderedTcpPacket packet)
         ;; Have to handle all messages at this point, because the receive buffer doesn't know what
         ;; the ISS for the other side is
         (cond
           [(packet-ack? packet)
            (cond
              [(= (: packet ack) (+ iss 1)) ; this is the only acceptable ACK
               (cond
                 [(packet-rst? packet)
                  (send status-updates (CommandFailed))
                  (halt-with-notification)]
                 [(packet-syn? packet)
                  ;; This is the typical SYN/ACK case (step 2 of the 3-way handshake). ReceiveBuffer
                  ;; will have calculated the rcv-nxt and sent the ACK, so we just need to do the
                  ;; transition
                  (finish-connecting)]
                 [else
                  ;; ACK acceptable but no other interesting fields set. Probably won't happen in
                  ;; reality.
                  (goto SynSent)])]
              [else ;; ACK present but not acceptable
               (abort-connection)
               (send status-updates (CommandFailed))
               (halt-with-notification)])]
           [else ;; no ACK present
            (cond
              [(packet-rst? packet)
               ;; drop the packet, because the RST probably comes from a previous instance of the
               ;; session
               (goto SynSent)]
              [(packet-syn? packet)
               ;; we got a SYN but no ACK: this is the simultaneous open case
               (send send-buffer (SendSyn))
               (goto SynReceived)]
              [else
               ;; not an important segment, so just drop it. Probably won't happen in reality
               (goto SynSent)])])]
        [(InternalAbort)
         (abort-connection)
         (send status-updates (CommandFailed))
         (halt-with-notification)]
        ;; None of these should happen at this point; ignore them
        [(Register h) (goto SynSent)]
        [(Write d h) (goto SynSent)]
        [(Close h) (goto SynSent)]
        [(ConfirmedClose h) (goto SynSent)]
        [(Abort h) (goto SynSent)]
        [(TheFinSeq seq) (goto SynSent)]
        [(RegisterTimeout) (goto SynSent)]
        [(TimeWaitTimeout) (goto SynSent)]))

    (define-state (SynReceived) (m)
      (case m
        [(OrderedTcpPacket packet)
         (cond
           [(packet-rst? packet)
            (case open
              [(ActiveOpen)
               ;; Can get here with a simultaneous open
               (send status-updates (CommandFailed))
               0]
              [(PassiveOpen r) 0])
            (halt-with-notification)]
           ;; We differ here slightly from the RFC, b/c the RFC doesn't make sense. To allow
           ;; simultaneous open, we should send a RST for SYN, but not SYN/ACK
           [(and (packet-syn? packet) (not (packet-ack? packet)))
            (abort-connection)
            (case open
              [(ActiveOpen) (send status-updates (CommandFailed)) 0]
              [(PassiveOpen r) 0])
            (halt-with-notification)]
           [(packet-ack? packet)
            ;; NOTE: I assume here that this packet does not have a payload (perhaps not always the
            ;; case, but good enough for this small sample program)
            (cond
              [(= (: packet ack) (+ iss 1))
               (finish-connecting)]
              [else
               (abort-connection)
               (goto SynReceived)])]
           [else (goto SynReceived)])]
        [(InternalAbort)
         (abort-connection)
         (send status-updates (CommandFailed))
         (halt-with-notification)]
        ;; None of these should happen at this point; ignore them
        [(Register h) (goto SynReceived)]
        [(Write d h) (goto SynReceived)]
        [(Close h) (goto SynReceived)]
        [(ConfirmedClose h) (goto SynReceived)]
        [(Abort h) (goto SynReceived)]
        [(TheFinSeq seq) (goto SynReceived)]
        [(RegisterTimeout) (goto SynReceived)]
        [(TimeWaitTimeout) (goto SynReceived)]))

    ;; We're waiting for the user to register an actor to send received octets to
    (define-state (AwaitingRegistration [registration-timer (Addr TimerCommand)]) (m)
      (case m
        [(OrderedTcpPacket packet)
         ;; shouldn't happen here: receive buffer is holding packets until we tell it to resume. We
         ;; add a little logic here just to make the conformance check happy, though
         (cond
           [(packet-rst? packet)
            (halt-with-notification)]
           [(packet-syn? packet)
            (abort-connection)
            (halt-with-notification)]
           [else
            ;; ignore other packets
            (goto AwaitingRegistration registration-timer)])]
        [(Register octet-handler)
         (send registration-timer (Stop))
         (send receive-buffer (Resume))
         (goto Established octet-handler)]
        [(Write data handler)
         ;; can't yet write
         (send handler (CommandFailed))
         (goto AwaitingRegistration registration-timer)]
        [(Close close-handler)
         (send close-handler (Closed))
         (start-close (Close close-handler)
                      (SentFin)
                      (spawn close-await-sink-EVICT Sink))]
        [(ConfirmedClose close-handler)
         (start-close (ConfirmedClose close-handler)
                      (SentFin)
                      (spawn confirmed-close-await-sink-EVICT Sink))]
        [(Abort close-handler)
         (abort-connection)
         (send close-handler (Aborted))
         (halt-with-notification)]
        [(InternalAbort)
         (abort-connection)
         (halt-with-notification)]
        [(RegisterTimeout)
         (abort-connection)
         (halt-with-notification)]
        ;; these shouldn't happen here
        [(TheFinSeq seq) (goto AwaitingRegistration registration-timer)]
        [(TimeWaitTimeout) (goto AwaitingRegistration registration-timer)]))

    (define-state (Established [octet-stream (Addr TcpSessionEvent)]) (m)
      (case m
        [(OrderedTcpPacket packet)
         (cond
           [(packet-rst? packet)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [(packet-syn? packet)
            (abort-connection)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [else
            (process-segment-text packet (variant True) octet-stream)
            ;; Finally, check for the FIN bit
            (cond
              [(packet-fin? packet)
               (send octet-stream (PeerClosed))
               (start-close (PeerClose) (WaitingOnPeerAck) octet-stream)]
              [else (goto Established octet-stream)])])]
        [(Register h)
         (goto Established octet-stream)]
        [(Write data handler)
         (send handler (WriteAck))
         (send send-buffer (SendText data))
         (goto Established octet-stream)]
        [(Close close-handler)
         (send close-handler (Closed))
         (send octet-stream (Closed))
         (start-close (Close close-handler) (SentFin) octet-stream)]
        [(ConfirmedClose close-handler)
         (start-close (ConfirmedClose close-handler) (SentFin) octet-stream)]
        [(Abort close-handler)
         (abort-connection)
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(InternalAbort)
         (abort-connection)
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(TheFinSeq seq) (goto Established octet-stream)]
        [(RegisterTimeout)
         (goto Established octet-stream)]
        [(TimeWaitTimeout)
         (goto Established octet-stream)]))

    ;; In the process of closing down; groups together FIN-WAIT-1, FIN-WAIT-2, CLOSING, and LAST-ACK
    ;; in the typical TCP state diagram
    (define-state (Closing [close-type CloseType]
                           [closing-state ClosingState]
                           [maybe-fin MaybeFinSeq]
                           [octet-stream (Addr TcpSessionEvent)]) (m)
      (case m
        [(OrderedTcpPacket packet)
         (cond
           [(packet-rst? packet)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [(packet-syn? packet)
            (send octet-stream (ErrorClosed))
            (abort-connection)
            (halt-with-notification)]
           [else
            (process-segment-text packet
                                  (case close-type
                                    [(ConfirmedClose h) (variant True)]
                                    [(Close h) (variant False)]
                                    [(PeerClose) (variant False)])
                                  octet-stream)
            (let ([all-data-is-acked?
                   (case maybe-fin
                     [(NoFinSeq)
                      ;; this shouldn't happen: we should receive the fin seq well before we get the
                      ;; ACK from the other side
                      (variant False)]
                     [(FinSeq seq)
                      (> (: packet ack) seq)])])
              ;; NOTE: Optimization: if this is the third duplicate ACK, go into fast recovery mode
              (case closing-state
                [(SentFin)
                 (cond
                   [(packet-fin? packet)
                    (case close-type
                      [(ConfirmedClose close-handler)
                       (send octet-stream (ConfirmedClosed))
                       (send close-handler (ConfirmedClosed))
                       0]
                      [(Close close-handler) 0]
                      [(PeerClose) 0])
                    (cond
                      [all-data-is-acked?
                       (goto-TimeWait octet-stream)]
                      [else
                       (goto Closing
                             close-type
                             (SentThenReceivedFin)
                             maybe-fin
                             octet-stream)])]
                   [all-data-is-acked?
                    (goto Closing
                          close-type
                          (WaitingOnPeerFin)
                          maybe-fin
                          octet-stream)]
                   [else
                    (goto Closing
                          close-type
                          (SentFin)
                          maybe-fin
                          octet-stream)])]
                [(WaitingOnPeerFin)
                 (cond
                   [(packet-fin? packet)
                    (case close-type
                      [(ConfirmedClose close-handler)
                       (send octet-stream (ConfirmedClosed))
                       (send close-handler (ConfirmedClosed))
                       0]
                      [(Close close-handler) 0]
                      [(PeerClose) 0])
                    (goto-TimeWait octet-stream)]
                   [else
                    (goto Closing
                          close-type
                          closing-state
                          maybe-fin
                          octet-stream)])]
                [(SentThenReceivedFin)
                 (cond
                   [all-data-is-acked? (goto-TimeWait octet-stream)]
                   [else
                    (goto Closing
                          close-type
                          closing-state
                          maybe-fin
                          octet-stream)])]
                [(WaitingOnPeerAck)
                 (cond
                   [all-data-is-acked?
                    (halt-with-notification)]
                   [else
                    (goto Closing
                          close-type
                          closing-state
                          maybe-fin
                          octet-stream)])]))])]
        [(Register h)
         (goto Closing close-type closing-state maybe-fin octet-stream)]
        [(Write d write-handler)
         (send write-handler (CommandFailed))
         (goto Closing close-type closing-state maybe-fin octet-stream)]
        [(Close close-handler)
         (send close-handler (CommandFailed))
         (goto Closing close-type closing-state maybe-fin octet-stream)]
        [(ConfirmedClose close-handler)
         (send close-handler (CommandFailed))
         (goto Closing close-type closing-state maybe-fin octet-stream)]
        [(Abort close-handler)
         (abort-connection)
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(InternalAbort)
         (abort-connection)
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(TheFinSeq seq) (goto Closing close-type closing-state (FinSeq seq) octet-stream)]
        [(RegisterTimeout)
         ;; shouldn't happen here
         (goto Closing close-type closing-state maybe-fin octet-stream)]
        [(TimeWaitTimeout)
         ;; shouldn't happen here
         (goto Closing close-type closing-state maybe-fin octet-stream)]))

    ;; Waiting to make sure the peer received our ACK of their FIN (we've already received an ACK for
    ;; our FIN)
    (define-state (TimeWait [octet-stream (Addr TcpSessionEvent)]
                            [time-wait-timer (Addr TimerCommand)]) (m)
      (case m
        [(OrderedTcpPacket packet)
         (cond
           [(packet-rst? packet)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [(packet-syn? packet)
            (send octet-stream (ErrorClosed))
            (abort-connection)
            (halt-with-notification)]
           [else
            (send time-wait-timer (Start (mult 2 max-segment-lifetime-in-ms)))
            (goto TimeWait octet-stream time-wait-timer)])]
        [(Register h) (goto TimeWait octet-stream time-wait-timer)]
        [(Write d write-handler)
         (send write-handler (CommandFailed))
         (goto TimeWait octet-stream time-wait-timer)]
        [(Close close-handler)
         (send close-handler (CommandFailed))
         (goto TimeWait octet-stream time-wait-timer)]
        [(ConfirmedClose close-handler)
         (send close-handler (CommandFailed))
         (goto TimeWait octet-stream time-wait-timer)]
        [(Abort close-handler)
         (abort-connection)
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(InternalAbort)
         (abort-connection)
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(TheFinSeq seq) (goto TimeWait octet-stream time-wait-timer)]
        [(RegisterTimeout) (goto TimeWait octet-stream time-wait-timer)]
        [(TimeWaitTimeout)
         ;; (send status-updates (ConnectionClosed))
         (halt-with-notification)]))

    (define-state (Closed) (m)
      (case m
        [(OrderedTcpPacket packet)
         (abort-connection)
         (goto Closed)]
        [(Register h) (goto Closed)]
        [(Write data handler)
         ;; can't write anymore
         (send handler (CommandFailed))
         (goto Closed)]
        [(Close close-handler)
         (send close-handler (CommandFailed))
         (goto Closed)]
        [(ConfirmedClose close-handler)
         (send close-handler (CommandFailed))
         (goto Closed)]
        [(Abort close-handler)
         (send close-handler (CommandFailed))
         (goto Closed)]
        [(InternalAbort) (goto Closed)]
        [(TheFinSeq seq) (goto Closed)]
        [(RegisterTimeout) (goto Closed)]
        ;; shouldn't happen here:
        [(TimeWaitTimeout) (goto Closed)]))))))

(define tcp-program
  `(program (receptionists [session TcpSessionInput])
            (externals [receive-buffer ReceiveBufferCommand]
                       [send-buffer SendBufferCommand]
                       [status-updates ConnectionStatus]
                       [close-notifications (Union [SessionCloseNotification SessionId])])
            ,@tcp-definitions
            (actors [session (spawn 1
                                    TcpSession
                                    (record [remote-address (record [ip ,remote-ip] [port ,remote-port])]
                                            [local-port ,local-port])
                                    ,local-iss
                                    (variant ActiveOpen)
                                    receive-buffer
                                    send-buffer
                                    status-updates
                                    close-notifications
                                    ,wait-time-in-milliseconds
                                    ,max-retries
                                    ,max-segment-lifetime
                                    ,user-response-wait-time)])))

;; ---------------------------------------------------------------------------------------------------
;; Testing

(module+ test
  (require
   asyncunit
   (only-in csa record variant :)
   csa/eval
   csa/testing
   racket/async-channel
   rackunit
   (for-syntax syntax/parse)
   "../csa.rkt" ; for csa-valid-type?
   "../desugar.rkt"
   "../main.rkt")

  (define-match-expander tcp-syn
    (lambda (stx)
      (syntax-parse stx
        [(_ dest-port)
         #`(csa-record
            (source-port _)
            (destination-port (== dest-port))
            (seq _)
            (ack _)
            (ack-flag (csa-variant NoAck))
            (rst (csa-variant NoRst))
            (syn (csa-variant Syn))
            (fin (csa-variant NoFin))
            (window _)
            (payload (vector)))])))

  (define-match-expander tcp-syn-ack
    (lambda (stx)
      (syntax-parse stx
        [(_ src-port dest-port iss-name expected-ack)
         #`(csa-record
            (source-port (== src-port))
            (destination-port (== dest-port))
            (seq iss-name)
            (ack (== expected-ack))
            (ack-flag (csa-variant Ack))
            (rst (csa-variant NoRst))
            (syn (csa-variant Syn))
            (fin (csa-variant NoFin))
            (window _)
            (payload (vector)))])))

  (define-match-expander tcp-ack
    (lambda (stx)
      (syntax-parse stx
        [(_ src-port dest-port seqno ackno)
         #`(csa-record
            (source-port (== src-port))
            (destination-port (== dest-port))
            (seq (== seqno))
            (ack (== ackno))
            (ack-flag (csa-variant Ack))
            (rst (csa-variant NoRst))
            (syn (csa-variant NoSyn))
            (fin (csa-variant NoFin))
            (window _)
            (payload (vector)))])))

  (define-match-expander tcp-rst
    (lambda (stx)
      (syntax-parse stx
        [(_ src-port dest-port seqno)
         #`(csa-record
            (source-port (== src-port))
            (destination-port (== dest-port))
            (seq (== seqno))
            (ack _)
            (ack-flag (csa-variant NoAck))
            (rst (csa-variant Rst))
            (syn (csa-variant NoSyn))
            (fin (csa-variant NoFin))
            (window _)
            (payload (vector)))])))

  (define-match-expander tcp-fin
    (lambda (stx)
      (syntax-parse stx
        [(_ src-port dest-port seqno ackno)
         #`(csa-record
            (source-port (== src-port))
            (destination-port (== dest-port))
            (seq (== seqno))
            (ack (== ackno))
            (ack-flag (csa-variant Ack))
            (rst (csa-variant NoRst))
            (syn (csa-variant NoSyn))
            (fin (csa-variant Fin))
            (window _)
            (payload (vector)))])))

  (define-match-expander tcp-normal
    (lambda (stx)
      (syntax-parse stx
        [(_ src-port dest-port seqno ackno the-payload)
         #`(csa-record
            (source-port (== src-port))
            (destination-port (== dest-port))
            (seq (== seqno))
            (ack (== ackno))
            (ack-flag (csa-variant Ack))
            (rst (csa-variant NoRst))
            (syn (csa-variant NoSyn))
            (fin (csa-variant NoFin))
            (window _)
            (payload the-payload))])))

  (define-match-expander OutPacket
    (lambda (stx)
      (syntax-parse stx
        [(_ ip-pattern packet-pattern)
         #`(quasiquote (variant OutPacket ,ip-pattern ,packet-pattern))])))

  (define desugared-program (desugar tcp-program))

  (define (start-prog)
    (define receive-buffer (make-async-channel))
    (define send-buffer (make-async-channel))
    (define status-updates (make-async-channel))
    (define close-notifications (make-async-channel))
    (values receive-buffer send-buffer status-updates close-notifications
      (csa-run desugared-program receive-buffer send-buffer status-updates close-notifications)))

  ;; Test data


  (define (send-packet addr packet)
    (async-channel-put addr `(variant OrderedTcpPacket ,packet)))
  (define (send-command addr cmd)
    (async-channel-put addr `(variant UserCommand ,cmd)))
  (define (send-session-command addr cmd)
    (async-channel-put addr cmd))

  (define (make-rst source-port dest-port seq)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack 0]
     [ack-flag (variant NoAck)]
     [rst (variant Rst)]
     [syn (variant NoSyn)]
     [fin (variant NoFin)]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  (define (make-syn src-port dest-port seqno)
    (record
     [source-port src-port]
     [destination-port dest-port]
     [seq seqno]
     [ack 0]
     [ack-flag (variant NoAck)]
     [rst (variant NoRst)]
     [syn (variant Syn)]
     [fin (variant NoFin)]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  (define (make-syn-ack source-port dest-port seq ack)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack ack]
     [ack-flag (variant Ack)]
     [rst (variant NoRst)]
     [syn (variant Syn)]
     [fin (variant NoFin)]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  ;; (define (make-ack source-port dest-port seqno ackno)
  ;;   (record
  ;;    ([source-port ,source-port]
  ;;     [destination-port ,dest-port]
  ;;     [seq ,seqno]
  ;;     [ack ,ackno]
  ;;     [ack-flag Ack]
  ;;     [rst NoRst]
  ;;     [syn NoSyn]
  ;;     [fin NoFin]
  ;;     [window DEFAULT-WINDOW-SIZE]
  ;;     [payload (vector)])))

  (define (make-normal-packet source-port dest-port seq ack payload)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack ack]
     [ack-flag (variant Ack)]
     [rst (variant NoRst)]
     [syn (variant NoSyn)]
     [fin (variant NoFin)]
     [window DEFAULT-WINDOW-SIZE]
     [payload payload]))

  (define (make-fin source-port dest-port seq ack)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack ack]
     [ack-flag (variant Ack)]
     [rst (variant NoRst)]
     [syn (variant NoSyn)]
     [fin (variant Fin)]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  (define (InetSocketAddress ip port)
    (record [ip ip] [port port]))

  (define-syntax (define-test-variants stx)
    (syntax-parse stx
      [(_ (tag:id args:id ...) ...)
       #`(begin
           (define (tag args ...) (variant tag args ...)) ...)]))

  (define-test-variants
    (SendSyn)
    (SendRst)
    (SendText data)
    (SendFin)
    (TheFinSeq seq)
    (Resume)
    (CommandFailed)
    (Register handler)
    (Write data handler)
    (WriteAck)
    (ReceivedData data)
    (Close handler)
    (Closed)
    (ConfirmedClose handler)
    (ConfirmedClosed)
    (Abort handler)
    (Aborted)
    (InternalAbort)
    (PeerClosed)
    (ErrorClosed))

  ;; Helpers to get to various states
  (define (connect)
    (define-values (rb sb su cn session) (start-prog))
    (send-packet session (make-syn-ack remote-port local-port remote-iss (add1 local-iss)))
    (match (async-channel-get su)
      [(csa-variant Connected _ session) (list sb session)]))

  (define (establish octet-handler)
    (match-define (list sb session) (connect))
    (send-session-command session (Register octet-handler))
    (list sb session))

  (define (check-closed? session)
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1) write-handler))
    (check-unicast write-handler (CommandFailed))))

(module+ test
  ;; Dynamic tests

  (test-case "SYN/ACK to SYN makes session send ACK, notifies user"
    (define-values (rb sb su cn session) (start-prog))
    (send-packet session (make-syn-ack remote-port local-port remote-iss (add1 local-iss)))
    (check-unicast-match su (csa-variant Connected _ _)))

  (test-case "Proper handshake/upper layer notification on simultaneous open"
    ;; Overall sequence is:
    ;; 1. SYN ->
    ;; 2. SYN <-
    ;; 3. SYN/ACK ->
    ;; 4. ACK <-
    (define-values (rb sb su cn session) (start-prog))
    (send-packet session (make-syn remote-port local-port remote-iss))
    (check-unicast sb (SendSyn))
    (send-packet session (make-normal-packet remote-port
                                             local-port
                                             (add1 remote-iss)
                                             (add1 local-iss)
                                             (vector)))
    (check-unicast-match su (csa-variant Connected _ _)))

  (test-case "Proper handshake/upper layer notification on simultaneous open with simultaneous SYN/ACK"
    ;; Overall sequence is:
    ;; 1. SYN ->
    ;; 2. SYN <-
    ;; 3. SYN/ACK ->
    ;; 3. SYN/ACK <-
    ;; 4. ACK ->
    (define-values (rb sb su cn session) (start-prog))
    (send-packet session (make-syn remote-port local-port remote-iss))
    (check-unicast sb (SendSyn))
    (send-packet session (make-syn-ack remote-port local-port remote-iss (add1 local-iss)))
    (check-unicast-match su (csa-variant Connected _ _)))

  (test-case "Eventually give up if get timeout after a simultaneous SYN"
    ;; Overall sequence is:
    ;; 1. SYN ->
    ;; 2. SYN <-
    ;; 3. SYN/ACK ->
    ;; 4. (timeout)
    (define-values (rb sb su cn session) (start-prog))
    (send-packet session (make-syn remote-port local-port remote-iss))
    (check-unicast sb (SendSyn))
    (async-channel-put session (InternalAbort))
    (check-unicast su (variant CommandFailed)))

  (test-case "Registered address receives the received octets"
    (match-define (list sb session) (connect))
    (define octet-dest (make-async-channel))
    (send-session-command session (Register octet-dest))
    (send-packet session (make-normal-packet remote-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-unicast octet-dest (ReceivedData (vector 1 2 3))))

  (test-case "Timeout before registration closes the session"
    (match-define (list sb session) (connect))
    (async-channel-put session (InternalAbort))
    (check-unicast sb (SendRst))
    (define octet-dest (make-async-channel))
    (send-session-command session (Register octet-dest))
    (send-packet session (make-normal-packet remote-port
                                             local-port
                                             (add1 remote-iss)
                                             (add1 local-iss)
                                             (vector 1 2 3)))
    (check-no-message octet-dest))

  (test-case "Octet stream receives data"
    (define octet-handler (make-async-channel))
    (match-define (list sb session) (establish octet-handler))
    (send-packet session (make-normal-packet remote-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-unicast octet-handler (ReceivedData (vector 1 2 3))))

  (test-case "Close on receiving a FIN"
    ;; NOTE: we assume that the session should end after receiving a FIN (this is the default in Akka,
    ;; although they also allow the option of maintaining a half-open connection until the user
    ;; decides to close)
    ;;
    ;; NOTE: this case corresponds to line 255 of TcpConnection.scala in the Akka codebase
    (define octet-dest (make-async-channel))
    (match-define (list sb session) (establish octet-dest))
    (send-packet session (make-fin remote-port local-port (add1 remote-iss) (add1 local-iss)))
    (check-unicast octet-dest (PeerClosed))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    ;; ACK the FIN
    (send-packet session (make-fin remote-port local-port (add1 remote-iss) (+ 1 fin-seq)))
    (check-closed? session))

  (test-case "ConfirmedClose, through the ACK-then-FIN route"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    ;; received packets *should* come through to the user (we're only half-closed)
    (send-packet session (make-normal-packet remote-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-unicast handler (ReceivedData (vector 1 2 3)))
    ;; now the peer sends its ACK and FIN and closes
    (send-packet session (make-normal-packet remote-port local-port (+ 4 remote-iss) (+ 1 fin-seq) (vector)))
    (send-packet session (make-fin remote-port           local-port (+ 4 remote-iss) (+ 1 fin-seq)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-closed? session))

  (test-case "ConfirmedClose, through the FIN-with-ACK route"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    (send-packet session (make-fin remote-port           local-port (add1 remote-iss) (+ 1 fin-seq)))
    (send-packet session (make-normal-packet remote-port local-port (+ 2 remote-iss) (+ 1 fin-seq) (vector)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-closed? session))

  (test-case "ConfirmedClose, through the FIN then ACK route"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    (send-packet session (make-fin remote-port local-port (add1 remote-iss) (+ 1 fin-seq)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-closed? session))

  (test-case "Close, through the ACK then FIN route"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (Close close-handler))
    (check-unicast handler (Closed))
    (check-unicast close-handler (Closed))
        (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    ;; received packets should not come through to the user
    (send-packet session (make-normal-packet remote-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-no-message handler #:timeout 0.5)

    ;; peer ACKs the FIN
    (send-packet session (make-normal-packet remote-port local-port (+ 4 remote-iss) (add1 fin-seq) (vector)))
    ;; peer sends its FIN
    (send-packet session (make-fin remote-port local-port (+ 4 remote-iss) (add1 fin-seq)))
    (check-closed? session))

  (test-case "Abort from ESTABLISHED"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (Abort close-handler))
    (check-unicast handler (Aborted))
    (check-unicast close-handler (Aborted))
    (check-unicast sb (SendRst))
    (check-closed? session)
    ;; received packets should not come through to the user
    (send-packet session (make-normal-packet remote-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-no-message handler #:timeout 0.5))

  (test-case "Abort from AwaitingRegistration"
    (match-define (list sb session) (connect))
    (define close-handler (make-async-channel))
    (send-session-command session (Abort close-handler))
    (check-unicast close-handler (Aborted))
    (check-unicast sb (SendRst))
    (check-closed? session))

  (test-case "ConfirmedClose from AwaitingRegistration"
    (match-define (list sb session) (connect))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    (send-packet session (make-normal-packet remote-port local-port (+ 1 remote-iss) (add1 fin-seq) (vector)))
    (send-packet session (make-fin remote-port           local-port (+ 1 remote-iss) (add1 fin-seq)))
    (check-unicast close-handler (ConfirmedClosed))
    (check-closed? session))

  (test-case "Close from AwaitingRegistration"
    (match-define (list sb session) (connect))
    (define close-handler (make-async-channel))
    (send-session-command session (Close close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    (check-unicast close-handler (Closed))
    (check-closed? session))

  (test-case "Can abort while closing"
    (define handler (make-async-channel))
    (match-define (list sb session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast sb (SendFin))
    (async-channel-put session (TheFinSeq fin-seq))
    (define abort-handler (make-async-channel))
    (send-session-command session (Abort abort-handler))
    (check-unicast sb (SendRst))
    (check-unicast abort-handler (Aborted))
    (check-unicast handler (Aborted))
    ;; the close handler gets NO message
    (check-no-message close-handler)
    (check-closed? session)))

;; Conformance Tests
;; (module+ test
;;   (define desugared-tcp-packet-type
;;     `(Record
;;       [source-port Nat]
;;       [destination-port Nat]
;;       [seq Nat]
;;       [ack Nat]
;;       [ack-flag (Union [Ack] [NoAck])]
;;       [rst (Union [Rst] [NoRst])]
;;       [syn (Union [Syn] [NoSyn])]
;;       [fin (Union [Fin] [NoFin])]
;;       [window Nat]
;;       [payload (Vectorof Nat)]))

;;   (define desugared-tcp-output
;;     `(Union [OutPacket Nat ,desugared-tcp-packet-type]))

;;   (define desugared-socket-address
;;     `(Record [ip Nat] [port Nat]))

;;   (define desugared-session-id
;;     `(Record [remote-address ,desugared-socket-address] [local-port Nat]))

;;   (define desugared-tcp-session-event
;;     `(Union
;;       [ReceivedData (Vectorof Nat)]
;;       [Closed]
;;       [ConfirmedClosed]
;;       [Aborted]
;;       [PeerClosed]
;;       [ErrorClosed]))

;;   (define desugared-write-response
;;     `(Union
;;       [CommandFailed]
;;       [WriteAck]))

;;   (define desugared-session-command
;;     `(Union
;;       (Register (Addr ,desugared-tcp-session-event))
;;       (Write (Vectorof Nat) (Addr ,desugared-write-response))
;;       (Close (Addr (Union [CommandFailed] [Closed])))
;;       (ConfirmedClose (Addr (Union [CommandFailed] [ConfirmedClosed])))
;;       (Abort (Addr (Union [CommandFailed] [Aborted])))))

;;   (define desugared-connection-status
;;     `(Union
;;       [CommandFailed]
;;       [Connected ,desugared-session-id
;;                  (Addr ,desugared-session-command)]))

;;   (define desugared-user-command
;;     `(Union
;;       [Connect ,desugared-socket-address (Addr ,desugared-connection-status)]
;;       [Bind Nat
;;             (Addr (Union [Bound] [CommandFailed]))
;;             (Addr ,desugared-connection-status)]))

;;   (define desugared-tcp-input
;;     `(Union
;;       (InPacket Nat ,desugared-tcp-packet-type)
;;       (UserCommand ,desugared-user-command)
;;       (SessionCloseNotification ,desugared-session-id)))

;;   (define tcp-session-program
;;     `(program (receptionists [launcher (Addr ConnectionStatus)])
;;               (externals [session-packet-dest (Addr (Union (InTcpPacket TcpPacket)))]
;;                          [packets-out (Union [OutPacket IpAddress TcpPacket])]
;;                          [close-notifications (Union [SessionCloseNotification SessionId])])
;;               ,@tcp-definitions
;;               (define-actor Nat
;;                 (Launcher [session-packet-dest (Addr (Addr (Union (InTcpPacket TcpPacket))))]
;;                           [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
;;                           [close-notifications (Addr (Union [SessionCloseNotification SessionId]))])
;;                 ()
;;                 (goto Init)
;;                 (define-state (Init) (status-updates)
;;                   (let ([session (spawn session
;;                                         TcpSession
;;                                         (SessionId (InetSocketAddress 1234 50) 80)
;;                                         (ActiveOpen)
;;                                         packets-out
;;                                         status-updates
;;                                         close-notifications
;;                                         30000
;;                                         3
;;                                         30000
;;                                         10000)])
;;                     ;; this makes the packet side of the session observable
;;                     (send session-packet-dest session)
;;                     (goto Done)))
;;                 (define-state (Done) (m) (goto Done)))
;;               (actors [launcher (spawn launcher
;;                                        Launcher
;;                                        session-packet-dest
;;                                        packets-out
;;                                        close-notifications)])))

;;   (define session-spec-behavior
;;     `((goto AwaitingRegistration)

;;       (define-state (AwaitingRegistration)
;;         [(variant Register app-handler) -> () (goto Connected app-handler)]
;;         [(variant Write * write-handler) ->
;;          ([obligation write-handler (variant CommandFailed)])
;;          (goto AwaitingRegistration)]
;;         [(variant Close close-handler) ->
;;          ([obligation close-handler (variant Closed)])
;;          (goto ClosedNoHandler)]
;;         ;; NOTE: this is a tricky spec. I want to say that eventually the session is guaranteed to
;;         ;; close, but the possibility of Abort means this close-handler might not get a response. Also
;;         ;; the blurring would make that hard to check even without the abort issue.
;;         [(variant ConfirmedClose close-handler) -> () (goto ClosingNoHandler close-handler)]
;;         [(variant Abort abort-handler) ->
;;          ([obligation abort-handler (variant Aborted)])
;;          (goto ClosedNoHandler)]
;;         ;; e.g. might close because of a registration timeout
;;         [unobs -> () (goto ClosedNoHandler)])

;;       (define-state (Connected app-handler)
;;         [(variant Register other-app-handler) -> () (goto Connected app-handler)]
;;         [(variant Write * write-handler) ->
;;          ;; NOTE: this would probably be WriteAck OR CommandFailed in a real implementation that has a
;;          ;; limit on its queue size
;;          ([obligation write-handler (variant WriteAck)])
;;          (goto Connected app-handler)]
;;         [(variant Close close-handler) ->
;;          ([obligation app-handler (variant Closed)]
;;           [obligation close-handler (variant Closed)])
;;          (goto Closed app-handler)]
;;         [(variant ConfirmedClose close-handler) -> () (goto Closing app-handler close-handler)]
;;         [(variant Abort abort-handler) ->
;;          ([obligation abort-handler (variant Aborted)]
;;           [obligation app-handler (variant Aborted)])
;;          (goto Closed app-handler)]
;;         ;; Possible unobserved events:
;;         [unobs -> ([obligation app-handler (variant ReceivedData *)]) (goto Connected app-handler)]
;;         [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)]
;;         [unobs -> ([obligation app-handler (variant PeerClosed)]) (goto Closed app-handler)])

;;       (define-state (Closing app-handler close-handler)
;;         [unobs ->
;;          ([obligation close-handler (variant ConfirmedClosed)]
;;           [obligation app-handler (variant ConfirmedClosed)])
;;          (goto Closed app-handler)]
;;         [(variant Register app-handler) -> () (goto Closing app-handler close-handler)]
;;         [(variant Write * write-handler) ->
;;          ([obligation write-handler (variant CommandFailed)])
;;          (goto Closing app-handler close-handler)]
;;         [(variant Close other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto Closing app-handler close-handler)]
;;         [(variant ConfirmedClose other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto Closing app-handler close-handler)]
;;         [(variant Abort abort-handler) ->
;;          ;; NOTE: no response at all on the ConfirmedClose handler: this is intentional (although
;;          ;; possibly not a good idea)
;;          ([obligation abort-handler (variant Aborted)]
;;           [obligation app-handler (variant Aborted)])
;;          (goto Closed app-handler)]
;;         [unobs ->
;;          ([obligation app-handler (variant ReceivedData *)])
;;          (goto Closing app-handler close-handler)]
;;         ;; NOTE: again, no response on close-handler. Again, intentional
;;         [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)])

;;       (define-state (ClosingNoHandler close-handler)
;;         [unobs -> ([obligation close-handler (variant ConfirmedClosed)]) (goto ClosedNoHandler)]
;;         [(variant Register app-handler) -> () (goto ClosingNoHandler close-handler)]
;;         [(variant Write * write-handler) ->
;;          ([obligation write-handler (variant CommandFailed)])
;;          (goto ClosingNoHandler close-handler)]
;;         [(variant Close other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto ClosingNoHandler close-handler)]
;;         [(variant ConfirmedClose other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto ClosingNoHandler close-handler)]
;;         [(variant Abort abort-handler) ->
;;          ([obligation abort-handler (variant Aborted)]) (goto ClosedNoHandler)]
;;         ;; NOTE: again, no response on close-handler. Again, intentional
;;         [unobs -> () (goto ClosedNoHandler)])

;;       (define-state (ClosedNoHandler)
;;         [(variant Register app-handler) -> () (goto ClosedNoHandler)]
;;         [(variant Write * write-handler) ->
;;          ([obligation write-handler (variant CommandFailed)])
;;          (goto ClosedNoHandler)]
;;         [(variant Close other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto ClosedNoHandler)]
;;         [(variant ConfirmedClose other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto ClosedNoHandler)]
;;         [(variant Abort abort-handler) ->
;;          ;; An abort during the close process could still succeed
;;          ([obligation abort-handler (or (variant Aborted) (variant CommandFailed))])
;;          (goto ClosedNoHandler)])

;;       (define-state (Closed app-handler)
;;         [(variant Register app-handler) -> () (goto Closed app-handler)]
;;         [(variant Write * write-handler) ->
;;          ([obligation write-handler (variant CommandFailed)])
;;          (goto Closed app-handler)]
;;         [(variant Close other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto Closed app-handler)]
;;         [(variant ConfirmedClose other-close-handler) ->
;;          ([obligation other-close-handler (variant CommandFailed)])
;;          (goto Closed app-handler)]
;;         [(variant Abort abort-handler) ->
;;          ;; An abort during the close process could still succeed
;;          ([obligation abort-handler (variant Aborted)]
;;           [obligation app-handler (variant Aborted)])
;;          (goto Closed app-handler)]
;;         ;; An abort during the close process could still succeed. Abort may or may not send on
;;         ;; app-handler, depending on which state it's in internally
;;         [(variant Abort abort-handler) ->
;;          ([obligation app-handler (variant CommandFailed)]
;;           [obligation abort-handler (variant CommandFailed)])
;;          (goto Closed app-handler)]
;;         [(variant Abort abort-handler) ->
;;          ([obligation abort-handler (variant CommandFailed)])
;;          (goto Closed app-handler)]
;;         ;; We might get some data while the other side is closing. Could probably split this into a
;;         ;; separate spec state, but I'm leaving it here for now
;;         [unobs -> ([obligation app-handler (variant ReceivedData *)]) (goto Closed app-handler)]
;;         [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)])))

;;   (define session-spec
;;     `(specification
;;       (receptionists [launcher (Addr ,desugared-connection-status)])
;;       (externals [session-packet-dest (Addr (Union [InTcpPacket ,desugared-tcp-packet-type]))]
;;                  [packets-out ,desugared-tcp-output]
;;                  [close-notifications (Union [SessionCloseNotification ,desugared-session-id])])
;;       [launcher (Addr ,desugared-connection-status)]
;;       ()
;;       (goto Init)
;;       (define-state (Init)
;;         [status-updates ->
;;          ([obligation status-updates (or (variant CommandFailed)
;;                                          (variant Connected * (fork ,@session-spec-behavior)))])
;;          (goto Done)])
;;       (define-state (Done)
;;         [* -> () (goto Done)])))

;;   ;; (test-true "Conformance for session"
;;   ;;   (check-conformance (desugar tcp-session-program) session-spec))

;;   (define manager-spec
;;     `(specification (receptionists [tcp ,desugared-tcp-input])
;;                     (externals [packets-out ,desugared-tcp-output])
;;        [tcp  (Union [UserCommand ,desugared-user-command])] ; obs interface
;;        ([tcp (Union [InPacket Nat ,desugared-tcp-packet-type])])  ; unobs interface
;;        (goto Managing)
;;        (define-state (Managing)
;;          [(variant UserCommand (variant Connect * status-updates)) ->
;;           ([fork (goto MaybeSend status-updates)
;;                  (define-state (MaybeSend status-updates)
;;                    [unobs ->
;;                     ([obligation status-updates
;;                                  (or (variant CommandFailed)
;;                                      (variant Connected * (fork ,@session-spec-behavior)))])
;;                     (goto Done)])
;;                  (define-state (Done))])
;;           (goto Managing)]
;;          [(variant UserCommand (variant Bind * bind-status bind-handler)) ->
;;           ;; on Bind, send back the response to bind-status and fork a spec that says we might get
;;           ;; some number of connections on this address
;;           ([obligation bind-status (or (variant CommandFailed) (variant Bound))]
;;            [fork (goto MaybeGetConnection bind-handler)
;;                  (define-state (MaybeGetConnection bind-handler)
;;                    [unobs ->
;;                     ([obligation bind-handler (variant Connected * (fork ,@session-spec-behavior))])
;;                     (goto MaybeGetConnection bind-handler)])])
;;           (goto Managing)])))

;;   (test-true "User command type" (csa-valid-type? desugared-user-command))
;;   (test-true "Conformance for manager"
;;     (check-conformance desugared-program manager-spec))


;;   (define session-wire-spec
;;     `(specification (receptionists [session ???])
;;                     (externals [receive-buffer ???]
;;                                [send-buffer ???])
;;        [session ???]
;;        ([session ???])
;;        (goto SynSent send-buffer)
;;        (define-state (SynSent send-buffer)
;;          ;; SYN: simultaneous open
;;          ;; SYN-ACK: regular open, go to established
;;          ;; else: ? (what assumptions do we make about what gets here?)
;;          [(record [source-port *] [destination-port *] [seq *] [ack *] [ack-flag Ack?] [rst Rst?] [syn Syn?] [fin Fin?] [window *] [payload *])]
;;          )

;;        ;; Other states:
;;        ;; * awaiting user registration, established, syn received, the 6 closing states, and Closed (that's a lot...)
;;        ))
;;   )
(module+ test
  (define desugared-tcp-packet-type
    `(Record
      [source-port Nat]
      [destination-port Nat]
      [seq Nat]
      [ack Nat]
      [ack-flag (Union [Ack] [NoAck])]
      [rst (Union [Rst] [NoRst])]
      [syn (Union [Syn] [NoSyn])]
      [fin (Union [Fin] [NoFin])]
      [window Nat]
      [payload (Vectorof Nat)]))

  (define desugared-tcp-output
    `(Union [OutPacket Nat ,desugared-tcp-packet-type]))

  (define desugared-socket-address
    `(Record [ip Nat] [port Nat]))

  (define desugared-session-id
    `(Record [remote-address ,desugared-socket-address] [local-port Nat]))

  (define desugared-tcp-session-event
    `(Union
      [ReceivedData (Vectorof Nat)]
      [Closed]
      [ConfirmedClosed]
      [Aborted]
      [PeerClosed]
      [ErrorClosed]))

  (define desugared-write-response
    `(Union
      [CommandFailed]
      [WriteAck]))

  (define desugared-session-command
    `(Union
      (Register (Addr ,desugared-tcp-session-event))
      (Write (Vectorof Nat) (Addr ,desugared-write-response))
      (Close (Addr (Union [CommandFailed] [Closed])))
      (ConfirmedClose (Addr (Union [CommandFailed] [ConfirmedClosed])))
      (Abort (Addr (Union [CommandFailed] [Aborted])))))

  (define desugared-session-input
    `(Union
      (OrderedTcpPacket ,desugared-tcp-packet-type)
      (Register (Addr ,desugared-tcp-session-event))
      (Write (Vectorof Nat) (Addr ,desugared-write-response))
      (Close (Addr (Union [CommandFailed] [Closed])))
      (ConfirmedClose (Addr (Union [CommandFailed] [ConfirmedClosed])))
      (Abort (Addr (Union [CommandFailed] [Aborted])))
      (InternalAbort)
      (TheFinSeq Nat)
      (RegisterTimeout)
      (TimeWaitTimeout)))

  (define desugared-connection-status
    `(Union
      [CommandFailed]
      [Connected ,desugared-session-id
                 (Addr ,desugared-session-command)]))

  (define desugared-receive-buffer-command
    `(Union (Resume)))

  (define desugared-send-buffer-command
    `(Union
      [SendSyn]
      [SendRst]
      [SendText (Vectorof Nat)]
      [SendFin]))

  ;; patterns to be used in the spec
  (define-syntax (make-packet-pattern stx)
    (syntax-parse stx
      [(_  ack rst syn fin)
       #`(let ([qack 'ack]
               [qrst 'rst]
               [qsyn 'syn]
               [qfin 'qfin])
           `(variant (OrderedTcpPacket
                      (record [source-port *]
                              [destination-port *]
                              [seq *]
                              [ack *]
                              [ack-flag ,qack]
                              [rst ,qrst]
                              [syn ,qsyn]
                              [fin ,qfin]
                              [window *]
                              [payload *]))))]))

  (define session-wire-spec
    `(specification (receptionists [session ,desugared-session-input])
                    (externals [receive-buffer ,desugared-receive-buffer-command]
                               [send-buffer ,desugared-send-buffer-command]
                               [status-updates ,desugared-connection-status]
                               [close-notifications
                                (Union [SessionCloseNotification ,desugared-session-id])])
       [session (Union (OrderedTcpPacket ,desugared-tcp-packet-type))]
       ([session (Union
                  (Register (Addr ,desugared-tcp-session-event))
                  (Write (Vectorof Nat) (Addr ,desugared-write-response))
                  (Close (Addr (Union [CommandFailed] [Closed])))
                  (ConfirmedClose (Addr (Union [CommandFailed] [ConfirmedClosed])))
                  (Abort (Addr (Union [CommandFailed] [Aborted])))
                  (InternalAbort)
                  (TheFinSeq Nat))])
       (goto DoNothing)
       (define-state (DoNothing)
         [* -> () (goto DoNothing)])
       ;; (goto SynSent send-buffer)
       ;; (define-state (SynSent send-buffer)
       ;;   [,(make-packet-pattern (variant Ack) (variant Rst) * *) ->
       ;;    ([obligation send-buffer (variant SendRst)])
       ;;    (goto Closed send-buffer)]
         
       ;;   ;; ACK:
       ;;   ;;   RST: fail, halt
       ;;   ;;   SYN: finish connecting
       ;;   ;;   else: ignore
       ;;   ;; SYN: simultaneous open
       ;;   ;; SYN-ACK: regular open, go to established
       ;;   ;; RST -> RST
       ;;   ;; else: ? (what assumptions do we make about what gets here?)

       ;;   )

       ;; Other states:
       ;; * awaiting user registration, established, syn received, the 6 closing states, and Closed (that's a lot...)
       ))

;; ionists [session ,desugared-session-input])
;;                     (externals [receive-buffer ,desugared-receive-buffer-command]
;;                                [send-buffer ,desugared-send-buffer-command]
;;                                [status-updates ,desugared-connection-status]

  (test-true "session input type" (csa-valid-type? desugared-session-input))
  (test-true "receive buffer command type" (csa-valid-type? desugared-receive-buffer-command))
  (test-true "send buffer command type" (csa-valid-type? desugared-send-buffer-command))
  (test-true "connection-status type" (csa-valid-type? desugared-connection-status))
  (test-true "Conformance for session controller"
    (check-conformance desugared-program session-wire-spec)))
