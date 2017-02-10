#lang racket

;; An implementation of TCP with an Akka-style application-layer interface
;; (http://doc.akka.io/docs/akka/current/scala/io-tcp.html)

(define DEFAULT-WINDOW-SIZE 29200)
(define MAXIMUM-SEGMENT-SIZE-IN-BYTES 536)
(define wait-time-in-milliseconds 2000)
(define max-retries 3)
;; NOTE: real MSL value is 2 minutes
(define max-segment-lifetime (* 1000 2)) ; defined in milliseconds
(define user-response-wait-time 3000)
(define register-timeout 5000) ; in milliseconds (5 seconds is the Akka default)
(define timeout-fudge-factor 500) ; in milliseconds

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

  (define-type Ack? Nat)
  (define-type Rst? Nat)
  (define-type Syn? Nat)
  (define-type Fin? Nat)
  (define-function (Ack) 1)
  (define-function (NoAck) 0)
  (define-function (Rst) 1)
  (define-function (NoRst) 0)
  (define-function (Syn) 1)
  (define-function (NoSyn) 0)
  (define-function (Fin) 1)
  (define-function (NoFin) 0)

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

  (define-function (make-rst/global [received-packet TcpPacket])
    (TcpPacket (: received-packet destination-port)
               (: received-packet source-port)
               0
               (: packet seq)
               (Ack)
               (Rst)
               (NoSyn)
               (NoFin)
               ,DEFAULT-WINDOW-SIZE
               (vector)))

  (define-function (packet-ack? [packet TcpPacket])
    (= (: packet ack-flag) 1))

  (define-function (packet-rst? [packet TcpPacket])
    (= (: packet rst) 1))

  (define-function (packet-syn? [packet TcpPacket])
    (= (: packet syn) 1))

  (define-function (packet-fin? [packet TcpPacket])
    (= (: packet fin) 1))

  ;; Returns the sequence number for the last octet in the segment, or the sequence number if the
  ;; segment carries no octets.
  (define-function (segment-last-seq [packet TcpPacket])
    (+ (: packet seq)
       (max 0 (- (vector-length (: packet payload)) 1))))

;; ---------------------------------------------------------------------------------------------------
;; Receive Buffer

  ;; The receive buffer buffers packets that have been received by a socket but are not yet ready to
  ;; be processed (because some other packet earlier in the stream is still missing).

  (define-type ReceiveBuffer (Vectorof TcpPacket))

  (define-record ReceiveBufferRetrieval
    [retrieved (Vectorof TcpPacket)]
    [remaining ReceiveBuffer])

  ;; Returns a ReceiveBuffer
  (define-function (create-empty-rbuffer)
    (vector))

  ;; Helper for rbuffer-add
  (define-record RBufferAddRec
    [buffer ReceiveBuffer]
    [added? (Union [True] [False])])

  ;; Returns a ReceiveBuffer that adds the packet to the correct portion of the sequence
  (define-function (rbuffer-add [buffer ReceiveBuffer] [packet TcpPacket])
    (let ([final-add-rec
           (for/fold ([add-rec (RBufferAddRec buffer (variant False))])
                     ([buffered-packet buffer])
             (cond
               [(and (< (: packet seq) (: buffered-packet seq))
                     (not (: add-rec added?)))
                (RBufferAddRec (vector-append (: add-rec buffer) (vector packet buffered-packet))
                               (variant True))]
               [else (RBufferAddRec (vector-append (: add-rec buffer) (vector buffered-packet))
                                    (: add-rec added?))]))])
      (cond
        [(: final-add-rec added?) (: final-add-rec buffer)]
        [else (vector-append (: final-add-rec buffer) (vector packet))])))

  ;; Gets all packets from the receive buffer whose SEQ is less than stop-seq. Returns a
  ;; ReceiveBufferRetrieval that also includes the remaining buffer.
  (define-function (rbuffer-retrieve-up-to [buffer ReceiveBuffer] [stop-seq Nat])
    (for/fold ([result (ReceiveBufferRetrieval (vector) buffer)])
              ([packet buffer])
      (cond
        [(<= (: packet seq) stop-seq)
         (ReceiveBufferRetrieval (vector-append (: result retrieved) (vector packet))
                                 (vector-drop (: result remaining) 1))]
        [else result])))

;; ---------------------------------------------------------------------------------------------------
;; Send Buffer

  ;; The send buffer holds the segment of our outgoing byte stream that has not yet been
  ;; acknowledged. It tracks how many times items have been retransmitted without a new ACK, the
  ;; sequence numbers at the beginning and end of the buffer, and the current window size.,

  (define-variant MaybeFinSeq
    [NoFinSeq]
    [FinSeq [num Nat]])
  (define-record SendBuffer
    [retransmit-count Nat]
    [unacked-seq Nat]
    [window Nat] ; window size in octets
    [send-next Nat]
    [maybe-fin MaybeFinSeq]
    [buffer (Vectorof Byte)])

  ;; Returns the total number of octets to send stored in the buffer
  (define-function (send-buffer-length [s SendBuffer])
    (vector-length (: s buffer)))

  ;; Returns true if the send buffer contains no more bytes/FINs to send
  (define-function (send-buffer-empty? [s SendBuffer])
    (and (= 0 (send-buffer-length s))
         (case (: send-buffer maybe-fin)
           [(FinSeq n) (variant False)]
           [(NoFinSeq) (variant True)])))

  (define-function (increment-retransmit-count [s SendBuffer])
    (SendBuffer (+ (: s retransmit-count) 1)
                (: s unacked-seq)
                (: s window)
                (: s send-next)
                (: s maybe-fin)
                (: s buffer)))

  ;; Adds the given octets to the send buffer and updates the send-next pointer
  (define-function (send-buffer-add-octets [s SendBuffer]
                                           [data (Vectorof Byte)]
                                           [send-next Nat])
    (SendBuffer (: s retransmit-count)
                (: s unacked-seq)
                (: s window)
                send-next
                (: s maybe-fin)
                (vector-append (: s buffer) data)))

  (define-function (send-buffer-add-fin [s SendBuffer])
    (SendBuffer (: s retransmit-count)
                (: s unacked-seq)
                (: s window)
                (+ (: s send-next) 1)
                (FinSeq (: s send-next))
                (: s buffer)))

;; ---------------------------------------------------------------------------------------------------
;; Timer

  (define-variant TimerCommand
    (Stop)
    (Start [timeout-in-milliseconds Nat]))

  (define-type ExpirationMessage
    (Union
     [RegisterTimeout]
     [RetransmitTimeout]
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

  (define-type BindStatus
    (Union [Bound] [CommandFailed]))
  (define-function (Bound) (variant Bound))

  (define-variant UserCommand
    (Connect [remote-address InetSocketAddress]
             [status-updates (Addr ConnectionStatus)])
    (Bind [port Nat] [bind-status (Addr BindStatus)] [bind-handler (Addr ConnectionStatus)]))

  (define-type PacketInputMessage (Union [InPacket IpAddress TcpPacket]))

  (define-variant TcpInput
    (InPacket [src IpAddress] [packet TcpPacket])
    (UserCommand [cmd UserCommand])
    (SessionCloseNotification [id SessionId]))

  (define-variant TcpOutput
    (OutPacket [dest IpAddress] [packet TcpPacket]))

  (define-function (get-new-port)
    ;; Allowed range for private/dynamic port numbers: 49152-65535
    ;; (https://www.iana.org/assignments/service-names-port-numbers/service-names-port-numbers.xhtml)
    (let ([first-allowed-port 49152]
          [last-allowed-port 65535])
      (+ first-allowed-port (random (- last-allowed-port first-allowed-port)))))

  (define-function (get-iss)
    ;; Racket's random can't do 32 bits, so we get to 16 bit numbers and plug them together
    (+ (arithmetic-shift (random #x10000) 16) (random #x10000)))

  (define-variant Open
    (ActiveOpen)
    (PassiveOpen [remote-seq Nat]))

  (define-variant RetransmitResult
    (RetransmitFailure)
    (RetransmitSuccess))

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

  (define-variant TcpSessionInput
    (InTcpPacket [packet TcpPacket])
    ;; a "private" variant, used only internally for an ordered queue of packets. We assume that they
    ;; are in order since the messages are sent to and from the same actor. The semantics doesn't
    ;; technically guarantee this, but any real implementation would order them.
    (OrderedTcpPacket [packet TcpPacket])
    (Register [handler (Addr TcpSessionEvent)])
    (Write [data (Vectorof Byte)] [handler (Addr WriteResponse)])
    (Close [close-handler (Addr (Union [CommandFailed] [Closed]))])
    (ConfirmedClose [close-handler (Addr (Union [CommandFailed] [ConfirmedClosed]))])
    (Abort [close-handler (Addr (Union [CommandFailed] [Aborted]))])
    ;; timeouts
    (RegisterTimeout)
    (RetransmitTimeout)
    (TimeWaitTimeout))

  ;;; The TCP session actor

  (define-actor TcpSessionInput
    (TcpSession [id SessionId]
                [open Open]
                [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
                [status-updates (Addr ConnectionStatus)]
                [close-notifications (Addr (Union [SessionCloseNotification SessionId]))]
                ;; REFACTOR: make these things constants instead
                [wait-time-in-milliseconds Nat]
                [max-retries Nat]
                [max-segment-lifetime-in-ms Nat]
                [user-response-wait-time Nat])
    ((define-function (send-to-ip [packet TcpPacket])
       (send packets-out (variant OutPacket (: (: id remote-address) ip) packet)))

     (define-function (halt-with-notification)
       (send close-notifications (SessionCloseNotification id))
       (goto Closed))

     ;;;; Packet helpers
     (define-function (make-syn [seq Nat])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seq
                  0
                  (NoAck)
                  (NoRst)
                  (Syn)
                  (NoFin)
                  ,DEFAULT-WINDOW-SIZE
                  (vector)))

     (define-function (make-syn-ack [seq Nat] [ack Nat])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seq
                  ack
                  (Ack)
                  (NoRst)
                  (Syn)
                  (NoFin)
                  ,DEFAULT-WINDOW-SIZE
                  (vector)))

     (define-function (make-rst [seq Nat])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seq
                  0
                  (NoAck)
                  (Rst)
                  (NoSyn)
                  (NoFin)
                  ,DEFAULT-WINDOW-SIZE
                  (vector)))

     (define-function (make-fin [seqno Nat] [ackno Nat])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seqno
                  ackno
                  (Ack)
                  (NoRst)
                  (NoSyn)
                  (Fin)
                  ,DEFAULT-WINDOW-SIZE
                  (vector)))

     (define-function (make-fin-with-payload [seqno Nat] [ackno Nat] [payload (Vectorof Byte)])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seqno
                  ackno
                  (Ack)
                  (NoRst)
                  (NoSyn)
                  (Fin)
                  ,DEFAULT-WINDOW-SIZE
                  payload))

     (define-function (make-normal-packet [seq Nat] [ack Nat] [payload (Vectorof Byte)])
       (TcpPacket (: id local-port)
                  (: (: id remote-address) port)
                  seq
                  ack
                  (Ack)
                  (NoRst)
                  (NoSyn)
                  (NoFin)
                  ,DEFAULT-WINDOW-SIZE
                  payload))

     ;; Computes the rcv-nxt value caused by the given packet, assuming that the packet is the
     ;; furthest-forward acceptable ACK.
     (define-function (compute-receive-next [packet TcpPacket])
       (+ (: packet seq)
          (+ (: packet syn)
             (+ (: packet fin)
                (vector-length (: packet payload))))))

     (define-function (finish-connecting [snd-nxt Nat] [rcv-nxt Nat] [window Nat])
       (send status-updates (Connected id self))
       (let ([reg-timer (spawn reg-timer-EVICT Timer (RegisterTimeout) self)])
         (send reg-timer (Start ,register-timeout))
         (goto AwaitingRegistration
               (SendBuffer 0 snd-nxt window snd-nxt (NoFinSeq) (vector))
               (vector)
               rcv-nxt
               (create-empty-rbuffer)
               reg-timer
               (spawn rxmt-timer-EVICT Timer (RetransmitTimeout) self))))

     ;; Transitions to time-wait, starting a timer on the way in
     (define-function (goto-TimeWait [snd-nxt Nat]
                                     [rcv-nxt Nat]
                                     [receive-buffer ReceiveBuffer]
                                     [octet-stream (Addr TcpSessionEvent)])
       (let ([timer (spawn time-wait-timer-EVICT Timer (TimeWaitTimeout) self)])
         (send timer (Start (mult 2 max-segment-lifetime-in-ms)))
         (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream timer)))

     ;; Returns true if the segment is "acceptable", where a segment is acceptable if its start falls
     ;; somewhere in the current receive window
     (define-function (segment-acceptable? [packet TcpPacket] [next-receive Nat])
       ;; NOTE: this is where receive window checking would go if we did that
       (>= (segment-last-seq packet) next-receive))

     ;; Returns true if the given sequence number is conceptually "part" of the given segment.
     (define-function (segment-contains-seq? [packet TcpPacket] [seq Nat])
       (and (>= seq (: packet seq)) (<= seq (segment-last-seq packet))))

     ;; Checks to see if the packet is acceptable, and if it is the next one, queues up segments for
     ;; full processing. Also drops packets with unset or in-the-future ACK. Returns the new receive
     ;; buffer.
     (define-function (process-incoming [packet TcpPacket]
                                        [rcv-nxt Nat]
                                        [receive-buffer ReceiveBuffer]
                                        [snd-nxt Nat])
       (cond
         [(segment-acceptable? packet rcv-nxt)
          ;; check if this contains the next expected thing
          (cond
            [(or (not (packet-ack? packet)) (> (: packet ack) snd-nxt))
             ;; Just drop packets with the ACK flag unset or that ACK something not yet sent
             receive-buffer]
            [(segment-contains-seq? packet rcv-nxt)
             ;; queue up this segment
             (send self (OrderedTcpPacket packet))
             ;; queue up any received segments from the receive buffer that immediately follow this
             ;; segment
             (let ([retrieval (rbuffer-retrieve-up-to receive-buffer (compute-receive-next packet))])
               (for/fold ([dummy 0])
                         ([packet (: retrieval retrieved)])
                 (send self (OrderedTcpPacket packet))
                 0)
               (: retrieval remaining))]
            [else
             ;; segment does not contain rcv-next, so add it to buffer
             (rbuffer-add receive-buffer packet)])]
         [(packet-rst? packet)
          ;; don't send an ACK for RST segments; presumably b/c it's from a previous connection
          receive-buffer]
         [else
          ;; not acceptable and not an RST, so send back the current ACK
          (send-to-ip (make-normal-packet snd-nxt rcv-nxt (vector)))
          receive-buffer]))

     ;; Adjust the send buffer as required by the ACK
     (define-function (process-ack [send-buffer SendBuffer]
                                   [ack Nat]
                                   [segment-window Nat]
                                   [rxmt-timer (Addr TimerCommand)])
       (let ([acked-new-data? (> ack (: send-buffer unacked-seq))]
             [new-snd-una (max ack (: send-buffer unacked-seq))])
         (cond
           [(and acked-new-data? (< (: send-buffer unacked-seq) (: send-buffer send-next)))
            ;; have more data to send
            (send rxmt-timer (Start wait-time-in-milliseconds))
            0]
           [else 0])
         (SendBuffer (if acked-new-data? 0 (: send-buffer retransmit-count))
                     new-snd-una
                     ;; NOTE: p. 71 of the RFC has information about when to update the send window,
                     ;; but I'm just going to update it when we get a new ACK
                     (if acked-new-data? segment-window (: send-buffer window))
                     (: send-buffer send-next)
                     (: send-buffer maybe-fin)
                     (vector-drop (: send-buffer buffer)
                                  ;; an ACK for a FIN means there will be more ACKed "bytes" than ther
                                  ;; are buffered bytes waiting to go, so we take the min here
                                  (min (- new-snd-una (: send-buffer unacked-seq))
                                       (vector-length (: send-buffer buffer)))))))

     ;; Does the necessary handling for segment text (and the FIN) on the next in-order packet,
     ;; returning the new receive-next
     (define-function (process-segment-text [segment TcpPacket]
                                            [send-buffer SendBuffer]
                                            [rcv-nxt Nat]
                                            [receive-data? (Union (True) (False))]
                                            [octet-stream (Addr TcpSessionEvent)])
       (let ([send-next (: send-buffer send-next)]
             [unseen-payload (vector-copy (: segment payload)
                                          (- rcv-nxt (: segment seq))
                                          (vector-length (: segment payload)))]
             [new-rcv-nxt (compute-receive-next segment)])
         ;; 1. send ACK if necessary
         (cond
           [(or (> (vector-length unseen-payload) 0) (packet-fin? packet))
            (send-to-ip (make-normal-packet send-next new-rcv-nxt (vector)))
            0]
           [else 0])
         ;; 2. send any unseen data to user
         (cond
           [(and (> (vector-length unseen-payload) 0) receive-data?)
            (send octet-stream (ReceivedData (: segment payload)))
            0]
           [else 0])
         new-rcv-nxt))

     ;; Splits a byte string into a list of byte strings with each one no longer than the given
     ;; size. We assume that the given byte string is non-empty, and that the size is greater than
     ;; zero.
     (define-function (segmentize [data (Vectorof Byte)] [max-segment-size Nat])
       (for/fold ([segments (vector (vector))])
                 ([b data])
         ;; get the last segment out of the list
         ;; if that segment is full, start a new one
         ;; else, add to that segment
         (let ([last-segment (vector-ref segments (- (vector-length segments) 1))])
           (cond
             [(< (vector-length last-segment) max-segment-size)
              (let ([previous-segments (vector-copy segments 0 (- (vector-length segments) 1))]
                    [updated-segment (vector-append last-segment (vector b))])
                (vector-append previous-segments (vector updated-segment)))]
             [else
              (let ([new-segment (vector b)])
                (vector-append segments (vector new-segment)))]))))

     ;; Accepts new octets to send from the user, sends the ones it can, and returns the new send
     ;; buffer with the new octets
     (define-function (accept-new-octets [octets (Vectorof Byte)]
                                         [send-buffer SendBuffer]
                                         [rcv-nxt Nat]
                                         [timer Timer])
       (let* ([first-seq-past-window (+ (: send-buffer unacked-seq) (: send-buffer window))]
              [octets-in-window
               (vector-copy octets
                            0
                            (min (vector-length octets)
                                 (- first-seq-past-window (: send-buffer send-next))))]
              [new-snd-nxt
               (for/fold ([snd-nxt (: send-buffer send-next)])
                         ([data (segmentize octets-in-window ,MAXIMUM-SEGMENT-SIZE-IN-BYTES)])
                 (send-to-ip (make-normal-packet (: send-buffer send-next) rcv-nxt data))
                 (+ (: send-buffer send-next) (vector-length data)))])
         (send timer (Start wait-time-in-milliseconds))
         (send-buffer-add-octets send-buffer octets new-snd-nxt)))

     (define-function (accept-new-fin [send-buffer SendBuffer]
                                      [rcv-nxt Nat]
                                      [timer Timer])
       ;; 1. send a FIN if we can (i.e. if it's in the window)
       (let ([first-seq-past-window (+ (: send-buffer unacked-seq) (: send-buffer window))])
         (cond
           [(< (: send-buffer send-next) first-seq-past-window)
            (send-to-ip (make-fin (: send-buffer send-next) rcv-nxt))
            0]
           [else 0]))
       (send timer (Start wait-time-in-milliseconds))
       ;; 2. mark the send buffer as needing to send a FIN
       (send-buffer-add-fin send-buffer))

     ;; Either retransmits the oldest unacked segment, or fails because it reached the retry limit
     ;; (returns RetransmitSuccess or RetransmitFailure)
     (define-function (maybe-retransmit [send-buffer SendBuffer]
                                        [rcv-nxt Nat]
                                        [timer Timer])
       (cond
         [(= (: send-buffer retransmit-count) max-retries)
          (RetransmitFailure)]
         [(not (send-buffer-empty? send-buffer))
          (let* ([payload-length (min (send-buffer-length send-buffer) ,MAXIMUM-SEGMENT-SIZE-IN-BYTES)]
                 [payload (vector-take (: send-buffer buffer) payload-length)])
            (case (: send-buffer maybe-fin)
              [(NoFinSeq)
               (send-to-ip (make-normal-packet (: send-buffer unacked-seq) rcv-nxt payload))]
              [(FinSeq fin-seq)
               (send-to-ip (make-fin-with-payload (: send-buffer unacked-seq) rcv-nxt payload))])
            (send timer (Start wait-time-in-milliseconds))
            (RetransmitSuccess))]
         [else (RetransmitSuccess)]))

     (define-function (abort-connection [snd-nxt Nat])
       (send-to-ip (make-rst snd-nxt)))

     (define-function (start-close [send-buffer SendBuffer]
                                   [rcv-nxt Nat]
                                   [receive-buffer ReceiveBuffer]
                                   [close-type CloseType]
                                   [closing-state ClosingState]
                                   [octet-stream (Addr TcpSessionEvent)]
                                   [rxmt-timer (Addr Timer)])
       (goto Closing
             (accept-new-fin send-buffer rcv-nxt rxmt-timer)
             rcv-nxt
             receive-buffer
             close-type
             closing-state
             octet-stream
             rxmt-timer)))

    ;; initialization
    (let ([iss (get-iss)])
      (case open
        [(ActiveOpen)
         (send-to-ip (make-syn iss))
         (goto SynSent (+ iss 1))]
        [(PassiveOpen remote-iss)
          (let ([rcv-nxt (+ 1 remote-iss)])
            (send-to-ip (make-syn-ack iss rcv-nxt))
            (goto SynReceived (+ 1 iss) rcv-nxt (create-empty-rbuffer)))]))

    (define-state/timeout (SynSent [snd-nxt Nat]) (m)
      (case m
        [(InTcpPacket packet)
         (cond
           [(packet-ack? packet)
            (cond
              [(= (: packet ack) snd-nxt) ; this is the only acceptable ACK
               (cond
                 [(packet-rst? packet)
                  (send status-updates (CommandFailed))
                  (halt-with-notification)]
                 [(packet-syn? packet)
                  ;; this is the typical SYN/ACK case (step 2 of the 3-way handshake)
                  (let ([rcv-nxt (compute-receive-next packet)])
                    (send-to-ip (make-normal-packet snd-nxt rcv-nxt (vector)))
                    (finish-connecting snd-nxt rcv-nxt (: packet window)))]
                 [else
                  ;; ACK acceptable but no other interesting fields set. Probably won't happen in
                  ;; reality.
                  (goto SynSent snd-nxt)])]
              [else ;; ACK present but not acceptable
               (send-to-ip (make-rst (: packet ack)))
               (send status-updates (CommandFailed))
               (halt-with-notification)])]
           [else ;; no ACK present
            (cond
              [(packet-rst? packet)
               ;; drop the packet, because the RST probably comes from a previous instance of the
               ;; session
               (goto SynSent snd-nxt)]
              [(packet-syn? packet)
               ;; we got a SYN but no ACK: this is the simultaneous open case
               (let ([iss (- snd-nxt 1)]
                     [rcv-nxt (+ (: packet seq) 1)])
                 (send-to-ip (make-syn-ack iss rcv-nxt))
                 (goto SynReceived (+ iss 1) rcv-nxt (create-empty-rbuffer)))]
              [else
               ;; not an important segment, so just drop it. Probably won't happen in reality
               (goto SynSent snd-nxt)])])]
        ;; None of these should happen at this point; ignore them
        [(OrderedTcpPacket packet) (goto SynSent snd-nxt)]
        [(Register h) (goto SynSent snd-nxt)]
        [(Write d h) (goto SynSent snd-nxt)]
        [(Close h) (goto SynSent snd-nxt)]
        [(ConfirmedClose h) (goto SynSent snd-nxt)]
        [(Abort h) (goto SynSent snd-nxt)]
        [(RegisterTimeout) (goto SynSent snd-nxt)]
        [(RetransmitTimeout) (goto SynSent snd-nxt)]
        [(TimeWaitTimeout) (goto SynSent snd-nxt)])

      [timeout wait-time-in-milliseconds
        (send status-updates (CommandFailed))
        (halt-with-notification)])

    (define-state (SynReceived [snd-nxt Nat] [rcv-nxt Nat] [receive-buffer ReceiveBuffer]) (m)
      (case m
        [(InTcpPacket packet)
         ;; RFC Errata 3305 notes that this acceptability test doesn't support all of the simultaneous
         ;; open cases, so I'm adding a special case for that instance
         (cond
           [(and (packet-syn? packet)
                 (= (: packet seq) (- rcv-nxt 1)))
            (send self (OrderedTcpPacket packet))
            (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
           [else
            (goto SynReceived
                  snd-nxt
                  rcv-nxt
                  (process-incoming packet rcv-nxt receive-buffer snd-nxt))])]
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
            (send-to-ip (make-rst snd-nxt))
            (case open
              [(ActiveOpen) (send status-updates (CommandFailed)) 0]
              [(PassiveOpen r) 0])
            (halt-with-notification)]
           [(packet-ack? packet)
            ;; NOTE: I assume here that this packet does not have a payload (perhaps not always the
            ;; case, but good enough for this small sample program)
            (cond
              [(= (: packet ack) snd-nxt)
               ;; If the packet had a SYN (part of the simultaneous open case), send an ACK
               (cond
                 [(packet-syn? packet)
                  (let ([rcv-nxt (compute-receive-next packet)])
                    (send-to-ip (make-normal-packet snd-nxt rcv-nxt (vector)))
                    (finish-connecting snd-nxt rcv-nxt (: packet window)))]
                 [else (finish-connecting snd-nxt rcv-nxt (: packet window))])]
              [else
               (send-to-ip (make-rst (: packet ack)))
               (goto SynReceived snd-nxt rcv-nxt receive-buffer)])]
           [else (goto SynReceived snd-nxt rcv-nxt receive-buffer)])]
        ;; None of these should happen at this point; ignore them
        [(Register h) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(Write d h) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(Close h) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(ConfirmedClose h) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(Abort h) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(RegisterTimeout) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(RetransmitTimeout) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(TimeWaitTimeout) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]))

    ;; We're waiting for the user to register an actor to send received octets to
    (define-state (AwaitingRegistration [send-buffer SendBuffer]
                                        [queued-packets (Vectorof TcpPacket)]
                                        [rcv-nxt Nat]
                                        [receive-buffer ReceiveBuffer]
                                        [registration-timer (Addr TimerCommand)]
                                        [rxmt-timer (Addr TimerCommand)]) (m)
      (case m
        [(InTcpPacket packet)
         ;; we don't need the handler just to process incoming packets, so we do it just like in Established
         (let ([new-receive-buffer (process-incoming packet rcv-nxt receive-buffer (: send-buffer send-next))])
           (goto AwaitingRegistration
                 send-buffer
                 queued-packets
                 rcv-nxt
                 new-receive-buffer
                 registration-timer
                 rxmt-timer))]
        [(OrderedTcpPacket packet)
         (goto AwaitingRegistration
               send-buffer
               (vector-append queued-packets (vector packet))
               rcv-nxt
               receive-buffer
               registration-timer
               rxmt-timer)]
        [(Register octet-handler)
         (send registration-timer (Stop))
         (for/fold ([dummy 0])
                   ([packet queued-packets])
           (send self (OrderedTcpPacket packet))
           0)
         (goto Established send-buffer rcv-nxt receive-buffer octet-handler rxmt-timer)]
        [(Write data handler)
         ;; can't yet write
         (send handler (CommandFailed))
         (goto AwaitingRegistration send-buffer queued-packets rcv-nxt receive-buffer registration-timer rxmt-timer)]
        [(Close close-handler)
         (send close-handler (Closed))
         (start-close send-buffer
                      rcv-nxt
                      receive-buffer
                      (Close close-handler)
                      (SentFin)
                      (spawn close-await-sink-EVICT Sink)
                      rxmt-timer)]
        [(ConfirmedClose close-handler)
         (start-close send-buffer
                      rcv-nxt
                      receive-buffer
                      (ConfirmedClose close-handler)
                      (SentFin)
                      (spawn confirmed-close-await-sink-EVICT Sink)
                      rxmt-timer)]
        [(Abort close-handler)
         (abort-connection (: send-buffer send-next))
         (send close-handler (Aborted))
         (halt-with-notification)]
        [(RegisterTimeout)
         (abort-connection (: send-buffer send-next))
         (halt-with-notification)]
        ;; these timeouts shouldn't happen here
        [(RetransmitTimeout)
         (goto AwaitingRegistration send-buffer queued-packets rcv-nxt receive-buffer registration-timer rxmt-timer)]
        [(TimeWaitTimeout)
         (goto AwaitingRegistration send-buffer queued-packets rcv-nxt receive-buffer registration-timer rxmt-timer)]))

    ;; REFACTOR: move these various receive-related params into the receive buffer
    (define-state (Established [send-buffer SendBuffer]
                               [rcv-nxt Nat]
                               [receive-buffer ReceiveBuffer]
                               [octet-stream (Addr TcpSessionEvent)]
                               [rxmt-timer (Addr TimerCommand)]) (m)
      (case m
        [(InTcpPacket packet)
         (let ([new-receive-buffer
                (process-incoming packet rcv-nxt receive-buffer (: send-buffer send-next))])
           (goto Established
                 send-buffer
                 rcv-nxt
                 new-receive-buffer
                 octet-stream
                 rxmt-timer))]
        [(OrderedTcpPacket packet)
         (cond
           [(or (packet-rst? packet) (packet-syn? packet))
            ;; REFACTOR: rename octet-stream to "handler" or something like that
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [else
            (let ([new-send-buffer
                   (process-ack send-buffer (: packet ack) (: packet window) rxmt-timer)]
                  [new-rcv-nxt (process-segment-text packet send-buffer rcv-nxt (variant True) octet-stream)])
              ;; NOTE: we could optimize here by going into fast recovery mode if this is the 3rd
              ;; duplicate ACK

              ;; Finally, check for the FIN bit
              (cond
                [(packet-fin? packet)
                 (send octet-stream (PeerClosed))
                 (start-close send-buffer
                              new-rcv-nxt
                              receive-buffer
                              (PeerClose)
                              (WaitingOnPeerAck)
                              octet-stream
                              rxmt-timer)]
                [else (goto Established
                            new-send-buffer
                            new-rcv-nxt
                            receive-buffer
                            octet-stream
                            rxmt-timer)]))])]
        [(Register h)
         (goto Established send-buffer rcv-nxt receive-buffer octet-stream rxmt-timer)]
        [(Write data handler)
         (send handler (WriteAck))
         (goto Established
               (accept-new-octets data send-buffer rcv-nxt rxmt-timer)
               rcv-nxt
               receive-buffer
               octet-stream
               rxmt-timer)]
        [(Close close-handler)
         (send close-handler (Closed))
         (send octet-stream (Closed))
         (start-close send-buffer
                      rcv-nxt
                      receive-buffer
                      (Close close-handler)
                      (SentFin)
                      octet-stream
                      rxmt-timer)]
        [(ConfirmedClose close-handler)
         (start-close send-buffer
                      rcv-nxt
                      receive-buffer
                      (ConfirmedClose close-handler)
                      (SentFin)
                      octet-stream
                      rxmt-timer)]
        [(Abort close-handler)
         (abort-connection (: send-buffer send-next))
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(RegisterTimeout)
         (goto Established send-buffer rcv-nxt receive-buffer octet-stream rxmt-timer)]
        [(RetransmitTimeout)
         (case (maybe-retransmit send-buffer rcv-nxt rxmt-timer)
           [(RetransmitSuccess)
            (goto Established
                  (increment-retransmit-count send-buffer)
                  rcv-nxt
                  receive-buffer
                  octet-stream
                  rxmt-timer)]
           [(RetransmitFailure)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)])]
        [(TimeWaitTimeout)
         (goto Established send-buffer rcv-nxt receive-buffer octet-stream rxmt-timer)]))

    ;; In the process of closing down; groups together FIN-WAIT-1, FIN-WAIT-2, CLOSING, and LAST-ACK
    ;; in the typical TCP state diagram
    (define-state (Closing [send-buffer SendBuffer]
                           [rcv-nxt Nat]
                           [receive-buffer ReceiveBuffer]
                           [close-type CloseType]
                           [closing-state ClosingState]
                           [octet-stream (Addr TcpSessionEvent)]
                           [rxmt-timer (Addr TimerCommand)]) (m)
      (case m
        [(InTcpPacket packet)
         (let ([new-receive-buffer
                (process-incoming packet rcv-nxt receive-buffer (: send-buffer send-next))])
           (goto Closing
                 send-buffer
                 rcv-nxt
                 new-receive-buffer
                 close-type
                 closing-state
                 octet-stream
                 rxmt-timer))]
        [(OrderedTcpPacket packet)
         (cond
           [(or (packet-rst? packet) (packet-syn? packet))
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [else
            (let ([new-send-buffer (process-ack send-buffer (: packet ack) (: packet window) rxmt-timer)]
                  [new-rcv-nxt (process-segment-text packet
                                                     send-buffer
                                                     rcv-nxt
                                                     (case close-type
                                                       [(ConfirmedClose h) (variant True)]
                                                       [(Close h) (variant False)]
                                                       [(PeerClose) (variant False)])
                                                     octet-stream)]
                  [all-data-is-acked? (>= (: packet ack) (- (: send-buffer send-next) 1))])
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
                       (goto-TimeWait (: send-buffer send-next) rcv-nxt receive-buffer octet-stream)]
                      [else
                       (goto Closing
                             send-buffer
                             rcv-nxt
                             receive-buffer
                             close-type
                             (SentThenReceivedFin)
                             octet-stream
                             rxmt-timer)])]
                   [all-data-is-acked?
                    (goto Closing
                          new-send-buffer
                          new-rcv-nxt
                          receive-buffer
                          close-type
                          (WaitingOnPeerFin)
                          octet-stream
                          rxmt-timer)]
                   [else
                    (goto Closing
                          new-send-buffer
                          new-rcv-nxt
                          receive-buffer
                          close-type
                          (SentFin)
                          octet-stream
                          rxmt-timer)])]
                [(WaitingOnPeerFin)
                 (cond
                   [(packet-fin? packet)
                    (send-to-ip (make-normal-packet (: send-buffer send-next) new-rcv-nxt (vector)))
                    (case close-type
                      [(ConfirmedClose close-handler)
                       (send octet-stream (ConfirmedClosed))
                       (send close-handler (ConfirmedClosed))
                       0]
                      [(Close close-handler) 0]
                      [(PeerClose) 0])
                    (goto-TimeWait (: send-buffer send-next)
                                   rcv-nxt
                                   receive-buffer
                                   octet-stream)]
                   [else
                    (goto Closing
                          new-send-buffer
                          new-rcv-nxt
                          receive-buffer
                          close-type
                          closing-state
                          octet-stream
                          rxmt-timer)])]
                [(SentThenReceivedFin)
                 (cond
                   [all-data-is-acked?
                    (goto-TimeWait (: send-buffer send-next)
                                   rcv-nxt
                                   receive-buffer
                                   octet-stream)]
                   [else
                    (goto Closing
                          new-send-buffer
                          new-rcv-nxt
                          receive-buffer
                          close-type
                          closing-state
                          octet-stream
                          rxmt-timer)])]
                [(WaitingOnPeerAck)
                 (cond
                   [all-data-is-acked?
                    (halt-with-notification)]
                   [else
                    (goto Closing
                          new-send-buffer
                          new-rcv-nxt
                          receive-buffer
                          close-type
                          closing-state
                          octet-stream
                          rxmt-timer)])]))])]
        [(Register h)
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]
        [(Write d write-handler)
         (send write-handler (CommandFailed))
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]
        [(Close close-handler)
         (send close-handler (CommandFailed))
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]
        [(ConfirmedClose close-handler)
         (send close-handler (CommandFailed))
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]
        [(Abort close-handler)
         (abort-connection (: send-buffer send-next))
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(RegisterTimeout)
         ;; shouldn't happen here
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]
        [(RetransmitTimeout)
         (case (maybe-retransmit send-buffer rcv-nxt rxmt-timer)
           [(RetransmitSuccess)
            (goto Closing
                  (increment-retransmit-count send-buffer)
                  rcv-nxt
                  receive-buffer
                  close-type
                  closing-state
                  octet-stream
                  rxmt-timer)]
           [(RetransmitFailure)
            (send octet-stream (ErrorClosed))
            (halt-with-notification)])]
        [(TimeWaitTimeout)
         ;; shouldn't happen here
         (goto Closing send-buffer rcv-nxt receive-buffer close-type closing-state octet-stream rxmt-timer)]))

    ;; Waiting to make sure the peer received our ACK of their FIN (we've already received an ACK for
    ;; our FIN)
    (define-state (TimeWait [snd-nxt Nat]
                            [rcv-nxt Nat]
                            [receive-buffer ReceiveBuffer]
                            [octet-stream (Addr TcpSessionEvent)]
                            [time-wait-timer (Addr TimerCommand)]) (m)
      (case m
        [(InTcpPacket packet)
         (let ([new-receive-buffer (process-incoming packet rcv-nxt receive-buffer snd-nxt)])
           (goto TimeWait snd-nxt rcv-nxt new-receive-buffer octet-stream time-wait-timer))]
        [(OrderedTcpPacket packet)
         (cond
           [(or (packet-rst? packet) (packet-syn? packet))
            (send octet-stream (ErrorClosed))
            (halt-with-notification)]
           [else
            ;; If we get this far, then this must be a retransmitted FIN, so send back an ACK
            (send-to-ip (make-normal-packet snd-nxt rcv-nxt (vector)))
            (send time-wait-timer (Start (mult 2 max-segment-lifetime-in-ms)))
            (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)])]
        [(Register h) (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(Write d write-handler)
         (send write-handler (CommandFailed))
         (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(Close close-handler)
         (send close-handler (CommandFailed))
         (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(ConfirmedClose close-handler)
         (send close-handler (CommandFailed))
         (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(Abort close-handler)
         (abort-connection snd-nxt)
         (send close-handler (Aborted))
         (send octet-stream (Aborted))
         (halt-with-notification)]
        [(RegisterTimeout) (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(RetransmitTimeout)
         ;; the other side has ACKed everything, so we can ignore the timer
         (goto TimeWait snd-nxt rcv-nxt receive-buffer octet-stream time-wait-timer)]
        [(TimeWaitTimeout)
         ;; (send status-updates (ConnectionClosed))
         (halt-with-notification)]))

    (define-state (Closed) (m)
      (case m
        [(InTcpPacket packet)
         (send-to-ip (make-rst/global packet))
         (goto Closed)]
        [(OrderedTcpPacket packet)
         (send-to-ip (make-rst/global packet))
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
         (halt-with-notification)]
        [(RegisterTimeout) (goto Closed)]
        ;; shouldn't happen here:
        [(RetransmitTimeout) (goto Closed)]
        [(TimeWaitTimeout) (goto Closed)])))

  ;;;; The main TCP actor

  (define-actor TcpInput
    (Tcp [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
         [wait-time-in-milliseconds Nat]
         [max-retries Nat]
         [max-segment-lifetime-in-ms Nat]
         [user-response-wait-time Nat])
    ()
    (goto Ready (hash) (hash))
    (define-state (Ready [session-table (Hash SessionId (Addr PacketInputMessage))]
                         [binding-table (Hash Nat (Addr PacketInputMessage))]) (m)
      (case m
        [(InPacket source-ip packet)
         (case (hash-ref session-table
                         (SessionId (InetSocketAddress source-ip (: packet source-port)) (: packet destination-port)))
           [(Just to-session)
             (send to-session (InTcpPacket packet))
             (goto Ready session-table binding-table)]
           [(Nothing)
            (cond
              [(packet-rst? packet)
               ;; just drop the packet
               (goto Ready session-table binding-table)]
              [(packet-ack? packet)
               (send packets-out (variant OutPacket source-ip (make-rst/global packet)))
               (goto Ready session-table binding-table)]
              [(packet-syn? packet)
               (case (hash-ref binding-table (: packet destination-port))
                 [(Just bind-handler)
                  (goto Ready session-table binding-table)
                  ;; TODO: put binding back in

                  ;; (let* ([session-id
                  ;;         (SessionId (InetSocketAddress source-ip (: packet source-port))
                  ;;                    (: packet destination-port))]
                  ;;        [session (spawn tcp-session
                  ;;                        TcpSession
                  ;;                        session-id
                  ;;                        (PassiveOpen (: packet seq))
                  ;;                        packets-out
                  ;;                        bind-handler
                  ;;                        self
                  ;;                        ;; REFACTOR: consider making these top-level constants
                  ;;                        wait-time-in-milliseconds
                  ;;                        max-retries
                  ;;                        max-segment-lifetime-in-ms
                  ;;                        user-response-wait-time)])
                  ;;    (goto Ready (hash-set session-table session-id session) binding-table))
                  ]
                 [(Nothing)
                   ;; RFC 793 on resets:
                   ;;
                   ;; In all states except SYN-SENT, all reset (RST) segments are validated by
                   ;; checking their SEQ-fields.  A reset is valid if its sequence number is in the
                   ;; window.  In the SYN-SENT state (a RST received in response to an initial SYN),
                   ;; the RST is acceptable if the ACK field acknowledges the SYN.
                   (send packets-out (variant OutPacket source-ip (make-rst/global packet)))
                   (goto Ready session-table binding-table)])]
              [else
               ;; don't send resets for non-ACK packets
               (goto Ready session-table binding-table)])])]
        [(UserCommand cmd)
         (case cmd
           [(Connect dest status-updates)
            (let* ([id (SessionId dest (get-new-port))]
                   [session-actor (spawn tcp-session
                                         TcpSession
                                         id
                                         (ActiveOpen)
                                         packets-out
                                         status-updates
                                         self
                                         wait-time-in-milliseconds
                                         max-retries
                                         max-segment-lifetime-in-ms
                                         user-response-wait-time)])
              (goto Ready (hash-set session-table id session-actor) binding-table))]
           [(Bind port bind-status-addr bind-handler)
             (send bind-status-addr (Bound))
             (goto Ready session-table (hash-set binding-table port bind-handler))])]
        [(SessionCloseNotification session-id)
         (goto Ready (hash-remove session-table session-id) binding-table)]))))))

(define tcp-program
  `(program (receptionists [tcp TcpInput]) (externals [packets-out TcpOutput])
            ,@tcp-definitions
            (actors [tcp (spawn 1 Tcp packets-out
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
            (ack-flag 0)
            (rst 0)
            (syn 1)
            (fin 0)
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
            (ack-flag 1)
            (rst 0)
            (syn 1)
            (fin 0)
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
            (ack-flag 1)
            (rst 0)
            (syn 0)
            (fin 0)
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
            (ack-flag 0)
            (rst 1)
            (syn 0)
            (fin 0)
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
            (ack-flag 1)
            (rst 0)
            (syn 0)
            (fin 1)
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
            (ack-flag 1)
            (rst 0)
            (syn 0)
            (fin 0)
            (window _)
            (payload the-payload))])))

  (define-match-expander OutPacket
    (lambda (stx)
      (syntax-parse stx
        [(_ ip-pattern packet-pattern)
         #`(quasiquote (variant OutPacket ,ip-pattern ,packet-pattern))])))

  (define desugared-program (desugar tcp-program))

  (define (start-prog)
    (define packets-out (make-async-channel))
    (values packets-out (csa-run desugared-program packets-out)))

  ;; Test data
  (define remote-ip 500) ; we're faking IPs with natural numbers, so the actual number doesn't matter
  (define server-port 80)
  (define client-port 55555)
  (define remote-iss 1024)

  (define (send-packet addr ip packet)
    (async-channel-put addr `(variant InPacket ,ip ,packet)))
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
     [ack-flag 0]
     [rst 1]
     [syn 0]
     [fin 0]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  (define (make-syn src-port dest-port seqno)
    (record
     [source-port src-port]
     [destination-port dest-port]
     [seq seqno]
     [ack 0]
     [ack-flag 0]
     [rst 0]
     [syn 1]
     [fin 0]
     [window DEFAULT-WINDOW-SIZE]
     [payload (vector)]))

  (define (make-syn-ack source-port dest-port seq ack)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack ack]
     [ack-flag 1]
     [rst 0]
     [syn 1]
     [fin 0]
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
     [ack-flag 1]
     [rst 0]
     [syn 0]
     [fin 0]
     [window DEFAULT-WINDOW-SIZE]
     [payload payload]))

  (define (make-fin source-port dest-port seq ack)
    (record
     [source-port source-port]
     [destination-port dest-port]
     [seq seq]
     [ack ack]
     [ack-flag 1]
     [rst 0]
     [syn 0]
     [fin 1]
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
    (Connect remote-addr response-dest)
    (Bind server-port bind-status-dest bind-handler)
    (CommandFailed)
    (Bound)
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
    (PeerClosed)
    (ErrorClosed))

  ;; Helpers to get to various states
  (define (connect connection-response)
    (define-values (packets-out tcp) (start-prog))
    (send-command tcp (Connect (InetSocketAddress remote-ip server-port) connection-response))
    (match-define (OutPacket _ (csa-record* (source-port local-port) (seq local-iss)))
      (async-channel-get packets-out))
    (send-packet tcp remote-ip (make-syn-ack server-port local-port remote-iss (add1 local-iss)))
    ;; eat the ACK
    (async-channel-get packets-out)
    (match (async-channel-get connection-response)
      [(csa-variant Connected _ session) (list packets-out tcp local-port local-iss session)]))

  (define (establish octet-handler)
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (send-session-command session (Register octet-handler))
    (list packets-out tcp local-port local-iss session))

  (define (check-closed? session)
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1) write-handler))
    (check-unicast write-handler (CommandFailed))))

(module+ test
  ;; Dynamic tests
  (test-case "Reset packet is dropped"
    (define-values (packets-out tcp) (start-prog))
    (send-packet tcp remote-ip (make-rst server-port client-port 10))
    (check-no-message packets-out))

  (test-case "Connect sends SYN, returns failure if timeout after SYN"
    (define-values (packets-out tcp) (start-prog))
    (define connection-response (make-async-channel))
    (send-command tcp (Connect (InetSocketAddress remote-ip server-port) connection-response))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-syn server-port)))
    (sleep (/ wait-time-in-milliseconds 1000))
    (check-unicast connection-response (CommandFailed)))

  (test-case "SYN/ACK to SYN makes session send ACK, notifies user"
    (define-values (packets-out tcp) (start-prog))
    (define connection-response (make-async-channel))
    (send-command tcp (Connect (InetSocketAddress remote-ip server-port) connection-response))
    (define syn (check-unicast-match packets-out
                                     (OutPacket (== remote-ip) (and syn (tcp-syn server-port)))
                                     #:result syn))
    (define local-port (: syn source-port))
    (define local-iss (: syn seq))
    (send-packet tcp remote-ip (make-syn-ack server-port local-port remote-iss (add1 local-iss)))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-ack local-port
                                             server-port
                                             (add1 local-iss)
                                             (add1 remote-iss))))
    (check-unicast-match connection-response (csa-variant Connected _ _)))

  (test-case "Proper handshake/upper layer notification on passive open"
    (define-values (packets-out tcp) (start-prog))
    (define bind-status-dest (make-async-channel))
    (define bind-handler (make-async-channel))
    (send-command tcp (Bind server-port bind-status-dest bind-handler))
    (check-unicast bind-status-dest (Bound))
    (send-packet tcp remote-ip (make-syn client-port server-port remote-iss))
    (define local-iss
      (check-unicast-match packets-out
        (OutPacket (== remote-ip) (tcp-syn-ack server-port client-port local-iss (add1 remote-iss)))
        #:result local-iss))
    (send-packet tcp remote-ip (make-normal-packet client-port
                                                   server-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector)))
    (check-unicast-match bind-handler (csa-variant Connected _ _)))

  (test-case "Proper handshake/upper layer notification on simultaneous open"
    ;; Overall sequence is:
    ;; 1. SYN ->
    ;; 2. SYN <-
    ;; 3. SYN/ACK ->
    ;; 4. ACK <-
    (define-values (packets-out tcp) (start-prog))
    (define status-updates (make-async-channel))
    (define remote-port client-port)
    (send-command tcp (Connect (InetSocketAddress remote-ip remote-port) status-updates))
    (match-define (list local-iss local-port)
      (check-unicast-match packets-out
                           (OutPacket (== remote-ip)
                                      (csa-record* [seq local-iss] [source-port remote-port]))
                           #:result (list local-iss remote-port)))
    (send-packet tcp remote-ip (make-syn remote-port local-port remote-iss))
    (check-unicast-match packets-out
      (OutPacket (== remote-ip) (tcp-syn-ack local-port remote-port local-iss (add1 remote-iss))))
    (send-packet tcp remote-ip (make-normal-packet remote-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector)))
    (check-unicast-match status-updates (csa-variant Connected _ _)))

  (test-case "Proper handshake/upper layer notification on simultaneous open with simultaneous SYN/ACK"
    ;; Overall sequence is:
    ;; 1. SYN ->
    ;; 2. SYN <-
    ;; 3. SYN/ACK ->
    ;; 3. SYN/ACK <-
    ;; 4. ACK ->
    (define-values (packets-out tcp) (start-prog))
    (define status-updates (make-async-channel))
    (define remote-port client-port)
    (send-command tcp (Connect (InetSocketAddress remote-ip remote-port) status-updates))
    (match-define (list local-iss local-port)
      (check-unicast-match packets-out
                           (OutPacket (== remote-ip)
                                      (csa-record* [seq local-iss] [source-port remote-port]))
                           #:result (list local-iss remote-port)))
    (send-packet tcp remote-ip (make-syn remote-port local-port remote-iss))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-syn-ack local-port remote-port _ (add1 remote-iss))))
    (send-packet tcp remote-ip (make-syn-ack remote-port local-port remote-iss (add1 local-iss)))
    (check-unicast-match packets-out
      (OutPacket (== remote-ip)
                 (tcp-ack local-port remote-port (+ local-iss 1) (+ remote-iss 1))))
    (check-unicast-match status-updates (csa-variant Connected _ _)))

  (test-case "Registered address receives the received octets"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (define octet-dest (make-async-channel))
    (send-session-command session (Register octet-dest))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-unicast octet-dest (ReceivedData (vector 1 2 3))))

  (test-case "Timeout before registration closes the session"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (sleep (/ (+ register-timeout timeout-fudge-factor) 1000))
    (check-unicast-match packets-out (OutPacket (== remote-ip)
                                                (tcp-rst local-port server-port (add1 local-iss))))
    (define octet-dest (make-async-channel))
    (send-session-command session (Register octet-dest))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-no-message octet-dest))

  (test-case "Octet stream receives data, and data is ACKed"
    (define octet-handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish octet-handler))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-unicast octet-handler (ReceivedData (vector 1 2 3)))
    (check-unicast-match packets-out (OutPacket (== remote-ip)
                                                (tcp-ack local-port
                                                         server-port
                                                         (add1 local-iss)
                                                         ;; add 1 for the SYN, 3 for the payload
                                                         (+ remote-iss 4)))))

  (test-case "Packet received while awaiting registration is sent to user after registration"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (define octet-dest (make-async-channel))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (sleep 1)
    (send-session-command session (Register octet-dest))
    (check-unicast octet-dest (ReceivedData (vector 1 2 3))))

  (test-case "Data received out-of-order is reordered"
    (define octet-handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish octet-handler))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (+ remote-iss 4)
                                                   (add1 local-iss)
                                                   (vector 4 5 6)))
    (send-packet tcp remote-ip (make-normal-packet server-port
                                                   local-port
                                                   (add1 remote-iss)
                                                   (add1 local-iss)
                                                   (vector 1 2 3)))
    (check-unicast octet-handler (ReceivedData (vector 1 2 3)))
    (check-unicast octet-handler (ReceivedData (vector 4 5 6))))

  (test-case "Can write data to other side; retransmit after no ACK for a while, then no retransmit after ACK"
    (match-define (list packets-out tcp local-port local-iss session) (establish (make-async-channel)))
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1 2 3) write-handler))
    (check-unicast write-handler (WriteAck))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) (vector 1 2 3))) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) (vector 1 2 3))) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (+ 4 local-iss) (vector)))
    (check-no-message packets-out #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000)))

  (test-case "Can write multiple segments when accepted data is longer than max segment size"
    (match-define (list packets-out tcp local-port local-iss session) (establish (make-async-channel)))
    (define write-handler (make-async-channel))
    (define data-to-write
      (vector 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223 224 225 226 227 228 229 230 231 232 233 234 235 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250 251 252 253 254 255 256 257 258 259 260 261 262 263 264 265 266 267 268 269 270 271 272 273 274 275 276 277 278 279 280 281 282 283 284 285 286 287 288 289 290 291 292 293 294 295 296 297 298 299 300 301 302 303 304 305 306 307 308 309 310 311 312 313 314 315 316 317 318 319 320 321 322 323 324 325 326 327 328 329 330 331 332 333 334 335 336 337 338 339 340 341 342 343 344 345 346 347 348 349 350 351 352 353 354 355 356 357 358 359 360 361 362 363 364 365 366 367 368 369 370 371 372 373 374 375 376 377 378 379 380 381 382 383 384 385 386 387 388 389 390 391 392 393 394 395 396 397 398 399 400 401 402 403 404 405 406 407 408 409 410 411 412 413 414 415 416 417 418 419 420 421 422 423 424 425 426 427 428 429 430 431 432 433 434 435 436 437 438 439 440 441 442 443 444 445 446 447 448 449 450 451 452 453 454 455 456 457 458 459 460 461 462 463 464 465 466 467 468 469 470 471 472 473 474 475 476 477 478 479 480 481 482 483 484 485 486 487 488 489 490 491 492 493 494 495 496 497 498 499 500 501 502 503 504 505 506 507 508 509 510 511 512 513 514 515 516 517 518 519 520 521 522 523 524 525 526 527 528 529 530 531 532 533 534 535 536))
    (send-session-command session (Write data-to-write write-handler))
    (check-unicast write-handler (WriteAck))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) _)) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) (vector 536))) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (+ 4 local-iss) (vector))))

  (test-case "Give up retransmit after 4 total attempts"
    (match-define (list packets-out tcp local-port local-iss session) (establish (make-async-channel)))
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1 2 3) write-handler))
    (check-unicast write-handler (WriteAck))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-no-message packets-out #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000)))

  (test-case "Close on receiving a FIN"
    ;; NOTE: we assume that the session should end after receiving a FIN (this is the default in Akka,
    ;; although they also allow the option of maintaining a half-open connection until the user
    ;; decides to close)
    ;;
    ;; NOTE: this case corresponds to line 255 of TcpConnection.scala in the Akka codebase
    (define octet-dest (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish octet-dest))
    (send-packet tcp remote-ip (make-fin server-port local-port (add1 remote-iss) (add1 local-iss)))
    (check-unicast octet-dest (PeerClosed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port server-port (add1 local-iss) (+ 2 remote-iss) (vector))))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (+ 2 remote-iss))))
    ;; ACK the FIN
    (send-packet tcp remote-ip (make-fin server-port local-port (add1 remote-iss) (+ 2 local-iss)))
    (check-closed? session))

  (test-case "ConfirmedClose, through the ACK-then-FIN route"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))

    ;; received packets *should* come through to the user (we're only half-closed)
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-unicast handler (ReceivedData (vector 1 2 3)))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 4 remote-iss)
                                                (vector))))
    ;; now the peer sends its ACK and FIN and closes
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (+ 4 remote-iss) (+ 2 local-iss) (vector)))
    (send-packet tcp remote-ip (make-fin server-port           local-port (+ 4 remote-iss) (+ 2 local-iss)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 5 remote-iss)
                                                (vector))))
    (check-closed? session))

  (test-case "ConfirmedClose, through the FIN-with-ACK route"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    (send-packet tcp remote-ip (make-fin server-port           local-port (add1 remote-iss) (+ 1 local-iss)))
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (+ 2 remote-iss) (+ 2 local-iss) (vector)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 2 remote-iss)
                                                (vector))))
    (check-closed? session))

  (test-case "ConfirmedClose, through the FIN then ACK route"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    (send-packet tcp remote-ip (make-fin server-port           local-port (add1 remote-iss) (+ 2 local-iss)))
    (check-unicast handler (ConfirmedClosed))
    (check-unicast close-handler (ConfirmedClosed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 2 remote-iss)
                                                (vector))))
    (check-closed? session))

  (test-case "Close, through the ACK then FIN route"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (Close close-handler))
    (check-unicast handler (Closed))
    (check-unicast close-handler (Closed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    ;; received packets should not come through to the user
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-no-message handler #:timeout 0.5)
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 4 remote-iss)
                                                (vector))))

    ;; peer ACKs the FIN
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (+ 4 remote-iss) (+ 2 local-iss) (vector)))
    ;; peer sends its FIN
    (send-packet tcp remote-ip (make-fin server-port local-port (+ 4 remote-iss) (+ 2 local-iss)))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 5 remote-iss)
                                                (vector))))
    (check-closed? session))

  (test-case "Abort from ESTABLISHED"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (Abort close-handler))
    (check-unicast handler (Aborted))
    (check-unicast close-handler (Aborted))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-rst local-port server-port (add1 local-iss))))
    (check-closed? session)
    ;; received packets should not come through to the user
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (add1 local-iss) (vector 1 2 3)))
    (check-no-message handler #:timeout 0.5))

  (test-case "Abort from AwaitingRegistration"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (define close-handler (make-async-channel))
    (send-session-command session (Abort close-handler))
    (check-unicast close-handler (Aborted))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-rst local-port server-port (add1 local-iss))))
    (check-closed? session))

  (test-case "ConfirmedClose from AwaitingRegistration"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (+ 1 remote-iss) (+ 2 local-iss) (vector)))
    (send-packet tcp remote-ip (make-fin server-port           local-port (+ 1 remote-iss) (+ 2 local-iss)))
    (check-unicast close-handler (ConfirmedClosed))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 2 remote-iss)
                                                (vector))))
    (check-closed? session))

  (test-case "Close from AwaitingRegistration"
    (match-define (list packets-out tcp local-port local-iss session) (connect (make-async-channel)))
    (define close-handler (make-async-channel))
    (send-session-command session (Close close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    (check-unicast close-handler (Closed))
    (check-closed? session)
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (+ 1 remote-iss) (+ 2 local-iss) (vector)))
    (send-packet tcp remote-ip (make-fin server-port           local-port (+ 1 remote-iss) (+ 2 local-iss)))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-normal local-port
                                                server-port
                                                (+ 2 local-iss)
                                                (+ 2 remote-iss)
                                                (vector)))))

  (test-case "Can abort while closing"
    (define handler (make-async-channel))
    (match-define (list packets-out tcp local-port local-iss session) (establish handler))
    (define close-handler (make-async-channel))
    (send-session-command session (ConfirmedClose close-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-fin local-port server-port (add1 local-iss) (add1 remote-iss))))
    (define abort-handler (make-async-channel))
    (send-session-command session (Abort abort-handler))
    (check-unicast-match packets-out
                         (OutPacket (== remote-ip)
                                    (tcp-rst local-port server-port (+ 2 local-iss))))
    (check-unicast abort-handler (Aborted))
    (check-unicast handler (Aborted))
    ;; the close handler gets NO message
    (check-no-message close-handler)
    (check-closed? session)))

;; Later: will probably need to add widening of state parameters to the widening code

;; Maybe things to test:
;; * receive RST in SynSent
;; * receive unacceptable ACK in SynSent
;; * in SynReceived, get ACK packet whose ACK is wrong (needs RST)

;; Conformance Tests
(module+ test
  (define desugared-tcp-packet-type
    `(Record
      [source-port Nat]
      [destination-port Nat]
      [seq Nat]
      [ack Nat]
      [ack-flag Nat]
      [rst Nat]
      [syn Nat]
      [fin Nat]
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

  (define desugared-connection-status
    `(Union
      [CommandFailed]
      [Connected ,desugared-session-id
                 (Addr ,desugared-session-command)]))

  (define desugared-user-command
    `(Union
      [Connect ,desugared-socket-address (Addr ,desugared-connection-status)]
      [Bind Nat
            (Addr (Union [Bound] [CommandFailed]))
            (Addr ,desugared-connection-status)]))

  (define desugared-tcp-input
    `(Union
      (InPacket Nat ,desugared-tcp-packet-type)
      (UserCommand ,desugared-user-command)
      (SessionCloseNotification ,desugared-session-id)))

  (define tcp-session-program
    `(program (receptionists [launcher (Addr ConnectionStatus)])
              (externals [session-packet-dest (Addr (Union (InTcpPacket TcpPacket)))]
                         [packets-out (Union [OutPacket IpAddress TcpPacket])]
                         [close-notifications (Union [SessionCloseNotification SessionId])])
              ,@tcp-definitions
              (define-actor Nat
                (Launcher [session-packet-dest (Addr (Addr (Union (InTcpPacket TcpPacket))))]
                          [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
                          [close-notifications (Addr (Union [SessionCloseNotification SessionId]))])
                ()
                (goto Init)
                (define-state (Init) (status-updates)
                  (let ([session (spawn session
                                        TcpSession
                                        (SessionId (InetSocketAddress 1234 50) 80)
                                        (ActiveOpen)
                                        packets-out
                                        status-updates
                                        close-notifications
                                        30000
                                        3
                                        30000
                                        10000)])
                    ;; this makes the packet side of the session observable
                    (send session-packet-dest session)
                    (goto Done)))
                (define-state (Done) (m) (goto Done)))
              (actors [launcher (spawn launcher
                                       Launcher
                                       session-packet-dest
                                       packets-out
                                       close-notifications)])))

  (define session-spec-behavior
    `((goto AwaitingRegistration)

      (define-state (AwaitingRegistration)
        [(variant Register app-handler) -> () (goto Connected app-handler)]
        [(variant Write * write-handler) ->
         ([obligation write-handler (variant CommandFailed)])
         (goto AwaitingRegistration)]
        [(variant Close close-handler) ->
         ([obligation close-handler (variant Closed)])
         (goto ClosedNoHandler)]
        ;; NOTE: this is a tricky spec. I want to say that eventually the session is guaranteed to
        ;; close, but the possibility of Abort means this close-handler might not get a response. Also
        ;; the blurring would make that hard to check even without the abort issue.
        [(variant ConfirmedClose close-handler) -> () (goto ClosingNoHandler close-handler)]
        [(variant Abort abort-handler) ->
         ([obligation abort-handler (variant Aborted)])
         (goto ClosedNoHandler)]
        ;; e.g. might close because of a registration timeout
        [unobs -> () (goto ClosedNoHandler)])

      (define-state (Connected app-handler)
        [(variant Register other-app-handler) -> () (goto Connected app-handler)]
        [(variant Write * write-handler) ->
         ;; NOTE: this would probably be WriteAck OR CommandFailed in a real implementation that has a
         ;; limit on its queue size
         ([obligation write-handler (variant WriteAck)])
         (goto Connected app-handler)]
        [(variant Close close-handler) ->
         ([obligation app-handler (variant Closed)]
          [obligation close-handler (variant Closed)])
         (goto Closed app-handler)]
        [(variant ConfirmedClose close-handler) -> () (goto Closing app-handler close-handler)]
        [(variant Abort abort-handler) ->
         ([obligation abort-handler (variant Aborted)]
          [obligation app-handler (variant Aborted)])
         (goto Closed app-handler)]
        ;; Possible unobserved events:
        [unobs -> ([obligation app-handler (variant ReceivedData *)]) (goto Connected app-handler)]
        [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)]
        [unobs -> ([obligation app-handler (variant PeerClosed)]) (goto Closed app-handler)])

      (define-state (Closing app-handler close-handler)
        [unobs ->
         ([obligation close-handler (variant ConfirmedClosed)]
          [obligation app-handler (variant ConfirmedClosed)])
         (goto Closed app-handler)]
        [(variant Register app-handler) -> () (goto Closing app-handler close-handler)]
        [(variant Write * write-handler) ->
         ([obligation write-handler (variant CommandFailed)])
         (goto Closing app-handler close-handler)]
        [(variant Close other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto Closing app-handler close-handler)]
        [(variant ConfirmedClose other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto Closing app-handler close-handler)]
        [(variant Abort abort-handler) ->
         ;; NOTE: no response at all on the ConfirmedClose handler: this is intentional (although
         ;; possibly not a good idea)
         ([obligation abort-handler (variant Aborted)]
          [obligation app-handler (variant Aborted)])
         (goto Closed app-handler)]
        [unobs ->
         ([obligation app-handler (variant ReceivedData *)])
         (goto Closing app-handler close-handler)]
        ;; NOTE: again, no response on close-handler. Again, intentional
        [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)])

      (define-state (ClosingNoHandler close-handler)
        [unobs -> ([obligation close-handler (variant ConfirmedClosed)]) (goto ClosedNoHandler)]
        [(variant Register app-handler) -> () (goto ClosingNoHandler close-handler)]
        [(variant Write * write-handler) ->
         ([obligation write-handler (variant CommandFailed)])
         (goto ClosingNoHandler close-handler)]
        [(variant Close other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto ClosingNoHandler close-handler)]
        [(variant ConfirmedClose other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto ClosingNoHandler close-handler)]
        [(variant Abort abort-handler) ->
         ([obligation abort-handler (variant Aborted)]) (goto ClosedNoHandler)]
        ;; NOTE: again, no response on close-handler. Again, intentional
        [unobs -> () (goto ClosedNoHandler)])

      (define-state (ClosedNoHandler)
        [(variant Register app-handler) -> () (goto ClosedNoHandler)]
        [(variant Write * write-handler) ->
         ([obligation write-handler (variant CommandFailed)])
         (goto ClosedNoHandler)]
        [(variant Close other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto ClosedNoHandler)]
        [(variant ConfirmedClose other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto ClosedNoHandler)]
        [(variant Abort abort-handler) ->
         ;; An abort during the close process could still succeed
         ([obligation abort-handler (or (variant Aborted) (variant CommandFailed))])
         (goto ClosedNoHandler)])

      (define-state (Closed app-handler)
        [(variant Register app-handler) -> () (goto Closed app-handler)]
        [(variant Write * write-handler) ->
         ([obligation write-handler (variant CommandFailed)])
         (goto Closed app-handler)]
        [(variant Close other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto Closed app-handler)]
        [(variant ConfirmedClose other-close-handler) ->
         ([obligation other-close-handler (variant CommandFailed)])
         (goto Closed app-handler)]
        [(variant Abort abort-handler) ->
         ;; An abort during the close process could still succeed
         ([obligation abort-handler (variant Aborted)]
          [obligation app-handler (variant Aborted)])
         (goto Closed app-handler)]
        ;; An abort during the close process could still succeed. Abort may or may not send on
        ;; app-handler, depending on which state it's in internally
        [(variant Abort abort-handler) ->
         ([obligation app-handler (variant CommandFailed)]
          [obligation abort-handler (variant CommandFailed)])
         (goto Closed app-handler)]
        [(variant Abort abort-handler) ->
         ([obligation abort-handler (variant CommandFailed)])
         (goto Closed app-handler)]
        ;; We might get some data while the other side is closing. Could probably split this into a
        ;; separate spec state, but I'm leaving it here for now
        [unobs -> ([obligation app-handler (variant ReceivedData *)]) (goto Closed app-handler)]
        [unobs -> ([obligation app-handler (variant ErrorClosed)]) (goto Closed app-handler)])))

  (define session-spec
    `(specification
      (receptionists [launcher (Addr ,desugared-connection-status)])
      (externals [session-packet-dest (Addr (Union [InTcpPacket ,desugared-tcp-packet-type]))]
                 [packets-out ,desugared-tcp-output]
                 [close-notifications (Union [SessionCloseNotification ,desugared-session-id])])
      [launcher (Addr ,desugared-connection-status)]
      ()
      (goto Init)
      (define-state (Init)
        [status-updates ->
         ([obligation status-updates (or (variant CommandFailed)
                                         (variant Connected * (fork ,@session-spec-behavior)))])
         (goto Done)])
      (define-state (Done)
        [* -> () (goto Done)])))

  ;; (test-true "Conformance for session"
  ;;   (check-conformance (desugar tcp-session-program) session-spec))

  (define manager-spec
    `(specification (receptionists [tcp ,desugared-tcp-input])
                    (externals [packets-out ,desugared-tcp-output])
       [tcp  (Union [UserCommand ,desugared-user-command])] ; obs interface
       ([tcp (Union [InPacket Nat ,desugared-tcp-packet-type])])  ; unobs interface
       (goto Managing)
       (define-state (Managing)
         [(variant UserCommand (variant Connect * status-updates)) ->
          ([obligation status-updates (or (variant CommandFailed)
                                          (variant Connected * (fork ,@session-spec-behavior)))])
          (goto Managing)]
         ;; TODO: add the real spec for Bind
         [(variant UserCommand (variant Bind * * *)) -> () (goto Managing)])))

  (test-true "User command type" (csa-valid-type? desugared-user-command))
  (test-true "Conformance for manager"
    (check-conformance desugared-program manager-spec)))
