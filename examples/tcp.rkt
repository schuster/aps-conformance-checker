#lang racket

;; An implementation of TCP with an Akka-style application-layer interface
;; (http://doc.akka.io/docs/akka/current/scala/io-tcp.html)

(define DEFAULT-WINDOW-SIZE 29200)
(define MAXIMUM-SEGMENT-SIZE-IN-BYTES 536)
(define wait-time-in-milliseconds 1000)
(define max-retries 3)
;; NOTE: real MSL value is 2 minutes
(define max-segment-lifetime (* 1000 2)) ; defined in milliseconds
(define user-response-wait-time 3000)
(define register-timeout 5000) ; in milliseconds (5 seconds is the Akka default)
(define timeout-fudge-factor 500) ; in milliseconds

(define tcp-program
  (quasiquote
(program (receptionists [tcp TcpInput]) (externals [packets-out TcpOutput])

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

  (define-record SendBuffer
    [retransmit-count Nat]
    [unacked-seq Nat]
    [window Nat] ; window size in octets
    [send-next Nat]
    [buffer (Vectorof Byte)])

  ;; Returns the total number of octets to send stored in the buffer
  (define-function (send-buffer-length [s SendBuffer])
    (vector-length (: s buffer)))

  ;; Returns true if the send buffer contains no more bytes to send
  (define-function (send-buffer-empty? [s SendBuffer])
    (= 0 (send-buffer-length s)))

  (define-function (increment-retransmit-count [s SendBuffer])
    (SendBuffer (+ (: s retransmit-count) 1)
                (: s unacked-seq)
                (: s window)
                (: s send-next)
                (: s buffer)))

  ;; Adds the given octets to the send buffer and updates the send-next pointer
  (define-function (send-buffer-add-octets [s SendBuffer]
                                           [data (Vectorof Byte)]
                                           [send-next Nat])
    (SendBuffer (: s retransmit-count)
                (: s unacked-seq)
                (: s window)
                send-next
                (vector-append (: s buffer) data)))

  (define-function (send-buffer-add-fin [s SendBuffer])
    (SendBuffer (: s retransmit-count)
                (: s unacked-seq)
                (: s window)
                (+ (: s send-next) 1)
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
     ;; TODO: add the other timeouts here
     ))

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

  (define-type WriteResponse
    (Union (CommandFailed) ; CommandFailed defined below
           (WriteAck)))
  (define-function (WriteAck) (variant WriteAck))

  (define-type TcpSessionCommand
    (Union
     (Register (Addr (Vectorof Byte)))
     (Write (Vectorof Byte) (Addr WriteResponse))
     ;; TODO: should have Close, ConfirmedClose, Abort
     ))

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

  (define-variant TcpSessionInput
    (InTcpPacket [packet TcpPacket])
    ;; a "private" variant, used only internally for an ordered queue of packets. We assume that they
    ;; are in order since the messages are sent to and from the same actor. The semantics doesn't
    ;; technically guarantee this, but any real implementation would order them.
    (OrderedTcpPacket [packet TcpPacket])
    (Register [handler (Addr (Vectorof Byte))])
    (Write [data (Vectorof Byte)] [handler (Addr WriteResponse)])
    ;; timeouts
    (RegisterTimeout)
    (RetransmitTimeout)
    ;; TODO: add the various closes

    ;; TODO: add the various timeouts
    )

  ;;; The TCP session actor

  (define-actor TcpSessionInput
    (TcpSession [id SessionId]
                [open Open]
                [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
                [status-updates (Addr ConnectionStatus)]
                [close-notifications (Addr (Union [SessionCloseNotification SessionId]))]
                [wait-time-in-milliseconds Nat]
                [max-retries Nat]
                [max-segment-lifetime-in-ms Nat]
                [user-response-wait-time Nat])
    ((define-function (send-to-ip [packet TcpPacket])
       (send packets-out (variant OutPacket (: (: id remote-address) ip) packet)))

     (define-function (halt-with-notification)
       (send close-notifications (SessionCloseNotification id))
       (goto Halt))

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

     ;; (define-function (make-fin [seq Nat] [ack Nat])
     ;;   (TcpPacket (: id local-port) (: id remote-port) seq ack 1 0 0 1 DEFAULT-WINDOW-SIZE (vector)))

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
          (+ (case (: packet syn) [(Syn) 1] [(NoSyn) 0])
             (+ (case (: packet fin) [(Fin) 1] [(NoFin) 0])
                (vector-length (: packet payload))))))

     (define-function (finish-connecting [snd-nxt Nat] [rcv-nxt Nat] [window Nat])
       (send status-updates (Connected id self))
       (let ([reg-timer (spawn reg-timer Timer (RegisterTimeout) self)])
         (send reg-timer (Start ,register-timeout))
         (goto AwaitingRegistration
               (SendBuffer 0 snd-nxt window snd-nxt (vector))
               (vector)
               rcv-nxt
               (create-empty-rbuffer)
               reg-timer)))

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
                     (vector-copy (: send-buffer buffer)
                                  (- new-snd-una (: send-buffer unacked-seq))
                                  (vector-length (: send-buffer buffer))))))

     ;; Does the necessary handling for segment text on the next in-order packet, returning the new
     ;; receive-next
     (define-function (process-segment-text [segment TcpPacket]
                                            [send-next Nat]
                                            [rcv-nxt Nat]
                                            [octet-stream (Addr (Vectorof Byte))])
       (let ([unseen-payload (vector-copy (: segment payload)
                                          (- rcv-nxt (: segment seq))
                                          (vector-length (: segment payload)))]
             [new-rcv-nxt (compute-receive-next segment)])
         (cond
           [(> (vector-length unseen-payload) 0)
            (send-to-ip (make-normal-packet send-next new-rcv-nxt (vector)))
            (send octet-stream (: segment payload))
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
                (vector-append previous-segments new-segment))]))))

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

     ;; Either retransmits the oldest unacked segment, or fails because it reached the retry limit
     ;; (returns RetransmitSuccess or RetransmitFailure)
     (define-function (maybe-retransmit [send-buffer SendBuffer]
                                        [rcv-nxt Nat]
                                        [timer Timer])
       (cond
         [(= (: send-buffer retransmit-count) max-retries)
          (RetransmitFailure)]
         [(not (send-buffer-empty? send-buffer))
          (let ([segment-length
                 (min (send-buffer-length send-buffer) ,MAXIMUM-SEGMENT-SIZE-IN-BYTES)])
            (send-to-ip (make-normal-packet (: send-buffer unacked-seq)
                                            rcv-nxt
                                            (vector-take (: send-buffer buffer) segment-length)))
            (send timer (Start wait-time-in-milliseconds))
            (RetransmitSuccess))]
         [else (RetransmitSuccess)]))

     (define-function (abort-connection [snd-nxt Nat])
       (send-to-ip (make-rst snd-nxt))))

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
        [(RegisterTimeout) (goto SynSent snd-nxt)]
        [(RetransmitTimeout) (goto SynSent snd-nxt)])

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
        [(RegisterTimeout) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]
        [(RetransmitTimeout) (goto SynReceived snd-nxt rcv-nxt receive-buffer)]))

    ;; We're waiting for the user to register an actor to send received octets to
    (define-state (AwaitingRegistration [send-buffer SendBuffer]
                                        [queued-packets (Vectorof TcpPacket)]
                                        [rcv-nxt Nat]
                                        [receive-buffer ReceiveBuffer]
                                        [registration-timer (Addr TimerCommand)]) (m)
      (case m
        [(InTcpPacket packet)
         ;; we don't need the handler just to process incoming packets, so we do it just like in Established
         (let ([new-receive-buffer (process-incoming packet rcv-nxt receive-buffer (: send-buffer send-next))])
           (goto AwaitingRegistration send-buffer queued-packets rcv-nxt new-receive-buffer registration-timer))]
        [(OrderedTcpPacket packet)
         (goto AwaitingRegistration
               send-buffer
               (vector-append queued-packets (vector packet))
               rcv-nxt
               receive-buffer
               registration-timer)]
        [(Register octet-handler)
         (send registration-timer (Stop))
         (for/fold ([dummy 0])
                   ([packet queued-packets])
           (send self (OrderedTcpPacket packet))
           0)
         (goto Established
               send-buffer
               rcv-nxt
               receive-buffer
               octet-handler
               (spawn rxmt-timer Timer (RetransmitTimeout) self))]
        [(Write data handler)
         ;; can't yet write
         (send handler (CommandFailed))
         (goto AwaitingRegistration send-buffer queued-packets rcv-nxt receive-buffer registration-timer)]
        [(RegisterTimeout)
         (abort-connection (: send-buffer send-next))
         (halt-with-notification)]
        ;; retransmit timeout shouldn't happen here
        [(RetransmitTimeout)
         (goto AwaitingRegistration send-buffer queued-packets rcv-nxt receive-buffer registration-timer)]))

    ;; REFACTOR: move these various receive-related params into the receive buffer
    (define-state (Established [send-buffer SendBuffer]
                               [rcv-nxt Nat]
                               [receive-buffer ReceiveBuffer]
                               [octet-stream (Addr (Vectorof Byte))]
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
            ;; TODO: figure out what message to send to close the connection
            ; (send status-updates (ConnectionReset))
            (halt-with-notification)]
           [else
            (let ([new-send-buffer
                   (process-ack send-buffer (: packet ack) (: packet window) rxmt-timer)]
                  [new-rcv-nxt
                   (process-segment-text packet (: send-buffer send-next) rcv-nxt octet-stream)])
              ;; NOTE: we could optimize here by going into fast recovery mode if this is the 3rd
              ;; duplicate ACK

              ;; Finally, check for the FIN bit
              (cond
                [(packet-fin? packet)
                 ;; TODO: figure out what notification to send here
                 ;; from original: (send status-updates (ConnectionClosing))
                 (send-to-ip (make-normal-packet (: send-buffer send-next) new-rcv-nxt (vector)))
                 (goto Closing
                              ;; TODO: use these parameters:
                              ;; send-buffer
                                      ;; new-rcv-nxt
                                      ;; receive-buffer
                                      ;; (ReceivedFin)
                                      ;; status-updates
                                      ;; octet-stream
                                      ;; timer
                                      )]
                [else (goto Established
                            new-send-buffer
                            new-rcv-nxt
                            receive-buffer
                            octet-stream
                            rxmt-timer)]))])]
         ;; ignore registrations and registration timeouts here
        [(Reigster h)
         (goto Established send-buffer rcv-nxt receive-buffer octet-stream rxmt-timer)]
        [(RegisterTimeout)
         (goto Established send-buffer rcv-nxt receive-buffer octet-stream rxmt-timer)]
        [(Write data handler)
         (send handler (WriteAck))
         (goto Established
               (accept-new-octets data send-buffer rcv-nxt rxmt-timer)
               rcv-nxt
               receive-buffer
               octet-stream
               rxmt-timer)]
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
            ;; TODO: do I need to send a message to the user here?
            (halt-with-notification)])]))

    (define-state (Closing) (m)
      ;; TODO: define this state
      (goto Closing)
      )

    ;; TODO: the rest of the states

    (define-state (Halt) (m)
      (case m
        [(Write data handler)
         ;; can't write anymore
         (send handler (CommandFailed))
         (goto Halt)]
        [(Register h) (goto Halt)]
        [(RegisterTimeout) (goto Halt)]
        [(InTcpPacket packet) (goto Halt)
         ;; TODO: should I send a reset?
         ]
        ;; TODO: handle other cases
        )))

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
                  (let* ([session-id
                          (SessionId (InetSocketAddress source-ip (: packet source-port))
                                     (: packet destination-port))]
                         [session (spawn passive-open
                                         TcpSession
                                         session-id
                                         (PassiveOpen (: packet seq))
                                         packets-out
                                         bind-handler
                                         self
                                         ;; TODO: consider making these top-level constants
                                         wait-time-in-milliseconds
                                         max-retries
                                         max-segment-lifetime-in-ms
                                         user-response-wait-time)])
                     (goto Ready (hash-set session-table session-id session) binding-table))]
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
                   [session-actor (spawn active-session
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
         (goto Ready (hash-remove session-table session-id) binding-table)])))

  (actors [tcp (spawn 1 Tcp packets-out
                            ,wait-time-in-milliseconds
                            ,max-retries
                            ,max-segment-lifetime
                            ,user-response-wait-time)]))))

;; ---------------------------------------------------------------------------------------------------
;; The tests

(module+ test
  (require
   asyncunit
   (only-in csa record variant :)
   csa/eval
   csa/testing
   racket/async-channel
   rackunit
   (for-syntax syntax/parse)
   "../desugar.rkt")

  (define-match-expander tcp-syn
    (lambda (stx)
      (syntax-parse stx
        [(_ dest-port)
         #`(csa-record
            (source-port _)
            (destination-port (== dest-port))
            (seq _)
            (ack _)
            ;; TODO: note bug: had a NoSyn here the first time instead of NoAck
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

  (define (InetSocketAddress ip port)
    (record [ip ip] [port port]))
  (define (Connect remote-addr response-dest)
    (variant Connect remote-addr response-dest))
  (define (Bind server-port bind-status-dest bind-handler)
      (variant Bind server-port bind-status-dest bind-handler))
  (define (CommandFailed)
    (variant CommandFailed))
  (define (Bound)
    (variant Bound))
  (define (Register handler)
    (variant Register handler))
  (define (Write data handler)
    (variant Write data handler))
  (define (WriteAck)
    (variant WriteAck))

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

  ;; The tests themselves
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
    (check-unicast-match octet-dest (vector 1 2 3)))

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
    (check-unicast octet-handler (vector 1 2 3))
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
    (check-unicast-match octet-dest (vector 1 2 3)))

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
    (check-unicast octet-handler (vector 1 2 3))
    (check-unicast octet-handler (vector 4 5 6)))

  (test-case "Can write data to other side; retransmit after no ACK for a while, then no retransmit after ACK"
    (match-define (list packets-out tcp local-port local-iss session) (establish (make-async-channel)))
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1 2 3) write-handler))
    (check-unicast write-handler (WriteAck))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) (vector 1 2 3))) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out (OutPacket (== remote-ip) (tcp-normal local-port server-port  (add1 local-iss) (add1 remote-iss) (vector 1 2 3))) #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (send-packet tcp remote-ip (make-normal-packet server-port local-port (add1 remote-iss) (+ 4 local-iss) (vector)))
    (check-no-message packets-out #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000)))

  (test-case "Give up retransmit after 4 total attempts"
    (match-define (list packets-out tcp local-port local-iss session) (establish (make-async-channel)))
    (define write-handler (make-async-channel))
    (send-session-command session (Write (vector 1 2 3) write-handler))
    (check-unicast write-handler (WriteAck))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-unicast-match packets-out _ #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))
    (check-no-message packets-out #:timeout (/ (+ wait-time-in-milliseconds timeout-fudge-factor) 1000))))

;; Todo list of tests/functionality:
;; * Don't acknowledge empty packet (e.g. simple ACK)
;; * receive FIN
;; * active ConfirmedClose, through closing
;; * active ConfirmedClose, through fin wait 2
;; * active ConfirmedClose, directly from fin wait 1 to time wait
;; * active Close, to any state
;; * abort (from Established)
;; * remaining TODOs, as I deem necessary
;; * check that all messages are handled in all states

;; Later: will probably need to add widening of state parameters to the widening code

;; Maybe things to test:
;; * receive RST in SynSent
;; * receive unacceptable ACK in SynSent
;; * in SynReceived, get ACK packet whose ACK is wrong (needs RST)


;; Conformance Tests
(module+ test
  (require
   "../csa.rkt" ; for csa-valid-type?
   "../main.rkt")

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

  (define desugared-session-command
    `(Union
      (Register (Addr (Vectorof Nat)))
      (Write (Vectorof Nat)
             (Addr (Union (CommandFailed)
                          (WriteAck))))))

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

  (define trivial-spec
    ;; TODO: maybe fix the types on receptionists and externals, although I don't think it really
    ;; matters
    `(specification (receptionists [tcp (Union)])
                    (externals [packets-out ,desugared-tcp-output])
       [tcp  (Union [UserCommand ,desugared-user-command])] ; obs interface
       ([tcp (Union [InPacket Nat ,desugared-tcp-packet-type])])  ; unobs interface
       (goto DoNothing)
       (define-state (DoNothing) [* -> () (goto DoNothing)])))

  (test-true "User command type" (csa-valid-type? desugared-user-command))

  (check-conformance desugared-program trivial-spec))
