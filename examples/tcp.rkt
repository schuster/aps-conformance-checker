#lang racket

;; An implementation of TCP with an Akka-style application-layer interface
;; (http://doc.akka.io/docs/akka/current/scala/io-tcp.html)

(define DEFAULT-WINDOW-SIZE 29200)
(define wait-time-in-milliseconds 1000)
(define max-retries 3)
;; NOTE: real MSL value is 2 minutes
(define max-segment-lifetime (* 1000 2)) ; defined in milliseconds
(define user-response-wait-time 3000)

(define tcp-program
  (quasiquote
(program (receptionists [tcp TcpInput]) (externals [packets-out OutPacket])

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

  (define-variant ConnectionStatus
    ;; TODO: add these as necessary
    ;; (ConnectionTimedOut)
    ;; (ConnectionReset)
    ;; (ConnectionEstablished [octets-to-session (Channel (Vectorof Byte))] [close-request (Channel)])
    ;; (ConnectionClosing)
    ;; (ConnectionClosed)
    )

  (define-variant UserCommand
    (Connect [remote-address InetSocketAddress]
             [status-updates (Addr ConnectionStatus)])
    ;; TODO: add bind
    ;; (Bind [port integer] [new-connections (Channel (Channel ConnectionResponse))])
    )

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
    (ActiveOpen [status-updates (Addr ConnectionStatus)])
    ;; TODO: design the passive open interface
    ;; (PassiveOpen [remote-seq Nat] [new-connections (Addr (Addr ConnectionResponse))])
    )

  (define-type TcpSessionInput
    (Union
     ;; TODO: add these as needed
     ;; [connection-response ConnectionResponse]
     ;; [retransmission-timer Unit]
     ;; [packets-in TcpPacket]
     ;; [ordered-packets TcpPacket] ; NOTE: this one should not be exposed outside this actor
     ;; [octets-to-send (Vectorof Byte)]
     ;; [close-request]
     ;; [time-wait-timer Unit]
     ))

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

  ;; (define-function (make-syn-ack [seq integer] [ack integer])
  ;;   (TcpPacket (: id local-port) (: id remote-port) seq ack 1 0 1 0 DEFAULT-WINDOW-SIZE (vector)))

  ;; (define-function (make-rst [seq integer])
  ;;   (TcpPacket (: id local-port) (: id remote-port) seq 0 0 1 0 0 DEFAULT-WINDOW-SIZE (vector)))

  ;; (define-function (make-fin [seq integer] [ack integer])
  ;;   (TcpPacket (: id local-port) (: id remote-port) seq ack 1 0 0 1 DEFAULT-WINDOW-SIZE (vector)))

  ;; (define-function (make-normal-packet [seq integer] [ack integer] [payload (Vectorof Byte)])
  ;;   (TcpPacket (: id local-port) (: id remote-port) seq ack 1 0 0 0 DEFAULT-WINDOW-SIZE payload))
     )

    ;; initialization
    (let ([iss (get-iss)])
      (case open
        [(ActiveOpen status-updates)
         (send-to-ip (make-syn iss))
         (goto SynSent (+ iss 1) status-updates)]
        ;; TODO: implement the passive open logic
        ;; [PassiveOpen (remote-iss new-connections-channel)
        ;;   (send new-connections-channel connection-response)
        ;;   (next-state (WaitForUserResponse (+ 1 remote-iss)))]
        )

      )

    (define-state (SynSent [snd-nxt Nat] [status-updates (Addr ConnectionStatus)]) (m)
      ;; TODO: implement this state
      (goto SynSent snd-nxt status-updates)
    ;; [packets-in (packet)
    ;;   (cond
    ;;    [(= (: packet ack-flag) 1)
    ;;     (cond
    ;;      [(= (: packet ack) snd-nxt) ; this is the only acceptable ACK
    ;;       (cond
    ;;        [(= (: packet rst) 1)
    ;;         (send connection-status (ConnectionReset))
    ;;         (halt-with-notification)]
    ;;        [(= (: packet syn) 1)
    ;;         ;; this is the typical SYN/ACK case (step 2 of the 3-way handshake)
    ;;         (define rcv-nxt (compute-receive-next packet))
    ;;         (send-to-ip (make-normal-packet snd-nxt rcv-nxt (vector)))
    ;;         (send status-updates (ConnectionEstablished octets-to-send close-request))
    ;;         (next-state (Established (SendBuffer 0 snd-nxt (: packet window) snd-nxt (vector))
    ;;                                  rcv-nxt
    ;;                                  (create-empty-buffer)
    ;;                                  status-updates
    ;;                                  octet-stream
    ;;                                  (create-timer (void) retransmission-timer)))]
    ;;        [else ;; ACK acceptable but no other interesting fields set. Probably won't happen in
    ;;              ;; reality.
    ;;         (next-state (SynSent snd-nxt status-updates octet-stream))])]
    ;;      [else ;; ACK present but not acceptable
    ;;       (send-to-ip (make-rst (: packet ack)))
    ;;       (send connection-status (ConnectionReset))
    ;;       (halt-with-notification)])]
    ;;    [else ;; no ACK present
    ;;     (cond
    ;;      [(= (: packet rst) 1)
    ;;       ;; drop the packet, because the RST probably comes from a previous instance of the session
    ;;       (next-state (SynSent snd-nxt status-updates octet-stream))]
    ;;      [(= (: packet syn) 1)
    ;;       ;; we got a SYN but no ACK: this is the simultaneous open case
    ;;       (define iss (- snd-nxt 1))
    ;;       (define rcv-nxt (+ (: packet seq) 1))
    ;;       (send-to-ip (make-syn-ack iss rcv-nxt))
    ;;       (next-state
    ;;        (SynReceived (+ iss 1) rcv-nxt (create-empty-buffer) status-updates octet-stream))]
    ;;      [else
    ;;       ;; not an important segment, so just drop it. Probably won't happen in reality
    ;;       (next-state (SynSent snd-nxt status-updates octet-stream))])])]
    ;; [after wait-time-in-milliseconds
    ;;   (send connection-status (ConnectionTimedOut))
    ;;   (halt-with-notification)]
      )

  ;; TODO: the rest of the states

  )


  (define-actor TcpInput
    (Tcp [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
         [wait-time-in-milliseconds Nat]
         [max-retries Nat]
         [max-segment-lifetime-in-ms Nat]
         [user-response-wait-time Nat])
    ()
    (goto Ready (hash) (hash))
    (define-state (Ready [session-table (Hash SessionId (Addr PacketInputMessage))]
                         [binding-table (Hash integer (Addr PacketInputMessage))]) (m)
      (case m
        [(InPacket source-ip packet)
         (goto Ready session-table binding-table)
         
         ;; TODO: implement this

         ;; (case (hash-ref session-table
         ;;                 (SessionId source-ip (: packet destination-port) (: packet source-port)))
         ;;   [Just (to-session)
         ;;         (send to-session packet)
         ;;         (next-state (Ready session-table binding-table))]
         ;;   [Nothing ()
         ;;            (cond
         ;;              [(= (: packet rst) 1)
         ;;               ;; just drop the packet
         ;;               (next-state (Ready session-table binding-table))]
         ;;              [(= (: packet ack-flag) 1)
         ;;               ;; NOTE: we should normally send a RST here, but since this code is used for demos on a
         ;;               ;; normal desktop machine, we just drop packets that might be headed for other processes
         ;;               ;; on the current host
         ;;               (next-state (Ready session-table binding-table))]
         ;;              [(= (: packet syn) 1)
         ;;               (case (hash-ref binding-table (: packet destination-port))
         ;;                 [Just (connection-channel)
         ;;                       (define session-id
         ;;                         (SessionId source-ip (: packet destination-port) (: packet source-port)))
         ;;                       (let-agent (_ _ session-packets-in _ _ _ _)
         ;;                         ((TcpSession session-id
         ;;                                      (PassiveOpen (: packet seq) connection-channel)
         ;;                                      wait-time-in-milliseconds
         ;;                                      max-retries
         ;;                                      max-segment-lifetime-in-ms
         ;;                                      user-response-wait-time)
         ;;                          [packets-out packets-out]
         ;;                          [connection-status connection-channel]
         ;;                          [close-notifications session-close-notifications])
         ;;                         (next-state (Ready (hash-set session-table session-id session-packets-in)
         ;;                                            binding-table)))]
         ;;                 [Nothing ()
         ;;                          ;; RFC 793 on resets:
         ;;                          ;;
         ;;                          ;; In all states except SYN-SENT, all reset (RST) segments are validated by checking
         ;;                          ;; their SEQ-fields.  A reset is valid if its sequence number is in the window.  In
         ;;                          ;; the SYN-SENT state (a RST received in response to an initial SYN), the RST is
         ;;                          ;; acceptable if the ACK field acknowledges the SYN.
         ;;                          (send packets-out
         ;;                                source-ip
         ;;                                TCP-PROTOCOL-NUMBER
         ;;                                (TcpPacket (: packet destination-port)
         ;;                                           (: packet source-port)
         ;;                                           0
         ;;                                           (: packet seq)
         ;;                                           1 1 0 0
         ;;                                           DEFAULT-WINDOW-SIZE
         ;;                                           (vector)))
         ;;                          (next-state (Ready session-table binding-table))])]

         ;;              [else
         ;;               ;; don't send resets for non-ACK packets
         ;;               (next-state (Ready session-table binding-table))])])
         ]
        [(UserCommand cmd)
         (case cmd
           [(Connect dest status-updates)
            (let* ([id (SessionId dest (get-new-port))]
                   [session-actor (spawn active-session
                                         TcpSession
                                         id
                                         (ActiveOpen status-updates)
                                         packets-out
                                         status-updates
                                         self
                                         wait-time-in-milliseconds
                                         max-retries
                                         max-segment-lifetime-in-ms
                                         user-response-wait-time)])
              (goto Ready (hash-set session-table id session-actor) binding-table))]
           ;; TODO: do the bind case
           ;; [Bind (port connection-channel)
           ;;       (next-state (Ready session-table (hash-set binding-table port connection-channel)))]
           )]
        ;; TODO: do session-close notifications
        ;; [session-close-notifications (session-id)
        ;;                              (next-state (Ready (hash-remove session-table session-id) binding-table))]
        )))

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
   (only-in csa record variant)
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

  (define (send-packet addr ip packet)
    (async-channel-put addr `(variant InPacket ,ip ,packet)))
  (define (send-command addr cmd)
    (async-channel-put addr `(variant UserCommand ,cmd)))

  (define (make-rst source-port dest-port seq)
    `([source-port ,source-port]
      [destination-port ,dest-port]
      [seq ,seq]
      [ack 0]
      [ack-flag NoAck]
      [rst Rst]
      [syn NoSyn]
      [fin NoFin]
      [window DEFAULT-WINDOW-SIZE]
      [payload (vector)]))

  (define (InetSocketAddress ip port)
    (record [ip ip] [port port]))
  (define (Connect remote-addr response-dest)
    (variant Connect remote-addr response-dest))
  (define (ConnectionTimedOut)
    (variant ConnectionTimedOut))

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
    (check-unicast connection-response (ConnectionTimedOut))))
