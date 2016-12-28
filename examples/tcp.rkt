#lang racket

;; An implementation of TCP with an Akka-style application-layer interface
;; (http://doc.akka.io/docs/akka/current/scala/io-tcp.html)

(define wait-time-in-milliseconds 1000)
(define max-retries 3)
;; NOTE: real MSL value is 2 minutes
(define max-segment-lifetime (* 1000 2)) ; defined in milliseconds
(define user-response-wait-time 3000)

(define tcp-program
  (quasiquote
(program (receptionists [tcp TcpInput]) (externals [packets-out OutPacket])

  (define-type IpAddress Nat) ; fake IP addresses with Nats

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

  (define-variant TcpInput
    (InPacket [src IpAddress] [packet TcpPacket]))

  (define-variant TcpOutput
    (OutPacket [dest IpAddress] [packet TcpPacket]))

  (define-actor TcpInput
    (Tcp [packets-out (Addr (Union [OutPacket IpAddress TcpPacket]))]
         [wait-time-in-milliseconds Nat]
         [max-retries Nat]
         [max-segment-lifetime-in-ms Nat]
         [user-response-wait-time Nat])
    ()
    (goto Init)
    (define-state (Init) (m) (goto Init)))

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
   csa/eval
   racket/async-channel
   rackunit
   "../desugar.rkt")

  (define desugared-program (desugar tcp-program))

  (define (start-prog)
    (define packets-out (make-async-channel))
    (values packets-out (csa-run desugared-program packets-out)))

  ;; Test data
  (define remote-ip 500) ; we're faking IPs with natural numbers, so the actual number doesn't matter
  (define server-port 80)
  (define client-port 55555)
  (define DEFAULT-WINDOW-SIZE 29200)

  (define (send-packet addr ip packet)
    (async-channel-put addr `(variant InPacket ,ip ,packet)))

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

  ;; The tests themselves
  (test-case "Reset packet is dropped"
    (define-values (packets-out tcp) (start-prog))
    (send-packet tcp remote-ip (make-rst server-port client-port 10))
    (check-no-message packets-out)))



  ;; (test-case "Bind gets a Bound result with listener address"
  ;;   (define tcp (csa-run desugared-program))
  ;;   (async-channel-put tcp )
  ;;   ))
