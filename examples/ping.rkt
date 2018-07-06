#lang racket

(define ping-program
  (quasiquote
(program (receptionists [ping-server (Addr PongResponse)]) (externals)
  (define-variant PongResponse (Pong))
  (define-actor (Addr PongResponse) (PingServer)
    ()
    (goto Always)
    (define-state (Always) response-addr
      (send response-addr (Pong))
      (goto Always)))
  (let-actors ([ping-server (spawn 0 PingServer)]) ping-server))))

(define ping-spec
  (quasiquote
   (specification (receptionists [ping-server (Addr (Union [Pong]))]) (externals)
     (mon-receptionist ping-server)
     (goto Always)
     (define-state (Always)
       [r -> [obligation r *] (goto Always)]))))

(define no-send-ping-spec
  (quasiquote
   (specification (receptionists [ping-server (Addr (Union [Pong]))]) (externals)
     (mon-receptionist ping-server)
     (goto Always)
     (define-state (Always)
       [r -> (goto Always)]))))

(module+ test
  (require
   rackunit
   "../main.rkt"
   "../desugar.rkt")

  (define desugared-prog (desugar ping-program))
  (test-true "Ping server conformance check"
    (check-conformance desugared-prog ping-spec))
  (test-false "Ping server does not match no-send spec"
    (check-conformance desugared-prog no-send-ping-spec)))
