#lang racket

(define ping-program
  (quasiquote
(program (receptionists [ping-server (Addr PongResponse)]) (externals)
  (define-variant PongResponse (Pong))
  (define-actor (Addr PongResponse) (PingServer)
    ()
    (goto Always)
    (define-state (Always) (response-addr)
      (send response-addr (Pong))
      (goto Always)))
  (actors [ping-server (spawn 0 PingServer)]))))

(define ping-spec
  (quasiquote
   (specification (receptionists [ping-server (Addr (Union [Pong]))]) (externals)
     [ping-server (Addr (Union [Pong]))]
     ()
     (define-state (Always)
       [r -> (with-outputs ([r *]) (goto Always))])
     (goto Always))))

(define no-send-ping-spec
  (quasiquote
   (specification (receptionists [ping-server (Addr (Union [Pong]))]) (externals)
     [ping-server (Addr (Union [Pong]))]
     ()
     (define-state (Always)
       [r -> (goto Always)])
     (goto Always))))

(module+ test
  (require
   rackunit
   "main.rkt"
   "desugar.rkt")

  (define desugared-prog (desugar ping-program))
  (test-true "Ping server conformance check"
    (model-check/static desugared-prog ping-spec))
  (test-false "Ping server does not match no-send spec"
    (model-check/static desugared-prog no-send-ping-spec)))
