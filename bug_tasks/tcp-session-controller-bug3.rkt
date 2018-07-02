#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp-session-controller.rkt")

(check-pair (make-tcp-program #f #f #t) session-wire-spec)
