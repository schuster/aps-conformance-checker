#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp-session-controller.rkt")

(check-pair (make-tcp-program #t #f #f) session-wire-spec)
