#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp.rkt")

(check-pair (make-tcp-program #f #t #f) passive-manager-spec)