#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp.rkt")

(check-pair (make-tcp-program #t #f #t) active-manager-spec)