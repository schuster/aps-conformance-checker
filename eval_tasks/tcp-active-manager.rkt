#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp.rkt")

(check-pair active-tcp-program active-manager-spec)
