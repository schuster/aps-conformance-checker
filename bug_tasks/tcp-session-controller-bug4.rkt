#lang racket

(require
 "../check-pair.rkt"
 "../examples/tcp-session-controller.rkt")

(check-pair tcp-program (make-session-wire-spec #t))
