#lang racket

(require
 "../check-pair.rkt"
 "../examples/spray-can.rkt")

(check-pair (make-manager-program #t #f) http-manager-spec)
