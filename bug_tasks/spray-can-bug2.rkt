#lang racket

(require
 "../check-pair.rkt"
 "../examples/spray-can.rkt")

(check-pair (make-manager-program #f #t) http-manager-spec)
