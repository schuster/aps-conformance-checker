#lang racket

(require
 "../check-pair.rkt"
 "../examples/flink.rkt")

(check-pair (make-job-manager-program-tm-pov #f #t) job-manager-tm-pov-spec)
