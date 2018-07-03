#lang racket

(require
 "../check-pair.rkt"
 "../examples/flink.rkt")

(check-pair (make-task-manager-program #t #f) task-manager-spec)
