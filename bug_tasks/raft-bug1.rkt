#lang racket

(require
 "../check-pair.rkt"
 "../examples/raft.rkt")

(check-pair raft-actor-prog (make-raft-spec #t))
