#lang racket

(require
 "../check-pair.rkt"
 "../examples/raft.rkt")

(check-pair (make-raft-actor-prog #t #f #f #f) raft-spec)
