#lang racket

(require
 "../check-pair.rkt"
 "../examples/raft.rkt")

(check-pair (make-raft-actor-prog #f #f #f #t) raft-spec)