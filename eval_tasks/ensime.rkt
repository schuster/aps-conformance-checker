#lang racket

(require
 "../check-pair.rkt"
 "../examples/ensime.rkt")

(check-pair ensime-program ensime-project-spec)
