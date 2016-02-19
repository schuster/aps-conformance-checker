#lang racket

(require data/queue)

(provide queue)

(define-syntax-rule (queue items ...)
  (let ([q (make-queue)])
  (for ([item (list items ...)])
    (enqueue! q item))
  q))
