#lang racket

(require data/queue)

(provide queue
         dequeue-if-non-empty!)

(define (queue . items)
  (let ([q (make-queue)])
  (map (curry enqueue! q) items)
  q))

(module+ test
  (check-equal? (queue->list (queue)) null))

(define (dequeue-if-non-empty! queue)
  (if (queue-empty? queue) #f (dequeue! queue)))

(module+ test
  (require rackunit)

  (check-false (dequeue-if-non-empty! (make-queue)))
  (test-begin
    (define q (make-queue))
    (enqueue! q 'a)
    (enqueue! q 'b)
    (check-equal? (dequeue-if-non-empty! q) 'a)
    (check-equal? (queue->list q) (list 'b))))
