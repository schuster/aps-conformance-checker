#lang racket

;; Defines various helper functions for dealing with lists

(provide find-with-rest)

;; like findf, but also returns the items before and after the element in the list
(define (find-with-rest pred? xs)
  (let loop ([before null]
             [after xs])
    (match after
      [(list) #f]
      [(list x after ...)
       (if (pred? x)
           (list (reverse before) x after)
           (loop (cons x before) after))])))

(module+ test
  (require rackunit)

  (check-equal?
   (find-with-rest (lambda (x) (equal? x 3)) (list 1 2 3 4 5))
   (list (list 1 2) 3 (list 4 5)))
  (check-false
   (find-with-rest (lambda (x) (equal? x 6)) (list 1 2 3 4 5))))
