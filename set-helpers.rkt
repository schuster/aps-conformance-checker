#lang racket

(provide
 set-freeze)

;; ---------------------------------------------------------------------------------------------------

;; Creates an immutable copy of the given set
(define (set-freeze s)
  (list->set (set->list s)))
