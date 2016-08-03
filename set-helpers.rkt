#lang racket

(provide
 set-immutable-copy)

;; ---------------------------------------------------------------------------------------------------

;; Creates an immutable copy of the given set
(define (set-immutable-copy s)
  (list->set (set->list s)))
