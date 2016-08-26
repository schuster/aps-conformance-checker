#lang racket

(provide
 set-immutable-copy
 set-findf)

;; ---------------------------------------------------------------------------------------------------

;; Creates an immutable copy of the given set
(define (set-immutable-copy s)
  (list->set (set->list s)))

;; Acts like findf, but on sets instead of lists
(define (set-findf proc s)
  (findf proc (set->list s)))
