#lang racket

;; Various helper checks for RackUnit
(provide
 check-same-items?)

;; ---------------------------------------------------------------------------------------------------
(require rackunit)

(define-simple-check (check-same-items? actual expected)
  (equal? (list->set actual) (list->set expected)))
