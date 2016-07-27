#lang racket

;; Various helper checks for RackUnit
(provide
 check-same-items?
 test-same-items?)

;; ---------------------------------------------------------------------------------------------------
(require
 rackunit
 redex/reduction-semantics
 (for-syntax syntax/parse))

(define-simple-check (check-same-items? actual expected)
  (equal? (list->set actual) (list->set expected)))

(define-syntax (test-same-items? stx)
  (syntax-parse stx
    [(_  name actual expected)
     #`(test-case name
         #,(syntax/loc stx (check-same-items? actual expected)))]
    [(_  actual expected)
     #`(test-begin
         #,(syntax/loc stx (check-same-items? actual expected)))]))
