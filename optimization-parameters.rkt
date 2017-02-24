#lang racket

;; Defines the parameters used to enable/disable various optmizations

(provide
 USE-WIDEN?
 MEMOIZE-EVAL-HANDLER?
 USE-EVICTION?)

(define USE-WIDEN? (make-parameter #t))
(define MEMOIZE-EVAL-HANDLER? (make-parameter #t))
(define USE-EVICTION? (make-parameter #t))

