#lang racket

(provide
 mutable-hash
 immutable-hash)

(require (for-syntax syntax/parse))

(define-syntax (mutable-hash stx)
  (syntax-parse stx
    [(_ (key val) ...)
     #`(make-hash (list (cons key val) ...))]))

(define-syntax (immutable-hash stx)
  (syntax-parse stx
    [(_ (key val) ...)
     #`(make-immutable-hash (list (cons key val) ...))]))
