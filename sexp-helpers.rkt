#lang racket

;; Various helpers for working with S-expressions

(provide
 sexp<?)

(module+ test
  (require rackunit))

(define (sexp<? a b)
  (string<? (sexp->string a) (sexp->string b)))

;; TODO: try caching the results of this function
(define (sexp->string s)
  (define port (open-output-string))
  (fprintf port "~s" s)
  (get-output-string port))

(module+ test
  (check-true (sexp<? null 'a))
  (check-true (sexp<? 'a 'b))
  (check-false (sexp<? 'b 'a))
  (check-false (sexp<? 'a null)))
