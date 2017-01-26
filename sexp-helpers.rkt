#lang racket

;; Various helpers for working with S-expressions

(provide
 sexp<?)

(module+ test
  (require rackunit))

(define (sexp<? a b)
  (match (sexp-compare a b)
    ['lt #t]
    [_ #f]))

(define (sexp-compare a b)
  (cond
    [(pair? a)
     (cond
       [(pair? b)
        (match (sexp-compare (car a) (car b))
          ['eq (sexp-compare (cdr a) (cdr b))]
          [other-result other-result])]
       [else 'gt])]
    [(null? a)
     (cond
       [(pair? b) 'lt]
       [(null? b) 'eq]
       [else 'gt])]
    [(symbol? a)
     (cond
       [(symbol? b)
        (cond
          [(eq? a b) 'eq]
          [(symbol<? a b) 'lt]
          [else 'gt])]
       [else 'lt])]
    [(string? a)
     (cond
       [(string? b)
        (cond
          [(string=? a b) 'eq]
          [(string<? a b) 'lt]
          [else 'gt])]
       [(symbol? b) 'gt]
       [else 'lt])]
    [(number? a)
     (cond
       [(number? b)
        (cond
          [(equal? a b) 'eq]
          [(< a b) 'lt]
          [else 'gt])]
       [(or (pair? b) (null? b)) 'lt]
       [else 'gt])]
    [else (error 'sexp-compare "Can't compare ~s and ~s" a b)]))

(module+ test
  (test-true "lesser pair" (sexp<? (cons 'a 'b) (cons 'c 'b)))
  (test-false "greater pair" (sexp<? (cons 'c 'b) (cons 'a 'b)))
  (test-false "same pair" (sexp<? (cons 'a 'b) (cons 'a 'b)))
  (test-false "equal lists" (sexp<? (list 'a 'b) (list 'a 'b)))
  (test-true "null to pair" (sexp<? null (cons 1 2)))
  (test-false "pair to null" (sexp<? (cons 'a 'b) null))
  (test-false "lists with different elements" (sexp<? (list 'a 'c) (list 'a 'b)))
  (test-true "lists with different elements 2" (sexp<? (list 'a 'b) (list 'a 'c)))
  (test-false "longer list" (sexp<? (list 'a 'b) (list 'a)))
  (test-true "shorter list" (sexp<? (list 'a) (list 'a 'b)))
  (test-false "list to symbol" (sexp<? (list 'a) 'b))
  (test-false "list to symbol 2" (sexp<? null 'b))
  (test-false "list to string" (sexp<? (list 'a) "foo"))
  (test-false "list to number" (sexp<? (list 'a) 1))
  (test-true "symbol to list" (sexp<? 'b (list 'a)))
  (test-true "string to list" (sexp<? "foo" (list 'a)))
  (test-true "number to list" (sexp<? 1 (list 'a)))
  (test-false "symbol to same symbol" (sexp<? 'a 'a))
  (test-true "lesser symbol" (sexp<? 'a 'b))
  (test-false "greater symbol" (sexp<? 'b 'a))
  (test-true "symbol to number" (sexp<? 'b 1))
  (test-false "number to symbol" (sexp<? 1 'b))
  (test-false "string to symbol" (sexp<? "foo" 'b))
  (test-true "symbol to string" (sexp<? 'a "foo"))
  (test-false "same string" (sexp<? "foo" "foo"))
  (test-false "greater string" (sexp<? "foo" "bar"))
  (test-true "lesser string" (sexp<? "bar" "foo"))
  (test-true "string to number" (sexp<? "foo" 1))
  (test-false "number to string" (sexp<? 1 "foo"))
  (test-false "same numbers" (sexp<? 1 1))
  (test-true "lesser number" (sexp<? 1 2))
  (test-false "greater number" (sexp<? 2 1)))
