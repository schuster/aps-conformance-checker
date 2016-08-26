#lang racket

;; Various helper checks for RackUnit
(provide
 check-same-items?
 test-same-items?
 check-hash-of-msets-equal?
 test-hash-of-msets-equal?)

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

;; A custom predicate to work around bug http://bugs.racket-lang.org/query/?cmd=view&pr=15342 . For
;; each value in the hash values (assumed to each be a set), just checks that the items contained are
;; all equal by doing (list->set (set->list s)).
(define (hash-of-msets-equal? h1 h2)
  (and (equal? (list->set (hash-keys h1)) (list->set (hash-keys h2)))
       (for/and ([key (hash-keys h1)])
         (equal? (list->set (set->list (hash-ref h1 key)))
                 (list->set (set->list (hash-ref h2 key)))))))

(define-binary-check (check-hash-of-msets-equal? hash-of-msets-equal? actual expected))

(define-syntax (test-hash-of-msets-equal? stx)
  (syntax-parse stx
    [(_  name actual expected)
     #`(test-case name
         #,(syntax/loc stx (check-hash-of-msets-equal? actual expected)))]))

(module+ test
  (define s1
    (let ()
      (define outer-set (mutable-set))
      (define middle-set (mutable-set))
      (set-add! outer-set middle-set)
      (set-add! middle-set (mutable-set))
      outer-set))

  (define s2
    (let ()
      (define outer-set (mutable-set))
      (define middle-set (mutable-set))
      (set-add! middle-set (mutable-set))
      (set-add! outer-set middle-set)
      outer-set))

  (define s3
    (let ()
      (define outer-set (mutable-set))
      (define middle-set (mutable-set))
      (set-add! middle-set (mutable-set 1))
      (set-add! outer-set middle-set)
      outer-set))

  (test-true "hash-of-msets-equal? success"
    (hash-of-msets-equal? (hash 'a s1) (hash 'a s2)))
  (test-false "hash-of-msets-equal? failure"
    (hash-of-msets-equal? (hash 'a s1) (hash 'a s3)))
  (test-false "hash-of-msets-equal? failure 2"
    (hash-of-msets-equal? (hash 'a s2) (hash 'a s3))))
