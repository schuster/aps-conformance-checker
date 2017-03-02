#lang racket

(provide check-pair)

(require
 "main.rkt")

(define (check-pair prog spec)
  (define widen? #f)
  (define memoize? #f)
  (define evict? #f)
  (define stats-dir #f)

  (command-line
   #:once-each ["--widen" "Enable widening" (set! widen? #t)]
   ["--memoize" "Enable memoization for eval-handler" (set! memoize? #t)]
   ["--evict" "Enable eviction" (set! evict? #t)]
   ["--stats-dir" dir "Directory for statistics output" (set! stats-dir dir)])

  (check-conformance prog spec
                     #:use-widen? widen?
                     #:memoize-eval-handler? memoize?
                     #:use-eviction? evict?
                     #:stats-directory stats-dir))
