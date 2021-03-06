#lang racket

(provide check-pair)

(require
 "main.rkt")

(define (check-pair prog spec)
  (define widen? #f)
  (define memoize? #f)
  (define evict? #f)
  (define detect-dead? #f)
  (define stats-dir #f)

  (command-line
   #:once-each ["--widen" "Enable widening" (set! widen? #t)]
   ["--memoize" "Enable memoization for eval-handler" (set! memoize? #t)]
   ["--evict" "Enable eviction" (set! evict? #t)]
   ["--detect-dead" "Enable dead-observable detection" (set! detect-dead? #t)]
   ["--stats-dir" dir "Directory for statistics output" (set! stats-dir dir)])

  (check-conformance prog spec
                     #:use-widen? widen?
                     #:memoize-eval-handler? memoize?
                     #:use-eviction? evict?
                     #:use-detect-dead-observables? detect-dead?
                     #:stats-directory stats-dir))
