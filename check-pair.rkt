#lang racket

(provide check-pair)

(require
 "desugar.rkt"
 "main.rkt")

(define (check-pair prog spec)
  (define widen? #f)
  (define memoize? #f)
  (define evict? #f)

  (command-line
   #:once-each ["--widen" "Enable widening" (set! widen? #t)]
   ["--memoize" "Enable memoization for eval-handler" (set! memoize? #t)]
   ["--evict" "Enable eviction" (set! evict? #t)])

  (check-conformance (desugar prog) spec
                     #:use-widen? widen?
                     #:memoize-eval-handler? memoize?
                     #:use-eviction? evict?))
