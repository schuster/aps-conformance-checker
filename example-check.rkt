#lang racket

;; A brief example to demonstrate how to model-check one of the example programs

(require
 "main.rkt" ; for check-conformance
 "examples/weather-average.rkt" ; for the running example program and spec
 )

;; Check conformance, with all optimizations enabled
(check-conformance weather-program manager-spec)

;; Check conformance, with all optimizations disabled
(check-conformance weather-program
                   manager-spec
                   #:use-widen? #f
                   #:use-eviction? #f
                   #:memoize-eval-handler? #f
                   #:use-detect-dead-observables? #f)
