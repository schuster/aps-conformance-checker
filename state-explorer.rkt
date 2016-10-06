#lang racket

;; A little debugging script for exploring the impl and spec steps from a given config pair

(require
 "checker-data-structures.rkt"
 "main.rkt")

(match-define (config-pair i s)
  (call-with-input-file "unrelated_6oct.rktd"
    (lambda (file)
      (read file))))

(define the-impl-steps (impl-steps-from i s))
(for ([i-step the-impl-steps])
  (displayln (impl-step-trigger i-step))
  (printf "Matching spec steps: ~s\n" (set-count (matching-spec-steps s i-step))))
