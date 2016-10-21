#lang racket

;; A little debugging script for exploring the impl and spec steps from a given config pair

(require
 "checker-data-structures.rkt"
 "main.rkt")

(match-define (config-pair i s)
  (call-with-input-file "auth_debug/maybe_before_unrelated.rktd"
    (lambda (file)
      (read file))))

(define the-impl-steps (impl-steps-from i s))
(for ([i-step the-impl-steps])
  (displayln (impl-step-trigger i-step))

  (printf "Number of matching spec steps: ~s\n" (set-count (matching-spec-steps s i-step)))
  (for ([matching-step (matching-spec-steps s i-step)])
    (printf "config pair: ~s\n"
            (pair->debug-pair (config-pair (impl-step-destination i-step)
                                           (spec-step-destination matching-step))))
    ;; (printf "~s\n\n" matching-step)
    ))
