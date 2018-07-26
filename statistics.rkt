#lang racket

;; Defines various statistics recorded during each run. We use the "STAT-" prefix naming convention to
;; mark the recorded statistics.

(provide (except-out (all-defined-out) stat set-stat-value!))

;; ---------------------------------------------------------------------------------------------------
;; Basic ref-cell for statistics

(struct stat ([value #:mutable]))

(define (stat-set! cell val)
  (set-stat-value! cell val))

;; ---------------------------------------------------------------------------------------------------
;; The statistics themselves

;; Simulation statistics
(define STAT-visited-pairs-count (stat 0))
(define STAT-unique-impl-configs-count (stat 0))
(define STAT-unique-spec-configs-count (stat 0))
(define STAT-visited-prog-transitions-count (stat 0))

;; Eval-cache statistics
(define STAT-num-eval-handler-calls (stat 0))
(define STAT-num-eval-handler-cache-hits (stat 0))

;; Widen statistics
(define STAT-widen-loop-count (stat 0))
(define STAT-widen-maybe-good-count (stat 0))
(define STAT-widen-attempt-count (stat 0))
(define STAT-widen-spec-match-count (stat 0))
(define STAT-widen-use-count (stat 0))

;; Checkpoint timestamps for each phase
(define STAT-start-time (stat #f))
(define STAT-simulation-finish-time (stat #f))
(define STAT-simulation-prune-finish-time (stat #f))
(define STAT-obligation-check-finish-time (stat #f))
(define STAT-obligation-prune-finish-time (stat #f))
(define STAT-finish-time (stat #f))

;; Pair counts for each stage of algorithm
(define STAT-rank1-simulation-size (stat #f))
(define STAT-simulation-size (stat #f))
(define STAT-obl-checked-size (stat #f))
(define STAT-conformance-size (stat #f))

(define (reset-statistics)
  (stat-set! STAT-visited-pairs-count 0)
  (stat-set! STAT-unique-impl-configs-count 0)
  (stat-set! STAT-unique-spec-configs-count 0)
  (stat-set! STAT-visited-prog-transitions-count 0)

  (stat-set! STAT-num-eval-handler-calls 0)
  (stat-set! STAT-num-eval-handler-cache-hits 0)

  (stat-set! STAT-widen-loop-count 0)
  (stat-set! STAT-widen-maybe-good-count 0)
  (stat-set! STAT-widen-attempt-count 0)
  (stat-set! STAT-widen-spec-match-count 0)
  (stat-set! STAT-widen-use-count 0)

  (stat-set! STAT-start-time #f)
  (stat-set! STAT-simulation-finish-time #f)
  (stat-set! STAT-simulation-prune-finish-time #f)
  (stat-set! STAT-obligation-check-finish-time #f)
  (stat-set! STAT-obligation-prune-finish-time #f)
  (stat-set! STAT-finish-time #f)

  (stat-set! STAT-rank1-simulation-size #f)
  (stat-set! STAT-simulation-size #f)
  (stat-set! STAT-obl-checked-size #f)
  (stat-set! STAT-conformance-size #f))

(define (print-statistics)
  (printf "STATISTICS:\n")
  (printf "Visited pairs: ~s\n" (stat-value STAT-visited-pairs-count))
  (printf "Unique impl configs: ~s\n" (stat-value STAT-unique-impl-configs-count))
  (printf "Unique spec configs: ~s\n" (stat-value STAT-unique-spec-configs-count))
  (printf "Visited program transitions: ~s\n" (stat-value STAT-visited-prog-transitions-count))
  (printf "Eval cache hits: ~s/~s\n"
          (stat-value STAT-num-eval-handler-cache-hits)
          (stat-value STAT-num-eval-handler-calls))

  (printf "\nWiden stats:\n")
  (printf "Widen loop count: ~s\n" (stat-value STAT-widen-loop-count))
  (printf "Widen maybe-good count: ~s\n" (stat-value STAT-widen-maybe-good-count))
  (printf "Widen attempt count: ~s\n" (stat-value STAT-widen-attempt-count))
  (printf "Widen spec match count: ~s\n" (stat-value STAT-widen-spec-match-count))
  (printf "Widen use count: ~s\n" (stat-value STAT-widen-use-count))

  (printf "\nCheckpoint times:\n")
  (printf "Start time: ~s\n" (stat-value STAT-start-time))
  (printf "Simulation finish time: ~s\n" (stat-value STAT-simulation-finish-time))
  (printf "Simulation prune finish time: ~s\n" (stat-value STAT-simulation-prune-finish-time))
  (printf "Obligation check finish time: ~s\n" (stat-value STAT-obligation-check-finish-time))
  (printf "Obligation prune finish time: ~s\n" (stat-value STAT-obligation-prune-finish-time))
  (printf "Finish time: ~s\n" (stat-value STAT-finish-time))

  (printf "\nSet sizes:\n")
  (printf "Rank-1 simulation size: ~s\n" (stat-value STAT-rank1-simulation-size))
  (printf "Simulation size: ~s\n" (stat-value STAT-simulation-size))
  (printf "Obligation checked size: ~s\n" (stat-value STAT-obl-checked-size))
  (printf "Conformance size: ~s\n" (stat-value STAT-conformance-size)))
