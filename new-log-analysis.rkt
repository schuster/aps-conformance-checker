#lang racket

(require
 racket/fasl
 "checker-data-structures.rkt"
 "main.rkt")

(define initial-pairs null)
(define exploring (mutable-set))
(define related-pairs (mutable-set))
(define unrelated-pairs (mutable-set))
(define incoming (make-hash))
(define related-spec-steps (make-hash))

(displayln "Reading the file")

(printf "Time 1: ~s\n" (current-seconds))

(define most-recent-pair #f)
(define pairs-so-far 0)

;; read in the file
(call-with-input-file "examples/checker_run_log.dat"
  (lambda (file)
    (let loop ()
      (match (fasl->s-exp file)
        [(? eof-object?) (void)]
        [(list 'initial-pair pair)
         (set! initial-pairs (cons pair initial-pairs))
         (loop)]
        [(list 'exploring pair)
         (set-add! exploring pair)
         (set! pairs-so-far (add1 pairs-so-far))
         (printf "read number ~s\n" pairs-so-far)
         (set! most-recent-pair pair)
         (loop)]
        [(list 'related-spec-step config-and-i-step related-steps)
         (hash-set! related-spec-steps config-and-i-step (list->set related-steps))
         (loop)]
        [(list 'unrelated pair)
         (set-add! unrelated-pairs pair)
         (loop)]
        [(list 'related pair)
         (set-add! related-pairs pair)
         (loop)]
        [(list 'incoming pair step)
         (match (hash-ref incoming pair #f)
           [#f
            (hash-set! incoming pair (mutable-set step))]
           [the-set
            (set-add! the-set step)])
         (loop)]))))

(printf "Time 2: ~s\n" (current-seconds))
(displayln "Read the whole file")

;; This is a copy of the remaining section of check-conformance/config, so that I can re-run the rest
;; of the algorithm on the logged data
(define (check initial-pairs
               rank1-pairs
               rank1-unrelated-successors
               incoming-steps
               rank1-related-spec-steps)
  (printf "Current time: ~s\n" (current-seconds))
  (printf "Num initial pairs: ~s\n" (length initial-pairs))
  (printf "Num related r1: ~s\n" (set-count rank1-pairs))
  (printf "Num unrelated r1: ~s\n" (set-count rank1-unrelated-successors))
  (printf "All in r1: ~s\n" (andmap (curry set-member? rank1-pairs) initial-pairs))
  (match-define (list simulation-pairs simulation-related-spec-steps)
    (prune-unsupported rank1-pairs
                       incoming-steps
                       rank1-related-spec-steps
                       rank1-unrelated-successors))
  (printf "Current time: ~s\n" (current-seconds))
  (printf "Num related simulation: ~s\n" (set-count simulation-pairs))
  (printf "All in simulation: ~s\n" (andmap (curry set-member? simulation-pairs) initial-pairs))
  (match-define (list commitment-satisfying-pairs unsatisfying-pairs)
    (partition-by-satisfaction simulation-pairs incoming-steps simulation-related-spec-steps))
  (printf "Current time: ~s\n" (current-seconds))
  (printf "Num com-sat: ~s\n" (set-count commitment-satisfying-pairs))
  (printf "Num com-unsat: ~s\n" (set-count unsatisfying-pairs))
  (printf "All in com-sat: ~s\n" (andmap (curry set-member? commitment-satisfying-pairs) initial-pairs))
  (match-define (list conforming-pairs _)
    (prune-unsupported commitment-satisfying-pairs
                       incoming-steps
                       simulation-related-spec-steps
                       unsatisfying-pairs))
  (printf "Current time: ~s\n" (current-seconds))
  (printf "Num conforming: ~s\n" (set-count conforming-pairs))
  (printf "All in conforming: ~s\n" (andmap (curry set-member? conforming-pairs) initial-pairs))
  (andmap (curry set-member? conforming-pairs) initial-pairs))

(displayln "Checking conformance")

(check initial-pairs related-pairs unrelated-pairs incoming related-spec-steps)
