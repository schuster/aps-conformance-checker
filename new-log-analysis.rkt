#lang racket

(require
 racket/date
 racket/fasl
 "checker-data-structures.rkt"
 "main.rkt")

(define all-configs (make-hash))
(define initial-pairs null)
(define exploring (mutable-set))
(define related-pairs (mutable-set))
(define unrelated-pairs (mutable-set))
(define incoming (make-hash))
(define related-spec-steps (make-hash))

(define (display-current-time)
  (printf "Current time: ~s\n" (date->string (seconds->date (current-seconds)) #t)))

(displayln "Reading the file")

(display-current-time)

(define most-recent-pair #f)
(define pairs-so-far 0)

;; Rather than creating multiple copies of the same object, look for an existing equal? value first
(define (get-config p)
  (match (hash-ref all-configs p #f)
    [#f
     (hash-set! all-configs p p)
     p]
    [pair pair]))

;; read in the file
(call-with-input-file "examples/checker_run_log.dat"
  (lambda (file)
    (let loop ()
      (match (fasl->s-exp file)
        [(? eof-object?) (void)]
        [(list 'initial-pair (config-pair i s))
         (define the-pair (config-pair (get-config i) (get-config s)))
         (set! initial-pairs (cons the-pair initial-pairs))
         (hash-set! incoming the-pair (mutable-set))
         (loop)]
        [(list 'exploring (config-pair i s))
         (set-add! exploring (config-pair (get-config i) (get-config s)))
         (set! pairs-so-far (add1 pairs-so-far))
         (printf "read number ~s\n" pairs-so-far)
         ;; (set! most-recent-pair pair)
         (loop)]
        [(list 'related-spec-step (list i (impl-step trigger from out dest)) related-steps)
         (define new-steps (mutable-set))
         (for ([step related-steps])
           (match-define (spec-step dest spawns sat-coms) step)
           (set-add! new-steps (spec-step (get-config dest)
                                          (map get-config spawns)
                                          sat-coms)))
         (hash-set! related-spec-steps
                    (list (get-config i) (impl-step trigger from out (get-config dest)))
                    new-steps)
         (loop)]
        [(list 'unrelated (config-pair i s))
         (set-add! unrelated-pairs (config-pair (get-config i) (get-config s)))
         (loop)]
        [(list 'related (config-pair i s))
         (set-add! related-pairs (config-pair (get-config i) (get-config s)))
         (loop)]
        [(list 'incoming (config-pair i s) (list (config-pair i2 s2)
                                                 (impl-step trig from out i-dest)
                                                 (spec-step s-dest spawns sat-coms)
                                                 mapping))
         (define pair (config-pair (get-config i) (get-config s)))
         (define step (list (config-pair (get-config i2) (get-config s2))
                            (impl-step trig from out (get-config i-dest))
                            (spec-step (get-config s-dest) (map get-config spawns) sat-coms)
                            mapping))
         (match (hash-ref incoming pair #f)
           [#f
            (hash-set! incoming pair (mutable-set step))]
           [the-set
            (set-add! the-set step)])
         (loop)]))))

(display-current-time)
(displayln "Read the whole file")

;; This is a copy of the remaining section of check-conformance/config, so that I can re-run the rest
;; of the algorithm on the logged data
(define (check initial-pairs
               rank1-pairs
               rank1-unrelated-successors
               incoming-steps
               rank1-related-spec-steps)
  (display-current-time)
  (printf "Num initial pairs: ~s\n" (length initial-pairs))
  (printf "Num related r1: ~s\n" (set-count rank1-pairs))
  (printf "Num unrelated r1: ~s\n" (set-count rank1-unrelated-successors))
  (printf "All in r1: ~s\n" (andmap (curry set-member? rank1-pairs) initial-pairs))
  (match-define (list simulation-pairs simulation-related-spec-steps)
    (prune-unsupported rank1-pairs
                       incoming-steps
                       rank1-related-spec-steps
                       rank1-unrelated-successors))
  (display-current-time)
  (printf "Num related simulation: ~s\n" (set-count simulation-pairs))
  (printf "All in simulation: ~s\n" (andmap (curry set-member? simulation-pairs) initial-pairs))
  (match-define (list commitment-satisfying-pairs unsatisfying-pairs)
    (partition-by-satisfaction simulation-pairs incoming-steps simulation-related-spec-steps))
  (display-current-time)
  (printf "Num com-sat: ~s\n" (set-count commitment-satisfying-pairs))
  (printf "Num com-unsat: ~s\n" (set-count unsatisfying-pairs))
  (printf "All in com-sat: ~s\n" (andmap (curry set-member? commitment-satisfying-pairs) initial-pairs))
  (match-define (list conforming-pairs _)
    (prune-unsupported commitment-satisfying-pairs
                       incoming-steps
                       simulation-related-spec-steps
                       unsatisfying-pairs))
  (display-current-time)
  (printf "Num conforming: ~s\n" (set-count conforming-pairs))
  (printf "All in conforming: ~s\n" (andmap (curry set-member? conforming-pairs) initial-pairs))
  (andmap (curry set-member? conforming-pairs) initial-pairs))

(displayln "Checking conformance")

(check initial-pairs related-pairs unrelated-pairs incoming related-spec-steps)
