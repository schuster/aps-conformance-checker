#lang racket

(require
 racket/fasl
 "checker-data-structures.rkt"
 "main.rkt")

(define initial-pairs-set (mutable-set))
(define exploring (mutable-set))
(define related-pairs (mutable-set))
(define unrelated-pairs (mutable-set))
(define incoming (make-hash))
(define related-spec-steps (make-hash))

(displayln "Reading the file")

;; read in the file
(call-with-input-file "checker_run_log.dat"
  (lambda (file)
    (let loop ()
      (match (fasl->s-exp file)
        [(? eof-object?) (void)]
        [(list 'initial-pair pair)
         (set-add! initial-pairs-set pair)
         (loop)]
        [(list 'exploring pair)
         (set-add! exploring pair)
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

;; This is a copy of the remaining section of check-conformance/config, so that I can re-run the rest
;; of the algorithm on the logged data
(define (check initial-pairs
               rank1-pairs
               rank1-unrelated-successors
               incoming-steps
               rank1-related-spec-steps)
  (match-define (list simulation-pairs simulation-related-spec-steps)
    (prune-unsupported rank1-pairs
                       incoming-steps
                       rank1-related-spec-steps
                       rank1-unrelated-successors))
  (match-define (list commitment-satisfying-pairs unsatisfying-pairs)
    (partition-by-satisfaction simulation-pairs incoming-steps simulation-related-spec-steps))
  (match-define (list conforming-pairs _)
    (prune-unsupported commitment-satisfying-pairs
                       incoming-steps
                       simulation-related-spec-steps
                       unsatisfying-pairs))
  (andmap (curry set-member? conforming-pairs) initial-pairs))

(displayln "Checking conformance")

(check (set->list initial-pairs-set) related-pairs unrelated-pairs incoming related-spec-steps)
