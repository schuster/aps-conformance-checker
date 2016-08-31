#lang racket

;; Summary:
;; Optimizations suggested by what I've seen so far:
;; * cache eval results for impl configs
;; * don't further explore out-com-only nodes where a no-pattern obs addr doesn't appear in impl config
;; * rather than forking off separate configs for obs addrs, abstract some addrs into special never-use-again address


(define (dead-address? exp addr)
  (cond
    [(equal? exp addr) #f]
    [(list? exp) (andmap (curryr dead-address? addr) exp)]
    [else #t]))

;; ---------------------------------------------------------------------------------------------------
;; Analysis body

(define tuples
  (call-with-input-file "/home/schu/research/conformance_checker/filtered_tuple_log_24_july_2016.dat"
    (lambda (file)
      (let loop ([reversed-tuples null])
        (match (read file)
          [(? eof-object?) (reverse reversed-tuples)]
          [tuple (loop (cons tuple reversed-tuples))])))))

(define unique-impl-configs (remove-duplicates (map first tuples)))
(define unique-spec-configs (remove-duplicates (map second tuples)))
(define out-com-only-tuples
  (filter (lambda (t)
            (let ()
              (define spec-config (second t))
              (define instances (first spec-config))
              (null? instances)))
          tuples))
(define (dead-out-com-tuple? t)
  (define spec-config (second t))
  ;; NOTE: this needs to changes to "third" for later spec configs
  (define out-coms (second spec-config))
  (define out-com-addr (first (first out-coms)))
  (dead-address? (first t) out-com-addr))

(define dead-out-com-only-tuples
  (filter dead-out-com-tuple? out-com-only-tuples))

(define non-dead-no-com-tuples
  (filter
   (lambda (t)
     ;; has no patterns
     (define spec-config (second t))
     ;; NOTE: this needs to changes to "third" for later spec configs
     (define out-coms (second spec-config))
     (null? (cdr (first out-coms)))
     )
      (filter (negate dead-out-com-tuple?) out-com-only-tuples)
)
  )

(printf "Number of tuples: ~s\n" (length tuples))
(printf "Number of unique impl configs: ~s\n" (length unique-impl-configs))
(printf "Number of unique spec configs: ~s\n" (length unique-spec-configs))
(printf "Number of tuples with out-com-only: ~s\n" (length out-com-only-tuples))
(printf "Number of dead out-com tuples: ~s\n" (length dead-out-com-only-tuples))
(printf "Number of alive but no pattern out-com tuples: ~s\n" (length non-dead-no-com-tuples))

;; (for ([t (filter (negate dead-out-com-tuple?) out-com-only-tuples)])
;;   (printf "tuple: ~s\n" t))
