#lang racket

;; A CSA program that generates actors that take the running average of a stream of temperature
;; data. Intended for use as a motivating example for CSA and APS.

;; actor names: (Feed) Processor and Manager

(require "desugar.rkt")

(define FullProcessorMessage
  `(Union
    [Temp Nat (Addr (Union [Ok] [NotOk]))]
    [GetMean (Addr Nat)]
    [Disable]
    [Enable (Addr Nat)]
    [Shutdown]))

(define ProcessorMessage
  `(Union
    [Temp Nat (Addr (Union [Ok] [NotOk]))]
    [GetMean (Addr Nat)]
    [Enable (Addr Nat)]
    [Disable]))

(define ManagerMessage
  `(Union
    [NewProcessor (Addr (Addr ,ProcessorMessage))]
    [ShutdownAll]))

(define weather-program
 (desugar
  `(program (receptionists [manager ,ManagerMessage]) (externals)

(define-actor ,FullProcessorMessage (Processor)
  ()
;; Initial state
(goto Off 0 0)

;; State definitions
(define-state (Off [sum Nat] [num-rdgs Nat]) (m)
  (case m
    [(Temp t r)
     (send r (variant NotOk))
     (goto Off sum num-rdgs)]
    [(GetMean r)
     (send r (/ sum num-rdgs))
     (goto Off sum num-rdgs)]
    [(Disable) (goto Off sum num-rdgs)]
    [(Enable redir) (goto On sum num-rdgs redir)]
    [(Shutdown) (goto Done)]))

(define-state (On [sum Nat] [num-rdgs Nat] [redir (Addr Nat)]) (m)
  (case m
    [(Temp t r)
     (send r (variant Ok))
     (send redir t)
     (goto On (+ sum t) (+ num-rdgs 1) redir)]
    [(GetMean r)
     (send r (/ sum num-rdgs))
     (goto On sum num-rdgs redir)]
    [(Disable) (goto Off sum num-rdgs)]
    [(Enable new-redir) (goto On sum num-rdgs new-redir)]
    [(Shutdown) (goto Done)]))

(define-state (Done) (m) (goto Done)))

(define-actor ,ManagerMessage (Manager)
  ()
  (goto Managing (list))
  (define-state (Managing [processors (List (Addr ProcessorMessage))]) (m)
    (case m
      [(NewProcessor r)
       (case (< (length processors) 100)
         [(True)
          (let ([p (spawn P Processor)])
            (send r p)
            (goto Managing (cons p processors)))]
         [(False) (goto Managing processors)])]
      [(ShutdownAll)
       (for/fold ([dummy-result (variant Shutdown)])
                 ([p processors])
         (send p (variant Shutdown)))
       (goto Managing (list))])))

(actors [manager (spawn M Manager)]))))

(module+ test
  (require
   racket/async-channel
   asyncunit
   (only-in csa variant)
   csa/eval
   csa/testing
   rackunit
   "main.rkt")

  (test-case "General test for the processor"
    (define manager (csa-run weather-program))
    ;; 1. Get a new processor
    (define client (make-async-channel))
    (async-channel-put manager (variant NewProcessor client))
    (define proc (check-unicast-match client p #:result p))

    ;; 2. Turn it on, send it temp data, get OK, check redir
    (define redir (make-async-channel))
    (async-channel-put proc (variant Enable redir))
    (async-channel-put proc (variant Temp 90 client))
    (check-unicast client (variant Ok))
    (check-unicast redir 90)

    ;; 3. Send it more temp data, get OK
    (async-channel-put proc (variant Temp 70 client))
    (check-unicast client (variant Ok))
    (check-unicast redir 70)

    ;; 4. Get mean
    (async-channel-put proc (variant GetMean client))
    (check-unicast client 80)

    ;; 5. disable
    (async-channel-put proc (variant Disable))

    ;; 6. send it more temp data, get NotOk
    (async-channel-put proc (variant Temp 102 client))
    (check-unicast client (variant NotOk))

    ;; 7. Get mean while disabled
    (async-channel-put proc (variant GetMean client))
    (check-unicast client 80)

    ;; 8. Enable, send more data, get OK
    (async-channel-put proc (variant Enable redir))
    (async-channel-put proc (variant Temp 50 client))
    (check-unicast client (variant Ok))
    (check-unicast redir 50)

    ;; 9. Shutdown All
    (async-channel-put manager (variant ShutdownAll))
    (sleep 1)

    ;; 10. Ask for mean, no response
    (async-channel-put proc (variant GetMean client))
    (check-no-message client #:timeout 3))

  (define processor-spec-parts
    `((goto Off)

      (define-state (Off)
        [(variant Temp * r) -> ([obligation r (variant NotOk)]) (goto Off)]
        [(variant GetMean r) -> ([obligation r *]) (goto Off)]
        [(variant Disable) -> () (goto Off)]
        [(variant Enable redir) -> () (goto On redir)]
        [unobs -> () (goto Done)])

      (define-state (On redir)
        [(variant Temp * r) ->
         ([obligation r (variant Ok)]
          [obligation redir *])
         (goto On redir)]
        [(variant GetMean r) -> ([obligation r *]) (goto On redir)]
        [(variant Disable) -> () (goto Off)]
        [(variant Enable new-redir) -> () (goto On new-redir)]
        [unobs -> () (goto Done)])

      (define-state (Done)
        [(variant Temp * r) -> () (goto Done)]
        [(variant GetMean r) -> () (goto Done)]
        [(variant Disable) -> () (goto Done)]
        [(variant Enable redir) -> () (goto Done)])))

  (define manager-spec
    `(specification (receptionists [manager ,ManagerMessage]) (externals)
       ([manager (Union [NewProcessor (Addr (Addr ,ProcessorMessage))])])
       ([manager (Union [ShutdownAll])])
       (goto Managing)
       (define-state (Managing)
         [(variant NewProcessor r) ->
          ([obligation r (delayed-fork ,@processor-spec-parts)])
          (goto Managing)]
         [(variant NewProcessor r) -> () (goto Managing)])))

  (test-true "Weather program conforms to spec"
    (check-conformance weather-program manager-spec)))