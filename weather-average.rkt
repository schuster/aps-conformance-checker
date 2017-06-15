#lang racket

;; A CSA program that generates actors that take the running average of a stream of temperature
;; data. Intended for use as a motivating example for CSA and APS.

;; actor names: (Feed) Processor and Manager

(require "desugar.rkt")

(define FullProcessorMessage
  `(Union
    [Temp Nat (Addr (Union [Ok] [NotOk]))]
    [GetMean (Addr Nat)]
    [Enable]
    [Disable (Addr Nat)]
    [Shutdown]))

(define ProcessorMessage
  `(Union
    [Temp Nat (Addr (Union [Ok] [NotOk]))]
    [GetMean (Addr Nat)]
    [Enable]
    [Disable (Addr Nat)]))

(define ManagerMessage
  `(Union
    [NewProcessor (Addr (Addr ,ProcessorMessage))]
    [ShutdownAll]))

(define weather-program
 (desugar
  `(program (receptionists [manager ,ManagerMessage]) (externals)

(define-actor ,FullProcessorMessage (Processor)
  ()
  (goto On 0 0)
  (define-state (On [sum Nat] [num-rdgs Nat]) (m)
    (case m
      [(Temp t r)
       (send r (variant Ok))
       (goto On (+ sum t) (+ num-rdgs 1))]
      [(GetMean r)
       (send r (/ sum num-rdgs))
       (goto On sum num-rdgs)]
      [(Enable) (goto On sum num-rdgs)]
      [(Disable redir) (goto Off sum num-rdgs redir)]
      [(Shutdown) (goto Done)]))
  (define-state (Off [sum Nat] [num-rdgs Nat] [redir (Addr Nat)]) (m)
    (case m
      [(Temp t r)
       (send r (variant NotOk))
       (send redir t)
       (goto Off sum num-rdgs redir)]
      [(GetMean r)
       (send r (/ sum num-rdgs))
       (goto Off sum num-rdgs redir)]
      [(Enable) (goto On sum num-rdgs)]
      [(Disable new-redir)
       (goto Off sum num-rdgs new-redir)]
      [(Shutdown) (goto Done)]))
  (define-state (Done) (m) (goto Done)))

(define-actor ,ManagerMessage (Manager)
  ()
  (goto Managing (list))
  (define-state (Managing [processors (Listof (Addr ProcessorMessage))]) (m)
    (case m
      [(NewProcessor r)
       (let ([p (spawn P Processor)])
         (send r p)
         (goto Managing (cons p processors)))]
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

    ;; 2. Send it temp data, get OK
    (async-channel-put proc (variant Temp 90 client))
    (check-unicast client (variant Ok))

    ;; 3. Send it more temp data, get OK
    (async-channel-put proc (variant Temp 70 client))
    (check-unicast client (variant Ok))

    ;; 4. Get mean
    (async-channel-put proc (variant GetMean client))
    (check-unicast client 80)

    ;; 5. disable
    (define redir (make-async-channel))
    (async-channel-put proc (variant Disable redir))

    ;; 6. send it more temp data, get NotOk
    (async-channel-put proc (variant Temp 102 client))
    (check-unicast client (variant NotOk))
    (check-unicast redir 102)

    ;; 7. Get mean while disabled
    (async-channel-put proc (variant GetMean client))
    (check-unicast client 80)

    ;; 8. Enable, send more data, get OK
    (async-channel-put proc (variant Enable))
    (async-channel-put proc (variant Temp 50 client))
    (check-unicast client (variant Ok))

    ;; 9. Shutdown All
    (async-channel-put manager (variant ShutdownAll))
    (sleep 1)

    ;; 10. Ask for mean, no response
    (async-channel-put proc (variant GetMean client))
    (check-no-message client #:timeout 3))

  (define processor-spec-parts
    `((goto On)
      (define-state (On)
        [(variant Temp * r) -> ([obligation r (variant Ok)]) (goto On)]
        [(variant GetMean r) -> ([obligation r *]) (goto On)]
        [(variant Enable) -> () (goto On)]
        [(variant Disable r) -> () (goto Off r)]
        [unobs -> () (goto Shutdown)])
      (define-state (Off redir)
        [(variant Temp * r) ->
         ([obligation r (variant NotOk)]
          [obligation redir *])
         (goto Off redir)]
        [(variant GetMean r) -> ([obligation r *]) (goto Off redir)]
        [(variant Enable) -> () (goto On)]
        [(variant Disable r) -> () (goto Off r)]
        [unobs -> () (goto Shutdown)])
      (define-state (Shutdown)
        [(variant Temp * r) -> () (goto Shutdown)]
        [(variant GetMean r) -> () (goto Shutdown)]
        [(variant Enable) -> () (goto Shutdown)]
        [(variant Disable r) -> () (goto Shutdown)])))

  (define manager-spec
    `(specification (receptionists [manager ,ManagerMessage]) (externals)
       ([manager (Union [NewProcessor (Addr (Addr ,ProcessorMessage))])])
       ([manager (Union [ShutdownAll])])
       (goto Managing)
       (define-state (Managing)
         [(variant NewProcessor r) ->
          ([obligation r (delayed-fork ,@processor-spec-parts)])
          (goto Managing)])))

  (test-true "Weather program conforms to spec"
    (check-conformance weather-program manager-spec)))
