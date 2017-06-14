#lang racket

;; A CSA program that generates actors that take the running average of a stream of temperature
;; data. Intended for use as a motivating example for CSA and APS.

;; actor names: (Feed) Processor and Manager

(require "desugar.rkt")

(define weather-program
 (desugar
  `(program (receptionists [manager ManagerMessage]) (externals)

(define-type ProcessorMessage
  (Union
   [Temp Nat (Addr (Union [Ok] [Off]))]
   [GetMean (Addr Nat)]
   [Enable]
   [Disable (Addr Nat)]
   [Shutdown]))

(define-actor ProcessorMessage (Processor)
  ()
  (goto Enabled 0 0)
  (define-state (Enabled [total Nat] [count Nat]) (m)
    (case m
      [(Temp t r)
       (send r (variant Ok))
       (goto Enabled (+ total t) (+ count 1))]
      [(GetMean r)
       (send r (/ total count))
       (goto Enabled total count)]
      [(Enable) (goto Enabled total count)]
      [(Disable redirect) (goto Disabled total count redirect)]
      [(Shutdown) (goto Shutdown)]))
  (define-state (Disabled [total Nat] [count Nat] [redirect (Addr Nat)]) (m)
    (case m
      [(Temp t r)
       (send r (variant Off))
       (send redirect t)
       (goto Disabled total count redirect)]
      [(GetMean r)
       (send r (/ total count))
       (goto Disabled total count redirect)]
      [(Enable) (goto Enabled total count)]
      [(Disable new-redirect)
       (goto Disabled total count new-redirect)]
      [(Shutdown) (goto Shutdown)]))
  (define-state (Shutdown) (m) (goto Shutdown)))

(define-type ManagerMessage
  (Union
   [NewProcessor (Addr (Addr ProcessorMessage))]
   [ShutdownAll]))

(define-actor ManagerMessage (Manager)
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
    (define redirect (make-async-channel))
    (async-channel-put proc (variant Disable redirect))

    ;; 6. send it more temp data, get Off
    (async-channel-put proc (variant Temp 102 client))
    (check-unicast client (variant Off))
    (check-unicast redirect 102)

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
    (check-no-message client #:timeout 3)))
