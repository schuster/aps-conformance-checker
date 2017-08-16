#lang racket

;; A CSA program that generates actors that take the running average of a stream of temperature
;; data. Intended for use as a motivating example for CSA and APS.

;; actor names: (Feed) Processor and Manager

(require "desugar.rkt")

(define ProcUserAPI
  `(Union
    [AddRdg Nat (Addr (Union [Ok] [NotOk]))]
    [GetMean]
    [Enable]
    [Disable]))

(define ManagerMessage
  `(Union
    [MakeProc (Addr (Addr ,ProcUserAPI)) (Addr Nat)]
    [ShutdownAll]))

(define ManagerUserAPI
  `(Union [MakeProc (Addr (Addr ,ProcUserAPI)) (Addr Nat)]))

(define ManagerSysAPI
  `(Union [ShutdownAll]))

(define weather-program
 (desugar
  `(program (receptionists [manager ,ManagerMessage]) (externals)

(define-actor
;; Processor's declared type
(Union [AddRdg Nat (Addr (Union [Ok] [NotOk]))]
       [GetMean]
       [Disable]
       [Enable]
       [Shutdown])

(Processor [mdest (Addr Nat)])
()

;; Initial state
(goto Off 0 0)

;; State definitions
(define-state (Off [sum Nat] [num-rdgs Nat]) (m)
  (case m
    [(AddRdg temp resp)
     (send resp (variant NotOk))
     (goto Off sum num-rdgs)]
    [(GetMean)
     (send mdest (/ sum num-rdgs))
     (goto Off sum num-rdgs)]
    [(Disable) (goto Off sum num-rdgs)]
    [(Enable) (goto On sum num-rdgs)]
    [(Shutdown) (goto Done)]))

(define-state (On [sum Nat] [num-rdgs Nat]) (m)
  (case m
    [(AddRdg temp resp)
     (send resp (variant Ok))
     (goto On (+ sum temp) (+ num-rdgs 1))]
    [(GetMean)
     (send mdest (/ sum num-rdgs))
     (goto On sum num-rdgs)]
    [(Disable) (goto Off sum num-rdgs)]
    [(Enable) (goto On sum num-rdgs)]
    [(Shutdown) (goto Done)]))

(define-state (Done) (m) (goto Done))
)

(define-type ProcAddr (Addr (Union [Shutdown])))

(define-actor ,ManagerMessage (Manager)
  ()
  (goto Managing (list))
  (define-state (Managing [processors (List ProcAddr)]) (m)
    (case m
      [(MakeProc resp mdest)
       (case (< (length processors) 100)
         [(True)
          (let ([p (spawn P Processor mdest)])
            (send resp p)
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
    (define mdest (make-async-channel))
    (async-channel-put manager (variant MakeProc client mdest))
    (define proc (check-unicast-match client p #:result p))

    ;; 2. Turn it on, send it temp data, get OK
    (async-channel-put proc (variant Enable))
    (async-channel-put proc (variant AddRdg 90 client))
    (check-unicast client (variant Ok))

    ;; 3. Send it more temp data, get OK
    (async-channel-put proc (variant AddRdg 70 client))
    (check-unicast client (variant Ok))

    ;; 4. Get mean
    (async-channel-put proc (variant GetMean))
    (check-unicast mdest 80)

    ;; 5. disable
    (async-channel-put proc (variant Disable))

    ;; 6. send it more temp data, get NotOk
    (async-channel-put proc (variant AddRdg 102 client))
    (check-unicast client (variant NotOk))

    ;; 7. Get mean while disabled
    (async-channel-put proc (variant GetMean))
    (check-unicast mdest 80)

    ;; 8. Enable, send more data, get OK
    (async-channel-put proc (variant Enable))
    (async-channel-put proc (variant AddRdg 50 client))
    (check-unicast client (variant Ok))

    ;; 9. Shutdown All
    (async-channel-put manager (variant ShutdownAll))
    (sleep 1)

    ;; 10. Ask for mean, no response
    (async-channel-put proc (variant GetMean))
    (check-no-message mdest #:timeout 3))

  (define processor-spec-parts
    `((goto Off mdest)

      (define-state (Off mdest)
        [(variant AddRdg * resp) -> ([obligation resp (variant NotOk)]) (goto Off mdest)]
        [(variant GetMean) -> ([obligation mdest *]) (goto Off mdest)]
        [(variant Disable) -> () (goto Off mdest)]
        [(variant Enable) -> () (goto On mdest)]
        [free -> () (goto Done)])

      (define-state (On mdest)
        [(variant AddRdg * resp) -> ([obligation resp (variant Ok)]) (goto On mdest)]
        [(variant GetMean) -> ([obligation mdest *]) (goto On mdest)]
        [(variant Disable) -> () (goto Off mdest)]
        [(variant Enable) -> () (goto On mdest)]
        [free -> () (goto Done)])

      (define-state (Done)
        [(variant AddRdg * resp) -> () (goto Done)]
        [(variant GetMean) -> () (goto Done)]
        [(variant Disable) -> () (goto Done)]
        [(variant Enable) -> () (goto Done)])))

  (define manager-spec
    `(specification (receptionists [manager ,ManagerMessage]) (externals)
       (obs-rec manager ,ManagerUserAPI ,ManagerSysAPI)
       (goto Managing)
       (define-state (Managing)
         [(variant MakeProc resp mdest) -> () (goto Managing)]
         [(variant MakeProc resp mdest) ->
          ([obligation resp (fork ,@processor-spec-parts)])
          (goto Managing)])))

  (test-true "Weather program conforms to spec"
    (check-conformance weather-program manager-spec)))
