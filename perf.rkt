#lang racket

;; Experimentations with speeding up the checker

(require
 redex/reduction-semantics
 "main.rkt"
 "csa.rkt"
 "aps.rkt")

;; ---------------------------------------------------------------------------------------------------
;; the code

(define forwarding-type (term (Record [result Nat] [dest (Addr Nat)])))

(define (make-down-and-back-server child-behavior)
  (term
   ((addr 0 (Addr Nat))
    (((define-state (Always [forwarding-server (Addr ,forwarding-type)]) (dest)
        (begin
          (spawn child-loc ,@child-behavior)
          (goto Always forwarding-server))))
     (goto Always (addr 1 ,forwarding-type))))))

(define self-send-forwarding-child
  (term
   (Nat
    (begin
      (send self 1)
      (goto AboutToSend forwarding-server))
    (define-state (AboutToSend [forwarding-server (Addr ,forwarding-type)]) (trigger)
      (begin
        (send forwarding-server (record [result 1] [dest dest]))
        (goto Done)))
    (define-state (Done) (dummy) (goto Done)))))

(define forwarding-server
  (term
   ((addr 1 (Record [result Nat] [dest (Addr Nat)]))
    (((define-state (ServerAlways) (rec)
        (begin
          (send (: rec dest) (: rec result))
          (goto ServerAlways))))
     (goto ServerAlways)))))

(define request-response-spec
  (term
   (((define-state (Always)
       [response-target -> (with-outputs ([response-target *]) (goto Always))]))
    (goto Always)
    (addr 0 (Addr Nat)))))

(check-conformance/config
 (make-empty-queues-config (list (make-down-and-back-server self-send-forwarding-child))
                           (list forwarding-server))
 (make-exclusive-spec request-response-spec))
