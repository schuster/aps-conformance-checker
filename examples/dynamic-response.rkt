#lang racket

;; A smaller example of the non-determinism problem in authN. The spec says that a given request
;; should get one of two possible resopnses. The program implements the spec by passing the request to
;; a second, internal actor, then responding to it. The problem is that in the abstract domain (and
;; sometimes even in the concrete domain, e.g. if the choice of response relies on data that changes
;; at run-time), the specification must choose which option to take before the program has made the
;; same decision. In this case, the specification will *always* lose, because the program always has
;; the option of taking the choice the spec did not take.

;; Unclear what the solution for this problem is, because modeling every possible choice in the spec
;; config seems unfeasible (although it would possibly simplify things... Am I already checking all of
;; these matches?). Maybe I should just punt on this issue.

(define request-type `(Addr (Union [A] [B])))

(define dynamic-response-program
  `(program
    (receptionists [input ,request-type])
    (externals)

    (define-actor ,request-type (Responder)
      ()
      (goto Always)
      (define-state (Always) r
        (send r (if (> 1 2) (variant A) (variant B)))
        (goto Always)))

    (define-actor ,request-type (InputWorker [responder (Addr ,request-type)])
      ()
      (goto Always)
      (define-state (Always) r
        (send responder r)
        (goto Always)))

    (let-actors ([responder (spawn 2 Responder)]
                 [input (spawn 1 InputWorker responder)])
      input)))

(define dynamic-response-spec
  `(specification (receptionists [input ,request-type]) (externals)
    (mon-receptionist input)
    (goto Always)
    (define-state (Always)
      [r -> ([obligation r (variant A)]) (goto Always)]
      [r -> ([obligation r (variant B)]) (goto Always)])))

(module+ test
  (require
   rackunit
   "../desugar.rkt"
   "../main.rkt")

  (test-true "Conformance for dynamic response program"
    (check-conformance (desugar dynamic-response-program) dynamic-response-spec)))
