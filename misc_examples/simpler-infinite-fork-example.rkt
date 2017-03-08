#lang racket

(define prog
  `(program
    (receptionists [the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    (externals [fork-dest (Union [Fork (Addr Nat)] [Response])])
    (actors [the-actor (let ()
      (spawn 1
             (Addr (Union [Fork (Addr Nat)] [Response]))
             (goto Spawning fork-dest)
             (define-state (Spawning [fork-dest (Addr (Union [Fork (Addr Nat)] [Response]))]) (m)
               ;; this is where I *would* spawn and send back the new child, but in this example to
               ;; get the infinite behavior I don't do that
               (goto Spawning m))))])))

(define spec
  `(specification
    (receptionists [the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    (externals [fork-dest (Union [Fork (Addr Nat)] [Response])])
    ([the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    ()
    (goto Forking fork-dest)
    (define-state (Forking fork-dest)
      [next-addr -> ([obligation
                      fork-dest
                      (variant Fork
                               (fork (goto Responding next-addr)
                                     (define-state (Responding a)
                                       [* -> ([obligation a (variant Response)]) (goto Responding a)])))])
                 (goto Forking fork-dest)])))

(require "../main.rkt")
(check-conformance prog spec)
