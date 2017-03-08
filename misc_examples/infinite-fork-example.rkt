#lang racket

(define prog
  `(program
    (receptionists [the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    (externals [init-ext-addr (Union [Fork (Addr Nat)] [Response])])
    (actors [the-actor (let ()
      (spawn 1
             (Addr (Union [Fork (Addr Nat)] [Response]))
             (goto Spawning init-ext-addr)
             (define-state (Spawning [init-ext-addr (Addr (Union [Fork (Addr Nat)] [Response]))]) (m)
               ;; this is where I *would* spawn and send back the new child, but in this example to
               ;; get the infinite behavior I don't do that
               (goto Spawning m))))])))

(define spec
  `(specification
    (receptionists [the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    (externals [init-ext-addr (Union [Fork (Addr Nat)] [Response])])
    ([the-actor (Addr (Union [Fork (Addr Nat)] [Response]))])
    ()
    (goto Forking init-ext-addr)
    (define-state (Forking prev-addr)
      [next-addr -> ([obligation
                      next-addr
                      (variant Fork
                               (fork (goto Responding prev-addr)
                                     (define-state (Responding a)
                                       [* -> ([obligation a (variant Response)]) (goto Responding a)])))])
                 (goto Forking next-addr)])))

(require "../main.rkt")
(check-conformance prog spec)
