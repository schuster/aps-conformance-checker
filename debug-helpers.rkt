#lang racket

(provide wrapped-call)

(define-syntax-rule (wrapped-call message e)
  (let ()
    (printf "in call: ~s\n" message)
    (define result e)
    (printf "finished call: ~s\n" message)
    result))
