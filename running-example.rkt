#lang racket

;; A simple distributed database example: the client can ask the directory actor for a particular
;; table, which the director provides (spawning an appropriate actor if it doesn't exist).

(require "desugar.rkt")

(define ddb-program
(desugar
  `(program (receptionists [directory DirectoryRequest]) (externals)

(define-variant TableCommand
  (Read [key String] [response-dest (Addr (Union [Nothing] [Just String]))])
  (Write [key String] [value String] [response-dest (Addr (Union [Written]))])
  (Lock [response-dest (Addr (Union [Unavailable] [Acquired]))])
  (Unlock))

(define-record DirectoryRequest
  [name String]
  [response-dest (Addr (Addr TableCommand))])

(define-actor TableCommand (TableActor)
  ()
  (goto Unlocked (hash))
  (define-state (Unlocked [data (Hash String String)]) (m)
    (case m
      [(Read k r)
       (send r (hash-ref data k))
       (goto Unlocked data)]
      [(Write k v r)
       ;; ignore writes in this state
       (goto Unlocked data)]
      [(Lock r)
       (send r (variant Acquired))
       (goto Locked data)]
      [(Unlock) (goto Unlocked data)]))
  (define-state/timeout (Locked [data (Hash String String)]) (m)
    (case m
      [(Read k r)
       (send r (hash-ref data k))
       (goto Locked data)]
      [(Write k v r)
       (send r (variant Written))
       (goto Locked (hash-set data k v))]
      [(Lock r)
       (send r (variant Unavailable))
       (goto Locked data)]
      [(Unlock) (goto Unlocked data)])
    (timeout 5 (goto Unlocked data))))

(define-actor DirectoryRequest (Directory)
  ()
  (goto Serving (hash))
  (define-state (Serving [tables (Hash String (Addr TableCommand))]) (req)
    (case (hash-ref tables (: req name))
      [(Nothing)
       (let ([new-table (spawn 1 TableActor)])
         (send (: req response-dest) new-table)
         (goto Serving (hash-set tables (: req name) new-table)))]
      [(Just t)
       (send (: req response-dest) t)
       (goto Serving tables)])))

(actors [directory (spawn 2 Directory)]))))

;; ---------------------------------------------------------------------------------------------------
;; Testing

(module+ test
  (require
   racket/async-channel
   asyncunit
   (only-in csa record variant)
   csa/eval
   csa/testing
   rackunit
   "main.rkt"))

(module+ test
  ;; Dynamic tests

  (test-case "Full test for distributed database"
    (define directory (csa-run ddb-program))
    ;; 1. get the table
    (define client (make-async-channel))
    (async-channel-put directory (record [name "Authors"] [response-dest client]))
    (define table (check-unicast-match client table #:result table))

    ;; 2. lock
    (async-channel-put table (variant Lock client))
    (check-unicast client (variant Acquired))

    ;; 3. write data x 2
    (async-channel-put table (variant Write "Moby Dick" "Melville" client))
    (check-unicast client (variant Written))
    (async-channel-put table (variant Write "To Kill a Mockingbird" "Lee" client))
    (check-unicast client (variant Written))

    ;; 4. get table again
    (async-channel-put directory (record [name "Authors"] [response-dest client]))
    (define table2 (check-unicast-match client table2 #:result table2))

    ;; 5. try to lock; fail
    (async-channel-put table2 (variant Lock client))
    (check-unicast client (variant Unavailable))

    ;; 6. get data
    (async-channel-put table (variant Read "Moby Dick" client))
    (check-unicast client (variant Just "Melville"))

    ;; 7. unlock
    (async-channel-put table (variant Unlock))

    ;; 8. get more data
    (async-channel-put table (variant Read "To Kill a Mockingbird" client))
    (check-unicast client (variant Just "Lee"))

    ;; 9. try to write; fail
    (async-channel-put table (variant Write "foo" "bar" client))
    (check-no-message client #:timeout 3)

    ;; 10. Get non-existent data
    (async-channel-put table (variant Read "foo" client))
    (check-unicast client (variant Nothing))

    ;; 11. relock possible after unlock
    (async-channel-put table (variant Lock client))
    (check-unicast client (variant Acquired)))

  (test-case "Timeout distributed database"
    (define directory (csa-run ddb-program))
    ;; 1. get the table
    (define client (make-async-channel))
    (async-channel-put directory (record [name "Authors"] [response-dest client]))
    (define table (check-unicast-match client table #:result table))

    ;; 2. lock
    (async-channel-put table (variant Lock client))
    (check-unicast client (variant Acquired))

    ;; 3. let the timeout elapse
    (sleep 6)

    ;; 4. try to write; fail
    (async-channel-put table (variant Write "foo" "bar" client))
    (check-no-message client #:timeout 3)))

;; ---------------------------------------------------------------------------------------------------
;; APS Specification

(define desugared-table-command
  `(Union
    [Read String (Addr (Union [Nothing] [Just String]))]
    [Lock (Addr (Union [Unavailable] [Acquired]))]
    [Unlock]
    [Write String String (Addr (Union [Written]))]))

(define desugared-directory-request
  `(Record
    [name String]
    [response-dest (Addr (Addr ,desugared-table-command))]))

(define table-spec-behavior
  `((goto Reading)
    (define-state (Reading)
      [(variant Read * r) -> ([obligation r (or (variant Nothing) (variant Just *))]) (goto Reading)]
      [(variant Write * * *) -> () (goto Reading)]
      [(variant Lock r) -> ([obligation r (variant Unavailable)]) (goto Reading)]
      [(variant Lock r) -> ([obligation r (variant Acquired)]) (goto Writing)]
      [(variant Unlock) -> () (goto Reading)])
    (define-state (Writing)
      [(variant Read * r) -> ([obligation r (or (variant Nothing) (variant Just *))]) (goto Writing)]
      [(variant Write * * r) -> ([obligation r (variant Written)]) (goto Writing)]
      [(variant Lock r) -> ([obligation r (variant Unavailable)]) (goto Writing)]
      [(variant Unlock) -> () (goto Reading)]
      ;; might timeout and go back to Reading
      [unobs -> () (goto Reading)])))

(define directory-spec
  `(specification (receptionists [directory ,desugared-directory-request]) (externals)
     ([directory ,desugared-directory-request])
     ()
     (goto Serving)
     (define-state (Serving)
       [(record [name *] [response-dest r]) ->
         ([obligation r (delayed-fork ,@table-spec-behavior)])
        (goto Serving)])))

(module+ test
  (test-true "Running example conforms to spec"
    (check-conformance ddb-program directory-spec)))
