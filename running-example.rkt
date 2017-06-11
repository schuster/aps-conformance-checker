#lang racket

;; A simple single-writer/multi-reader distributed database example. The client can either ask the
;; server to create a new table (giving the client exclusive write access), or ask it to find an
;; existing table for reading. The writer can then add entries to the table while the table actor is
;; in "write" mode, or switch it over to "read" mode so other clients can read from it.

(require "desugar.rkt")

(define TableCommand
  `(Union
    [Read
     String ; key
     (Addr (Union [Nothing] [Just String]))] ; response-dest
    [Write
     String ; key
     String ; values
     (Addr (Union [Written]))] ; response-dest
    [Edit]
    [Save]))

(define TableEditorCommand
  `(Union
    [Write String String (Addr (Union [Written]))]
    [Edit]
    [Save]))

(define TableReaderCommand
  `(Union
    [Read String (Addr (Union [Unavailable] [Nothing] [Just String]))]))

(define DirectoryRequest
  `(Union
    [Create
     String ; name
     (Addr (Union [AlreadyExists] [NewTable (Addr ,TableEditorCommand)]))] ; response-dest
    [Find
     String ; name
     (Addr (Union [Nothing] [Just (Addr ,TableReaderCommand)]))])) ; response-dest

(define ddb-program
(desugar
  `(program (receptionists [directory ,DirectoryRequest]) (externals)

(define-actor ,TableCommand (TableActor)
  ()
  (goto Editing (hash))
  (define-state/timeout (Editing [data (Hash String String)]) (m)
    (case m
      [(Read k r)
       (send r (variant Unavailable))
       (goto Editing data)]
      [(Write k v r)
       (send r (variant Written))
       (goto Editing (hash-set data k v))]
      [(Edit) (goto Editing data)]
      [(Save) (goto Reading data)])
    (timeout 5 (goto Reading data)))
  (define-state (Reading [data (Hash String String)]) (m)
    (case m
      [(Read k r)
       (send r (hash-ref data k))
       (goto Reading data)]
      [(Write k v r)
       ;; ignore writes in this state
       (goto Reading data)]
      [(Edit) (goto Editing data)]
      [(Save) (goto Reading data)])))

(define-actor ,DirectoryRequest (Directory)
  ()
  (goto Serving (hash))
  (define-state (Serving [tables (Hash String (Addr TableCommand))]) (req)
    (case req
      [(Create name r)
       (case (hash-ref tables name)
       [(Nothing)
        (let ([new-table (spawn 1 TableActor)])
          (send r (variant NewTable new-table))
          (goto Serving (hash-set tables name new-table)))]
       [(Just t)
        (send r (variant AlreadyExists))
        (goto Serving tables)])]
      [(Find name r)
       (send r (hash-ref tables name))
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
    ;; 1. create the table
    (define client (make-async-channel))
    (async-channel-put directory (variant Create "Authors" client))
    (define table (check-unicast-match client (csa-variant NewTable table) #:result table))

    ;; 3. write data x 2
    (async-channel-put table (variant Write "Moby Dick" "Melville" client))
    (check-unicast client (variant Written))
    (async-channel-put table (variant Write "To Kill a Mockingbird" "Lee" client))
    (check-unicast client (variant Written))

    ;; 4. find table
    (async-channel-put directory (variant Find "Authors" client))
    (define table2 (check-unicast-match client (csa-variant Just table2) #:result table2))

    ;; 6. get data (unavailable)
    (async-channel-put table2 (variant Read "Moby Dick" client))
    (check-unicast client (variant Unavailable))

    ;; 7. save
    (async-channel-put table (variant Save))

    ;; 8. get data
    (async-channel-put table2 (variant Read "Moby Dick" client))
    (check-unicast client (variant Just "Melville"))

    ;; 9. try to write; fail
    (async-channel-put table (variant Write "foo" "bar" client))
    (check-no-message client #:timeout 3)

    ;; 10. Get non-existent data
    (async-channel-put table (variant Read "foo" client))
    (check-unicast client (variant Nothing))

    ;; 11. edit possible after save
    (async-channel-put table (variant Edit))
    (async-channel-put table (variant Write "foo" "bar" client))
    (check-unicast client (variant Written)))

  (test-case "Timeout distributed database"
    (define directory (csa-run ddb-program))
    ;; 1. create the table
    (define client (make-async-channel))
    (async-channel-put directory (variant Create "Authors" client))
    (define table (check-unicast-match client (csa-variant NewTable table) #:result table))

    ;; 2. let the timeout elapse
    (sleep 6)

    ;; 4. try to write; fail
    (async-channel-put table (variant Write "foo" "bar" client))
    (check-no-message client #:timeout 3)))

;; ---------------------------------------------------------------------------------------------------
;; APS Specification

(define editable-table-behavior
  `((goto Writing)
    (define-state (Writing)
      [(variant Write * * r) -> ([obligation r (variant Written)]) (goto Writing)]
      [(variant Save) -> () (goto Reading)]
      [(variant Edit) -> () (goto Writing)]
      ;; might timeout and go back to Reading
      [unobs -> () (goto Reading)])
    (define-state (Reading)
      [(variant Write * * r) -> () (goto Reading)]
      [(variant Save) -> () (goto Reading)]
      [(variant Edit) -> () (goto Writing)])))

(define readable-table-behavior
  `((goto ReadingOrWriting)
    (define-state (ReadingOrWriting)
      [(variant Read * r) ->
       ([obligation r (or (variant Unavailable)
                          (variant Nothing)
                          (variant Just *))])
       (goto ReadingOrWriting)])))

(define directory-spec
  `(specification (receptionists [directory ,DirectoryRequest]) (externals)
     ([directory ,DirectoryRequest])
     ()
     (goto Serving)
     (define-state (Serving)
       [(variant Create * r) ->
        ([obligation r (or (variant AlreadyExists)
                           (variant NewTable (delayed-fork ,@editable-table-behavior)))])
        (goto Serving)]
       [(variant Find * r) ->
        ([obligation r (or (variant Nothing)
                           (variant Just (delayed-fork ,@readable-table-behavior)))])
        (goto Serving)])))

(module+ test
  (test-true "Running example conforms to spec"
    (check-conformance ddb-program directory-spec)))
