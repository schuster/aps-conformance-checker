#lang racket

(require
 "desugar.rkt"
 "main.rkt"
 simple-workers
 racket/async-channel
 racket/runtime-path
 "examples/authenticated-session.rkt")

(define-runtime-path tasks-directory "eval_tasks")
(define-runtime-path output-directory "eval_output")

(define WAIT-TIME-IN-MILLISECONDS
  (* 1000 ; milliseconds/second
     60 ; seconds/minute
     60 ; minutes/hour
     24 ; 24 hours
     ))

(define NUM-WORKERS 16)

;; Returns a thunk that when run will run the given script file with the given optimizations for up to
;; WAIT-TIME-IN-MILLISECONDS. Any output generated (from stdout or stderr) is sent to a new output
;; file.
(define (make-job script-name widen? memoize? evict?)
  (lambda ()
    (unless (directory-exists? output-directory)
      (make-directory output-directory))

    (define output-file-name
      (format "~a_~a_~a_~a.txt"
              script-name
              (if widen? "widen" "nowiden")
              (if memoize? "memoize" "nomemoize")
              (if evict? "evict" "noevict")))

    (call-with-output-file* (build-path output-directory output-file-name)
      (lambda (output-port)
        (define script-args
          (append
           (if widen? (list "--widen") null)
           (if memoize? (list "--memoize") null)
           (if evict? (list "--evict") null)))

        (define cutoff-time (+ (current-inexact-milliseconds) WAIT-TIME-IN-MILLISECONDS))
        (define-values (proc in out err)
          (apply subprocess
                 output-port
                 #f
                 'stdout
                 (find-executable-path "racket")
                 (build-path tasks-directory script-name)
                 script-args))
        (sync proc (alarm-evt cutoff-time))
        (subprocess-kill proc #f)))))

(parameterize ([current-subprocess-custodian-mode 'interrupt])
  (define job-queue (make-async-channel))
  (for ([script (directory-list tasks-directory)])
    (async-channel-put job-queue (make-job script #t #t #t))
    (async-channel-put job-queue (make-job script #f #f #f))
    (async-channel-put job-queue (make-job script #f #t #t))
    (async-channel-put job-queue (make-job script #t #f #t)))

  ;; block until all jobs are complete
  (sync (start-workers NUM-WORKERS job-queue)))
