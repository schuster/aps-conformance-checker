#lang racket

;; A simplified core of Apache Flink, used to implement a MapReduce-like structure for counting words
;; in documents

(define task-wait-time 1500) ; amount of time to wait before executing a task, to allow Cancel a
                             ; chance to happen

(define flink-definitions
  (quasiquote
(
(define-variant Boolean (True) (False))

(define-variant ExecutionState ; comes from runtime/execution/ExecutionState.java
  (Finished [result Nat])
  ;; TODO: the rest of the states
  )

(define-variant TaskInfo
  (Map [initial-data (Listof String)])
  (Reduce [left (Hash String Nat)] [right (Hash String Nat)]))

;; TODO: move this into some other definition
(define-variant MiscCommands
  (UpdateTaskExecutionState [job-id Nat] [task-id Nat] [state ExecutionState])
  (SubmitTask [job-id Nat] [task-id Nat] [info TaskInfo] [ack-dest (Addr (Union (Acknowledge Nat Nat)))])
  (RunTask [job-id Nat] [task-id Nat] [info TaskInfo])
  (RequestNextInputSplit [job-id Nat]
                         [task-id Nat]
                         [target (Addr (Union (NextInputSplit (Listof String))))])
  (NextInputSplit [items (Listof String)])
  ;; NOTE: this one is my own command, since the real Apache Flink cheats and uses threads to execute
  ;; tasks
  ;; TODO: fix this type
  (RegisterRunner [addr (Addr TaskRunnerInput)])
  (Acknowledge [job-id Nat] [task-id Nat]))

(define-type TaskRunnerInput
  (Union
   ;; TODO: put other stuff here
   [RunTask Nat Nat TaskInfo]))

(define-function (word-count-increment [h (Hash String Nat)] [word String])
  (hash-set h
            word
            (case (hash-ref h word)
              [(Nothing) 1]
              [(Just n) (+ n 1)])))

;; should track what task we're running, for cancellations and success reports
;;
;; Inputs:
;; * submit task
;; * cancel task
;; * more items
(define-actor TaskRunnerInput
  ;; TODO: add real types for job/task managers
  (TaskRunner [job-manager (Addr JobManagerInput)] [task-manager (Addr TaskManagerInput)])
  ((define-function (count-new-words [job-id Nat]
                                     [task-id Nat]
                                     [word-count (Hash String Nat)]
                                     [words (Listof String)])
     (let ([result-so-far
            (for/fold ([result word-count])
                      ([word words])
              (word-count-increment result word))])
       (send job-manager (RequestNextInputSplit job-id task-id self))
       (goto WaitingForNextSplit job-id task-id result-so-far))))
  ;; Can't send message from actor that starts at the start of the program, so we use a timeout-zero
  ;; state instead
  (goto AboutToRegister)
  (define-state/timeout (AboutToRegister)
    (m) (goto AboutToRegister) ; this shouldn't happen
    (timeout 0
      (send task-manager (RegisterRunner self))
      (goto AwaitingTask)))
  (define-state (AwaitingTask) (m)
    (case m
      [(RunTask job-id task-id info)
       (goto AboutToRunTask job-id task-id info)]
      ;; TODO: other commands
      ))
  (define-state/timeout (AboutToRunTask [job-id Nat] [task-id Nat] [info TaskInfo]) (m)
    (case m
      [(RunTask new-job-id new-task-id new-info)
       ;; TODO: drop the existing task; presumably the task manager knows about it anyway
       (goto AboutToRunTask new-job-id new-task-id new-info)]
      ;; TODO: other commands
      )
    (timeout ,task-wait-time
      (case info
        [(Map words) (count-new-words job-id task-id (hash) words)]
        [(Reduce left right)
         (let ([final-result
                (for/fold ([result left])
                          ([key (hash-keys right)])
                  (let ([left-value
                         (case (hash-ref result key)
                           ;; this case should never happen, but the type system will make us handle
                           ;; it anyway
                           [(Nothing) 0]
                           [(Just n) n])]
                        [right-value (case (hash-ref right key) [(Nothing) 0] [(Just n) n])])
                    (hash-set result key (+ left-value right-value))))])
           (send task-manager (UpdateTaskExecutionState job-id task-id (Finished final-result)))
           (goto AwaitingTask))])))
  (define-state (WaitingForNextSplit [job-id Nat] [task-id Nat] [word-count (Hash String Nat)]) (m)
    (case m
      ;; TODO: other commands
      [(NextInputSplit words)
       (case (list-as-variant words)
         [(Empty)
          (send task-manager (UpdateTaskExecutionState job-id task-id (Finished word-count)))
          (goto AwaitingTask)]
         [(Cons w ws) (count-new-words job-id task-id word-count words)])])))

(define-record BusyRunner
  [job-id Nat]
  [task-id Nat]
  ;; TODO: fix this type
  [addr (Addr TaskRunnerInput)])

;; Task manager inputs:
;; * submit task (respond with Acknowledge of Failure)
;; * CancelTask (respond with TaskOperationResult if okay, False if not)
;; * (internal) TriggerTaskManagerRegistration
;; * AcknowledgeRegistration
;; * AlreadyRegistered
;; * UpdateTaskExecutionState (from Task)
;;
;; The TaskManager comes with some number of TaskRunners, which are constant throughout its
;; lifetime. There would be as many TaskRunners as tehre are cores on the TaskManager's host, so that
;; each task has its own core to run on.

;; The TaskManager should record a list of infos about its TaskRunners, including their state and what
;; task they're working on
;;
;; TODO: put the real type here
(define-actor TaskManagerInput
  (TaskManager [job-manager (Addr JobManagerInput)])
  ()
  (goto Running (list) (list))
  ;; TODO: fix type on idle-runners
  (define-state (Running [idle-runners (Listof (Addr TaskRunnerInput))]
                         [busy-runners (Listof BusyRunner)]) (m)
    (case m
      [(RegisterRunner runner) (goto Running (cons runner idle-runners) busy-runners)]
      [(SubmitTask job-id task-id info ack-dest)
       (case (list-as-variant idle-runners)
         [(Empty)
          ;; TODO: figure out the failure message here
          ;; (send ack-dest (???))
          (goto Running idle-runners busy-runners)]
         [(Cons runner other-runners)
          (send runner (RunTask job-id task-id info))
          ;; NOTE: *almost* forgot the acknowledgment here, until I saw my old comment
          (send ack-dest (Acknowledge job-id task-id))
          (goto Running other-runners (cons (BusyRunner job-id task-id runner) busy-runners))])]
      [(UpdateTaskExecutionState job-id task-id state)
       ;; Remove the runner for this job ID and task ID
       (let ([new-runners
              (for/fold ([new-runners (record [idle idle-runners] [busy (list)])])
                        ([busy-runner busy-runners])
                (if (and (= job-id (: busy-runner job-id)) (= task-id (: busy-runner task-id)))
                    (record [idle (cons (: busy-runner addr) (: new-runners idle))]
                            [busy (: new-runners busy)])
                    (record [idle (: new-runners idle)]
                            [busy (cons busy-runner (: new-runners busy))])))])
         (send job-manager m)
         (goto Running (: new-runners idle) (: new-runners busy)))
       ;; NOTE: interesting question I want to ask here (during removal): can I ever have two runners
       ;; trying to run the exact same task? What if I tried to cancel it before, failed, then retried
       ;; and now I have two runners doing it?
       ])))

;; Job manager needs to track:
;; * running jobs, and their state (cancelled or not)
;; * running tasks, tasks waiting to go
;; * available partitions (remove them once they're done)
;; * registered task managers (maybe I do this part later... just assume static topology at first and deal with task managers later)
;; * available slots on task managers

;; So, Job Manager inputs:
;; * SubmitJob
;; * CancelJob
;; * Register task manager
;; * Heartbeat (maybe)
;; * TaskResult (UpdateTaskExecutionState)
;;   * this also triggers new consumers to be queued
;; * FreeSlot (whatever this is called in their system)
;; * RequestNextInputSplit
;; * timeouts?

;; (define-actor JobManagerInput
;;   (JobManager)
;;   ()
;;   (goto ManagingJobs)
;;   (define-state (ManagingJobs)))
)))

;; Tests to run/scenarios to complete:
;; * send job, it completes
;; * multiple jobs running at once
;; * cancel a job while running
;; * cancel a job after it completed
;; * task manager is lost while processing a task; task is restarted elsewhere
;; * lost task manager tries to send a result (maybe I don't need to deal with that level of reliability)
;; * task manager rejoins after being lost

;; Plan: successful path, then cancellation, then registration/deregistration

;; Tests for TaskRunner:
;; * submit then cancel (say, right after submission): make sure there's no result

(module+ test
  (require
   racket/async-channel
   (only-in csa record variant :)
   csa/eval
   csa/testing
   rackunit
   asyncunit
   "../desugar.rkt"
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (define task-runner-only-program
    (desugar
     ;; TODO: put real types here
     `(program (receptionists [task-runner Nat]) (externals [job-manager Nat] [task-manager Nat])
               ,@flink-definitions
               (actors [task-runner (spawn task-runner-loc TaskRunner job-manager task-manager)]))))
  (test-case "TaskRunner can complete a reduce task"
    (define jm (make-async-channel))
    (define tm (make-async-channel))
    (define runner (csa-run task-runner-only-program jm tm))
    ;; registration happens first
    (check-unicast-match tm (csa-variant RegisterRunner _))
    (async-channel-put runner (variant RunTask
                                       1
                                       1
                                       (variant Reduce
                                                (hash "a" 1 "b" 2 "c" 3)
                                                (hash "a" 3 "b" 4 "d" 5))))
    (check-unicast tm (variant UpdateTaskExecutionState
                               1
                               1
                               (variant Finished (hash "a" 4 "b" 6 "c" 3 "d" 5)))
                   #:timeout 3))

  (test-case "TaskRunner can complete a map task"
    (define jm (make-async-channel))
    (define tm (make-async-channel))
    (define runner (csa-run task-runner-only-program jm tm))
    ;; registration happens first
    (check-unicast-match tm (csa-variant RegisterRunner _))
    (async-channel-put runner (variant RunTask 1 1 (variant Map (list "a" "b" "b"))))
    (define split-target
      (check-unicast-match jm (csa-variant RequestNextInputSplit 1 1 target) #:result target #:timeout 3))
    (async-channel-put split-target (variant NextInputSplit (list "c" "a" "d")))
    (define split-target2
      (check-unicast-match jm (csa-variant RequestNextInputSplit 1 1 target) #:result target #:timeout 3))
    (async-channel-put split-target2 (variant NextInputSplit (list)))
    (check-unicast tm (variant UpdateTaskExecutionState
                               1
                               1
                               (variant Finished (hash "a" 2 "b" 2 "c" 1 "d" 1)))
                   #:timeout 3))

  (define task-manager-program
    (desugar
     ;; TODO: put real types here
     `(program (receptionists [task-manager Nat]) (externals [job-manager Nat])
               ,@flink-definitions
               (actors [task-manager (spawn task-manager-loc TaskManager job-manager)]
                       [task-runner1 (spawn runner1-loc TaskRunner job-manager task-manager)]
                       [task-runner2 (spawn runner2-loc TaskRunner job-manager task-manager)]))))

  (test-case "TaskManager can run three tasks to completion (waiting for TaskRunner completions)"
    (define jm (make-async-channel))
    (define task-manager (csa-run task-manager-program jm))
    (sleep 0.5) ; give some time for the TaskRunner registrations to happen first
    (async-channel-put task-manager (variant SubmitTask
                                             1
                                             1
                                             (variant Reduce
                                                      (hash "a" 1 "b" 2 "c" 3)
                                                      (hash "a" 3 "b" 4 "d" 5))
                                             jm))
    (check-unicast jm (variant Acknowledge 1 1))
    (async-channel-put task-manager (variant SubmitTask
                                             2
                                             1
                                             (variant Reduce
                                                      (hash "a" 1)
                                                      (hash "a" 3))
                                             jm))
    (check-unicast jm (variant Acknowledge 2 1))
    (define result1 (check-unicast-match jm result #:result result #:timeout 3))
    (define result2 (check-unicast-match jm result #:result result #:timeout 3))
    (check-equal? (set result1 result2)
                  (set (variant UpdateTaskExecutionState
                                1
                                1
                                (variant Finished (hash "a" 4 "b" 6 "c" 3 "d" 5)))
                       (variant UpdateTaskExecutionState
                                2
                                1
                                (variant Finished (hash "a" 4)))))
    (async-channel-put task-manager (variant SubmitTask 1 2 (variant Reduce (hash) (hash "b" 2)) jm))
    (check-unicast jm (variant Acknowledge 1 2))
    (check-unicast jm (variant UpdateTaskExecutionState
                               1
                               2
                               (variant Finished (hash "b" 2))) #:timeout 3)))

;; TODO: task manager responds with failure if it can't run a task right away
