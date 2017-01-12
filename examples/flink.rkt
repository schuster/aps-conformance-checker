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
  (Map [initial-data (Listof String)] [partition-id Nat])
  (Reduce [left (Hash String Nat)] [right (Hash String Nat)]))

;; TODO: move this into some other definition
(define-variant MiscCommands
  (UpdateTaskExecutionState [job-id Nat] [task-id Nat] [state ExecutionState])
  (SubmitTask [job-id Nat] [task-id Nat] [info TaskInfo]))

(define-type TaskRunnerInput
  (Union
   ;; TODO: put other stuff here
   [SubmitTask Nat Nat TaskInfo]))


;; should track what task we're running, for cancellations and success reports
;;
;; Inputs:
;; * submit task
;; * cancel task
(define-actor TaskRunnerInput
  ;; TODO: add real types for job/task managers
  (TaskRunner [job-manager (Addr JobManagerInput)] [task-manager (Addr TaskManagerInput)])
  ()
  (goto AwaitingTask)
  (define-state (AwaitingTask) (m)
    (case m
      [(SubmitTask job-id task-id info)
       (goto AboutToRunTask job-id task-id info)]
      ;; TODO: other commands
      ))
  (define-state/timeout (AboutToRunTask [job-id Nat] [task-id Nat] [info TaskInfo]) (m)
    (case m
      [(SubmitTask new-job-id new-task-id new-info)
       ;; TODO: drop the existing task; presumably the task manager knows about it anyway
       (goto AboutToRunTask new-job-id new-task-id new-info)]
      ;; TODO: other commands
      )
    (timeout ,task-wait-time
      (case info
        ;; TODO: do the map case
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
           (goto AwaitingTask))]))))

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
;; (define-actor TaskManagerInput
;;   (TaskManager)
;;   ()
;;   (goto Running)
;;   (define-state (Running)))

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
;; * submit map task, go through process of getting more inputs, eventually succeed with right answer
;; * submit reduce task, get right input

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
    (async-channel-put runner (variant SubmitTask
                                       1
                                       1
                                       (variant Reduce
                                                (hash "a" 1 "b" 2 "c" 3)
                                                (hash "a" 3 "b" 4 "d" 5))))
    (check-unicast tm (variant UpdateTaskExecutionState
                               1
                               1
                               (variant Finished (hash "a" 4 "b" 6 "c" 3 "d" 5)))
                   #:timeout 3)))
