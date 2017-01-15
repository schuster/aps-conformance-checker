#lang racket

;; A simplified core of Apache Flink, used to implement a MapReduce-like structure for counting words
;; in documents

(define task-wait-time 1500) ; amount of time to wait before executing a task, to allow Cancel a
                             ; chance to happen

(define partition-chunk-size 3)

(define flink-definitions
  (quasiquote
(
;; ---------------------------------------------------------------------------------------------------
;; Misc. Types

(define-variant Boolean (True) (False))

;;---------------------------------------------------------------------------------------------------
;; Math

(define-function (max [a Nat] [b Nat])
  (if (> a b) a b))

(define-function (min [a Nat] [b Nat])
  (if (< a b) a b))

;; ---------------------------------------------------------------------------------------------------
;; JobManager's Client-facing API

(define-variant TaskDescription
  (Map [data (Vectorof Nat)])
  (Reduce [left-task-id Nat] [right-task-id Nat]))

(define-record Task
  [id Nat]
  [type TaskDescription])

(define-record Job
  [id Nat]
  [tasks (Listof Task)]
  [final-task-id Nat])

;; ---------------------------------------------------------------------------------------------------
;; Type Aliases

(define-type TaskManagerId Nat) ; ideally this would be an opaque alias

;; ---------------------------------------------------------------------------------------------------
;; Internal State for JobManager

(define-record JobTaskId
  [job-id Nat]
  [task-id Nat])

(define-variant MaybeReduceData
  (WaitingOn [task-id JobTaskId])
  (Ready [data Nat]))

(define-record WaitingReduceTask
  [id JobTaskId]
  [left MaybeReduceData]
  [right MaybeReduceData])

(define-variant ReadyTaskWork
  (MapWork [initial-data (Vectorof String)])
  (ReduceWork [left (Hash String Nat)] [right (Hash String Nat)]))

;; A task with all of its required input data
(define-record ReadyTask
  [id JobTaskId]
  [work ReadyTaskWork])

;; A partition for a task with a pointer to the index to start sending from on the next
;; "RequestNextInputSpilt" (this index will be beyond the range of the vector once the data is
;; exhausted)
(define-record UsedPartition
  [data (Vectorof Nat)]
  [next-send Nat])

(define-record RunningTask
  [task-manager Nat]
  [type TaskExecutionType])

(define-record ManagedTaskManager
  ;; TODO: fix this type
  [addr (Addr TaskManagerInput)]
  [available-slots Nat])

;; Represents a task known to be running on the specified task manager
(define-record RunningTaskExecution
  [task ReadyTask]
  [task-manager TaskManagerId])

(define-record JobCompletionInfo
  [final-task-id Nat]
  [client (Addr Nat)])

;; ---------------------------------------------------------------------------------------------------

(define-variant ExecutionState ; comes from runtime/execution/ExecutionState.java
  (Finished [result (Hash String Nat)])
  ;; TODO: the rest of the states
  )

;; TODO: move this into some other definition
(define-variant MiscCommands
  ;; TODO: fix the type on RegisterTaskManager's addr
  (RegisterTaskManager [id Nat] [num-slots Nat] [addr (Addr TaskManagerInput)])
  (UpdateTaskExecutionState [id JobTaskId] [state ExecutionState])
  (SubmitTask [task ReadyTask] [ack-dest (Addr (Union [Acknowledge Nat Nat]))])
  (RunTask [task ReadyTask])
  (RequestNextInputSplit [id JobTaskId]
                         [target (Addr (Union [NextInputSplit (Vectorof String)]))])
  (NextInputSplit [items (Vectorof String)])
  ;; NOTE: this one is my own command, since the real Apache Flink cheats and uses threads to execute
  ;; tasks
  ;; TODO: fix this type
  (RegisterRunner [addr (Addr TaskRunnerInput)])
  (SubmitJob [job Job] [client (Addr (Hash String Nat))])

  ;; these two are responses to SubmitTask
  (Acknowledge [id JobTaskId])
  (Failure [id JobTaskId])

  ;; Response to RegisterTaskManager
  (AcknowledgeRegistration))

(define-type TaskRunnerInput
  (Union
   ;; TODO: put other stuff here
   [RunTask Nat Nat TaskExecutionType]))

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
  ((define-function (count-new-words [id JobTaskId]
                                     [word-count (Hash String Nat)]
                                     [words (Vectorof String)])
     (let ([result-so-far
            (for/fold ([result word-count])
                      ([word words])
              (word-count-increment result word))])
       (send job-manager (RequestNextInputSplit id self))
       (goto WaitingForNextSplit id result-so-far))))
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
      [(RunTask task)
       (goto AboutToRunTask task)]
      ;; TODO: other commands
      ))
  (define-state/timeout (AboutToRunTask [task ReadyTask]) (m)
    (case m
      [(RunTask new-task)
       ;; NOTE: drop the existing task; presumably the task manager knows about it anyway
       (goto AboutToRunTask new-task)]
      ;; TODO: other commands
      )
    (timeout ,task-wait-time
      (case (: task work)
        [(MapWork words) (count-new-words (: task id) (hash) words)]
        [(ReduceWork left right)
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
           (send task-manager (UpdateTaskExecutionState (: task id) (Finished final-result)))
           (goto AwaitingTask))])))
  (define-state (WaitingForNextSplit [id JobTaskId] [word-count (Hash String Nat)]) (m)
    (case m
      ;; TODO: other commands
      [(NextInputSplit words)
       (cond
         [(= 0 (vector-length words))
          (send task-manager (UpdateTaskExecutionState id (Finished word-count)))
          (goto AwaitingTask)]
         [else (count-new-words id word-count words)])])))

;; A runner currently running a task with the given ID
(define-record BusyRunner
  [id JobTaskId]
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
  (TaskManager [my-id Nat] [job-manager (Addr JobManagerInput)])
  ()
  (goto Init)
  (define-state/timeout (Init) (m)
    (goto Init)
    (timeout 0
      (send job-manager (RegisterTaskManager my-id 2 self))
      (goto AwaitingRegistration (list))))
  (define-state (AwaitingRegistration [idle-runners (Listof (Addr TaskRunnerInput))]) (m)
    (case m
      ;; TODO: other actions
      [(AcknowledgeRegistration) (goto Running idle-runners (list))]
      [(RegisterRunner runner) (goto AwaitingRegistration (cons runner idle-runners))]))

  ;; TODO: fix type on idle-runners
  (define-state (Running [idle-runners (Listof (Addr TaskRunnerInput))]
                         [busy-runners (Listof BusyRunner)]) (m)
    (case m
      [(AcknowledgeRegistration) (goto Running idle-runners busy-runners)]
      [(RegisterRunner runner) (goto Running (cons runner idle-runners) busy-runners)]
      [(SubmitTask task ack-dest)
       (case (list-as-variant idle-runners)
         [(Empty)
          (send ack-dest (Failure (: task id)))
          (goto Running idle-runners busy-runners)]
         [(Cons runner other-runners)
          (send runner (RunTask task))
          ;; NOTE: *almost* forgot the acknowledgment here, until I saw my old comment
          (send ack-dest (Acknowledge (: task id)))
          (goto Running other-runners (cons (BusyRunner (: task id) runner) busy-runners))])]
      [(UpdateTaskExecutionState id state)
       ;; Remove the runner for this job ID and task ID
       (let ([new-runners
              (for/fold ([new-runners (record [idle idle-runners] [busy (list)])])
                        ([busy-runner busy-runners])
                (if (= id (: busy-runner id))
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

;; TODO: add numeric IDs to task managers; put into registration message

(define-actor JobManagerInput
  (JobManager)
  (
   ;; Adds the given tasks for the given job to the waiting-tasks and ready-tasks lists as needed, as
   ;; well as the new data partitions
   (define-function (triage-submitted-tasks [job-id Nat]
                                            [tasks (Listof Task)]
                                            [waiting-tasks (Listof WatingReduceTask)]
                                            [ready-tasks (Listof ReadyTask)]
                                            [partitions (Hash JobTaskId UsedPartition)])
     (for/fold ([all-tasks (record [need-data waiting-tasks]
                                   [ready ready-tasks]
                                   [partitions partitions])])
               ([task tasks])
       (let ([full-id (JobTaskId job-id (: task id))])
         (case (: task type)
           [(Map data)
            (let ([partition-next-send (min ,partition-chunk-size (vector-length data))])
              (record [need-data (: all-tasks need-data)]
                      [ready (cons (ReadyTask full-id (MapWork (vector-take data partition-next-send)))
                                   (: all-tasks ready))]
                      [partitions
                       (hash-set (: all-tasks partitions)
                                 full-id
                                 (UsedPartition data partition-next-send))]))]
           [(Reduce left-id right-id)
            (record [need-data (cons (WaitingReduceTask full-id
                                                        (WaitingOn (JobTaskId job-id left-id))
                                                        (WaitingOn (JobTaskId job-id right-id)))
                                     (: all-tasks need-data))]
                    [ready (: all-tasks ready)]
                    [partitions (: all-tasks partitions)])]))))

   ;; Returns (Just id) for the id of a task manager with at least 1 open slot; Nothing if there is no
   ;; task manager with an open slot
   (define-function (find-available-slot [task-managers (Hash Nat ManagedTaskManager)])
     (for/fold ([result (variant Nothing)])
               ([id (hash-keys task-managers)])
       (case (hash-ref task-managers id)
         [(Nothing)
          ;; shouldn't happen
          result]
         [(Just m)
          ;; Note that this will always send the *last* slot available in the list
          (if (= (: m available-slots) 0)
              result
              (variant Just id))])))

   ;; Submits tasks from the ready tasks list for execution on task managers with available slots
   ;; until we run out of either slots or tasks
   (define-function (send-ready-tasks [task-managers (Hash Nat ManagedTaskManager)]
                                      ;; TODO: types
                                      [ready-tasks (Listof ReadyTask)]
                                      [running-tasks (Hash JobTaskId RunningTaskExecution)])
     (for/fold ([state (record [task-managers task-managers]
                               [unsent-tasks (list)]
                               [running-tasks running-tasks])])
               ([task ready-tasks])
       (case (find-available-slot (: state task-managers))
         [(Nothing)
          ;; no slot available, so have to wait
          (record [task-managers (: state task-managers)]
                  [unsent-tasks (cons task (: state unsent-tasks))]
                  [running-tasks (: state running-tasks)])]
         [(Just task-manager-id)
          (case (hash-ref (: state task-managers) task-manager-id)
            [(Nothing) ; shouldn't happen
             state]
            [(Just manager-record)
             (send (: manager-record addr) (SubmitTask task self))
             (let ([new-manager-record (ManagedTaskManager
                                        (: manager-record addr)
                                        (- (: manager-record available-slots) 1))])
               (record [task-managers (hash-set (: state task-managers) task-manager-id new-manager-record)]
                       [unsent-tasks (: state unsent-tasks)]
                       [running-tasks (hash-set (: state running-tasks)
                                                (: task id)
                                                (RunningTaskExecution task task-manager-id))]))])])))

   ;; Remove the task from the active jobs list and free up a slot on the TaskManager
   (define-function (deactivate-task [id JobTaskId]
                                     [task-managers (Hash Nat ManagedTaskManager)]
                                     [running-tasks (Hash JobTaskId RunningTaskExecution)])
     (case (hash-ref running-tasks id)
       [(Nothing)
        (record [task-managers task-managers] [running-tasks running-tasks])]
       [(Just execution)
        (case (hash-ref task-managers (: execution task-manager))
          ;; Might not be around anymore if the task manager was deregistered
          [(Nothing)
           (record [task-managers task-managers] [running-tasks (hash-remove running-tasks id)])]
          [(Just manager-record)
           (let ([new-record (ManagedTaskManager (: manager-record addr)
                                                 (+ 1 (: manager-record available-slots)))])
             (record [task-managers (hash-set task-managers
                                              (: execution task-manager)
                                              new-record)]
                     [running-tasks (hash-remove running-tasks id)]))])]))

   (define-function (maybe-populate-input [maybe-data MaybeReduceData]
                                          [id JobTaskId]
                                          [task-result (Hash String Nat)])
     (case maybe-data
       [(WaitingOn waiting-for-id)
        (if (= id waiting-for-id)
            (Ready task-result)
            maybe-data)]
       [(Ready data) maybe-data]))

   ;; Puts the result data into the tasks for any data that's waiting for it
   (define-function (push-to-consumer [id JobTaskId]
                                      [task-result (Hash String Nat)]
                                      [waiting-tasks (Listof WaitingTask)]
                                      [ready-tasks (Listof ReadyTask)])
     (for/fold ([result (record [waiting-tasks (list)] [ready-tasks ready-tasks])])
               ([waiting-task waiting-tasks])
       (let* ([new-left (maybe-populate-input (: waiting-task left) id task-result)]
              [new-right (maybe-populate-input (: waiting-task right) id task-result)]
              [new-waiting-task (WaitingReduceTask (: waiting-task id) new-left new-right)])
         (case new-left
           [(Ready left-data)
            (case new-right
              [(Ready right-data)
               (record [waiting-tasks (: result waiting-tasks)]
                       [ready-tasks (cons (ReadyTask (: waiting-task id) (ReduceWork left-data right-data))
                                          (: result ready-tasks))])]
              [(WaitingOn t)
               (record [waiting-tasks (cons new-waiting-task (: result waiting-tasks))]
                       [ready-tasks (: result ready-tasks)])])]
           [(WaitingOn t)
            (record [waiting-tasks (cons new-waiting-task (: result waiting-tasks))]
                    [ready-tasks (: result ready-tasks)])])))))

  (goto ManagingJobs (hash) (hash) (list) (list) (hash) (hash))

  ;; NOTE: I'm ignoring for now the ordering of waiting-tasks. In a real implementation it would use a
  ;; queue to avoid starvation of any tasks/jobs, but I'm making the simplifying assumption that that
  ;; won't be an issue in my uses
  (define-state (ManagingJobs
                 [task-managers-index (Hash Nat ManagedTaskManagerp)]
                 [active-jobs (Hash Nat JobCompletionInfo)]
                 ;; Tasks that are waiting on their input tasks to complete
                 [waiting-tasks (Listof WatingReduceTask)]
                 [ready-tasks (Listof ReadyTask)]
                 [running-tasks (Hash JobTaskId RunningTaskExecution)]
                 [partitions (Hash JobTaskId UsedPartition)]) (m)
    (case m
      [(RegisterTaskManager id slots addr)
       (send addr (AcknowledgeRegistration))
       (let* ([task-managers-index (hash-set task-managers-index id (ManagedTaskManager addr slots))]
              [submission-result (send-ready-tasks task-managers-index ready-tasks running-tasks)])
         (goto ManagingJobs
               (: submission-result task-managers)
               active-jobs
               waiting-tasks
               (: submission-result unsent-tasks)
               (: submission-result running-tasks)
               partitions))]
      [(SubmitJob job client)
       ;; TODO:
       ;; divide into tasks that can be done now and those that can't
       (let* ([triage-result (triage-submitted-tasks (: job id)
                                                     (: job tasks)
                                                     waiting-tasks
                                                     ready-tasks
                                                     partitions)]
              [submission-result (send-ready-tasks task-managers-index
                                                   (: triage-result ready)
                                                   running-tasks)])
         (goto ManagingJobs
               (: submission-result task-managers)
               (hash-set active-jobs (: job id) (JobCompletionInfo (: job final-task-id) client))
               (: triage-result need-data)
               (: submission-result unsent-tasks)
               (: submission-result running-tasks)
               (: triage-result partitions)))]
      [(Acknowledge id)
       (goto ManagingJobs task-managers-index active-jobs waiting-tasks ready-tasks running-tasks partitions)]
      [(RequestNextInputSplit id target)

       (let ([new-partitions
              (case (hash-ref partitions id)
                [(Nothing)
                 (send target (NextInputSplit (vector)))
                 partitions]
                [(Just partition)
                 (let* ([data (: partition data)]
                        [len (vector-length data)]
                        [next-send (: partition next-send)]
                        [num-items-to-send (min ,partition-chunk-size (- len next-send))])
                   (send target (NextInputSplit (vector-copy data next-send (+ next-send num-items-to-send))))
                   (hash-set partitions id (UsedPartition data (+ next-send num-items-to-send))))])])
         (goto ManagingJobs task-managers-index active-jobs waiting-tasks ready-tasks running-tasks new-partitions))]
      [(UpdateTaskExecutionState id state)
       ;; Remove the task from the running tasks list and free up a slot on the TaskManager
       (let* ([deactivate-result (deactivate-task id task-managers-index running-tasks)]
              [task-managers-index (: deactivate-result task-managers)]
              [running-tasks (: deactivate-result running-tasks)])
         (case state
           ;; TODO: other states
           [(Finished result)
            ;; 1. remove the partition
            (let* ([partitions (hash-remove partitions id)]
                   ;; 2. update any tasks that depended on this one, move them into ready if necessary
                   [push-result (push-to-consumer id result waiting-tasks ready-tasks)]
                   [waiting-tasks (: push-result waiting-tasks)]
                   [ready-tasks (: push-result ready-tasks)]
                   ;; 3. send more ready tasks
                   [submission-result (send-ready-tasks task-managers-index ready-tasks running-tasks)]
                   [task-managers-index (: submission-result task-managers)]
                   [ready-tasks (: submission-result unsent-tasks)]
                   [running-tasks (: submission-result running-tasks)])
              ;; 4. if job is finished: send result to client and remove from active jobs
              (case (hash-ref active-jobs (: id job-id))
                [(Nothing) ; could happen if this was a duplicate result or job was cancelled
                 (goto ManagingJobs task-managers-index active-jobs waiting-tasks ready-tasks running-tasks partitions)]
                [(Just job-info)
                 (cond
                   [(= (: id task-id) (: job-info final-task-id))
                    (send (: job-info client) result)
                    (goto ManagingJobs
                          task-managers-index
                          (hash-remove active-jobs (: id job-id))
                          waiting-tasks
                          ready-tasks
                          running-tasks
                          partitions)]
                   [else
                    (goto ManagingJobs
                          task-managers-index
                          active-jobs
                          waiting-tasks
                          ready-tasks
                          running-tasks
                          partitions)])]))]))]
      ;; TODO: other commands
      ;; TODO: remove partition when a task completes successfully (or when its task/job is cancelled)
      )
    ;; handle now: submit job, register, task result, free slot?, request next input

    ;; state:
    ;; remaininig partition data (hmm.. what if we restart a task?)
    ;; task managers: available slots
    ;; running jobs
    ;; running tasks? (at least need to be able to tell TMs to cancel tasks when user wants to cancel a job)

    ;; Job manager needs to track:
    ;; * running jobs, and their state (cancelled or not)
    ;; * running tasks, tasks waiting to go
    ;; * available partitions (remove them once they're done)
    ;; * registered task managers (maybe I do this part later... just assume static topology at first and deal with task managers later)
    ;; * available slots on task managers

    )))))

;; Tests to run/scenarios to complete:
;; * send job, it completes
;; * multiple jobs running at once
;; * cancel a job while running
;; * cancel a job after it completed
;; * task manager is lost while processing a task; task is restarted elsewhere
;; * lost task manager tries to send a result (maybe I don't need to deal with that level of reliability)
;; * task manager rejoins after being lost

;; Plan: successful path, then cancellation, then registration/deregistration

;; Idea: de-registration happens like this: we timeout if the task doesn't come back for a while. When that happens, we assume the task manager is dead (but don't try to kill its other tasks, because that's hard - we let them time out). Then we let it re-register (how does it know it needs to re-register? Hmm... Maybe it has to timeout on waiting for messages from the job manager. Interesting property: for *every* task from job manager, we reset the re-register timer)

;; Tests for TaskRunner:
;; * submit then cancel (say, right after submission): make sure there's no result

(module+ test
  (require
   racket/async-channel
   (only-in csa record variant :)
   (for-syntax syntax/parse)
   csa/eval
   csa/testing
   rackunit
   asyncunit
   "../desugar.rkt"
   "../main.rkt"

   ;; just to check that the desugared type is correct
   redex/reduction-semantics
   "../csa.rkt")

  (define (Job id tasks final-task-id) (record [id id] [tasks tasks] [final-task-id final-task-id]))
  (define (Task id type) (record [id id] [type type]))
  (define (Map data) (variant Map data))
  (define (Reduce left right) (variant Reduce left right))
  (define (JobTaskId job-id task-id) (record [job-id job-id] [task-id task-id]))
  (define (RunTask t) (variant RunTask t))
  (define (ReadyTask id work) (record [id id] [work work]))
  (define (MapWork initial-data) (variant MapWork initial-data))
  (define (ReduceWork left right) (variant ReduceWork left right))
  (define (SubmitJob job client) (variant SubmitJob job client))
  (define (AcknowledgeRegistration) (variant AcknowledgeRegistration))

  (define-match-expander JobTaskId/pat
    (lambda (stx)
      (syntax-parse stx
        [(_ job task)
         #`(csa-record [job-id job] [task-id task])])))

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
                                       (ReadyTask (JobTaskId 1 1)
                                                  (ReduceWork (hash "a" 1 "b" 2 "c" 3)
                                                              (hash "a" 3 "b" 4 "d" 5)))))
    (check-unicast tm (variant UpdateTaskExecutionState
                               (JobTaskId 1 1)
                               (variant Finished (hash "a" 4 "b" 6 "c" 3 "d" 5)))
                   #:timeout 3))

  (test-case "TaskRunner can complete a map task"
    (define jm (make-async-channel))
    (define tm (make-async-channel))
    (define runner (csa-run task-runner-only-program jm tm))
    ;; registration happens first
    (check-unicast-match tm (csa-variant RegisterRunner _))
    (async-channel-put runner (variant RunTask (ReadyTask (JobTaskId 1 1) (variant MapWork (list "a" "b" "b")))))
    (define split-target
      (check-unicast-match jm (csa-variant RequestNextInputSplit (JobTaskId/pat 1 1) target)
                           #:result target
                           #:timeout 3))
    (async-channel-put split-target (variant NextInputSplit (vector "c" "a" "d")))
    (define split-target2
      (check-unicast-match jm (csa-variant RequestNextInputSplit (JobTaskId/pat 1 1) target)
                           #:result target
                           #:timeout 3))
    (async-channel-put split-target2 (variant NextInputSplit (vector)))
    (check-unicast tm (variant UpdateTaskExecutionState
                               (JobTaskId 1 1)
                               (variant Finished (hash "a" 2 "b" 2 "c" 1 "d" 1)))
                   #:timeout 3))

  (define task-manager-program
    (desugar
     ;; TODO: put real types here
     `(program (receptionists [task-manager Nat]) (externals [job-manager Nat])
               ,@flink-definitions
               (actors [task-manager (spawn task-manager-loc TaskManager 1 job-manager)]
                       [task-runner1 (spawn runner1-loc TaskRunner job-manager task-manager)]
                       [task-runner2 (spawn runner2-loc TaskRunner job-manager task-manager)]))))

  (test-case "TaskManager can run three tasks to completion (waiting for TaskRunner completions)"
    (define jm (make-async-channel))
    (define task-manager (csa-run task-manager-program jm))
    (check-unicast-match jm (csa-variant RegisterTaskManager 1 2 _))
    (async-channel-put task-manager (AcknowledgeRegistration))
    (sleep 0.5) ; give some time for the TaskRunner registrations to happen first
    (async-channel-put task-manager (variant SubmitTask
                                             (ReadyTask
                                              (JobTaskId 1 1)
                                              (ReduceWork (hash "a" 1 "b" 2 "c" 3)
                                                          (hash "a" 3 "b" 4 "d" 5)))
                                             jm))
    (check-unicast jm (variant Acknowledge (JobTaskId 1 1)))
    (async-channel-put task-manager (variant SubmitTask (ReadyTask
                                                         (JobTaskId 2 1)
                                                         (ReduceWork
                                                          (hash "a" 1)
                                                          (hash "a" 3)))
                                             jm))
    (check-unicast jm (variant Acknowledge (JobTaskId 2 1)))
    (define result1 (check-unicast-match jm result #:result result #:timeout 3))
    (define result2 (check-unicast-match jm result #:result result #:timeout 3))
    (check-equal? (set result1 result2)
                  (set (variant UpdateTaskExecutionState
                                (JobTaskId 1 1)
                                (variant Finished (hash "a" 4 "b" 6 "c" 3 "d" 5)))
                       (variant UpdateTaskExecutionState
                                (JobTaskId 2 1)
                                (variant Finished (hash "a" 4)))))
    (async-channel-put task-manager (variant SubmitTask (ReadyTask (JobTaskId 1 2) (ReduceWork (hash) (hash "b" 2))) jm))
    (check-unicast jm (variant Acknowledge (JobTaskId 1 2)))
    (check-unicast jm (variant UpdateTaskExecutionState (JobTaskId 1 2)
                               (variant Finished (hash "b" 2))) #:timeout 3))

  (test-case "TaskManager fails a SubmitTask if it has no runners"
    (define task-manager-only-program
      (desugar
       ;; TODO: put real types here
       `(program (receptionists [task-manager Nat]) (externals [job-manager Nat])
                 ,@flink-definitions
                 (actors [task-manager (spawn task-manager-loc TaskManager 1 job-manager)]))))
    (define jm (make-async-channel))
    (define task-manager (csa-run task-manager-only-program jm))
    (check-unicast-match jm (csa-variant RegisterTaskManager 1 2 _))
    (async-channel-put task-manager (AcknowledgeRegistration))
    (async-channel-put task-manager (variant SubmitTask
                                             (ReadyTask (JobTaskId 1 1)
                                                        (ReduceWork (hash "a" 1 "b" 2 "c" 3)
                                                                    (hash "a" 3 "b" 4 "d" 5)))
                                             jm))
    (check-unicast jm (variant Failure (JobTaskId 1 1))))

  (test-case "TaskManager fails a SubmitTask if all its runners are busy"
    (define jm (make-async-channel))
    (define task-manager (csa-run task-manager-program jm))
    (check-unicast-match jm (csa-variant RegisterTaskManager 1 2 _))
    (async-channel-put task-manager (AcknowledgeRegistration))
    (sleep 0.5) ; give some time for the TaskRunner registrations to happen first
    (async-channel-put task-manager (variant SubmitTask
                                             (ReadyTask (JobTaskId 1 1)
                                                        (variant ReduceWork
                                                                 (hash "a" 1 "b" 2 "c" 3)
                                                                 (hash "a" 3 "b" 4 "d" 5)))
                                             jm))
    (async-channel-put task-manager (variant SubmitTask
                                             (ReadyTask (JobTaskId 1 2)
                                                        (variant ReduceWork
                                                                 (hash "a" 1 "b" 2 "c" 3)
                                                                 (hash "a" 3 "b" 4 "d" 5)))
                                             jm))
    (async-channel-put task-manager (variant SubmitTask
                                             (ReadyTask (JobTaskId 1 3)
                                                        (variant ReduceWork
                                                                 (hash "a" 1 "b" 2 "c" 3)
                                                                 (hash "a" 3 "b" 4 "d" 5)))
                                             jm))
    (check-unicast jm (variant Acknowledge (JobTaskId 1 1)))
    (check-unicast jm (variant Acknowledge (JobTaskId 1 2)))
    (check-unicast jm (variant Failure (JobTaskId 1 3))))

  (define job-manager-program
    (desugar
     ;; TODO: put real types on receptionists here
     `(program (receptionists [job-manager Nat]) (externals)
               ,@flink-definitions
               (actors [job-manager (spawn jm-loc JobManager)]
                       [task-manager1 (spawn task-manager1-loc TaskManager 1 job-manager)]
                       [task-manager2 (spawn task-manager2-loc TaskManager 2 job-manager)]
                       [task-runner1 (spawn runner1-loc TaskRunner job-manager task-manager1)]
                       [task-runner2 (spawn runner2-loc TaskRunner job-manager task-manager1)]
                       [task-runner3 (spawn runner3-loc TaskRunner job-manager task-manager2)]
                       [task-runner4 (spawn runner4-loc TaskRunner job-manager task-manager2)]))))

  (test-case "Job manager runs a job to completion"
    (define jm (csa-run job-manager-program))
    ;; 1. Wait for the task managers to register with the job manager
    (sleep 3)
    ;; 2. Submit the job
    (define job (Job 1
                     (list (Task 1 (Map (vector "a" "b" "c" "a" "b" "c")))
                           (Task 2 (Map (vector "a" "b")))
                           (Task 3 (Map (vector "a" "b")))
                           (Task 4 (Map (vector "a" "b")))
                           (Task 5 (Reduce 1 2))
                           (Task 6 (Reduce 3 4))
                           (Task 7 (Reduce 5 6)))
                     7))
    (define client (make-async-channel))
    (async-channel-put jm (SubmitJob job client))
    ;; 3. Wait for response
    (check-unicast client (hash "a" 5 "b" 5 "c" 2) #:timeout 30)))

;; Job manager: multiple jobs can be completed even when there are more tasks than TaskRunners
