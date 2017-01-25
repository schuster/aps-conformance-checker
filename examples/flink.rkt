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

(define-variant JobResult
  (JobResultSuccess [result (Hash String Nat)])
  (JobResultFailure))

(define-variant CancellationResult
  (CancellationSuccess)
  (CancellationFailure))

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
;; "RequestNextInputSplit" (this index will be beyond the range of the vector once the data is
;; exhausted)
(define-record UsedPartition
  [data (Vectorof Nat)]
  [next-send Nat])

(define-record ManagedTaskManager
  [address (Addr TaskManagerCommand)]
  [available-slots Nat])

;; Represents a task known to be running on the specified task manager
(define-record RunningTaskExecution
  [task ReadyTask]
  [task-manager TaskManagerId])

(define-record JobCompletionInfo
  [final-task-id Nat]
  [client (Addr JobResult)])

;; ---------------------------------------------------------------------------------------------------
;; JobManager -> TaskManager Communication

(define-variant ExecutionState ; comes from runtime/execution/ExecutionState.java
  (Finished [result (Hash String Nat)])
  (Cancelled))

(define-type CancelResponse
  (Union
   (Acknowledge JobTaskId)
   (Failure JobTaskId)))

(define-type SubmitCancelResponse
  (Union
   (Acknowledge JobTaskId)
   (Failure JobTaskId)))

(define-type TaskManagerCommand
  (Union
   [AcknowledgeRegistration]
   [SubmitTask ReadyTask (Addr SubmitCancelResponse)]
   [CancelTask JobTaskId (Addr SubmitCancelResponse)]))

;; ---------------------------------------------------------------------------------------------------
;; TaskRunner -> JobManager Communication

(define-type InputSplitRequest
  (Union
   [RequestNextInputSplit JobTaskId (Addr (Union [NextInputSplit (Vectorof String)]))]))

;; ---------------------------------------------------------------------------------------------------
;; TaskRunner -> TaskManager Communication

(define-type TaskManagerNotification
  (Union
   [RegisterRunner (Addr TaskRunnerInput)]
   [UpdateTaskExecutionState JobTaskId ExecutionState]))

;; ---------------------------------------------------------------------------------------------------
;; TaskManager -> TaskRunner Communication

(define-type RunnerCommand
  (Union
   [RunTask ReadyTask]
   [CancelRunnerTask JobTaskId]))

;; ---------------------------------------------------------------------------------------------------
;; TaskManager -> JobManager Communication

(define-type TaskManagerToJobManager
  (Union
   [RegisterTaskManager Nat Nat (Addr TaskManagerCommand)]
   [UpdateTaskExecutionState JobTaskId ExecutionState]))

;; ---------------------------------------------------------------------------------------------------
;; Actor Input Types

(define-variant TaskRunnerInput
  (RunTask [task ReadyTask])
  (CancelRunnerTask [id JobTaskId])
  (NextInputSplit [items (Vectorof String)]))

(define-variant TaskManagerInput
  (AcknowledgeRegistration)
  (RegisterRunner [address (Addr TaskRunnerInput)])
  (SubmitTask [task ReadyTask] [ack-dest (Addr (Addr SubmitCancelResponse))])
  (CancelTask [id JobTaskId] [ack-dest (Addr (Addr SubmitCancelResponse))])
  (UpdateTaskExecutionState [id JobTaskId] [state ExecutionState])
  ;; DeathWatch message (models the Terminated messages generated by the Akka framework)
  (JobManagerTerminated))

(define-variant JobManagerInputVariant
  (RegisterTaskManager [id Nat] [num-slots Nat] [address (Addr TaskManagerCommand)])
  (RequestNextInputSplit [id JobTaskId]
                         [target (Addr (Union [NextInputSplit (Vectorof String)]))])
  (SubmitJob [job Job] [client (Addr JobResult)])
  (CancelJob [id Nat] [result-dest (Addr CancellationResult)])
  ;; these two are responses to SubmitTask
  (Acknowledge [id JobTaskId])
  (Failure [id JobTaskId])
  ;; UpdateTaskExecutionState would also be in here, if not for it being defined in TaskManagerInput

  ;; DeathWatch message (models the Terminated messages generated by the Akka framework)
  (TaskManagerTerminated [id TaskManagerId]))

(define-type JobManagerInput
  (Union
   (RegisterTaskManager Nat Nat (Addr TaskManagerCommand))
   (SubmitJob Job (Addr JobResult))
   (Acknowledge JobTaskId)
   (Failure JobTaskId)
   (RequestNextInputSplit JobTaskId (Addr (Union [NextInputSplit (Vectorof String)])))
   (UpdateTaskExecutionState JobTaskId ExecutionState)
   (TaskManagerTerminated TaskManagerId)
   (CancelJob Nat (Addr CancellationResult))))

;; ---------------------------------------------------------------------------------------------------
;; TaskRunner

(define-function (word-count-increment [h (Hash String Nat)] [word String])
  (hash-set h
            word
            (case (hash-ref h word)
              [(Nothing) 1]
              [(Just n) (+ n 1)])))

(define-actor TaskRunnerInput
  (TaskRunner [job-manager (Addr InputSplitRequest)] [task-manager (Addr TaskManagerNotification)])
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
      [(CancelRunnerTask id) (goto AwaitingTask)]
      [(NextInputSplit items) (goto AwaitingTask)]))
  (define-state/timeout (AboutToRunTask [task ReadyTask]) (m)
    (case m
      [(RunTask new-task)
       ;; drop the existing task; presumably the task manager knows about it anyway
       (goto AboutToRunTask new-task)]
      [(CancelRunnerTask to-cancel-id)
       (cond
         [(= to-cancel-id (: task id))
          (send task-manager (UpdateTaskExecutionState to-cancel-id (Cancelled)))
          (goto AwaitingTask)]
         [else (goto AboutToRunTask task)])]
      [(NextInputSplit items) (goto AboutToRunTask task)])
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
      [(RunTask task)
       ;; drop the current task and notify the task manager
       (send task-manager (UpdateTaskExecutionState id (Cancelled)))
       (goto AboutToRunTask task)]
      [(NextInputSplit words)
       (cond
         [(= 0 (vector-length words))
          (send task-manager (UpdateTaskExecutionState id (Finished word-count)))
          (goto AwaitingTask)]
         [else (count-new-words id word-count words)])]
      [(CancelRunnerTask to-cancel-id)
       (cond
         [(= to-cancel-id id)
          (send task-manager (UpdateTaskExecutionState id (Cancelled)))
          (goto AwaitingTask)]
         [else (goto WaitingForNextSplit id word-count)])])))

;; ---------------------------------------------------------------------------------------------------
;; TaskManager Internal State

;; A runner currently running a task with the given ID
(define-record BusyRunner
  [id JobTaskId]
  [address (Addr RunnerCommand)])

;; ---------------------------------------------------------------------------------------------------
;; TaskManager

;; The TaskManager comes with some number of TaskRunners, which are constant throughout its
;; lifetime. There would be as many TaskRunners as there are cores on the TaskManager's host, so that
;; each task has its own core to run on.
(define-actor TaskManagerInput
  (TaskManager [my-id Nat] [job-manager (Addr TaskManagerToJobManager)])
  ()
  (goto Init)
  (define-state/timeout (Init) (m)
    (goto Init)
    (timeout 0
      (send job-manager (RegisterTaskManager my-id 2 self))
      (goto AwaitingRegistration (list))))
  (define-state/timeout (AwaitingRegistration [idle-runners (Listof (Addr TaskRunnerInput))]) (m)
    (case m
      [(AcknowledgeRegistration) (goto Running idle-runners (list))]
      [(RegisterRunner runner) (goto AwaitingRegistration (cons runner idle-runners))]
      [(SubmitTask task ack-dest)
       (send ack-dest (Failure (: task id)))
       (goto AwaitingRegistration idle-runners)]
      [(CancelTask id ack-dest)
       (send ack-dest (Failure id))
       (goto AwaitingRegistration idle-runners)]
      [(UpdateTaskExecutionState id state)
       ;; might happen if we got disconnected but the runners were still running
       (goto AwaitingRegistration idle-runners)]
      [(JobManagerTerminated) (goto AwaitingRegistration idle-runners)])
    (timeout 5000
      (send job-manager (RegisterTaskManager my-id 2 self))
      (goto AwaitingRegistration idle-runners)))
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
      [(CancelTask id ack-dest)
       (send ack-dest (Acknowledge id))
       (for/fold ([dummy 0])
                 ([busy-runner busy-runners])
         (cond
           [(= id (: busy-runner id))
            (send (: busy-runner address) (CancelRunnerTask id))
            0]
           [else 0]))
       (goto Running idle-runners busy-runners)]
      [(UpdateTaskExecutionState id state)
       ;; Remove the runner for this job ID and task ID
       (let ([new-runners
              (for/fold ([new-runners (record [idle idle-runners] [busy (list)])])
                        ([busy-runner busy-runners])
                (if (= id (: busy-runner id))
                    (record [idle (cons (: busy-runner address) (: new-runners idle))]
                            [busy (: new-runners busy)])
                    (record [idle (: new-runners idle)]
                            [busy (cons busy-runner (: new-runners busy))])))])
         (send job-manager m)
         (goto Running (: new-runners idle) (: new-runners busy)))
       ;; NOTE: interesting question I want to ask here (during removal): can I ever have two runners
       ;; trying to run the exact same task? What if I tried to cancel it before, failed, then retried
       ;; and now I have two runners doing it?
       ]
      [(JobManagerTerminated)
       (let ([idle-runners
              (for/fold ([idle-runners idle-runners])
                        ([busy-runner busy-runners])
                (send (: busy-runner address) (CancelRunnerTask (: busy-runner id)))
                (cons (: busy-runner address) idle-runners))])
         (send job-manager (RegisterTaskManager my-id 2 self))
         (goto AwaitingRegistration idle-runners))])))

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
                                      [ready-tasks (Listof ReadyTask)]
                                      [running-tasks (Hash JobTaskId RunningTaskExecution)])
     (for/fold ([state (record [task-managers task-managers]
                               [remaining-ready-tasks ready-tasks]
                               [running-tasks running-tasks])])
               ([task ready-tasks])
       (case (find-available-slot (: state task-managers))
         [(Nothing)
          ;; no slot available, so have to wait
          (record [task-managers (: state task-managers)]
                  [remaining-ready-tasks (: state remaining-ready-tasks)]
                  [running-tasks (: state running-tasks)])]
         [(Just task-manager-id)
          (case (hash-ref (: state task-managers) task-manager-id)
            [(Nothing) ; shouldn't happen
             state]
            [(Just manager-record)
             (send (: manager-record address) (SubmitTask task self))
             (let ([new-manager-record (ManagedTaskManager
                                        (: manager-record address)
                                        (- (: manager-record available-slots) 1))])
               (record [task-managers (hash-set (: state task-managers) task-manager-id new-manager-record)]
                       [remaining-ready-tasks (remove task (: state remaining-ready-tasks))]
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
           (let ([new-record (ManagedTaskManager (: manager-record address)
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
     (for/fold ([result (record [waiting-tasks waiting-tasks] [ready-tasks ready-tasks])])
               ([waiting-task waiting-tasks])
       (let* ([waiting-tasks (remove waiting-task (: result waiting-tasks))]
              [new-left (maybe-populate-input (: waiting-task left) id task-result)]
              [new-right (maybe-populate-input (: waiting-task right) id task-result)]
              [new-waiting-task (WaitingReduceTask (: waiting-task id) new-left new-right)])
         (case new-left
           [(Ready left-data)
            (case new-right
              [(Ready right-data)
               (record [waiting-tasks waiting-tasks]
                       [ready-tasks (cons (ReadyTask (: waiting-task id) (ReduceWork left-data right-data))
                                          (: result ready-tasks))])]
              [(WaitingOn t)
               (record [waiting-tasks (cons new-waiting-task waiting-tasks)]
                       [ready-tasks (: result ready-tasks)])])]
           [(WaitingOn t)
            (record [waiting-tasks (cons new-waiting-task waiting-tasks)]
                    [ready-tasks (: result ready-tasks)])]))))

   (define-function (reset-partition [partitions (Hash JobTaskId UsedPartition)] [task-id JobTaskId])
     (case (hash-ref partitions task-id)
       [(Nothing) partitions]
       [(Just partition)
        (hash-set partitions
                  task-id
                  (UsedPartition (: partition data)
                                 (min ,partition-chunk-size (vector-length (: partition data)))))])))

  (goto ManagingJobs (hash) (hash) (list) (list) (hash) (hash))

  ;; NOTE: I'm ignoring for now the ordering of waiting-tasks. In a real implementation it would use a
  ;; queue to avoid starvation of any tasks/jobs, but I'm making the simplifying assumption that that
  ;; won't be an issue in my uses
  (define-state (ManagingJobs
                 [task-managers (Hash Nat ManagedTaskManager)]
                 [active-jobs (Hash Nat JobCompletionInfo)]
                 ;; Tasks that are waiting on their input tasks to complete
                 [waiting-tasks (Listof WatingReduceTask)]
                 [ready-tasks (Listof ReadyTask)]
                 [running-tasks (Hash JobTaskId RunningTaskExecution)]
                 [partitions (Hash JobTaskId UsedPartition)]) (m)
    (case m
      [(RegisterTaskManager id slots address)
       (send address (AcknowledgeRegistration))
       (let* ([task-managers (hash-set task-managers id (ManagedTaskManager address slots))]
              [submission-result (send-ready-tasks task-managers ready-tasks running-tasks)])
         (goto ManagingJobs
               (: submission-result task-managers)
               active-jobs
               waiting-tasks
               (: submission-result remaining-ready-tasks)
               (: submission-result running-tasks)
               partitions))]
      [(SubmitJob job client)
       (let* ([triage-result (triage-submitted-tasks (: job id)
                                                     (: job tasks)
                                                     waiting-tasks
                                                     ready-tasks
                                                     partitions)]
              [submission-result (send-ready-tasks task-managers
                                                   (: triage-result ready)
                                                   running-tasks)])
         (goto ManagingJobs
               (: submission-result task-managers)
               (hash-set active-jobs (: job id) (JobCompletionInfo (: job final-task-id) client))
               (: triage-result need-data)
               (: submission-result remaining-ready-tasks)
               (: submission-result running-tasks)
               (: triage-result partitions)))]
      ;; My implementation doesn't actually do anything with acknowldgments adn failures, for now
      [(Acknowledge id)
       (goto ManagingJobs task-managers active-jobs waiting-tasks ready-tasks running-tasks partitions)]
      [(Failure id)
       (goto ManagingJobs task-managers active-jobs waiting-tasks ready-tasks running-tasks partitions)]
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
         (goto ManagingJobs task-managers active-jobs waiting-tasks ready-tasks running-tasks new-partitions))]
      [(UpdateTaskExecutionState id state)
       ;; Remove the task from the running tasks list and free up a slot on the TaskManager
       (let* ([deactivate-result (deactivate-task id task-managers running-tasks)]
              [task-managers (: deactivate-result task-managers)]
              [running-tasks (: deactivate-result running-tasks)])
         (case state
           [(Finished result)
            ;; 1. remove the partition
            (let* ([partitions (hash-remove partitions id)]
                   ;; 2. update any tasks that depended on this one, move them into ready if necessary
                   [push-result (push-to-consumer id result waiting-tasks ready-tasks)]
                   [waiting-tasks (: push-result waiting-tasks)]
                   [ready-tasks (: push-result ready-tasks)]
                   ;; 3. send more ready tasks
                   [submission-result (send-ready-tasks task-managers ready-tasks running-tasks)]
                   [task-managers (: submission-result task-managers)]
                   [ready-tasks (: submission-result remaining-ready-tasks)]
                   [running-tasks (: submission-result running-tasks)])
              ;; 4. if job is finished: send result to client and remove from active jobs
              (case (hash-ref active-jobs (: id job-id))
                [(Nothing) ; could happen if this was a duplicate result or job was cancelled
                 (goto ManagingJobs task-managers active-jobs waiting-tasks ready-tasks running-tasks partitions)]
                [(Just job-info)
                 (cond
                   [(= (: id task-id) (: job-info final-task-id))
                    (send (: job-info client) (JobResultSuccess result))
                    (goto ManagingJobs
                          task-managers
                          (hash-remove active-jobs (: id job-id))
                          waiting-tasks
                          ready-tasks
                          running-tasks
                          partitions)]
                   [else
                    (goto ManagingJobs
                          task-managers
                          active-jobs
                          waiting-tasks
                          ready-tasks
                          running-tasks
                          partitions)])]))]
           [(Cancelled)
            ;; we would have already removed all other items related to the task, so we don't need to
            ;; do anything else
            (goto ManagingJobs
                  task-managers
                  active-jobs
                  waiting-tasks
                  ready-tasks
                  running-tasks
                  (reset-partition partitions id))]))]
      [(TaskManagerTerminated task-manager-id)
       (let* ([task-managers (hash-remove task-managers task-manager-id)]
              [move-result
               (for/fold ([result (record [ready-tasks ready-tasks]
                                          [running-tasks running-tasks]
                                          [partitions partitions])])
                         ([execution (hash-values running-tasks)])
                 (cond
                   [(= (: execution task-manager) task-manager-id)
                    (let* ([task (: execution task)]
                           [task-id (: task id)])
                      ;; move the task from running-tasks to ready-tasks and reset its partition
                      (record [ready-tasks (cons task (: result ready-tasks))]
                              [running-tasks (hash-remove (: result running-tasks) task-id)]
                              [partitions (reset-partition partitions task-id)]))]
                   [else result]))]
              [ready-tasks (: move-result ready-tasks)]
              [running-tasks (: move-result running-tasks)]
              [partitions (: move-result partitions)]
              ;; Try to resend the ready tasks
              [submission-result (send-ready-tasks task-managers ready-tasks running-tasks)])
         (goto ManagingJobs
               (: submission-result task-managers)
               active-jobs
               waiting-tasks
               (: submission-result remaining-ready-tasks)
               (: submission-result running-tasks)
               partitions))]
      [(CancelJob id-to-cancel result-dest)
       (case (hash-ref active-jobs id-to-cancel)
         [(Nothing)
          (send result-dest (CancellationFailure))
          (goto ManagingJobs task-managers active-jobs waiting-tasks ready-tasks running-tasks partitions)]
         [(Just job-info)
          ;; 1. Cancel running tasks
          (let* ([run-remove-result
                  (for/fold ([result (record [task-managers task-managers]
                                             [running-tasks running-tasks])])
                            ([execution (hash-values running-tasks)])
                    (let ([task-id (: (: execution task) id)])
                      (cond
                        [(= (: task-id job-id) id-to-cancel)
                         (record [task-managers
                                  (case (hash-ref (: result task-managers) (: execution task-manager))
                                    [(Nothing) (: result task-managers)]
                                    [(Just m)
                                     (send (: m address) (CancelTask task-id self))
                                     (hash-set (: result task-managers)
                                               (: execution task-manager)
                                               (ManagedTaskManager (: m address) (+ (: m available-slots) 1)))])
                                  ]
                                 [running-tasks (hash-remove running-tasks task-id)])]
                        [else result])))]
                 [task-managers (: run-remove-result task-managers)]
                 [running-tasks (: run-remove-result running-tasks)]
                 ;; 2. Clear partitions
                 [partitions
                  (for/fold ([remaining-partitions partitions])
                            ([key (hash-keys partitions)])
                    (if (= (: key job-id) id-to-cancel)
                        (hash-remove remaining-partitions key)
                        remaining-partitions))]
                 ;; 3. Remove ready tasks
                 [ready-tasks
                  (for/fold ([ready-tasks ready-tasks])
                            ([ready-task ready-tasks])
                    (if (= (: (: ready-task id) job-id) id-to-cancel)
                        (remove read-task ready-tasks)
                        ready-tasks))]
                 ;; 4. Remove waiting tasks
                 [waiting-tasks
                  (for/fold ([waiting-tasks waiting-tasks])
                            ([waiting-task waiting-tasks])
                    (if (= (: (: waiting-task id) job-id) id-to-cancel)
                        (remove waiting-task waiting-tasks)
                        waiting-tasks))])
            (send (: job-info client) (JobResultFailure))
            (send result-dest (CancellationSuccess))
            (goto ManagingJobs
                  task-managers
                  (hash-remove active-jobs id-to-cancel)
                  waiting-tasks
                  ready-tasks
                  running-tasks
                  partitions))])])))

(define-actor Nat
  (TaskManagerCreator [job-manager (Addr TaskManagerToJobManager)])
  ()
  (goto Init)
  (define-state/timeout (Init) (m)
    (goto Init)
    (timeout 0
      (let ([task-manager (spawn task-manager-loc TaskManager 1 job-manager)])
        (for/fold ([dummy 0])
                  ([n (list 1 2)])
          (spawn runner-loc TaskRunner job-manager task-manager))
        (goto Done))))
  (define-state (Done) (m) (goto Done)))

(define-actor Nat
  (TaskManagersCreator [manager-ids (Listof Nat)] [job-manager (Addr TaskManagerToJobManager)])
  ()
  (goto Init)
  (define-state/timeout (Init) (m)
    (goto Init)
    (timeout 0
      (for/fold ([dummy 0])
                ([manager-id manager-ids])
        (let ([task-manager (spawn task-manager-loc TaskManager manager-id job-manager)])
          (for/fold ([dummy 0])
                    ([n (list 1 2)])
            (spawn runner-loc TaskRunner job-manager task-manager))))
      (goto Done)))
  (define-state (Done) (m) (goto Done))))))

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
  (define (TaskManagerTerminated id) (variant TaskManagerTerminated id))
  (define (JobManagerTerminated) (variant JobManagerTerminated))
  (define (JobResultSuccess result) (variant JobResultSuccess result))
  (define (JobResultFailure) (variant JobResultFailure))
  (define (CancelJob id canceller) (variant CancelJob id canceller))
  (define (CancellationSuccess) (variant CancellationSuccess))
  (define (CancellationFailure) (variant CancellationFailure))

  (define desugared-job-task-id `(Record [job-id Nat] [task-id Nat]))
  (check-true (redex-match? csa-eval τ desugared-job-task-id))

  (define desugared-ready-task
    `(Record [id ,desugared-job-task-id]
             [work (Union (MapWork (Vectorof String))
                          (ReduceWork (Hash String Nat) (Hash String Nat)))]))
  (check-true (redex-match? csa-eval τ desugared-ready-task))
  (define desugared-submit-cancel-response
    `(Union
      (Acknowledge ,desugared-job-task-id)
      (Failure ,desugared-job-task-id)))
  (check-true (redex-match? csa-eval τ desugared-submit-cancel-response))
  (define desugared-task-manager-command
    `(Union
      [AcknowledgeRegistration]
      [SubmitTask ,desugared-ready-task (Addr ,desugared-submit-cancel-response)]
      [CancelTask ,desugared-job-task-id (Addr ,desugared-submit-cancel-response)]))
  (check-true (redex-match? csa-eval τ desugared-task-manager-command))
  (define desugared-execution-state
    `(Union
      (Finished (Hash String Nat))
      (Cancelled)))
  (check-true (redex-match? csa-eval τ desugared-execution-state))
  (define desugared-tm-to-jm-type
    `(Union
      [RequestNextInputSplit ,desugared-job-task-id (Addr (Union [NextInputSplit (Vectorof String)]))]
      [RegisterTaskManager Nat Nat (Addr ,desugared-task-manager-command)]
      [UpdateTaskExecutionState ,desugared-job-task-id ,desugared-execution-state]))
  (check-true (redex-match? csa-eval τ desugared-tm-to-jm-type))
  (define desugared-tm-test-input-type
    `(Union
      [JobManagerTerminated]
      [AcknowledgeRegistration]
      [SubmitTask ,desugared-ready-task (Addr ,desugared-submit-cancel-response)]
      [CancelTask ,desugared-job-task-id (Addr ,desugared-submit-cancel-response)]))
  (check-true (redex-match? csa-eval τ desugared-tm-test-input-type))

  ;; client-level API
  (define desugared-task-description
    `(Union [Map (Vectorof Nat)] [Reduce Nat Nat]))
  (define desugared-task `(Record [id Nat] [type ,desugared-task-description]))
  (define desugared-job `(Record [id Nat] [tasks (Listof ,desugared-task)] [final-task-id Nat]))
  (define desugared-job-result
    `(Union [JobResultSuccess (Hash String Nat)] [JobResultFailure]))
  (define desugared-cancellation-result
    `(Union (CancellationSuccess) (CancellationFailure)))
  (define desugared-job-manager-command
    `(Union [SubmitJob ,desugared-job (Addr ,desugared-job-result)]
            [CancelJob Nat (Addr ,desugared-cancellation-result)]))
  (check-true (redex-match? csa-eval τ desugared-job-manager-command))

  (define-match-expander JobTaskId/pat
    (lambda (stx)
      (syntax-parse stx
        [(_ job task)
         #`(csa-record [job-id job] [task-id task])])))

  (define task-runner-only-program
    (desugar
     `(program (receptionists [task-runner Nat]) (externals [job-manager Nat] [task-manager Nat])
               ,@flink-definitions
               (actors [task-runner (spawn task-runner-loc TaskRunner job-manager task-manager)]))))


  (define task-manager-program
    (desugar
     `(program (receptionists)
               (externals [job-manager ,desugared-tm-to-jm-type])
               ,@flink-definitions
               (actors [creator (spawn creator-loc TaskManagerCreator job-manager)]))))

  (define job-manager-program
    (desugar
     `(program (receptionists [job-manager Nat]) (externals)
               ,@flink-definitions
               (actors [job-manager (spawn jm-loc JobManager)]
                       [task-managers-creator
                        (spawn creator-loc TaskManagersCreator (list 1 2) job-manager)]))))

  (define single-tm-job-manager-program
    (desugar
     `(program (receptionists [job-manager Nat] [task-manager1 Nat]) (externals)
               ,@flink-definitions
               (actors [job-manager (spawn jm-loc JobManager)]
                       [task-manager1 (spawn task-manager1-loc TaskManager 1 job-manager)]
                       [task-runner1 (spawn runner1-loc TaskRunner job-manager task-manager1)]
                       [task-runner2 (spawn runner2-loc TaskRunner job-manager task-manager1)])))))

(module+ test
  ;; Dynamic tests

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

  (test-case "TaskManager can run three tasks to completion (waiting for TaskRunner completions)"
    (define jm (make-async-channel))
    (csa-run task-manager-program jm)
    (define task-manager
      (check-unicast-match jm (csa-variant RegisterTaskManager 1 2 tm) #:result tm))
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
    (csa-run task-manager-program jm)
    (define task-manager
      (check-unicast-match jm (csa-variant RegisterTaskManager 1 2 tm) #:result tm))
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
    (check-unicast client (JobResultSuccess (hash "a" 5 "b" 5 "c" 2)) #:timeout 30))

  (test-case "Job manager runs multiple jobs to completion (more tasks than task runners)"
    (define jm (csa-run job-manager-program))
    ;; 1. Wait for the task managers to register with the job manager
    (sleep 3)
    ;; 2. Submit the jobs
    (define job1 (Job 1
                      (list (Task 1 (Map (vector "a" "b" "c" "a" "b" "c")))
                            (Task 2 (Map (vector "a" "b")))
                            (Task 3 (Map (vector "a" "b")))
                            (Task 4 (Map (vector "a" "b")))
                            (Task 5 (Reduce 1 2))
                            (Task 6 (Reduce 3 4))
                            (Task 7 (Reduce 5 6)))
                      7))
    (define client1 (make-async-channel))
    (define job2 (Job 2
                      (list (Task 1 (Map (vector "x" "y" "y" "z" "x")))
                            (Task 2 (Map (vector "y" "y" "y" "z" "z" "z" "x")))
                            (Task 3 (Reduce 1 2)))
                      3))
    (define client2 (make-async-channel))
    (async-channel-put jm (SubmitJob job1 client1))
    (async-channel-put jm (SubmitJob job2 client2))
    ;; 3. Wait for response
    (check-unicast client1 (JobResultSuccess (hash "a" 5 "b" 5 "c" 2)) #:timeout 30)
    (check-unicast client2 (JobResultSuccess (hash "x" 3 "y" 5 "z" 4)) #:timeout 30))

  (test-case "One task manager of two drops out; all tasks are still completed"
    (match-define-values (jm _) (csa-run single-tm-job-manager-program))
    (async-channel-put jm (variant RegisterTaskManager 2 2 (make-async-channel)))
    (sleep 1) ; wait for the registrations to go through
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
    (async-channel-put jm (TaskManagerTerminated 2))
    (check-unicast client (JobResultSuccess (hash "a" 5 "b" 5 "c" 2)) #:timeout 30))

  (test-case "Only task manager drops out then reconnects; all tasks are still completed"
    (match-define-values (jm tm) (csa-run single-tm-job-manager-program))
    (sleep 1) ; wait for the registrations to go through
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
    (async-channel-put jm (TaskManagerTerminated 1))
    (sleep 1)
    (async-channel-put tm (JobManagerTerminated))
    ;; At this point, the TaskManager should attempt to re-register, then finish the remaining tasks
    (check-unicast client (JobResultSuccess (hash "a" 5 "b" 5 "c" 2)) #:timeout 30))

  (test-case "Cancelling a job sends cancel result to canceller and client, client gets no result"
    (define jm (csa-run job-manager-program))
    (sleep 1) ; wait for the registrations to go through
    (define job (Job 1
                     (list (Task 1 (Map (vector "a" "b" "c" "a" "b" "c")))
                           (Task 2 (Map (vector "a" "b")))
                           (Task 5 (Reduce 1 2)))
                     5))
    (define client (make-async-channel))
    (async-channel-put jm (SubmitJob job client))
    (sleep 1)
    (define canceller (make-async-channel))
    (async-channel-put jm (CancelJob 1 canceller))
    (check-unicast canceller (CancellationSuccess))
    (check-unicast client (JobResultFailure))
    (check-no-message client #:timeout 10))

  (test-case "Cancelling a non-existent job sends back cancel-failure"
    (define jm (csa-run job-manager-program))
    (sleep 1) ; wait for the registrations to go through
    (define canceller (make-async-channel))
    (async-channel-put jm (CancelJob 1 canceller))
    (check-unicast canceller (CancellationFailure)))

  (test-case "Cancelling a job after completion ends with CancellationFailure"
    (define jm (csa-run job-manager-program))
    ;; 1. Wait for the task managers to register with the job manager
    (sleep 3)
    ;; 2. Submit the job
    (define job (Job 1
                     (list (Task 1 (Map (vector "a" "b" "c" "a" "b" "c")))
                           (Task 2 (Map (vector "a" "b")))
                           (Task 5 (Reduce 1 2)))
                     5))
    (define client (make-async-channel))
    (async-channel-put jm (SubmitJob job client))
    ;; 3. Wait for response
    (check-unicast client (JobResultSuccess (hash "a" 3 "b" 3 "c" 2)) #:timeout 30)
    (define canceller (make-async-channel))
    (async-channel-put jm (CancelJob 1 canceller))
    (check-unicast canceller (CancellationFailure))))

(module+ test
  (define task-manager-spec-behavior
    `((goto Unregistered job-manager)
      (define-state (Unregistered job-manager)
        [(variant JobManagerTerminated) -> () (goto Unregistered job-manager)]
        [(variant AcknowledgeRegistration) -> () (goto Registered job-manager)]
        [(variant SubmitTask * ack-dest) ->
         ([obligation ack-dest (variant Failure *)])
         (goto Unregistered job-manager)]
        [(variant CancelTask * ack-dest) ->
         ([obligation ack-dest (variant Failure *)])
         (goto Unregistered job-manager)]
        [unobs ->
               ([obligation job-manager (variant RegisterTaskManager * * self)])
               (goto Unregistered job-manager)]
        ;; These two messages might still happen during Unregistered because the runners are
        ;; cancelled later
        [unobs ->
               ([obligation job-manager (variant UpdateTaskExecutionState * *)])
               (goto Unregistered job-manager)]
        [unobs ->
               ([obligation job-manager (variant RequestNextInputSplit * *)])
               (goto Unregistered job-manager)])
      (define-state (Registered job-manager)
        [(variant JobManagerTerminated) -> () (goto Unregistered job-manager)]
        [(variant AcknowledgeRegistration) -> () (goto Registered job-manager)]
        [(variant SubmitTask * ack-dest) ->
         ([obligation ack-dest (or (variant Acknowledge *) (variant Failure *))])
         (goto Registered job-manager)]
        [(variant CancelTask * ack-dest) ->
         ([obligation ack-dest (or (variant Acknowledge *) (variant Failure *))])
         (goto Registered job-manager)]
        [unobs ->
               ([obligation job-manager (variant UpdateTaskExecutionState * *)])
               (goto Registered job-manager)]
        [unobs ->
               ([obligation job-manager (variant RequestNextInputSplit * *)])
               (goto Registered job-manager)])))

  (define task-manager-spec
    `(specification (receptionists) (externals [job-manager ,desugared-tm-to-jm-type])
       UNKNOWN
       ()
       (goto Init job-manager)
       (define-state (Init job-manager)
         [unobs ->
           ([obligation job-manager
                        (variant RegisterTaskManager * * (fork ,@task-manager-spec-behavior))])
           (goto Done)])
       (define-state (Done))))

  (test-true "Task manager conforms to its spec"
    (check-conformance task-manager-program task-manager-spec))

  (define send-job-result-anytime-behavior
    `((goto SendAnytime dest)
      (define-state (SendAnytime dest)
        [unobs -> ([obligation dest (variant JobResultSuccess *)]) (goto SendAnytime dest)]
        [unobs -> ([obligation dest (variant JobResultFailure)]) (goto SendAnytime dest)])))

  (define job-manager-client-pov-spec
    `(specification (receptionists [job-manager ,desugared-job-manager-command]) (externals)
       [job-manager ,desugared-job-manager-command]
       ([job-manager (Union [TaskManagerTerminated Nat])])
       (goto Running)
       (define-state (Running)
         [(variant CancelJob * dest) ->
          ([obligation dest (or (variant CancellationSuccess) (variant CancellationFailure))])
          (goto Running)]
         ;; In the AI, the best we can say is that we might get any number of results back on this
         ;; address (because the abstraction never actually removes addresses from collections), so
         ;; the spec just states the possible results.
         [(variant SubmitJob * dest) -> ([fork ,@send-job-result-anytime-behavior]) (goto Running)])))

  (test-true "Job manager conforms to its client POV spec"
    (check-conformance job-manager-program job-manager-client-pov-spec)))

;; Specs to check:
;; * JobManager, from TaskManager/Task perspective:
;;   * respond to registration requests, then sends other commands (SubmitTask, CancelTask)
;;   * respond to RequestNextInputSplit

;; Missed responses to check with specs:

;; * TaskManager registration acknowledgment
