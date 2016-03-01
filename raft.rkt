#lang racket

;; A full test of the Raft port to CSA, verified against its spec

(require
 rackunit
 redex/reduction-semantics
 "csa.rkt"
 "desugar.rkt"
 "main.rkt")

;; TODO: put this in a common place so it isn't repeated across files
(define single-agent-concrete-addr (term (addr 0)))

;; 0. Define the spec
(define raft-spec
  (term
   (((define-state (Init)
       [* -> (goto Init)])
     ;; (define-state (Follower)
     ;;   [(RequestVote _ candidate _ _) -> ]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     ;; (define-state (Candidate)
     ;;   [(RequestVote _ candidate _ _) -> ???]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     ;; (define-state (Leader)
     ;;   [(RequestVote _ candidate _ _) -> ???]
     ;;   [(VoteCandidate _ _) -> ???]
     ;;   [(DeclineCandidate _ _) -> ???]
     ;;   [(AppendEntries _ _ _ _ _ leader _) -> ???]
     ;;   [(AppendRejected _ _ _) -> ???]
     ;;   [(AppendSuccessful _ _ _) -> ???])
     )
    (goto Init)
    ,single-agent-concrete-addr)))

(check-not-false (redex-match aps-eval z raft-spec))

;; 1. Define Raft in the basic syntax
(define raft-actor-def
  (term
   (define-actor (Raft)
     (goto Init)
     (define-state (Init) (m)
       (goto Init)))))

;; TODO: write a test that checks the Raft program's grammar (later: and type-checks it)

;; 2. Desugar that into the actor definition the verifier needs/translate it into the structural
;; version, using arbitrary addresses for each initial output address
(define desugared-raft-actor (desugar-actor raft-actor-def single-agent-concrete-addr))

;; 3. Move the actor definition into a config, with addresses assigned appropriately
(define raft-config (make-single-agent-config desugared-raft-actor))

;; 4. Run the verifier
(check-true (analyze raft-config
                     raft-spec
                     (term (Union)) (term (Union))
                     (hash 'Init 'Init
                           'Follower 'Follower
                           'Candidate 'Candidate
                           'Leader 'Leader)))
