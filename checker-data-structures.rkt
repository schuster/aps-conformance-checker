#lang racket

;; Defines various data structures needed by different parts of the conformance checker

(provide
 (struct-out config-pair)
 (struct-out impl-step)
 (struct-out spec-step))

;; ---------------------------------------------------------------------------------------------------
;; Data Structures

;; A pair of an implementation configuration and a specification configuration discovered during the
;; search for pairs in the rank-1 simulation. The algorithm uses these pairs as vertices in a
;; graph-like structure that constitutes a proof that all of its vertices are in the conformance
;; relation. Earlier in the algorithm, the graph is unsound, and the algorithm uses a coinductive
;; technique to remove the "local lies" and propagate the conseequences of retracting these nodes,
;; until we reach a sound fixpoint.
;;
;; Initially, every such pair is either in the rank-1 simulation or is an unrelated successor (through
;; the transition relations) of one of the related pairs.  When the algorithm terminates, all
;; remaining config-pairs <i, s> in the related set have the property that the abstract implementation
;; state i (abstractly) conforms to the abstract specification state s.
;;
;; We use this general technique for multiple relations, each of which is a subset of the previous
;; one, eventually leading to the spec conformance relation.
(struct config-pair (impl-config spec-config) #:prefab)

;; A possible transition step of an implementation configuration, representing the computation of a
;; single message/timeout handler. Fields are as follows:
;;
;; trigger: A representation of the message-receive or timeout that kicked off this computation. Exact
;; representation matches the trigger# form in csa#.
;;
;; from-observer?: A boolean indicating whether the trigger was caused by the "observer" portion of
;; the environment, as described in the conformance semantics. Can be true only for steps with
;; external-receive triggers.
;;
;; outputs: A list of abstract address/abstract value pairs indicating the messages sent to the
;; environment during the computation.
;;
;; destination: The implementation configuration reached at the end of this transition step
(struct impl-step (trigger from-observer? outputs destination) #:prefab)

;; A possible (weak handler-level) transition step of a specification configuration, representing the
;; actions taken to match some (handler-level) implementation transition step. Weak transitions
;; correspond to the general idea of weak simulations; see the dissertation for details. Fields are as
;; follows:
;;
;; destination: The specification configuration reached at the end of the weak transition.
;;
;; spawns: The list of specification configurations forked off by this transition step. A conforming
;; implementation configuration must conform to all of these configs in addition to destination.
;;
;; satisfied-commitments: The list of output commitments (address/output-pattern pairs) that are
;; satisfied by taking this step.
(struct spec-step (destination spawns satisfied-commitments) #:prefab)

;; ---------------------------------------------------------------------------------------------------
;; "Type" Definitions

;; IncomingStepsDict = (Hash config-pair
;;                          (MutableSetof (List config-pair impl-step spec-step (Hash Addr Addr))))
;;
;; Records all implementation and specification transitions that led to some pair discovered during
;; the initial construction of the rank-1 simulation. Formally, for all pairs <i, s> in either the
;; related pairs or unrelated successors returned by find-rank1-simulation, incoming-steps(i, s) = a
;; set of tuples of the form (<i', s'>, i-step, s-step, address-map), where i-step is some transition
;; from i', s-step is a transition from s' that matches i-step, and <i, s> ∈ sbc(i'', s'') where i''
;; and s'' are the destination configurations from i-step and s-step, respectively, and address-map
;; maps the addresses in <i', s'> to those in <i, s>.
;;
;; In prune-unsupported, we use this data structure to determine the set of related pairs and
;; transitions that depend on this pair to prove their own membership in a relation.

;; RelatedSpecStepsDict = (Hash (List config-pair impl-step) (MutableSetof spec-step))
;;
;; Records all specification transitions currently believed to match the given implementation
;; transition for some relation. To be in a simulation, every transition of the implementation
;; configuration must have at least one such related pair. Specification steps will be removed from
;; these sets when their destinations are found to be unrelated for the current relation.
;;
;; Formally, related-spec-steps(<i, s>, i-step) = {s-step, ...} such that if <i, s> is a related pair
;; for some relation R and i-step is a transition from i, s-step matches i-step and all pairs <i', s'>
;; ∈ sbc(i-step.destination, s-step.destination) are also related pairs in R.
