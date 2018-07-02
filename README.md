Here are the important files in the conformance checker:

main.rkt:           Implements the top-level function, "check-conformance", and includes the core of the
                    conformance-checking algorithm

commitment-satisfaction.rkt: Defines the commitment-satisfaction-check algorithm

checker-data-structures.rkt: Defines various data structures needed by different parts of the conformance checker

csa.rkt: 		    Concrete standard semantic domains for CSA, and associated functions
csa-abstract.rkt	Abstract standard semantic domains for CSA#, and associated functions

aps.rkt				Concrete semantic domains for APS (specification language), and associated functions
aps-abstract.rkt    Abstract semantic domains for APS (specification language), and associated functions

desugar.rkt			Nanopass-based desugarer for the bigger language (desugars down to CSA)

graph.rkt           A simple graph implementation and related algorithms

raft.rkt			A larger test of the conformance-checker, for an implementation of Raft

Naming Conventions
==================

A "/mf" suffix at the end of a name indicates a Redex metafunction, and a "/j"
suffix indicates a Redex judgment. Unfortunately, as of this writing those
suffixes are not used universally for metafunctions and judgments.

Misc. Notes
===========

All Redex operations should be contained into the various APS and CSA files -
main.rkt should be Redex-agnostic (with the exception of constructing test
cases).

As of July 2018, there appears to be a performance regression in Racket 6.12
that severely slows down performance. It appears related to using large
S-expressions as keys in hash tables. Use Racket 6.11 or earlier for better
performance.
