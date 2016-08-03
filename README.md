Here are the important files in the model checker:

main.rkt:           Implements the top-level function, "model-check", and includes the
                    core of the model-checking algorithm

csa.rkt: 		    Concrete standard semantic domains for CSA, and associated functions
csa-abstract.rkt	Abstract standard semantic domains for CSA#, and associated functions

aps.rkt				Concrete semantic domains for APS (specification language), and associated functions
aps-abstract.rkt    Abstract semantic domains for APS (specification language), and associated functions

desugar.rkt			Nanopass-based desugarer for the bigger language (desugars down to CSA)

raft.rkt			A larger test of the model-checker, for an implementation of Raft

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
