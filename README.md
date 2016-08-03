Here are the important files in the model checker:

main.rkt:           Implements the top-level function, "model-check", and includes the
                    core of the model-checking algorithm

csa.rkt: 		    Concrete standard semantic domains for CSA, and associated functions
csa-abstract.rkt	Abstract standard semantic domains for CSA#, and associated functions

aps.rkt				Concrete semantic domains for APS (specification language), and associated functions
aps-abstract.rkt    Abstract semantic domains for APS (specification language), and associated functions

desugar.rkt			Nanopass-based desugarer for the bigger language (desugars down to CSA)

raft.rkt			A larger test of the model-checker, for an implementation of Raft
