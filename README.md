This repository contains the code for a model checker for the APS specification
language, as described in my PhD dissertation, along with various example
programs.

Setup/Prerequisites
===================

1. Install Racket if you don't already have it (note the issue with Racket
   version 6.12 mentioned below)
2. Navigate to the directory containing this README, then run "raco pkg
   install". Install the requested dependencies.

Running the Model Checker
=========================

The file main.rkt in this repository provides a function "check-conformance"
that takes a CSA program and an APS specification (both represented as
S-expressions) and returns true (#t) if the program conforms to the
specification, or false (#f) otherwise. The function also prints various
information about the check as it executes.

The test cases used to evaluate the model checker are found in the examples/
directory.

All optimizations are enabled by default. They can be explicitly enabled or
disabled with the following keyword arguments to check-conformance (some of
these use old names for the optimizations):
* #:use-widen? - for acceleration
* #:use-eviction? - for eviction
* #:memoize-eval-handler? - for memoization
* #:use-detect-dead-observables? - for dead-marker detection

The file example-check.rkt in this directory gives an example of running the
checker on the stream-processing/weather-average example.

File Overview
=============

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
