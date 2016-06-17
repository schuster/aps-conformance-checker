#lang racket

;; A simple graph module, with the connections between edges and vertices represented as fields in
;; structs. Roughly corresponds to an adjacency list implementation, because I expect graphs to be
;; sparse.

(provide
 make-graph ; need this object to easily get all edges for backwards walk
 graph-vertices
 graph-edges
 graph-find-vertex ; takes a graph and a vertex value, plus an optional is-equal? predicate
 graph-add-edge! ; takes graph, edge value, source vertex, dest vertex
 graph-add-vertex! ; takes a graph and the vertex value; adds it as an unconnected vertex; returns the new vertex

 vertex-value
 vertex-incoming
 vertex-outgoing

 edge-value
 edge-source
 edge-destination)

(module+ test
  (require rackunit))

(struct graph ([vertices #:mutable] [edges #:mutable]) #:transparent)

(struct vertex (value [incoming #:mutable] [outgoing #:mutable]) #:transparent)

(struct edge (value source destination) #:transparent)

;; ---------------------------------------------------------------------------------------------------

(define (make-graph) (graph null null))

(define (graph-add-vertex! g val)
  (define v (vertex val null null))
  (set-graph-vertices! g (cons v (graph-vertices g)))
  v)

(define (graph-find-vertex g val #:is-equal? [is-equal? equal?])
  (findf (lambda (v) (is-equal? (vertex-value v) val))
         (graph-vertices g)))

(module+ test
  (define empty-graph (make-graph))
  (define g1 (make-graph))
  (define v1 (graph-add-vertex! g1 1))
  (define v2 (graph-add-vertex! g1 2))
  (define v3 (graph-add-vertex! g1 3))

  (check-false (graph-find-vertex g1 4))
  (check-equal? (graph-find-vertex g1 1) v1))

(define (graph-add-edge! g val src dest)
  (define e (edge val src dest))
  (set-graph-edges! g (cons e (graph-edges g)))
  (set-vertex-outgoing! src (cons e (vertex-outgoing src)))
  (set-vertex-incoming! dest (cons e (vertex-incoming src)))
  e)

(module+ test
  ;; TODO: what's the test here?
  ;; check that adding an edge puts edge in in/out, and the src/dest are correct
  (define e1 (graph-add-edge! g1 "foo" v1 v2))
  (check-equal? (edge-source e1) v1)
  (check-equal? (edge-destination e1) v2)
  (check-equal? (edge-value e1) "foo")
  (check-equal? (vertex-outgoing v1) (list e1))
  (check-equal? (vertex-incoming v2) (list e1)))

