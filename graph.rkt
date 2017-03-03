#lang racket

;; A simple graph module, with the connections between edges and vertices represented as fields in
;; structs. Roughly corresponds to an adjacency list implementation, because I expect graphs to be
;; sparse.

(provide
 make-graph
 graph-literal
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
 edge-destination

 ;; Misc. graph algorithms
 graph-transpose
 graph-find-sccs

 ;; testing helpers
 graph-equal?
 check-graph-equal?
 test-graph-equal?
 print-graph)

(require
 (for-syntax syntax/parse))

(module+ test
  (require rackunit))

(struct graph ([vertices #:mutable] [edges #:mutable]) #:transparent)

(struct vertex (value [incoming #:mutable] [outgoing #:mutable]) #:transparent)

(struct edge (value source destination) #:transparent)

;; ---------------------------------------------------------------------------------------------------

(require
 rackunit)

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
  (define g0 (make-graph))
  (define v1 (graph-add-vertex! g0 1))
  (define v2 (graph-add-vertex! g0 2))
  (define v3 (graph-add-vertex! g0 3))

  (check-false (graph-find-vertex g0 4))
  (check-equal? (graph-find-vertex g0 1) v1))

(define (graph-add-edge! g val src dest)
  (define e (edge val src dest))
  (set-graph-edges! g (cons e (graph-edges g)))
  (set-vertex-outgoing! src (cons e (vertex-outgoing src)))
  (set-vertex-incoming! dest (cons e (vertex-incoming dest)))
  e)

(module+ test
  ;; check that adding an edge puts edge in in/out, and the src/dest are correct
  (define e1 (graph-add-edge! g0 "foo" v1 v2))
  (check-equal? (edge-source e1) v1)
  (check-equal? (edge-destination e1) v2)
  (check-equal? (edge-value e1) "foo")
  (check-equal? (vertex-outgoing v1) (list e1))
  (check-equal? (vertex-incoming v2) (list e1))

  (test-case "graph-add-edge!"
    (define g
      (graph-literal [vertices [a 'a] [b 'b] [c 'c]]
                     [edges ['ab a b] ['bc b c]]))
    (check-equal? (map edge-value (vertex-incoming (graph-find-vertex g 'c)))
                  (map edge-value (vertex-outgoing (graph-find-vertex g 'b)))))

  (test-case "graph-add-edge! 2"
    (define g (make-graph))
    (define a (graph-add-vertex! g 'a))
    (define b (graph-add-vertex! g 'b))
    (define c (graph-add-vertex! g 'c))
    (graph-add-edge! g 'ab a b)
    (graph-add-edge! g 'bc b c)
    (check-equal? (map edge-value (vertex-incoming c))
                  (map edge-value (vertex-outgoing b)))))

;; Returns #t if the graphs are isomorphic; #f otherwise. Assumes every vertex has a unique label, and
;; every edge has a label distinct from that of all other edges going to and from the same vertex.
(define (graph-equal? g1 g2)
  (and
   (equal? (list->set (map vertex-value (graph-vertices g1)))
           (list->set (map vertex-value (graph-vertices g2))))
   ;; For each vertex, check that the other graph has a matching vertex and their outgoing edges are
   ;; the same
   (for/and ([v1 (graph-vertices g1)])
     (match (graph-find-vertex g2 (vertex-value v1))
       [#f #f]
       [v2
        ;; Loop over all outgoing edges, check that each one has a match from the other vertex
        (let loop ([out1 (vertex-outgoing v1)]
                   [out2 (vertex-outgoing v2)])
          (match out1
            [(list) (null? out2)]
            [(list e1 out1 ...)
             (define-values (equal-edges unequal-edges) (partition (curry edge-equal? e1) out2))
             (match equal-edges
               [(list _) (loop out1 unequal-edges)]
               [_ #f])]))]))))

(module+ test
  (define g1 (make-graph))
  (define g1a (graph-add-vertex! g1 'a))
  (define g1b (graph-add-vertex! g1 'b))
  (void (graph-add-edge! g1 'x g1a g1b))

  (define g2 (make-graph))
  (define g2b (graph-add-vertex! g2 'b))
  (define g2a (graph-add-vertex! g2 'a))
  (void (graph-add-edge! g2 'x g2a g2b))

  ;; g3 is missing a vertex
  (define g3 (make-graph))
  (define g3a (graph-add-vertex! g3 'a))

  ;; g4 is missing the edge
  (define g4 (make-graph))
  (define g4a (graph-add-vertex! g4 'a))
  (define g4b (graph-add-vertex! g4 'b))

  ;; g5 has wrong label on edge
  (define g5 (make-graph))
  (define g5a (graph-add-vertex! g5 'a))
  (define g5b (graph-add-vertex! g5 'b))
  (void (graph-add-edge! g5 'y g5a g5b))

  (test-true "graph-equal? 1" (graph-equal? g1 g2))
  (test-false "graph-equal? 1" (graph-equal? g1 g3))
  (test-false "graph-equal? 1" (graph-equal? g1 g4))
  (test-false "graph-equal? 1" (graph-equal? g1 g5)))

;; Returns #t if the two edges are equal (i.e. have the same label and their sources and destinations
;; have the same labels, respetively); #f otherwise
(define (edge-equal? e1 e2)
  (and (equal? (edge-value e1) (edge-value e2))
       (equal? (vertex-value (edge-source e1)) (vertex-value (edge-source e2)))
       (equal? (vertex-value (edge-destination e1)) (vertex-value (edge-destination e2)))))

(module+ test
  (test-true "edge-equal? 1"
    (edge-equal? (edge 'x (vertex 'a #f #f) (vertex 'b #f #f))
                 (edge 'x (vertex 'a #f #f) (vertex 'b #f #f))))
  (test-false "edge-equal? 2"
    (edge-equal? (edge 'x (vertex 'a #f #f) (vertex 'b #f #f))
                 (edge 'y (vertex 'a #f #f) (vertex 'b #f #f))))
  (test-false "edge-equal? 3"
    (edge-equal? (edge 'x (vertex 'a #f #f) (vertex 'b #f #f))
                 (edge 'x (vertex 'c #f #f) (vertex 'b #f #f))))
  (test-false "edge-equal? 4"
    (edge-equal? (edge 'x (vertex 'a #f #f) (vertex 'b #f #f))
                 (edge 'x (vertex 'a #f #f) (vertex 'd #f #f)))))

(define-syntax (graph-literal stx)
  (syntax-parse stx
    #:datum-literals (vertices edges)
    [(_ (vertices [v:id vertex-val] ...)
        (edges [edge-val v1:id v2:id] ...))
     #`(let ()
         (define g (make-graph))
         (define v (graph-add-vertex! g vertex-val)) ...
         (void (graph-add-edge! g edge-val v1 v2)) ...
         g)]))

(module+ test
  (test-true "graph-literal"
    (graph-equal? g1
                  (graph-literal [vertices [a 'a] [b 'b]]
                                 [edges ['x a b]]))))

(define-binary-check (check-graph-equal? graph-equal? actual expected))

(define-syntax (test-graph-equal? stx)
  (syntax-parse stx
    [(_  name actual expected)
     #`(test-case name
         #,(syntax/loc stx (check-graph-equal? actual expected)))]))

(define (print-graph g)
  (for ([v (graph-vertices g)])
    (printf "Vertex: ~s\n" (vertex-value v))
    (for ([e (vertex-outgoing v)])
      (printf "  Out Edge:\n" )
      (printf "    Value: ~s\n" (edge-value e))
      (printf "    Source: ~s\n" (vertex-value (edge-source e)))
      (printf "    Dest: ~s\n" (vertex-value (edge-destination e))))
    (for ([e (vertex-incoming v)])
      (printf "  In Edge:\n" )
      (printf "    Value: ~s\n" (edge-value e))
      (printf "    Source: ~s\n" (vertex-value (edge-source e)))
      (printf "    Dest: ~s\n" (vertex-value (edge-destination e))))))

;; Transposes the given graph by returning a new graph that is like g but reverses the direction of
;; all arrows
(define (graph-transpose g)
  (define g-transpose (make-graph))
  (for ([v (graph-vertices g)])
    (graph-add-vertex! g-transpose (vertex-value v)))
  (for ([v (graph-vertices g)])
    (define v-transpose (graph-find-vertex g-transpose (vertex-value v)))
    (for ([e (vertex-outgoing v)])
      (graph-add-edge! g-transpose
                       (edge-value e)
                       (graph-find-vertex g-transpose (vertex-value (edge-destination e)))
                       v-transpose)))
  g-transpose)

(module+ test
  (test-graph-equal? "graph-transpose"
    (graph-transpose
     (graph-literal
      [vertices [a 'a] [b 'b] [c 'c] [d 'd] [e 'e]]
      [edges ['ac a c]
             ['ae a e]
             ['ba b a]
             ['cb c b]
             ['cd c d]
             ['de d e]]))
    (graph-literal
     [vertices [a 'a] [b 'b] [c 'c] [d 'd] [e 'e]]
     [edges ['ac c a]
            ['ae e a]
            ['ba a b]
            ['cb b c]
            ['cd d c]
            ['de e d]])))


;; Graph -> (Setof (Setof Vertex))
;;
;; Returns sets of vertices that represent the strongly connected components of g.
(define (graph-find-sccs g)
  ;; Implements Kosaraju's algorithm (https://en.wikipedia.org/wiki/Kosaraju%27s_algorithm)

  ;; Visits the vertex u as in the Wikipedia description linked above; returns the updated visited and
  ;; L as multiple values
  (define (visit u visited L)
    (cond
      [(set-member? visited u) (values visited L)]
      [else
       (define-values (new-visited new-L)
         ;; recursively visit each out-neighbor
         (for/fold ([visited (set-add visited u)]
                    [L L])
                   ([out-edge (vertex-outgoing u)])
           (visit (edge-destination out-edge) visited L)))
       (values new-visited (cons u new-L))]))

  ;; Assigns u and its in-neighbors to an SCC in SCCs if u has not already been assigned, as in the
  ;; algorithm described in the above Wikipedia link. Returns the updated this-scc.
  (define (assign u this-scc other-sccs)
    (cond
      [(ormap (curryr set-member? u) (cons this-scc other-sccs))
       this-scc]
      [else
       ;; has not been assigned
       (for/fold ([this-scc (set-add this-scc u)])
                 ([in-edge (vertex-incoming u)])
         (assign (edge-source in-edge) this-scc other-sccs))]))

  (define-values (visited L)
    (for/fold ([visited (set)]
               [L null])
              ([u (graph-vertices g)])
      (visit u visited L)))

  (list->set
   (for/fold ([sccs null])
             ([u L])
     (define new-scc (set))
     (match (assign u new-scc sccs)
       ;; Throw out empty SCCs, since they're meaningless
       [(? set-empty?) sccs]
       [new-scc (set-add sccs new-scc)]))))

(module+ test
  (let ()
    (define scc-test-graph
      (graph-literal
       [vertices [a 'a] [b 'b] [c 'c] [d 'd] [e 'e] [f 'f] [g 'g]]
       [edges ['ac a c]
              ['ae a e]
              ['ba b a]
              ['cb c b]
              ['cd c d]
              ['de d e]
              ['fe f e]
              ['gf g f]
              ['fg f g]]))
    (test-equal? "graph-find-sccs"
      (graph-find-sccs scc-test-graph)
      (set (set (graph-find-vertex scc-test-graph 'a)
                (graph-find-vertex scc-test-graph 'b)
                (graph-find-vertex scc-test-graph 'c))
           (set (graph-find-vertex scc-test-graph 'd))
           (set (graph-find-vertex scc-test-graph 'e))
           (set (graph-find-vertex scc-test-graph 'f)
                (graph-find-vertex scc-test-graph 'g))))))
