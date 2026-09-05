import Mathlib

/-!
# Tracks, branches, subdivisions and cyclic 3-connectivity

Section 5 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas;
published/Annals version, printed pages 18–28).

Everything in this file concerns the **host** graph `H` — the graph that gets subdivided and
whose line graph appears inside the Berge graph `G`.  All the notions here are *ordinary*
(non-induced) graph theory: a track is a subgraph, **not** an induced subgraph, so the host
graph is allowed to have further edges among the vertices of a track.  This is the essential
difference from the paper's notion of *path*, which is induced.
-/

set_option autoImplicit false

namespace Workspace.Types.Tracks

namespace SPGT

/-- **Track** (printed p. 19).

PAPER: *"A track `P` is a non-null connected graph, not a cycle, in which every vertex has
degree ≤ 2; and its length is the number of edges in it. (Its ends and internal vertices are
defined in the natural way.) A track in a graph `H` means a subgraph of `H` (not necessarily
induced) which is a track."*

A non-null connected graph which is not a cycle and in which every vertex has degree ≤ 2 is
exactly a (graph-theoretic) simple path, so we represent a track by the list `q` of its
vertices in order: `q` is non-null, has no repeated vertex, and consecutive entries are
adjacent in `H`.

Note the contrast with the paper's *paths* (which are induced): here there is **no** "only if"
direction.  A track is a subgraph of `H`, not an induced subgraph, so `H` may well have extra
edges between non-consecutive vertices of `q`; the edges *of the track* are exactly the
consecutive pairs (see `trackEdges`). -/
def IsTrackList {W : Type*} (H : SimpleGraph W) (q : List W) : Prop :=
  q ≠ [] ∧ q.Nodup ∧ ∀ i : ℕ, (h : i + 1 < q.length) → H.Adj q[i] q[i + 1]

/-- **Length of a track** (printed p. 19).

PAPER: *"and its length is the number of edges in it."*

A track on `q.length` vertices has `q.length - 1` edges. -/
def trackLength {W : Type*} (q : List W) : ℕ := q.length - 1

/-- **The edge set of a track** (printed p. 19), i.e. the edges of the subgraph that the track
`q` is; PAPER: *"its length is the number of edges in it"* and *"the edge-set of a track
becomes the vertex-set of a path"* (the track/path correspondence, printed p. 19).

Since a track is a subgraph and not an induced subgraph, its edges are exactly the pairs of
consecutive vertices of `q` — never a "chord" of `q` that happens to be an edge of the host
graph. -/
def trackEdges {W : Type*} (q : List W) : Set (Sym2 W) :=
  {e : Sym2 W | ∃ i : ℕ, ∃ _h : i + 1 < q.length, e = s(q[i], q[i + 1])}

/-- **Internal vertices of a track** (printed p. 19).

PAPER: *"(Its ends and internal vertices are defined in the natural way.)"*

The internal vertices of the track `q` are all of its vertices except its two ends, i.e.
`q` with its first and last entries removed. -/
def trackInterior {W : Type*} (q : List W) : List W := q.tail.dropLast

/-- **A track with prescribed ends** (printed p. 19).

PAPER: *"(Its ends and internal vertices are defined in the natural way.)"*

`IsTrackFrom H q u v` says that `q` is a track of `H` whose two ends are `u` and `v`.
A track consisting of a single vertex has both ends equal to that vertex. -/
def IsTrackFrom {W : Type*} (H : SimpleGraph W) (q : List W) (u v : W) : Prop :=
  IsTrackList H q ∧ q.head? = some u ∧ q.getLast? = some v

/-- **Branch-vertex** (printed p. 19).

PAPER: *"A branch-vertex of a graph `H` means a vertex with degree ≥ 3;"*

The degree of `v` is written here as `(H.neighborSet v).ncard`, the number of neighbours of
`v`; for a finite graph this is exactly `SimpleGraph.degree`.  Writing it this way keeps the
definition free of a `DecidableRel H.Adj` instance argument, which `SimpleGraph.degree`
requires and which would otherwise have to be carried by every definition below. -/
def branchVertices {W : Type*} (H : SimpleGraph W) : Set W :=
  {v : W | 3 ≤ (H.neighborSet v).ncard}

/-- **Branch** (printed p. 19).

PAPER: *"and a branch of `H` means a maximal track `P` in `H` such that no internal vertex of
`P` is a branch-vertex."*

So `q` is a track of `H`, none of whose internal vertices is a branch-vertex, and which is
maximal with this property.  Maximality is maximality *as a subgraph*: if `q'` is another such
track whose subgraph contains the subgraph of `q` (every edge of `q` is an edge of `q'`, and
every vertex of `q` is a vertex of `q'`), then `q'` is the same subgraph as `q`.  Stating the
conclusion on edge sets makes a track and its reverse count as the same branch, as they should,
since they are the same subgraph. -/
def IsBranch {W : Type*} (H : SimpleGraph W) (q : List W) : Prop :=
  IsTrackList H q ∧
    (∀ v ∈ trackInterior q, v ∉ branchVertices H) ∧
    (∀ q' : List W, IsTrackList H q' →
      (∀ v ∈ trackInterior q', v ∉ branchVertices H) →
      trackEdges q ⊆ trackEdges q' → (∀ v ∈ q, v ∈ q') →
      trackEdges q' = trackEdges q)

/-- **`δ(v)`, `δ_H(v)`** (printed p. 22).

PAPER: *"If `v` is a vertex of `H`, the set of edges of `H` incident with `v` is denoted by
`δ(v)` or `δ_H(v)`."* -/
def incidentEdges {W : Type*} (H : SimpleGraph W) (v : W) : Set (Sym2 W) :=
  {e ∈ H.edgeSet | v ∈ e}

/-- **Subdivision** (printed pp. 19–20).

PAPER: *"Subdividing an edge `uv` means deleting the edge `uv`, adding a new vertex `w`, and
adding two new edges `uw` and `wv`. Starting with a graph `J`, the effect of repeatedly
subdividing edges is to replace each edge of `J` by a track joining the same pair of vertices,
where these tracks are disjoint except for their ends. We call the graph we obtain a
subdivision of `J`. Note that `V(J) ⊆ V(H)`."*

We formalize the paper's own characterisation — the second sentence — which is what the rest of
the paper actually uses.  `H` is a subdivision of `J` when there is an injection `ι` embedding
the vertices of `J` into those of `H` (this is the paper's `V(J) ⊆ V(H)`) together with, for
each edge `uv` of `J`, a track `T u v` of `H` joining `ι u` to `ι v`:

* each `T u v` is a track from `ι u` to `ι v` with at least one edge, and reversing the edge
  reverses the track;
* *"these tracks are disjoint except for their ends"*: no internal vertex of one track lies on
  a different track, and no internal vertex of a track is one of the `ι u` (an old vertex of
  `J`) — the new vertices created by subdividing are all new;
* `H` is exactly what one obtains, and nothing more: every vertex of `H` is either an old
  vertex `ι u` or an internal vertex of one of the tracks, and every edge of `H` is an edge of
  one of the tracks (and conversely). -/
def IsSubdivision {U W : Type*} (J : SimpleGraph U) (H : SimpleGraph W) : Prop :=
  ∃ (ι : U → W) (T : U → U → List W),
    Function.Injective ι ∧
    (∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v)) ∧
    (∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v)) ∧
    (∀ u v : U, J.Adj u v → T v u = (T u v).reverse) ∧
    (∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v') ∧
    (∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι) ∧
    (∀ w : W, (∃ u : U, w = ι u) ∨ ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v)) ∧
    H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v)

/-- **Bipartite subdivision** (the phrase *"a bipartite subdivision `H` of `K_4`"* is used
throughout; e.g. in the definition of `F₁`, printed p. 6, and in 5.1, printed p. 18).

`H` is a subdivision of `J` which is moreover bipartite. -/
def IsBipartiteSubdivision {U W : Type*} (J : SimpleGraph U) (H : SimpleGraph W) : Prop :=
  IsSubdivision J H ∧ H.IsBipartite

/-- **`k`-connected** (printed p. 20).

PAPER: *"(We use the convention that a `k`-connected graph must have `> k` vertices.)"*,
together with the standard meaning of `k`-connectivity.

So `H` is `k`-connected when it has more than `k` vertices and deleting any set of fewer than
`k` vertices leaves a connected graph.  (Mathlib has no notion of `k`-connectivity, so this is
defined from scratch.) -/
def IsKConnected {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) : Prop :=
  k < Fintype.card W ∧ ∀ S : Set W, S.ncard < k → (H.induce Sᶜ).Connected

/-- **Cyclically 3-connected** (printed p. 20).

PAPER: *"We say `H` is cyclically 3-connected if it is a subdivision of some 3-connected graph
`J`. (We remind the reader that in this paper, all graphs are simple by definition.)"*

"Some finite graph `J`" is rendered, as everywhere in this project, by quantifying over
`SimpleGraph (Fin n)` for some `n`. -/
def CyclicallyThreeConnected {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (n : ℕ) (J : SimpleGraph (Fin n)), IsKConnected J 3 ∧ IsSubdivision J H

/-- **Same biparity** (printed p. 22).

PAPER: *"When `H` is connected and bipartite, we speak of vertices having the same or different
biparity depending whether every track between them is even or odd respectively."*

`u` and `v` have the same biparity when every track of `H` between them has even length.  (That
for connected bipartite `H` exactly one of `SameBiparity` and `DifferentBiparity` holds is a
fact about bipartite graphs, not part of the definition, so it is not asserted here.) -/
def SameBiparity {W : Type*} (H : SimpleGraph W) (u v : W) : Prop :=
  ∀ q : List W, IsTrackFrom H q u v → Even (trackLength q)

/-- **Different biparity** (printed p. 22).

PAPER: *"When `H` is connected and bipartite, we speak of vertices having the same or different
biparity depending whether every track between them is even or odd respectively."*

`u` and `v` have different biparity when every track of `H` between them has odd length. -/
def DifferentBiparity {W : Type*} (H : SimpleGraph W) (u v : W) : Prop :=
  ∀ q : List W, IsTrackFrom H q u v → Odd (trackLength q)

/-- **Disjoint edges** (printed p. 22).

PAPER: *"Two edges of `G` are disjoint if they have no end in common, and otherwise they
meet."*

(The published paper writes `G` here, but the surrounding discussion — and the use made of the
notion in 5.7 — is about edges of `H`; the same slip is present in the arXiv version.  We
transcribe the intended notion: two edges of a graph on the vertex type `W` are disjoint when
no vertex is an end of both.) -/
def DisjointEdges {W : Type*} (e f : Sym2 W) : Prop :=
  ∀ w : W, ¬(w ∈ e ∧ w ∈ f)

/-- **Meeting edges** (printed p. 22).

PAPER: *"Two edges of `G` are disjoint if they have no end in common, and otherwise they
meet."*

So two edges meet exactly when they are not disjoint, i.e. when they have an end in common. -/
def MeetEdges {W : Type*} (e f : Sym2 W) : Prop :=
  ¬ DisjointEdges e f

end SPGT

end Workspace.Types.Tracks
