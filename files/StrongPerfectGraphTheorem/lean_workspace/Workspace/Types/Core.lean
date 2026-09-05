import Mathlib

/-!
# Core vocabulary for the Strong Perfect Graph Theorem

This module fixes the basic language of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem*.  Every definition below is a direct
transcription of a sentence from Section 1 (and the opening of Section 2) of the
paper; the relevant sentence is quoted in the doc-comment.

Ambient conventions used throughout:

* the vertex set is a type `V`;
* the complement `G̅` of the paper is Mathlib's `Gᶜ`;
* the subgraph `G|X` induced on a set `X : Set V` is Mathlib's `G.induce X`;
* paths, antipaths, holes and antiholes are represented by the **list of their
  vertices in order**, and "induced" is encoded by stating adjacency as an
  *if and only if* between vertices of the list.
-/

namespace Workspace.Types.Core

namespace SPGT

variable {V : Type*}

/-- PAPER: *"A path in `G` is an induced subgraph of `G` which is non-null,
connected, not a cycle, and in which every vertex has degree ≤ 2 (this definition
is highly nonstandard, and we apologise, but it avoids writing 'induced' about
600 times)."*

A path is represented by the list `p` of its vertices in order.  The list is
non-null and has no repeated vertex, and two vertices of the list are adjacent in
`G` **exactly when** their positions differ by one.  The "only if" direction is
what makes the subgraph induced; the "if" direction gives connectedness, and
together they force every vertex to have degree at most `2` and the two ends of a
list of at least three vertices to be non-adjacent (so the subgraph is not a
cycle). -/
def IsPathList (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧
    ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
      (G.Adj (p[i]'hi) (p[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i))

/-- PAPER: *"The length of a path is the number of edges in it ... We therefore
recognize paths and antipaths of length 0."*

For a path given by its list of vertices, the number of edges is one less than
the number of vertices (natural subtraction, so the empty list also gets `0`). -/
def pathLength (p : List V) : ℕ := p.length - 1

/-- PAPER: *"If `P` is a path, `P*` denotes the set of internal vertices of `P`,
called the interior of `P`; and similarly for antipaths."*

The interior of `p` is `p` with its first and last vertex removed. -/
def interior (p : List V) : List V := p.tail.dropLast

/-- PAPER: *"an antipath is an induced subgraph whose complement is a path ...
the length of an antipath is the number of edges in its complement."*

So `p` is an antipath of `G` exactly when it is a path of the complement `Gᶜ`,
and its length is again `pathLength p`. -/
def IsAntipathList (G : SimpleGraph V) (p : List V) : Prop := IsPathList Gᶜ p

/-- Rendering of the paper's "a path from `u` to `v`", "a path between `u` and
`v`", and "`u`-`P`-`v`": `p` is a path of `G` whose first vertex is `u` and whose
last vertex is `v`. -/
def IsPathFrom (G : SimpleGraph V) (p : List V) (u v : V) : Prop :=
  IsPathList G p ∧ p.head? = some u ∧ p.getLast? = some v

/-- Rendering of the paper's "an antipath from `u` to `v`": `p` is an antipath of
`G` (equivalently a path of `Gᶜ`) whose first vertex is `u` and whose last vertex
is `v`. -/
def IsAntipathFrom (G : SimpleGraph V) (p : List V) (u v : V) : Prop :=
  IsPathFrom Gᶜ p u v

/-- PAPER: *"A hole of `G` is an induced subgraph of `G` which is a cycle of
length at least 4."*

A hole is represented by the list `c` of its vertices in cyclic order: `c` has at
least four vertices, no repeated vertex, and two vertices of `c` are adjacent in
`G` **exactly when** their positions are cyclically consecutive. -/
def IsHoleList (G : SimpleGraph V) (c : List V) : Prop :=
  4 ≤ c.length ∧ c.Nodup ∧
    ∀ (i j : ℕ) (hi : i < c.length) (hj : j < c.length),
      (G.Adj ((c)[i]'hi) ((c)[j]'hj) ↔ (j = (i + 1) % c.length ∨ i = (j + 1) % c.length))

/-- The length of a cycle is its number of edges, which for a cycle equals its
number of vertices. -/
def holeLength (c : List V) : ℕ := c.length

/-- PAPER: *"An antihole of `G` is an induced subgraph of `G` whose complement is
a hole in `G̅`."*

So `c` is an antihole of `G` exactly when it is a hole of `Gᶜ`; its length is
again `holeLength c`. -/
def IsAntiholeList (G : SimpleGraph V) (c : List V) : Prop := IsHoleList Gᶜ c

/-- PAPER: *"A graph `G` is Berge if every hole and antihole of `G` has even
length."* -/
def Berge (G : SimpleGraph V) : Prop :=
  (∀ c : List V, IsHoleList G c → Even (holeLength c)) ∧
  (∀ c : List V, IsHoleList Gᶜ c → Even (holeLength c))

/-- PAPER: *"A clique in `G` is a subset `X` of `V(G)` such that every two
members of `X` are adjacent.  A graph `G` is perfect if for every induced subgraph
`H` of `G`, the chromatic number of `H` equals the size of the largest clique of
`H`."*

The induced subgraphs of `G` are exactly the `G.induce X` for `X : Set V`;
`SimpleGraph.chromaticNumber` is the chromatic number (valued in `ℕ∞`) and
`SimpleGraph.cliqueNum` is the size of a largest clique. -/
def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ X : Set V, (G.induce X).chromaticNumber = ((G.induce X).cliqueNum : ℕ∞)

/-- PAPER: *"If `X ⊆ V(G)` and `v ∈ V(G)`, we say `v` is `X`-complete if `v` is
adjacent to every vertex in `X` (and consequently `v ∉ X`) ..."* -/
def VertexComplete (G : SimpleGraph V) (v : V) (X : Set V) : Prop :=
  ∀ x ∈ X, G.Adj v x

/-- PAPER: *"... and `v` is `X`-anticomplete if `v` has no neighbours in `X`."* -/
def VertexAnticomplete (G : SimpleGraph V) (v : V) (X : Set V) : Prop :=
  ∀ x ∈ X, ¬ G.Adj v x

/-- PAPER: *"If `X, Y ⊆ V(G)` are disjoint, we say `X` is complete to `Y` (or the
pair `(X,Y)` is complete) if every vertex in `X` is `Y`-complete ..."*

Disjointness is stated by the paper as a separate hypothesis wherever it is
needed, so it is deliberately not built into this definition. -/
def Complete (G : SimpleGraph V) (X Y : Set V) : Prop :=
  ∀ x ∈ X, VertexComplete G x Y

/-- PAPER: *"... and being anticomplete to `Y` is defined similarly."*

That is, `X` is anticomplete to `Y` if every vertex of `X` is `Y`-anticomplete.
As above, disjointness is not built into the definition. -/
def Anticomplete (G : SimpleGraph V) (X Y : Set V) : Prop :=
  ∀ x ∈ X, VertexAnticomplete G x Y

/-- PAPER (start of Section 2): *"If `X ⊆ V(G)`, we say an edge `uv` is
`X`-complete if `u,v` are both `X`-complete."* -/
def EdgeComplete (G : SimpleGraph V) (X : Set V) (u v : V) : Prop :=
  G.Adj u v ∧ VertexComplete G u X ∧ VertexComplete G v X

/-- PAPER: *"A set `X ⊆ V(G)` is connected if `G|X` is connected (so `∅` is
connected) ..."*

Since the empty set must count as connected, this is Mathlib's
`SimpleGraph.Preconnected` (every two vertices are joined by a walk) rather than
`SimpleGraph.Connected`, which additionally demands nonemptiness. -/
def ConnectedSet (G : SimpleGraph V) (X : Set V) : Prop := (G.induce X).Preconnected

/-- PAPER: *"... and [`X` is] anticonnected if `G̅|X` is connected."* -/
def AnticonnectedSet (G : SimpleGraph V) (X : Set V) : Prop := ConnectedSet Gᶜ X

/-- PAPER: *"A maximal connected subset of a nonempty set `A ⊆ V(G)` is called a
component of `A` ..."*

`C` is a component of `A` if `C ⊆ A`, `C` is connected, and `C` is maximal with
these two properties. -/
def IsComponent (G : SimpleGraph V) (A C : Set V) : Prop :=
  C ⊆ A ∧ ConnectedSet G C ∧ ∀ D : Set V, C ⊆ D → D ⊆ A → ConnectedSet G D → D = C

/-- PAPER: *"... and a maximal anticonnected subset is called an anticomponent of
`A`."*

That is, an anticomponent of `A` in `G` is a component of `A` in `Gᶜ`. -/
def IsAnticomponent (G : SimpleGraph V) (A C : Set V) : Prop := IsComponent Gᶜ A C

/-- PAPER: *"Let `A, B` be disjoint subsets of `V(G)`.  We say the pair `(A,B)` is
balanced if there is no odd path between nonadjacent vertices in `B` with interior
in `A`, and there is no odd antipath between adjacent vertices in `A` with
interior in `B`."*

Disjointness of `A` and `B` is a hypothesis of the surrounding statements in the
paper, so it is not part of this definition. -/
def Balanced (G : SimpleGraph V) (A B : Set V) : Prop :=
  (∀ (u v : V) (p : List V), u ∈ B → v ∈ B → ¬ G.Adj u v → IsPathFrom G p u v →
      (∀ x ∈ SPGT.interior p, x ∈ A) → ¬ Odd (pathLength p)) ∧
  (∀ (u v : V) (p : List V), u ∈ A → v ∈ A → G.Adj u v → IsAntipathFrom G p u v →
      (∀ x ∈ SPGT.interior p, x ∈ B) → ¬ Odd (pathLength p))

/-- PAPER: statement 1.2 of the paper reads *"A graph is perfect if and only if it
is Berge."*  A counterexample to 1.2 is therefore a graph for which being perfect
and being Berge do not agree.

Ranging over `SimpleGraph (Fin n)` for all `n : ℕ` is how we quantify over all
finite graphs: every finite simple graph is isomorphic to one of these. -/
def IsCounterexampleToSPGT {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ¬ (IsPerfect H ↔ Berge H)

/-- PAPER: *"By a minimum imperfect graph we mean a counterexample to 1.2 with as
few vertices as possible (in particular, any such graph is Berge and not
perfect)."*

So `G` is a counterexample to "perfect iff Berge", and no finite graph with fewer
vertices is a counterexample. -/
def MinimumImperfect [Fintype V] (G : SimpleGraph V) : Prop :=
  (¬ (IsPerfect G ↔ Berge G)) ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)), (¬ (IsPerfect H ↔ Berge H)) → Fintype.card V ≤ n

end SPGT

end Workspace.Types.Core
