import Mathlib
import Workspace.Types.Core

/-!
# Section 16 — odd wheels

Verbatim source: `paper/pdf/S16_Odd_wheels.md`, `## Definitions` block (the section
preamble, printed p. 96).  Every definition below quotes the paper's own sentence.

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a hole is the list `C` of its vertices in cyclic order (`SPGT.IsHoleList`);
* a path is the list of its vertices in order (`SPGT.IsPathList`);
* a vertex set is a `Set V`;
* `V(C)` for a list `C` is `{v | v ∈ C}`.

Throughout, a **cyclically consecutive block** of a list `H` is rendered as a
prefix of some rotation of `H`, i.e. `S <+: H.rotate k` for some `k : ℕ`; as `k`
ranges over `ℕ` this describes exactly the blocks of consecutive entries of `H`,
including the ones that wrap around the end of `H`.
-/

namespace Workspace.Types.Wheels

open Workspace.Types.Core

namespace SPGT

variable {V : Type*}

/-- PAPER (printed p. 96): *"A wheel in a graph `G` is a pair `(C,Y)`, satisfying:*

*   `C` *is a hole of length* `≥ 6`;
*   `Y` *is a non-null anticonnected set disjoint from* `C`;
*   *there are two disjoint* `Y`*-complete edges of* `C`.*"

PAPER (printed p. 96): *"We call `C` the rim and `Y` the hub of the wheel."*  The
*rim* and the *hub* are therefore just names for the two components `C` and `Y` of
the pair; they carry no content beyond the pair itself and so get no separate
definition.

Encoding notes.

* `C` is the list of the vertices of the hole in cyclic order, and its length —
  the paper's length of a cycle — is `SPGT.holeLength C = C.length`.
* "non-null" is `Y.Nonempty`; "disjoint from `C`" says that no vertex of the hole
  lies in `Y`.
* An *edge of* `C` is a pair of adjacent vertices of `C`.  Since a hole is an
  induced subgraph, two vertices of `C` are adjacent in `G` exactly when they are
  cyclically consecutive in `C`; so "`ab` is a `Y`-complete edge of `C`" is
  `a ∈ C`, `b ∈ C` together with `SPGT.EdgeComplete G Y a b` (which already
  contains `G.Adj a b`).
* Two edges are *disjoint* when they have no end in common, i.e. the four listed
  ends are pairwise distinct across the two edges. -/
def IsWheel (G : SimpleGraph V) (C : List V) (Y : Set V) : Prop :=
  (SPGT.IsHoleList G C ∧ 6 ≤ SPGT.holeLength C) ∧
  (Y.Nonempty ∧ SPGT.AnticonnectedSet G Y ∧ ∀ v ∈ C, v ∉ Y) ∧
  (∃ a b c d : V,
    a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
    SPGT.EdgeComplete G Y a b ∧ SPGT.EdgeComplete G Y c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)

/-- PAPER (printed p. 96): *"A maximal path in a path or hole `H` whose vertices
are all `Y`-complete is called a segment or `Y`-segment of `H`."*

`IsSegment G H Y S` says that `S` is a `Y`-segment of `H`.  The ambient
path-or-hole `H` and the candidate segment `S` are both given as lists of
vertices, and `Y : Set V`.

Encoding notes.

* *"a path in `H`"*: `S` is a path of `G` (`SPGT.IsPathList`, so in particular
  non-null and induced) whose vertices are vertices of `H` occupying consecutive
  positions of `H`.  A single definition covers the paper's two cases, "a path or
  hole `H`", by taking the consecutive positions **cyclically**, i.e. `S` (in one
  of its two orientations, since a path has no preferred direction) is a prefix of
  some rotation of `H`.  This is the intended reading when `H` is a hole.  It is
  also correct when `H` is a path: a block of `H` that wraps around the end of the
  list contains the consecutive pair (last vertex of `H`, first vertex of `H`),
  and for a path `H` those two vertices are non-adjacent, so the conjunct
  `SPGT.IsPathList G S` already rules such a block out (when `H` has at most two
  vertices a wrap-around block is just a reordering of a genuine block of `H`).
  Dually, when `H` is a hole, the block consisting of all of `H` is a cycle and is
  likewise excluded by `SPGT.IsPathList G S`.
* *"whose vertices are all `Y`-complete"*: every vertex of `S` satisfies
  `SPGT.VertexComplete G · Y`.
* *"maximal"*: no strictly larger path of `H` with all vertices `Y`-complete
  contains `S`.  Since the objects compared are blocks of the one list `H`,
  containment is recorded on vertex sets: for every `T` with the same three
  properties, if every vertex of `S` is a vertex of `T` then every vertex of `T`
  is a vertex of `S`. -/
def IsSegment (G : SimpleGraph V) (H : List V) (Y : Set V) (S : List V) : Prop :=
  (SPGT.IsPathList G S ∧
    (∃ k : ℕ, S <+: H.rotate k ∨ S.reverse <+: H.rotate k) ∧
    ∀ w ∈ S, w ∈ H ∧ SPGT.VertexComplete G w Y) ∧
  (∀ T : List V,
    SPGT.IsPathList G T →
    (∃ k : ℕ, T <+: H.rotate k ∨ T.reverse <+: H.rotate k) →
    (∀ w ∈ T, w ∈ H ∧ SPGT.VertexComplete G w Y) →
    (∀ w ∈ S, w ∈ T) → ∀ w ∈ T, w ∈ S)

/-- PAPER (printed p. 96): *"A wheel `(C,Y)` is odd if some segment has odd
length."*

The segments meant are the `Y`-segments of the rim `C`, and the length of a
segment is the length of the path, i.e. its number of edges
(`SPGT.pathLength S = S.length - 1`). -/
def IsOddWheel (G : SimpleGraph V) (C : List V) (Y : Set V) : Prop :=
  IsWheel G C Y ∧ ∃ S : List V, IsSegment G C Y S ∧ Odd (SPGT.pathLength S)

/-- PAPER (printed p. 96): *"Let us say that distinct vertices `u,v` of the rim of
a wheel `(C,Y)` have the same wheel-parity if there is a path of the rim joining
them containing an even number of `Y`-complete edges (and hence by 2.3, so does
the second path, if `u,v` are nonadjacent); and opposite wheel-parity
otherwise."*

Encoding notes.

* *"distinct vertices `u,v` of the rim"* is `u ≠ v`, `u ∈ C`, `v ∈ C`.
* *"a path of the rim joining them"* is one of the two arcs of the hole `C`
  between `u` and `v`: a path `P` of `G` whose vertices occupy consecutive
  positions of `C` cyclically (a prefix of some rotation of `C`) and whose two
  ends are `u` and `v`, in either order.  Both arcs arise this way: the arc that
  runs from `u` forwards to `v` is described by `SPGT.IsPathFrom G P u v`, and the
  arc that runs from `v` forwards to `u` by `SPGT.IsPathFrom G P v u`.
* *"containing an even number of `Y`-complete edges"* counts the edges of that arc
  that are `Y`-complete: the set of indices `i` such that the `i`-th edge
  `P[i]P[i+1]` of `P` is `Y`-complete in the sense of `SPGT.EdgeComplete`.
* The parenthetical *"(and hence by 2.3, so does the second path, if `u,v` are
  nonadjacent)"* is a remark on well-definedness, not a further condition, and so
  is not formalized here. -/
def SameWheelParity (G : SimpleGraph V) (C : List V) (Y : Set V) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ C ∧ v ∈ C ∧
  ∃ P : List V,
    (SPGT.IsPathFrom G P u v ∨ SPGT.IsPathFrom G P v u) ∧
    (∃ k : ℕ, P <+: C.rotate k) ∧
    Even {i : ℕ | ∃ h : i + 1 < P.length, SPGT.EdgeComplete G Y P[i] P[i + 1]}.ncard

/-- PAPER (printed p. 96): *"Let us say that distinct vertices `u,v` of the rim of
a wheel `(C,Y)` have the same wheel-parity if there is a path of the rim joining
them containing an even number of `Y`-complete edges (and hence by 2.3, so does
the second path, if `u,v` are nonadjacent); and opposite wheel-parity
otherwise."*

"Otherwise" is read inside the scope the paper sets up, namely that of *distinct
vertices `u,v` of the rim*: `u` and `v` are distinct vertices of `C` for which no
path of the rim joining them contains an even number of `Y`-complete edges.  Thus
`SameWheelParity` and `OppositeWheelParity` are mutually exclusive, and exactly
one of them holds for every pair of distinct vertices of the rim. -/
def OppositeWheelParity (G : SimpleGraph V) (C : List V) (Y : Set V) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ C ∧ v ∈ C ∧ ¬ SameWheelParity G C Y u v

end SPGT

end Workspace.Types.Wheels
