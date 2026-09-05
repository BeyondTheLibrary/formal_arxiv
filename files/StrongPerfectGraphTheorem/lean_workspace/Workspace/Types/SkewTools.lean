import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions

/-!
# Section 4 vocabulary: loose skew partitions, path pairs, antipath pairs, kernels

Section 4 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas;
published/Annals version, printed pages 14–18) introduces four pieces of vocabulary about a
skew partition `(A,B)` of a graph `G`:

* `SPGT.IsLooseSkewPartition` — `(A,B)` is *loose* (printed p. 15);
* `SPGT.AdmitsLooseSkewPartition` — `G` *admits a loose skew partition* (printed p. 15, 4.2);
* `SPGT.IsPathPair` — `(A',B')` is a *path pair* (printed p. 16);
* `SPGT.IsAntipathPair` — `(A',B')` is an *antipath pair* (printed p. 16);
* `SPGT.IsKernel` — `W` is a *kernel* for the skew partition `(A,B)` (printed p. 17).

Each of these notions is stated by the paper *relative to a skew partition* `(A,B)` of `G`
("If `(A,B)` is a skew partition of `G`, and `A'` is a component of `A`, and `B'` is an
anticomponent of `B`, …"; "Let `(A,B)` be a skew partition of `G`. We say that an
anticonnected subset `W` of `B` …"), so that standing context is carried along as part of the
definition rather than being left implicit.

A path pair and an antipath pair are exactly the two ways the pair `(A',B')` can fail to be
*balanced* in the sense of `SPGT.Balanced` from `Workspace.Types.Core`: the paper's definition
of *balanced* forbids an odd path between nonadjacent vertices of the second set with interior
in the first set, and an odd antipath between adjacent vertices of the first set with interior
in the second set; a path pair (resp. antipath pair) asserts the existence of exactly such a
path (resp. antipath), with the same assignment of ends, interior and adjacency.
-/

set_option autoImplicit false

namespace Workspace.Types.SkewTools

open Workspace.Types.Core Workspace.Types.Decompositions

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (printed p. 15, immediately after the proof of 4.1): *"Let us say a skew partition
`(A,B)` of `G` is **loose** if either some vertex in `B` has no neighbour in some component of
`A`, or some vertex in `A` is complete to some anticomponent of `B`."*

"`b` has no neighbour in `A'`" is `b` being `A'`-anticomplete, and "`a` is complete to `B'`"
is `a` being `B'`-complete; both are the `Core` notions. The two alternatives appear in the
order printed. -/
def IsLooseSkewPartition (G : SimpleGraph V) (A B : Set V) : Prop :=
  SPGT.IsSkewPartition G A B ∧
    ((∃ b ∈ B, ∃ A' : Set V, SPGT.IsComponent G A A' ∧ SPGT.VertexAnticomplete G b A') ∨
      (∃ a ∈ A, ∃ B' : Set V, SPGT.IsAnticomponent G B B' ∧ SPGT.VertexComplete G a B'))

/-- PAPER (printed p. 15, statement 4.2): *"If `G` is Berge, and **admits a loose skew
partition**, then it admits a balanced skew partition."*

`G` admits a loose skew partition if some skew partition `(A,B)` of `G` is loose. -/
def AdmitsLooseSkewPartition (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsLooseSkewPartition G A B

/-- PAPER (printed p. 16, immediately after the proof of 4.3): *"If `(A,B)` is a skew partition
of `G`, and `A'` is a component of `A`, and `B'` is an anticomponent of `B`, we call the pair
`(A',B')` a **path pair** if there is an odd path in `G` with ends nonadjacent vertices of `B'`
and with interior in `A'`; and `(A',B')` is an antipath pair if there is an odd antipath in `G`
with ends adjacent vertices of `A'` and with interior in `B'`."*

The path is given by the list `p` of its vertices in order; its ends are `u` and `v`, its
interior is `SPGT.interior p`, and "odd" refers to its length `SPGT.pathLength p`. -/
def IsPathPair (G : SimpleGraph V) (A B A' B' : Set V) : Prop :=
  SPGT.IsSkewPartition G A B ∧ SPGT.IsComponent G A A' ∧ SPGT.IsAnticomponent G B B' ∧
    ∃ (p : List V) (u v : V),
      u ∈ B' ∧ v ∈ B' ∧ ¬ G.Adj u v ∧ SPGT.IsPathFrom G p u v ∧
        (∀ x ∈ SPGT.interior p, x ∈ A') ∧ Odd (SPGT.pathLength p)

/-- PAPER (printed p. 16, immediately after the proof of 4.3): *"If `(A,B)` is a skew partition
of `G`, and `A'` is a component of `A`, and `B'` is an anticomponent of `B`, we call the pair
`(A',B')` a path pair if there is an odd path in `G` with ends nonadjacent vertices of `B'` and
with interior in `A'`; and `(A',B')` is an **antipath pair** if there is an odd antipath in `G`
with ends adjacent vertices of `A'` and with interior in `B'`."*

The antipath is given by the list `p` of its vertices in order (equivalently, `p` is a path of
`Gᶜ`); its ends are the adjacent vertices `u` and `v` of `A'`, its interior is
`SPGT.interior p`, and "odd" refers to its length `SPGT.pathLength p`. -/
def IsAntipathPair (G : SimpleGraph V) (A B A' B' : Set V) : Prop :=
  SPGT.IsSkewPartition G A B ∧ SPGT.IsComponent G A A' ∧ SPGT.IsAnticomponent G B B' ∧
    ∃ (p : List V) (u v : V),
      u ∈ A' ∧ v ∈ A' ∧ G.Adj u v ∧ SPGT.IsAntipathFrom G p u v ∧
        (∀ x ∈ SPGT.interior p, x ∈ B') ∧ Odd (SPGT.pathLength p)

/-- PAPER (printed p. 17, immediately after the proof of 4.5): *"Let `(A,B)` be a skew partition
of `G`. We say that an anticonnected subset `W` of `B` is a **kernel** for the skew partition if
some component of `A` contains no `W`-complete vertex."* -/
def IsKernel (G : SimpleGraph V) (A B W : Set V) : Prop :=
  SPGT.IsSkewPartition G A B ∧ SPGT.AnticonnectedSet G W ∧ W ⊆ B ∧
    ∃ A' : Set V, SPGT.IsComponent G A A' ∧ ∀ v ∈ A', ¬ SPGT.VertexComplete G v W

end SPGT

end Workspace.Types.SkewTools
