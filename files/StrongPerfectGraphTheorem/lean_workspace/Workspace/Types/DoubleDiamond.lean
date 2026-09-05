import Mathlib
import Workspace.Types.Core

/-!
# Section 14 of the Strong Perfect Graph Theorem: the double diamond

Verbatim transcription of the nine definitions of Section 14 (printed pages 87–88)
of Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*.

Conventions (see `paper/spec/CONVENTIONS.md`):

* the paper's `Ḡ` is Mathlib's `Gᶜ`, and `G|X` is `G.induce X`;
* holes are represented by the list of their vertices in cyclic order,
  via `Workspace.Types.Core.SPGT.IsHoleList`;
* the ambient standing hypotheses of the section ("Let `G` be Berge", "`A, B`
  disjoint subsets of `V(G)`", "`G ∈ F₅`") are *not* built into the definitions;
  as in `Core`, they are supplied by the numbered statements that use them.
-/

namespace Workspace.Types.DoubleDiamond

open Workspace.Types.Core
open Workspace.Types.Core.SPGT

namespace SPGT

variable {V : Type*}

/-- PAPER (printed page 87): *"Now we turn to a different type of subgraph, the
double diamond.  A double diamond means the graph with eight vertices
`a₁, …, a₄, b₁, …, b₄` and with the following adjacencies: every two `aᵢ`'s are
adjacent except `a₃a₄`, every two `bᵢ`'s are adjacent except `b₃b₄`, and `aᵢbᵢ` is
an edge for `1 ≤ i ≤ 4`."*

`IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄` says that these eight *distinct*
vertices of `G` induce a double diamond: the listed pairs are edges of `G` and
every other pair of the eight is a non-edge (which is exactly what it means for
the subgraph of `G` induced on the eight vertices to be a double diamond).  The
first block below lists the `aᵢaⱼ` adjacencies, the second the `bᵢbⱼ`
adjacencies, the third the four edges `aᵢbᵢ`, and the last records that the
remaining twelve pairs `aᵢbⱼ` with `i ≠ j` are non-edges.

Hence the paper's *"`G` contains a double diamond as an induced subgraph"* is
`∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄`. -/
def IsDoubleDiamond (G : SimpleGraph V) (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V) : Prop :=
  ([a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄] : List V).Nodup ∧
    -- every two `aᵢ`'s are adjacent except `a₃a₄`
    (G.Adj a₁ a₂ ∧ G.Adj a₁ a₃ ∧ G.Adj a₁ a₄ ∧ G.Adj a₂ a₃ ∧ G.Adj a₂ a₄ ∧
      ¬ G.Adj a₃ a₄) ∧
    -- every two `bᵢ`'s are adjacent except `b₃b₄`
    (G.Adj b₁ b₂ ∧ G.Adj b₁ b₃ ∧ G.Adj b₁ b₄ ∧ G.Adj b₂ b₃ ∧ G.Adj b₂ b₄ ∧
      ¬ G.Adj b₃ b₄) ∧
    -- `aᵢbᵢ` is an edge for `1 ≤ i ≤ 4`
    (G.Adj a₁ b₁ ∧ G.Adj a₂ b₂ ∧ G.Adj a₃ b₃ ∧ G.Adj a₄ b₄) ∧
    -- there are no further adjacencies among the eight vertices
    (¬ G.Adj a₁ b₂ ∧ ¬ G.Adj a₁ b₃ ∧ ¬ G.Adj a₁ b₄ ∧
      ¬ G.Adj a₂ b₁ ∧ ¬ G.Adj a₂ b₃ ∧ ¬ G.Adj a₂ b₄ ∧
      ¬ G.Adj a₃ b₁ ∧ ¬ G.Adj a₃ b₂ ∧ ¬ G.Adj a₃ b₄ ∧
      ¬ G.Adj a₄ b₁ ∧ ¬ G.Adj a₄ b₂ ∧ ¬ G.Adj a₄ b₃)

/-- PAPER (printed page 87): *"Let `G` be Berge.  If `A, B` are disjoint subsets
of `V(G)`, we say a square in `(A, B)` is a hole `a₁`-`b₁`-`b₂`-`a₂`-`a₁` of
length 4, where `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`."*

The hole is given by the list of its vertices in cyclic order, so "of length 4"
is automatic: `Core.SPGT.holeLength [a₁, b₁, b₂, a₂] = 4`.

As in `Core`, the section's standing hypotheses (`G` Berge, `A` and `B` disjoint)
are not built in; they are supplied wherever the paper states them. -/
def IsSquare (G : SimpleGraph V) (A B : Set V) (a₁ b₁ b₂ a₂ : V) : Prop :=
  IsHoleList G [a₁, b₁, b₂, a₂] ∧ a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B

/-- PAPER (printed page 87): *"The pair `(A, B)` is square-connected if:*

* *`|A|, |B| ≥ 2`,*
* *for every partition `(X, Y)` of `A` with `X, Y` nonempty, there is a square
  `a₁`-`b₁`-`b₂`-`a₂`-`a₁` with `a₁ ∈ X` and `a₂ ∈ Y`*
* *for every partition `(X, Y)` of `B` with `X, Y` nonempty, there is a square
  `a₁`-`b₁`-`b₂`-`a₂`-`a₁` with `b₁ ∈ X` and `b₂ ∈ Y`."*

`|A| ≥ 2` is rendered as `Set.Nontrivial A` (`A` has two distinct members); a
*partition* `(X, Y)` of `A` is a pair of sets with `X ∪ Y = A` and `X` disjoint
from `Y`.

The paper's next sentence — *"It follows that if `(A, B)` is square-connected
then every vertex of `A ∪ B` is in a square"* — is flagged as a consequence, and
so is deliberately not a conjunct of the definition. -/
def SquareConnected (G : SimpleGraph V) (A B : Set V) : Prop :=
  (A.Nontrivial ∧ B.Nontrivial) ∧
    (∀ X Y : Set V, X ∪ Y = A → Disjoint X Y → X.Nonempty → Y.Nonempty →
      ∃ a₁ b₁ b₂ a₂ : V, IsSquare G A B a₁ b₁ b₂ a₂ ∧ a₁ ∈ X ∧ a₂ ∈ Y) ∧
    (∀ X Y : Set V, X ∪ Y = B → Disjoint X Y → X.Nonempty → Y.Nonempty →
      ∃ a₁ b₁ b₂ a₂ : V, IsSquare G A B a₁ b₁ b₂ a₂ ∧ b₁ ∈ X ∧ b₂ ∈ Y)

/-- PAPER (printed page 87): *"An antisquare is a square in `Ḡ`; that is, an
antihole `a₁`-`b₁`-`b₂`-`a₂`-`a₁` with `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`"*.

Since an antihole of `G` is a hole of `Gᶜ` (`Core.SPGT.IsAntiholeList`), this is
literally `IsSquare Gᶜ A B`. -/
def IsAntisquare (G : SimpleGraph V) (A B : Set V) (a₁ b₁ b₂ a₂ : V) : Prop :=
  IsSquare Gᶜ A B a₁ b₁ b₂ a₂

/-- PAPER (printed page 87): *"... and `(A, B)` is antisquare-connected if it is
square-connected in `Ḡ`."* -/
def AntisquareConnected (G : SimpleGraph V) (A B : Set V) : Prop :=
  SquareConnected Gᶜ A B

/-- PAPER (printed page 87): *"We say a quadruple `(A, B, C, D)` of subsets of
`V(G)` is a cube in `G` if it satisfies the following conditions:*

* *`A, B, C, D` are pairwise disjoint and nonempty*
* *`A` is complete to `C`, and `B` to `D`, and `A` is anticomplete to `D`, and
  `B` to `C`*
* *`(A, B)` is square-connected, and `(C, D)` is antisquare-connected."* -/
def IsCube (G : SimpleGraph V) (A B C D : Set V) : Prop :=
  ((Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧
      Disjoint B C ∧ Disjoint B D ∧ Disjoint C D) ∧
    A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ D.Nonempty) ∧
    (Complete G A C ∧ Complete G B D ∧ Anticomplete G A D ∧ Anticomplete G B C) ∧
    (SquareConnected G A B ∧ AntisquareConnected G C D)

/-- PAPER (printed page 87): *"A cube `(A, B, C, D)` is maximal if there is no
cube `(A′, B′, C′, D′)` with `A ⊆ A′`, `B ⊆ B′`, `C ⊆ C′`, and `D ⊆ D′` such that
`(A, B, C, D) ≠ (A′, B′, C′, D′)`."*

Equivalently (and this is the form stated below): `(A, B, C, D)` is a cube, and
every cube `(A′, B′, C′, D′)` containing it componentwise is equal to it. -/
def MaximalCube (G : SimpleGraph V) (A B C D : Set V) : Prop :=
  IsCube G A B C D ∧
    ∀ A' B' C' D' : Set V, IsCube G A' B' C' D' →
      A ⊆ A' → B ⊆ B' → C ⊆ C' → D ⊆ D' → A = A' ∧ B = B' ∧ C = C' ∧ D = D'

/-- PAPER (printed page 87): *"The subgraph `G|(A ∪ B ∪ C ∪ D)` is called the
graph formed by the cube."*

So the vertex set `V(K)` of the graph `K` formed by the cube `(A, B, C, D)` is
`A ∪ B ∪ C ∪ D`, and that is what we write wherever the paper writes `V(K)`. -/
def FormedByCube (G : SimpleGraph V) (A B C D : Set V) :
    SimpleGraph ↥(A ∪ B ∪ C ∪ D) :=
  G.induce (A ∪ B ∪ C ∪ D)

/-- PAPER (printed page 88): *"Say a vertex `v ∈ V(G) \ V(K)` is minor if the
first case of 14.1 applies to it, and major if the second case applies."*

Here `(A, B, C, D)` is a maximal cube forming `K`, and the first case of 14.1
(printed page 87) reads, with `X` the set of neighbours of `v` in `V(K)`:

> *"`X` is a subset of one of `A ∪ B`, `C ∪ D`, `A ∪ C`, `B ∪ D`, and
> `X ∩ (A ∪ C)` is complete to `X ∩ (B ∪ D)`"*.

`V(K)` is `A ∪ B ∪ C ∪ D` and `X` is `G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)`.  The
hypotheses of 14.1 (`G ∈ F₅`, and `(A, B, C, D)` maximal) are supplied by the
statements that use this notion, not built into it. -/
def MinorForCube (G : SimpleGraph V) (A B C D : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∪ D ∧
    (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
      G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ⊆ C ∪ D ∨
      G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ⊆ A ∪ C ∨
      G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ⊆ B ∪ D) ∧
    Complete G (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C))
      (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D))

/-- PAPER (printed page 88): *"Say a vertex `v ∈ V(G) \ V(K)` is minor if the
first case of 14.1 applies to it, and major if the second case applies."*

Here `(A, B, C, D)` is a maximal cube forming `K`, and the second case of 14.1
(printed page 88) reads, with `X` the set of neighbours of `v` in `V(K)`:

> *"`X` includes one of `A ∪ B`, `C ∪ D`, `A ∪ D`, `B ∪ C`, and `(A ∪ D) \ X` is
> anticomplete to `(B ∪ C) \ X`"*.

"`X` includes `S`" means `S ⊆ X`.  As for `MinorForCube`, `V(K)` is
`A ∪ B ∪ C ∪ D`, `X` is `G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)`, and the hypotheses
of 14.1 are supplied by the statements that use this notion. -/
def MajorForCube (G : SimpleGraph V) (A B C D : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∪ D ∧
    (A ∪ B ⊆ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∨
      C ∪ D ⊆ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∨
      A ∪ D ⊆ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∨
      B ∪ C ⊆ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) ∧
    Anticomplete G ((A ∪ D) \ (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)))
      ((B ∪ C) \ (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)))

end SPGT

end Workspace.Types.DoubleDiamond
