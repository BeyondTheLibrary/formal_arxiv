import Mathlib
import Workspace.Types.Core

/-!
# Prisms, even/odd prisms, and hyperprisms

Transcription of the definitions of Section 7 (*Rung replacement*, printed
pp. 34–35) and Section 10 (*The even prism*, printed pp. 56 and 60–61) of
Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*
(published version).

Conventions (see `paper/spec/CONVENTIONS.md`):

* a path of the paper is given by the list of its vertices in order
  (`SPGT.IsPathList`, `SPGT.IsPathFrom`); its length is `SPGT.pathLength`
  (one less than the number of vertices) and its interior `P*` is
  `SPGT.interior`;
* the vertex set `V(P)` of such a list `P` is `{v | v ∈ P}`, so "`u ∈ V(P)`"
  is written `u ∈ P`;
* the paper's indices `1, 2, 3` are the three elements `0, 1, 2` of `Fin 3`,
  so the paper's `a₁, a₂, a₃` are `a 0, a 1, a 2`.

The words *saturates*, *major* and *local* are defined several times in the
paper, for different objects; each name below therefore records the object it
refers to — `SaturatesPrism`, `MajorForPrism`, `LocalForPrism` and
`LocalForHyperprism` — to keep those senses apart.
-/

namespace Workspace.Types.Prisms

open Workspace.Types.Core

namespace SPGT

variable {V : Type*}

/-- PAPER (§7, printed pp. 34–35): *"A prism means a graph consisting of two
vertex-disjoint triangles `{a₁, a₂, a₃}`, `{b₁, b₂, b₃}`, and three paths
`P₁, P₂, P₃`, where each `Pᵢ` has ends `aᵢ, bᵢ`, and for `1 ≤ i < j ≤ 3` the
only edges between `V(Pᵢ)` and `V(Pⱼ)` are `aᵢaⱼ` and `bᵢbⱼ`."*

PAPER (§7, printed p. 35): *"The three paths `P₁, P₂, P₃` are said to form the
prism."*

So `FormPrism G a b P₁ P₂ P₃` says that the three paths `P₁, P₂, P₃` of `G`
form a prism of `G` with triangles `{a 0, a 1, a 2}` and `{b 0, b 1, b 2}`.
The conjuncts are, in order:

* `{a₁, a₂, a₃}` is a triangle (three pairwise adjacent vertices; adjacency in
  a simple graph forces them to be distinct);
* `{b₁, b₂, b₃}` is a triangle;
* the two triangles are vertex-disjoint;
* for each `i`, `Pᵢ` is a path of `G` with ends `aᵢ` and `bᵢ`;
* for `1 ≤ i < j ≤ 3`, an edge of `G` runs between `V(Pᵢ)` and `V(Pⱼ)`
  **exactly when** it is `aᵢaⱼ` or `bᵢbⱼ` — the paper's "the only edges …
  are …" asserts both that these two are edges and that there are no others,
  so it is rendered as an `↔`.

Nothing further is imposed: that `P₁, P₂, P₃` are pairwise vertex-disjoint,
and that each has length ≥ 1, are consequences of the above, and are therefore
not stated. -/
def FormPrism (G : SimpleGraph V) (a b : Fin 3 → V) (P₁ P₂ P₃ : List V) : Prop :=
  (∀ i j : Fin 3, i ≠ j → G.Adj (a i) (a j)) ∧
  (∀ i j : Fin 3, i ≠ j → G.Adj (b i) (b j)) ∧
  (∀ i j : Fin 3, a i ≠ b j) ∧
  SPGT.IsPathFrom G P₁ (a 0) (b 0) ∧
  SPGT.IsPathFrom G P₂ (a 1) (b 1) ∧
  SPGT.IsPathFrom G P₃ (a 2) (b 2) ∧
  (∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a 0 ∧ v = a 1) ∨ (u = b 0 ∧ v = b 1))) ∧
  (∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a 0 ∧ v = a 2) ∨ (u = b 0 ∧ v = b 2))) ∧
  (∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a 1 ∧ v = a 2) ∨ (u = b 1 ∧ v = b 2)))

/-- PAPER (§7, printed pp. 34–35): *"A prism means a graph consisting of two
vertex-disjoint triangles `{a₁, a₂, a₃}`, `{b₁, b₂, b₃}`, and three paths
`P₁, P₂, P₃`, …"*

The paper writes `K` for the prism itself and `V(K)` for its vertex set (as in
10.1: *"Let `R₁, R₂, R₃` form a prism `K` in a Berge graph `G` …"*, and
`F ⊆ V(G) \ V(K)`).  Since a prism of `G` is an induced subgraph of `G`, it is
determined by its vertex set, which is the union of the vertex sets of the
three paths forming it.  `IsPrism G K` says that `K : Set V` is the vertex set
of a prism of `G`. -/
def IsPrism (G : SimpleGraph V) (K : Set V) : Prop :=
  ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
    FormPrism G a b P₁ P₂ P₃ ∧
      K = {v | v ∈ P₁} ∪ {v | v ∈ P₂} ∪ {v | v ∈ P₃}

/-- PAPER (§7, printed p. 35): *"The prism is long if at least one of the three
paths has length > 1."*

`IsLongPrism G a b P₁ P₂ P₃` says that `P₁, P₂, P₃` form a prism of `G` with
triangles `{a 0, a 1, a 2}`, `{b 0, b 1, b 2}`, and that this prism is long. -/
def IsLongPrism (G : SimpleGraph V) (a b : Fin 3 → V) (P₁ P₂ P₃ : List V) : Prop :=
  FormPrism G a b P₁ P₂ P₃ ∧
    (1 < SPGT.pathLength P₁ ∨ 1 < SPGT.pathLength P₂ ∨ 1 < SPGT.pathLength P₃)

/-- PAPER (§10, printed p. 56): *"By 7.2, the three paths `R₁, R₂, R₃` all have
lengths of the same parity.  A prism is even if the three paths `R₁, R₂, R₃`
have even length, and odd otherwise."*

`IsEvenPrism G a b R₁ R₂ R₃` says that `R₁, R₂, R₃` form a prism of `G` with
triangles `{a 0, a 1, a 2}`, `{b 0, b 1, b 2}`, and that this prism is even.
(The quoted appeal to 7.2 is a remark about Berge graphs, not part of the
definition, so it is not built in.) -/
def IsEvenPrism (G : SimpleGraph V) (a b : Fin 3 → V) (R₁ R₂ R₃ : List V) : Prop :=
  FormPrism G a b R₁ R₂ R₃ ∧
    Even (SPGT.pathLength R₁) ∧ Even (SPGT.pathLength R₂) ∧ Even (SPGT.pathLength R₃)

/-- PAPER (§10, printed p. 56): *"A prism is even if the three paths
`R₁, R₂, R₃` have even length, and odd otherwise."*

So a prism is odd exactly when it fails to be even, i.e. when it is not the
case that all three of `R₁, R₂, R₃` have even length.  (In a Berge graph the
three lengths have the same parity, by 7.2, so there "odd" amounts to all
three lengths being odd; that is a theorem about Berge graphs and is not part
of the definition.) -/
def IsOddPrism (G : SimpleGraph V) (a b : Fin 3 → V) (R₁ R₂ R₃ : List V) : Prop :=
  FormPrism G a b R₁ R₂ R₃ ∧
    ¬ (Even (SPGT.pathLength R₁) ∧ Even (SPGT.pathLength R₂) ∧ Even (SPGT.pathLength R₃))

/-- PAPER (§10, printed p. 56): *"A subset `X ⊆ V(G)` saturates the prism if at
least two vertices of each triangle belong to `X`."*

The two triangles of the prism are `{a 0, a 1, a 2}` and `{b 0, b 1, b 2}`, so
this says that each of these two three-element sets meets `X` in at least two
vertices. -/
def SaturatesPrism (a b : Fin 3 → V) (X : Set V) : Prop :=
  2 ≤ (({a 0, a 1, a 2} : Set V) ∩ X).ncard ∧
  2 ≤ (({b 0, b 1, b 2} : Set V) ∩ X).ncard

/-- PAPER (§10, printed p. 56): *"… and a vertex is major with respect to the
prism if its neighbour set saturates it."* -/
def MajorForPrism (G : SimpleGraph V) (a b : Fin 3 → V) (v : V) : Prop :=
  SaturatesPrism a b (G.neighborSet v)

/-- PAPER (§10, printed p. 56): *"A subset `X ⊆ V(K)` is local with respect to
the prism if either `X ⊆ V(Rᵢ)` for some `i`, or `X` is a subset of one of the
triangles."*

Here `K` is the prism formed by the three paths `R₁, R₂, R₃`, and its two
triangles are `{a 0, a 1, a 2}` and `{b 0, b 1, b 2}`.  The ambient assumption
`X ⊆ V(K)` is not restated as a conjunct: it is implied by each of the five
alternatives, since each triangle vertex `aᵢ` (resp. `bᵢ`) is an end of `Rᵢ`
and hence lies in `V(K)`. -/
def LocalForPrism (a b : Fin 3 → V) (R₁ R₂ R₃ : List V) (X : Set V) : Prop :=
  X ⊆ {v | v ∈ R₁} ∨ X ⊆ {v | v ∈ R₂} ∨ X ⊆ {v | v ∈ R₃} ∨
    X ⊆ ({a 0, a 1, a 2} : Set V) ∨ X ⊆ ({b 0, b 1, b 2} : Set V)

/-- PAPER (§10, printed p. 60, in the proof of 10.6): *"For `1 ≤ i ≤ 3`, a path
from `Aᵢ` to `Bᵢ` with interior in `Cᵢ` is called an `i`-rung."*

`IsRungOfHyperprism G A B C i p` says that the list `p` is an `i`-rung for the
nine sets `Aⱼ, Bⱼ, Cⱼ` (`j : Fin 3`): a path of `G` one of whose ends lies in
`A i` and the other in `B i`, all of whose internal vertices lie in `C i`. -/
def IsRungOfHyperprism (G : SimpleGraph V) (A B C : Fin 3 → Set V) (i : Fin 3)
    (p : List V) : Prop :=
  ∃ x y : V, x ∈ A i ∧ y ∈ B i ∧ SPGT.IsPathFrom G p x y ∧ ∀ w ∈ SPGT.interior p, w ∈ C i

/-- PAPER (§10, printed p. 60, in the proof of 10.6): *"… we can choose in `G` a
collection of nine sets*

```
A₁ C₁ B₁
A₂ C₂ B₂
A₃ C₃ B₃
```

*with the following properties:*

* *all these sets are nonempty and pairwise disjoint*
* *for `1 ≤ i < j ≤ 3`, `Aᵢ` is complete to `Aⱼ` and `Bᵢ` is complete to `Bⱼ`,
  and there are no other edges between `Aᵢ ∪ Bᵢ ∪ Cᵢ` and `Aⱼ ∪ Bⱼ ∪ Cⱼ`*
* *for `1 ≤ i ≤ 3`, every vertex of `Aᵢ ∪ Bᵢ ∪ Cᵢ` belongs to a path between
  `Aᵢ` and `Bᵢ` with interior in `Cᵢ`*
* *some path between `A₁` and `B₁` with interior in `C₁` is even.*

*We call this collection of nine sets a hyperprism."*

"Pairwise disjoint" is spelled out as the six families of disjointness
conditions between the nine sets `A i, B i, C i` (`i : Fin 3`).  "There are no
other edges" is the implication that any edge between `Aᵢ ∪ Bᵢ ∪ Cᵢ` and
`Aⱼ ∪ Bⱼ ∪ Cⱼ` runs from `Aᵢ` to `Aⱼ` or from `Bᵢ` to `Bⱼ`.  A "path between
`Aᵢ` and `Bᵢ` with interior in `Cᵢ`" is an `i`-rung, and a path is even when
its length is even.

(The paper's subsequent instruction *"Choose the hyperprism with `V(H)`
maximal"* is a choice made inside the proof of 10.6, not part of the definition
of a hyperprism, and so is not included here.) -/
def IsHyperprism (G : SimpleGraph V) (A B C : Fin 3 → Set V) : Prop :=
  (∀ i : Fin 3, (A i).Nonempty ∧ (B i).Nonempty ∧ (C i).Nonempty) ∧
  (∀ i j : Fin 3, Disjoint (A i) (B j)) ∧
  (∀ i j : Fin 3, Disjoint (A i) (C j)) ∧
  (∀ i j : Fin 3, Disjoint (B i) (C j)) ∧
  (∀ i j : Fin 3, i ≠ j → Disjoint (A i) (A j)) ∧
  (∀ i j : Fin 3, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i j : Fin 3, i ≠ j → Disjoint (C i) (C j)) ∧
  (∀ i j : Fin 3, i < j →
      SPGT.Complete G (A i) (A j) ∧ SPGT.Complete G (B i) (B j) ∧
        ∀ u ∈ A i ∪ B i ∪ C i, ∀ v ∈ A j ∪ B j ∪ C j,
          G.Adj u v → (u ∈ A i ∧ v ∈ A j) ∨ (u ∈ B i ∧ v ∈ B j)) ∧
  (∀ i : Fin 3, ∀ v ∈ A i ∪ B i ∪ C i,
      ∃ p : List V, IsRungOfHyperprism G A B C i p ∧ v ∈ p) ∧
  (∃ p : List V, IsRungOfHyperprism G A B C 0 p ∧ Even (SPGT.pathLength p))

/-- PAPER (§10, printed p. 61, in the proof of 10.6): *"A subset `X ⊆ V(H)` is
local (with respect to the hyperprism) if `X` is a subset of one of
`S₁, S₂, S₃, A` or `B`."*

Here (printed p. 60) *"`Sᵢ = Aᵢ ∪ Bᵢ ∪ Cᵢ` for `1 ≤ i ≤ 3`, and
`A = A₁ ∪ A₂ ∪ A₃`, and `B = B₁ ∪ B₂ ∪ B₃`"*, and `H` is the subgraph of `G`
induced on the union of the nine sets.  The ambient assumption `X ⊆ V(H)` is
not restated as a conjunct: it is implied by each of the five alternatives. -/
def LocalForHyperprism (A B C : Fin 3 → Set V) (X : Set V) : Prop :=
  X ⊆ A 0 ∪ B 0 ∪ C 0 ∨ X ⊆ A 1 ∪ B 1 ∪ C 1 ∨ X ⊆ A 2 ∪ B 2 ∪ C 2 ∨
    X ⊆ A 0 ∪ A 1 ∪ A 2 ∨ X ⊆ B 0 ∪ B 1 ∪ B 2

end SPGT

end Workspace.Types.Prisms
