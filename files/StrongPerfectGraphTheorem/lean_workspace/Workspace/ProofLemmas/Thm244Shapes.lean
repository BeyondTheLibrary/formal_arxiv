import Mathlib
import Workspace.Types.Core

/-!
# The three shapes of the printed proof of 24.4

The proof of 24.4 (Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph
Theorem*, printed p. 144) chooses `F` minimal and then says, with no argument:

> From the minimality of `F`, there are (up to symmetry) three cases:
>
> 1. for `i = 1,2,3` there is a unique `Xᵢ`-complete vertex `vᵢ ∈ F`; there is a
>    vertex `u ∈ F` different from `v₁,v₂,v₃`, and three paths `P₁,P₂,P₃` in `F`,
>    all of length `≥ 1`, such that each `Pᵢ` is from `vᵢ` to `u`, and for
>    `1 ≤ i < j ≤ 3`, `V(Pᵢ \ u)` is disjoint from `V(Pⱼ \ u)` and there is no edge
>    between them, or
> 2. for `i = 1,2,3` there is a unique `Xᵢ`-complete vertex `vᵢ ∈ F`; there are
>    three paths `P₁,P₂,P₃` in `F`, where each `Pᵢ` is from `vᵢ` to some `uᵢ` say,
>    possibly of length 0; and for `1 ≤ i < j ≤ 3`, `V(Pᵢ)` is disjoint from
>    `V(Pⱼ)` and the only edge between `V(Pᵢ), V(Pⱼ)` is `uᵢuⱼ`, or
> 3. for `i = 1,2` there is a unique `Xᵢ`-complete vertex `vᵢ ∈ F`, and there is a
>    path `P` in `F` between `v₁,v₂` containing at least one `X₃`-complete vertex.

This module contains **only the three predicates**, so that the derivation of the
trichotomy (`Workspace.ProofLemmas.Thm244Trichotomy`) and the three refutations
(`Thm244Case1`, `Thm244Case2`, `Thm244Case3`) can be developed against one frozen
interface.

The predicates are stated for an arbitrary family `N : Fin 3 → Set V` of pairwise
disjoint "terminal" sets, because the trichotomy itself is a purely
graph-theoretic statement about a minimal connected set meeting three sets.  At
the 24.4 call site one takes `N i = {w | VertexComplete G w (X i)}`.  Indexing by
`Fin 3` (rather than by three separate names `X₁ X₂ X₃`) is what makes the
paper's *"up to symmetry"* a one-line reindexing at the call sites.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm244Shapes

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- **Case 1 of the trichotomy — a spider with centre `u`.**

*"there is a unique `Nᵢ`-vertex `vᵢ ∈ F`; there is a vertex `u ∈ F` different from
`v₁,v₂,v₃`, and three paths `P₁,P₂,P₃` in `F`, all of length `≥ 1`, such that each
`Pᵢ` is from `vᵢ` to `u`, and for `i ≠ j`, `V(Pᵢ \ u)` is disjoint from
`V(Pⱼ \ u)` and there is no edge between them."*

*"all of length `≥ 1`"* is not a separate conjunct: it follows from `u ≠ v i`
together with `IsPathFrom G (P i) (v i) u`. -/
def Spider (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V)
    (v : Fin 3 → V) (u : V) (P : Fin 3 → List V) : Prop :=
  (∀ i : Fin 3, v i ∈ N i) ∧
  (∀ i : Fin 3, ∀ w ∈ F, w ∈ N i → w = v i) ∧
  (∀ i : Fin 3, u ≠ v i) ∧
  (∀ i : Fin 3, IsPathFrom G (P i) (v i) u) ∧
  (∀ i : Fin 3, ∀ w ∈ P i, w ∈ F) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a ≠ u → b ≠ u → a ≠ b ∧ ¬ G.Adj a b)

/-- **Case 2 of the trichotomy — three legs hanging off a triangle.**

*"there is a unique `Nᵢ`-vertex `vᵢ ∈ F`; there are three paths `P₁,P₂,P₃` in `F`,
where each `Pᵢ` is from `vᵢ` to some `uᵢ` say, possibly of length 0; and for
`i ≠ j`, `V(Pᵢ)` is disjoint from `V(Pⱼ)` and the only edge between `V(Pᵢ),V(Pⱼ)`
is `uᵢuⱼ`."*

Note that *"the only edge … **is** `uᵢuⱼ`"* asserts in particular that `uᵢuⱼ` **is**
an edge, so `{u₁,u₂,u₃}` is a triangle; that is recovered from the last conjunct
by instantiating it at `a := u i`, `b := u j`. -/
def TriangleLegs (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V)
    (v u : Fin 3 → V) (P : Fin 3 → List V) : Prop :=
  (∀ i : Fin 3, v i ∈ N i) ∧
  (∀ i : Fin 3, ∀ w ∈ F, w ∈ N i → w = v i) ∧
  (∀ i : Fin 3, IsPathFrom G (P i) (v i) (u i)) ∧
  (∀ i : Fin 3, ∀ w ∈ P i, w ∈ F) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a ≠ b) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, (G.Adj a b ↔ (a = u i ∧ b = u j)))

/-- **Case 3 of the trichotomy — a single path through the third terminal.**

*"for `i = 1,2` there is a unique `Nᵢ`-vertex `vᵢ ∈ F`, and there is a path `P` in
`F` between `v₁,v₂` containing at least one `N₃`-vertex."*

The paper's *"up to symmetry"* is the explicit choice of which two of the three
indices play the roles of `1, 2`; here that is the triple `i, j, k` of pairwise
distinct elements of `Fin 3`. -/
def ThroughPath (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V)
    (i j k : Fin 3) (P : List V) (a b : V) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
  IsPathFrom G P a b ∧
  (∀ w ∈ P, w ∈ F) ∧
  a ∈ N i ∧ b ∈ N j ∧
  (∀ w ∈ F, w ∈ N i → w = a) ∧
  (∀ w ∈ F, w ∈ N j → w = b) ∧
  (∃ w ∈ P, w ∈ N k)

end Workspace.ProofLemmas.Thm244Shapes
