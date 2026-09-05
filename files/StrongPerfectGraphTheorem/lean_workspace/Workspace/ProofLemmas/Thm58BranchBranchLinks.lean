import Workspace.ProofLemmas.Thm58BranchBranchStars
import Workspace.ProofLemmas.Thm58BranchBranchLinkSteps
import Workspace.Types.RousselRubio

/-!
# The two remaining triangle-link constructions in 5.8 (7)

These are the remaining gaps. In the published argument the paths come from a
cycle through the first branch that avoids one end of the second branch, together
with the outside path and part of the second branch. The applications of 2.4 and
the cases where a unique neighbor is an end-edge are proved separately.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- GAP — PAPER (5.8 (7), printed p. 28): "If `p₁` has only one neighbour
`r ∈ R_{u₁v₁}`, then we may assume that `r` is in the interior of `R_{u₁v₁}`,
by (6), and so `r` can be linked onto `T`, contrary to 2.4."

The hypothesis on `r`'s edge expresses that it is internal to the rung: neither
endpoint is a branch-vertex. The triangle can be ordered with two vertices that
are not adjacent to `r`, which is the content needed for the quoted contradiction.
The cycle and the three disjoint paths described just before this sentence remain
to be constructed. -/
theorem singleton_interior_link_gap
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {r : V} (hrK : r ∈ K) (hpr : G.Adj p₁ r)
    (hunique : ∀ y ∈ K, G.Adj p₁ y → y = r)
    (hinternal : ∀ c ∈ branchVertices H, c ∉ (φ.symm ⟨r, hrK⟩).1) :
    ∃ a b c : V, VertexCanBeLinkedOntoTriangle G r a b c ∧
      ¬ G.Adj r a ∧ ¬ G.Adj r b := by
  exfalso
  exact Thm58BranchBranchLinkSteps.interior_singleton_absurd h hq₁ hq₂ hX₁ hX₂ hrK hpr
    hunique hinternal

/-- GAP — PAPER (5.8 (7), printed p. 28): "If `p₁` has two nonadjacent
neighbours in `R_{u₁v₁}`, then `p₁` can be linked onto `T`, again a contradiction."

The three paths are supplied by the cycle through the first branch and the path
through `F` into the second branch. At most one triangle vertex can be a neighbor
of `p₁`, so two can be named first as in the conclusion. Constructing these paths
and checking the cross edges is the remaining gap. -/
theorem nonadjacent_neighbors_link_gap
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    (hpa : G.Adj p₁ a) (hpb : G.Adj p₁ b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b) :
    ∃ a b c : V, VertexCanBeLinkedOntoTriangle G p₁ a b c ∧
      ¬ G.Adj p₁ a ∧ ¬ G.Adj p₁ b := by
  exfalso
  exact Thm58BranchBranchLinkSteps.nonadjacent_neighbors_absurd h hq₁ hq₂ hX₁ hX₂ haK hbK
    hpa hpb hab hnadj

end Workspace.ProofLemmas.Thm58BranchBranch
