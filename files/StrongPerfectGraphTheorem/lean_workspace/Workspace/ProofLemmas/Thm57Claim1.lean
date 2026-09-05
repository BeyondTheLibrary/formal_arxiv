import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim1Konig
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# 5.7, printed claim (1)

PAPER (printed p. 22):

> **(1) We may assume that there are two disjoint edges in `X`.**
>
> For if not, then by König's theorem, there is a vertex of `H` incident with every edge in
> `X`, and then one of statements 2,3 of the theorem hold.  This proves (1).

So the contrapositive-shaped carve-out below: *if no two edges of `X` are disjoint, then
alternative 2 or alternative 3 of 5.7 holds.*  (Alternatives 2 and 3 together are exactly
`Appearances.LocalForLineGraph H X`.)

The `X = ∅` corner is covered by alternative 2: `H` is cyclically 3-connected, hence a
subdivision of a 3-connected `J`, hence has a branch-vertex, and `∅ ⊆ δ(b)`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **5.7 (1)** — if `X` contains no two disjoint edges then 5.7's alternative 2 or 3 holds. -/
theorem thm57Claim1 (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hno : ¬ TwoDisjointEdges H X) :
    Stmt57_2 H X ∨ Stmt57_3 H X := by
  classical
  by_cases hX : X.Nonempty
  · have hmeet : ∀ e ∈ X, ∀ f ∈ X, ¬ DisjointEdges e f := by
      intro e he f hf hdisj
      exact hno ⟨e, he, f, hf, hdisj⟩
    obtain ⟨b, hb⟩ :=
      Thm57Claim1Konig.exists_common_vertex hbip X hXE hX hmeet
    obtain ⟨n, J, hJ, ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hc3
    have hdeg : ∀ u : Fin n, 3 ≤ (J.neighborSet u).ncard := fun u ↦
      SubdivisionCounting.three_le_degree_of_three_connected J hJ u
    have hbv₁ : Set.range ι ⊆ branchVertices H :=
      SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
    have hbv₂ : branchVertices H ⊆ Set.range ι :=
      SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
    by_cases hbBV : b ∈ branchVertices H
    · exact Or.inl ⟨b, hbBV, fun e he ↦ ⟨hXE he, hb e he⟩⟩
    · rcases hcover b with ⟨u, rfl⟩ | ⟨u, v, huv, hbint⟩
      · exact absurd (hbv₁ ⟨u, rfl⟩) hbBV
      · right
        have hTint : ∀ w ∈ trackInterior (T u v), w ∉ branchVertices H := by
          intro w hw hwbv
          exact hnew u v huv w hw (hbv₂ hwbv)
        have hbranch : IsBranch H (T u v) :=
          Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
            (fun h ↦ huv.ne (hι h)) hTint (hbv₁ ⟨u, rfl⟩) (hbv₁ ⟨v, rfl⟩)
        refine ⟨T u v, hbranch, ?_⟩
        intro e he
        exact Thm57Claim1Konig.incidentEdges_subset_trackEdges hrev hdisjint hedges huv hbint
          ⟨hXE he, hb e he⟩
  · obtain ⟨n, J, hJ, ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hc3
    have hdeg : ∀ u : Fin n, 3 ≤ (J.neighborSet u).ncard := fun u ↦
      SubdivisionCounting.three_le_degree_of_three_connected J hJ u
    have hn : 3 < n := by simpa using hJ.1
    left
    refine ⟨ι ⟨0, by omega⟩, ?_, ?_⟩
    · exact SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg
        ⟨⟨0, by omega⟩, rfl⟩
    · intro e he
      exact absurd ⟨e, he⟩ hX

end Workspace.ProofLemmas.Thm57Claim1
