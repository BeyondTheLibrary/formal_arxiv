import Workspace.ProofLemmas.Thm58StarStarBasics
import Workspace.ProofLemmas.Thm57EndgameConnectivity

/-!
# Locality from a common end

The proof of 5.8 (3) applies 5.6, whose last hypothesis is *"no vertex of `V(H)` is incident
with all edges in `A₁ ∪ A₂`"*.  The paper justifies it in one clause: *"Since `X = A₁ ∪ A₂` is
not local, there is no `w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`."*  The step that is left implicit is
that a common end which is *not* a branch-vertex is just as good: such a vertex is internal to
a branch, and then every edge at it is an edge of that branch, so the set is local for the
second reason in the definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapLocal

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- PAPER, proof of 5.8 (3), printed p. 26: *"Since `X = A₁ ∪ A₂` is not local, there is no
`w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`."*  A set of edges of `H` with a common end is local. -/
theorem local_of_common_vertex {m : ℕ} {J : SimpleGraph (Fin m)} {H : SimpleGraph W}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {X : Set (Sym2 W)} {w : W} (hX : X ⊆ incidentEdges H w) :
    LocalForLineGraph H X := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdeg
  have hbrange : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  rcases hcover w with ⟨u, rfl⟩ | ⟨u, v, huv, hwint⟩
  · exact Or.inl ⟨ι u, hrange ⟨u, rfl⟩, hX⟩
  · have hbranch : IsBranch H (T u v) := by
      apply Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
      · exact fun hc => huv.ne (hι hc)
      · intro z hz hzb
        exact hnew u v huv z hz (hbrange hzb)
      · exact hrange ⟨u, rfl⟩
      · exact hrange ⟨v, rfl⟩
    obtain ⟨j, hj, hjw⟩ := (SubdivisionCounting.mem_trackInterior_iff (T u v) w).mp hwint
    refine Or.inr ⟨T u v, hbranch, ?_⟩
    have hsub' : incidentEdges H ((T u v)[j + 1]'(by omega)) ⊆ trackEdges (T u v) :=
      Thm57Claim2Structure.incidentEdges_internal_subset hbranch (by omega) (by omega)
    rw [hjw] at hsub'
    exact hX.trans hsub'

end Workspace.ProofLemmas.Thm58StarStarGapLocal
