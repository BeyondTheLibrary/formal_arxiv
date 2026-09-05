import Workspace.ProofLemmas.Thm61Claim12Common

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Claim12ThirdEdge

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.Thm61BranchChoice

/-- Claim (12): "If `v ≠ b₃` and `v` has degree 3, then the third edge incident with `v`
is `vb₃`." Since this edge meets the first edge of `B₃`, that branch has length one. -/
theorem third_edge
    {m n : ℕ} (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (H : SimpleGraph (Fin n)) (hsub : IsBipartiteSubdivision J H)
    {X : Set (Sym2 (Fin n))} {b b₁ b₃ v : Fin n}
    {B₃ : List (Fin n)} {e₃ d₁ d₂ : Sym2 (Fin n)}
    (hB₃ : IsBranch H B₃) (hfrom₃ : IsTrackFrom H B₃ b b₃)
    (hB₃pos : 1 ≤ trackLength B₃) (he₃B₃ : e₃ ∈ trackEdges B₃)
    (he₃ : e₃ ∈ incidentEdges H b) (hbb₃ : b ≠ b₃)
    (h01 : H.Adj b b₁) (h1v : H.Adj b₁ v)
    (hvb : v ≠ b) (hvb₃ : v ≠ b₃)
    (hvdeg : (H.neighborSet v).ncard = 3)
    (hd₁d₂ : d₁ ≠ d₂)
    (hother : ∀ g ∈ incidentEdges H v, g ≠ d₁ → g ≠ d₂ → g ∈ X ∧ MeetEdges g e₃) :
    s(v, b₃) ∈ incidentEdges H v ∧ s(v, b₃) ≠ d₁ ∧ s(v, b₃) ≠ d₂ ∧
      s(v, b₃) ∈ X ∧ e₃ = s(b, b₃) ∧ trackLength B₃ = 1 := by
  classical
  obtain ⟨g, hg, hg₁, hg₂⟩ : ∃ g ∈ incidentEdges H v, g ≠ d₁ ∧ g ≠ d₂ := by
    by_contra hn
    have hs : incidentEdges H v ⊆ ({d₁, d₂} : Set (Sym2 (Fin n))) := by
      intro e he
      by_cases h₁ : e = d₁
      · simp [h₁]
      by_cases h₂ : e = d₂
      · simp [h₂]
      exact False.elim (hn ⟨e, he, h₁, h₂⟩)
    have hle := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [incidentEdges_ncard, hvdeg, Set.ncard_pair hd₁d₂] at hle
    omega
  obtain ⟨hgX, hmeet⟩ := hother g hg hg₁ hg₂
  have hvV : v ∈ branchVertices H := by change 3 ≤ _; omega
  have hgB : g ∉ trackEdges B₃ := fun h =>
    branch_edge_avoids_other_branchVertex hB₃ hfrom₃ h hvV hvb hvb₃ hg.2
  obtain ⟨w, hwg, hwe⟩ := exists_common_end hmeet
  have hwb₃ : w = b₃ := by
    rcases external_edge_meets_branch_only_at_ends hB₃ hfrom₃ he₃B₃ hg.1 hgB hwg hwe with hw | hw
    · have heq : g = s(b, v) := eq_sym2_of_mem_mem hvb.symm (hw ▸ hwg) hg.2
      exact False.elim (no_triangle_of_bipartite hsub.2 h01 h1v
        (H.mem_edgeSet.mp (heq ▸ hg.1)))
    · exact hw
  have hgeq : g = s(v, b₃) := eq_sym2_of_mem_mem hvb₃ hg.2 (hwb₃ ▸ hwg)
  have heq : e₃ = s(b, b₃) := eq_sym2_of_mem_mem hbb₃ he₃.2 (hwb₃ ▸ hwe)
  have hadj : H.Adj b b₃ := H.mem_edgeSet.mp (heq ▸ he₃.1)
  exact ⟨hgeq ▸ hg, hgeq ▸ hg₁, hgeq ▸ hg₂, hgeq ▸ hgX, heq,
    branch_length_one_of_adj J hJ H hsub.1 hB₃ hfrom₃ hB₃pos hadj⟩

end Workspace.ProofLemmas.Thm61Claim12ThirdEdge
