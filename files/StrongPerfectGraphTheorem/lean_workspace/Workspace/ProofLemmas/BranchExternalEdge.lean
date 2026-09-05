import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-!
# An edge outside a branch meets it only at an end

This is the intrinsic graph-theoretic fact used in the proof of 7.5(2): an internal vertex of
a branch has degree at most two, while the two branch edges through it already account for two
distinct incident edges.  A third edge therefore cannot meet the branch there.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.BranchExternalEdge

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-- An edge outside a branch cannot meet a branch edge at an internal vertex. -/
theorem external_edge_meets_branch_only_at_ends
    {W : Type*} [Finite W] {H : SimpleGraph W} {B : List W} {a b w : W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    {e f : Sym2 W} (heB : e ∈ trackEdges B) (hfE : f ∈ H.edgeSet)
    (hfout : f ∉ trackEdges B) (hwf : w ∈ f) (hwe : w ∈ e) : w = a ∨ w = b := by
  have hwB : w ∈ B := by
    obtain ⟨i, hi, hie⟩ := heB
    rw [hie] at hwe
    rcases Sym2.mem_iff.mp hwe with h | h
    · rw [h]
      exact List.getElem_mem _
    · rw [h]
      exact List.getElem_mem _
  by_contra hends
  simp only [not_or] at hends
  have hwint : w ∈ trackInterior B := by
    by_contra hnint
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
        hfrom.2.1 hfrom.2.2 hwB hnint with h | h
    · exact hends.1 h
    · exact hends.2 h
  apply hbranch.2.1 w hwint
  obtain ⟨j, hj, hjw⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff B w).mp hwint
  let d₁ : Sym2 W := s(B[j]'(by omega), B[j + 1]'(by omega))
  let d₂ : Sym2 W := s(B[j + 1]'(by omega), B[j + 2]'(by omega))
  have hd₁B : d₁ ∈ trackEdges B := ⟨j, by omega, rfl⟩
  have hd₂B : d₂ ∈ trackEdges B := ⟨j + 1, by omega, rfl⟩
  have hd₁E : d₁ ∈ H.edgeSet := hfrom.1.2.2 j (by omega)
  have hd₂E : d₂ ∈ H.edgeSet := hfrom.1.2.2 (j + 1) (by omega)
  have hwd₁ : w ∈ d₁ := by
    change w ∈ s(B[j]'(by omega), B[j + 1]'(by omega))
    rw [← hjw]
    simp
  have hwd₂ : w ∈ d₂ := by
    change w ∈ s(B[j + 1]'(by omega), B[j + 2]'(by omega))
    rw [← hjw]
    simp
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    dsimp [d₁, d₂] at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · have := hfrom.1.2.1.getElem_inj_iff.mp h
      omega
    · have := hfrom.1.2.1.getElem_inj_iff.mp h
      omega
  have hd₁f : d₁ ≠ f := fun h => hfout (h ▸ hd₁B)
  have hd₂f : d₂ ≠ f := fun h => hfout (h ▸ hd₂B)
  have hsub : ({d₁, d₂, f} : Set (Sym2 W)) ⊆ incidentEdges H w := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨hd₁E, hwd₁⟩
    · exact ⟨hd₂E, hwd₂⟩
    · exact ⟨hfE, hwf⟩
  have hcard : ({d₁, d₂, f} : Set (Sym2 W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨d₁, d₂, f, hd₁d₂, hd₁f, hd₂f, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, Workspace.ProofLemmas.Thm84RungEndDictionary.incidentEdges_ncard] at hle
  exact hle

end Workspace.ProofLemmas.BranchExternalEdge
