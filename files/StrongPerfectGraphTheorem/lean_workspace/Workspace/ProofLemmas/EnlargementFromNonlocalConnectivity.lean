import Workspace.ProofLemmas.Thm55BranchReach
import Workspace.ProofLemmas.Thm55Structure

/-! Adding an edge after promoting the two attachment vertices. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalConnectivity

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.SubdivisionCounting

/-- The promoted skeleton is 3-connected after adding the new edge.
Deleting at most two vertices leaves the old branch vertices connected. Any
remaining component would be contained in one old branch, together with the
separator. The new edge would put both attachment vertices on that branch. -/
theorem three_connected {W : Type*} [Fintype W] (B : SimpleGraph W)
    (hc : CyclicallyThreeConnected B) (a b : W) (hab : a ≠ b)
    (hcover : ∀ v, v ∈ branchVertices B ∨ v = a ∨ v = b)
    (hnb : ¬ ∃ q, IsBranch B q ∧ a ∈ q ∧ b ∈ q) :
    IsKConnected (B ⊔ SimpleGraph.edge a b) 3 := by
  classical
  let C := B ⊔ SimpleGraph.edge a b
  have cedge : C.Adj a b := Or.inr (by simp [SimpleGraph.edge_adj, hab])
  have hcard : 3 < Fintype.card W := by
    obtain ⟨n, J, hJ, ι, _, hi, _⟩ := hc
    have hle := Fintype.card_le_of_injective ι hi
    have hn : 3 < n := by simpa using hJ.1
    simpa only [Fintype.card_fin] using lt_of_lt_of_le hJ.1 hle
  refine ⟨hcard, ?_⟩
  intro S hS
  obtain ⟨z, hzb, hz⟩ : ∃ z ∈ branchVertices B, z ∈ Sᶜ := by
    obtain ⟨n, J, hJ, ι, T, hi, ht, hl, _, hd, hn, _, _⟩ := hc
    have hr := range_subset_branchVertices hi ht hl hd hn
      (three_le_degree_of_three_connected J hJ)
    by_contra hh
    have hs : Set.range ι ⊆ S := by
      intro z hz
      by_contra hnot
      exact hh ⟨z, hr hz, hnot⟩
    have hcard := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    have hn : 3 < n := by simpa using hJ.1
    omega
  have lift_reach : ∀ {x y}, RchIn B Sᶜ x y → RchIn C Sᶜ x y := by
    rintro x y ⟨hx, hy, ⟨w⟩⟩
    exact ⟨hx, hy, ⟨w.map (⟨id, fun {_ _} h => Or.inl h⟩ :
      (B.induce Sᶜ) →g (C.induce Sᶜ))⟩⟩
  have reaches : ∀ x ∈ Sᶜ, RchIn C Sᶜ x z := by
    intro x hx
    by_contra hn
    let E : Set W := {v | v ∈ Sᶜ ∧ ¬ RchIn C Sᶜ v z}
    have hclosedC : ∀ v ∈ E, ∀ w ∈ Sᶜ, C.Adj v w → w ∈ E := by
      intro v hv w hw hvw
      exact ⟨hw, fun h => hv.2 ((RchIn.of_adj hv.1 hw hvw).trans h)⟩
    have hclosedB : ∀ v ∈ E, ∀ w ∈ Sᶜ, B.Adj v w → w ∈ E := by
      intro v hv w hw hvw
      exact hclosedC v hv w hw (Or.inl hvw)
    have hnobranch : ∀ v ∈ E, v ∉ branchVertices B := by
      intro v hv hvb
      exact hv.2 (lift_reach (Thm55BranchReach.branch_rchIn_compl_of_ncard_le_two
        hc S (by omega) hvb hzb hv.1 hz))
    have hxE : x ∈ E := ⟨hx, hn⟩
    have habES : a ∈ E ∪ S ∧ b ∈ E ∪ S := by
      rcases hcover x with hxb | hxa | hxb
      · exact (hnobranch x hxE hxb).elim
      · have haE : a ∈ E := hxa ▸ hxE
        refine ⟨Or.inl haE, ?_⟩
        by_cases hbS : b ∈ S
        · exact Or.inr hbS
        · exact Or.inl (hclosedC a haE b hbS cedge)
      · have hbE : b ∈ E := hxb ▸ hxE
        refine ⟨?_, Or.inl hbE⟩
        by_cases haS : a ∈ S
        · exact Or.inr haS
        · exact Or.inl (hclosedC b hbE a haS cedge.symm)
    obtain ⟨q, hq, hqs, _⟩ := Thm55Structure.branchless_side_contained B hc S E
      (by omega) ⟨x, hxE⟩ (fun _ h => h.1) hclosedB hnobranch
    exact hnb ⟨q, hq, hqs habES.1, hqs habES.2⟩
  haveI : Nonempty (↥Sᶜ) := ⟨⟨z, hz⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨_, _, h⟩ := (reaches x x.2).trans (reaches y y.2).symm
  exact h

end Workspace.ProofLemmas.EnlargementFromNonlocalConnectivity
