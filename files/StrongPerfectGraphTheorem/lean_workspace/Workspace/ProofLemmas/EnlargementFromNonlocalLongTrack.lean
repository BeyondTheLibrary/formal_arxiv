import Workspace.ProofLemmas.Thm55BranchReach
import Workspace.ProofLemmas.Thm55Structure
import Workspace.ProofLemmas.LineGraphDegree

/-! Tracks joining two vertices which lie on no common branch. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalLongTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W]

/-- Deleting two vertices on no common branch leaves a connected set. The
branch-free side of any separation would put both deleted vertices in one branch. -/
theorem connected_compl_pair {H : SimpleGraph W} (hc : CyclicallyThreeConnected H)
    (a b : W) (hnb : ¬ ∃ q, IsBranch H q ∧ a ∈ q ∧ b ∈ q) :
    ConnectedSet H ({a, b} : Set W)ᶜ := by
  classical
  have hex : ∃ z ∈ branchVertices H, z ∈ ({a, b} : Set W)ᶜ := by
    obtain ⟨n, J, hJ, ι, T, hi, ht, hl, _, hd, hn, _, _⟩ := hc
    have hr := range_subset_branchVertices hi ht hl hd hn
      (three_le_degree_of_three_connected J hJ)
    by_contra hh
    have hs : Set.range ι ⊆ ({a, b} : Set W) := by
      intro z hz
      by_contra hnot
      exact hh ⟨z, hr hz, hnot⟩
    have hcard := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    have htwo : ({a, b} : Set W).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le a ({b} : Set W)
    have hn : 3 < n := by simpa using hJ.1
    omega
  obtain ⟨z, hzb, hz⟩ := hex
  have reaches : ∀ x ∈ ({a, b} : Set W)ᶜ, RchIn H ({a, b} : Set W)ᶜ x z := by
    intro x hx
    by_contra hn
    let E : Set W := {w | w ∈ ({a, b} : Set W)ᶜ ∧
      ¬ RchIn H ({a, b} : Set W)ᶜ w z}
    have hclosed : ∀ v ∈ E, ∀ w ∈ ({a, b} : Set W)ᶜ, H.Adj v w → w ∈ E := by
      intro v hv w hw hvw
      exact ⟨hw, fun h => hv.2 ((RchIn.of_adj hv.1 hw hvw).trans h)⟩
    have hnobranch : ∀ v ∈ E, v ∉ branchVertices H := by
      intro v hv hvb
      exact hv.2 (Thm55BranchReach.branch_rchIn_compl_pair hc hvb hzb hv.1 hz)
    obtain ⟨q, hq, hqs, _⟩ := Thm55Structure.branchless_side_contained H hc
      {a, b} E (by simpa using Set.ncard_insert_le a ({b} : Set W)) ⟨x, hx, hn⟩
      (fun _ h => h.1) hclosed hnobranch
    exact hnb ⟨q, hq, hqs (Or.inr (Or.inl rfl)), hqs (Or.inr (Or.inr rfl))⟩
  intro x y
  obtain ⟨_, _, h⟩ := (reaches x x.2).trans (reaches y y.2).symm
  exact h

/-- The enlargement assertion uses an old track of length at least three.
Choose distinct neighbours of the attachment vertices and join them after deleting
the attachments. The two added end edges give the required length. -/
theorem exists_long_track {H : SimpleGraph W} (hc : CyclicallyThreeConnected H)
    (a b : W) (hab : a ≠ b) (hnadj : ¬ H.Adj a b)
    (hnb : ¬ ∃ q, IsBranch H q ∧ a ∈ q ∧ b ∈ q) :
    ∃ q, IsTrackFrom H q a b ∧ 3 ≤ trackLength q := by
  classical
  have hdeg : ∀ w, 2 ≤ (H.neighborSet w).ncard := by
    obtain ⟨n, J, hJ, hs⟩ := hc
    exact LineGraphDegree.two_le_degree_of_isSubdivision hJ hs
  obtain ⟨y, hy⟩ : (H.neighborSet b).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by have := hdeg b; omega)
  obtain ⟨x, hx, hxy⟩ := Set.exists_ne_of_one_lt_ncard
    (s := H.neighborSet a) (by have := hdeg a; omega) y
  have hxs : x ∈ ({a, b} : Set W)ᶜ := by
    rintro (h | h)
    · exact hx.ne h.symm
    · exact hnadj (h ▸ hx)
  have hys : y ∈ ({a, b} : Set W)ᶜ := by
    rintro (h | h)
    · exact hnadj (h ▸ hy.symm)
    · exact hy.ne h.symm
  have hr : RchIn H ({a, b} : Set W)ᶜ x y :=
    ⟨hxs, hys, connected_compl_pair hc a b hnb ⟨x, hxs⟩ ⟨y, hys⟩⟩
  obtain ⟨w, hw⟩ := NoCrossTrackBranch.walk_of_rchIn hr
  obtain ⟨q, hq, hqw, _⟩ := NoCrossTrackBranch.exists_track_of_walk w
  have hqs : ∀ t ∈ q, t ∈ ({a, b} : Set W)ᶜ := fun t ht => hw t (hqw t ht)
  have ha : a ∉ q := fun h => hqs a h (Or.inl rfl)
  have hb : b ∉ q := fun h => hqs b h (Or.inr rfl)
  have hq2 : 2 ≤ q.length := by
    have hpos : 0 < q.length := List.length_pos_iff.mpr hq.1.1
    by_contra hh
    obtain ⟨t, he⟩ := List.length_eq_one_iff.mp (show q.length = 1 by omega)
    rw [he] at hq
    have hx' : t = x := Option.some.inj hq.2.1
    have hy' : t = y := Option.some.inj hq.2.2
    exact hxy (hx'.symm.trans hy')
  have hqa := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hq)
    hx.symm (by simpa using ha)
  have hqab := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hqa) hy.symm
    (by simp [hb, hab.symm])
  refine ⟨_, hqab, ?_⟩
  simp only [trackLength, List.length_append, List.length_reverse, List.length_cons,
    List.length_nil]
  omega

end Workspace.ProofLemmas.EnlargementFromNonlocalLongTrack
