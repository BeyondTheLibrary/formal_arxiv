import Workspace.ProofLemmas.Thm57Claim2Connectivity
import Workspace.ProofLemmas.Thm57Claim2Join
import Workspace.ProofLemmas.InducedPathExtraction

/-! # The common outer neighbour in the same-biparity case of 5.7 (2) -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2SameEnds

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.Thm57Claim2DeletedWindow Workspace.ProofLemmas.Thm57Claim2Connectivity
open Workspace.ProofLemmas.Thm57Claim2Join
open Workspace.ProofLemmas.TrackSlice Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A single edge, read as a track. -/
theorem pair_track {H : SimpleGraph W} {a b : W} (hab : H.Adj a b) :
    IsTrackFrom H [a, b] a b := by
  refine ⟨⟨by simp, by simp [hab.ne], ?_⟩, rfl, rfl⟩
  intro k hk
  have hk0 : k = 0 := by simpa using hk
  subst k
  exact hab

/-- PAPER: *"Choose `cᵢaᵢ ∈ Aᵢ` ... if possible such that `a₁ ≠ a₂`. ...
it follows ... that `T` has length 2, that is, `a₁ = a₂`."* -/
theorem outer_neighbors_equal (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hnotrack : NoEvenTrack57 H X) {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (houtside : X \ trackEdges (slice B i j) ⊆ incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hsame : SameBiparity H B[i] B[j]) {a₁ a₂ : W}
    (hA₁ : s(B[i], a₁) ∈ ASet H X (slice B i j) B[i])
    (hA₂ : s(B[j], a₂) ∈ ASet H X (slice B i j) B[j]) : a₁ = a₂ := by
  by_contra hne
  let C := slice B i j
  have hadj₁ : H.Adj B[i] a₁ := hA₁.1.1.1
  have hadj₂ : H.Adj B[j] a₂ := hA₂.1.1.1
  have hcne : B[i]'(by omega) ≠ B[j]'hj := by
    intro h
    have := hB.1.2.1.getElem_inj_iff.mp h
    omega
  have ha₁j : a₁ ≠ B[j]'hj := by
    intro h
    exact hA₁.2 (by rw [h]; exact end_edge_in_window hc3 hB hij hj (h ▸ hadj₁))
  have ha₂i : a₂ ≠ B[i]'(by omega) := by
    intro h
    apply hA₂.2
    rw [h, Sym2.eq_swap]
    exact end_edge_in_window hc3 hB hij hj (h ▸ hadj₂.symm)
  have ha₁ : a₁ ∈ Outside C \ {B[i], B[j]} :=
    ⟨outside_edge_ends hB hij hj hA₁.1.1.1 hA₁.2 a₁ (by simp), by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hadj₁.ne.symm, ha₁j⟩⟩
  have ha₂ : a₂ ∈ Outside C \ {B[i], B[j]} :=
    ⟨outside_edge_ends hB hij hj hA₂.1.1.1 hA₂.2 a₂ (by simp), by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha₂i, hadj₂.ne.symm⟩⟩
  obtain ⟨R, hRp, hRmem⟩ := InducedPathExtraction.exists_isPathFrom_of_connected
    (window_complement_connected H hc3 hB hij hj) ha₁ ha₂
  have hRd : IsTrackFrom (H.deleteEdges (trackEdges C)) R a₁ a₂ := by
    refine ⟨⟨hRp.1.1, hRp.1.2.1, ?_⟩, hRp.2⟩
    intro k hk
    exact (hRp.1.2.2 k (k + 1) (by omega) hk).2 (Or.inl rfl)
  have hR : IsTrackFrom H R a₁ a₂ :=
    ⟨⟨hRd.1.1, hRd.1.2.1, fun k hk => (SimpleGraph.deleteEdges_adj.mp (hRd.1.2.2 k hk)).1⟩,
      hRd.2⟩
  have hRlen : 2 ≤ R.length := by
    have hpos := List.length_pos_of_ne_nil hR.1.1
    by_contra h
    have hlen1 : R.length = 1 := by omega
    have h1 := track_head hR hpos
    have h2 := last_vertex hR
    rw [getElem_eq_of_index_eq R (show R.length - 1 = 0 by omega) (by omega) (by omega)] at h2
    exact hne (h1.symm.trans h2)
  have hiR : B[i]'(by omega) ∉ R := by
    intro h
    exact (hRmem _ h).2 (Or.inl rfl)
  have hjR : B[j]'hj ∉ R := by
    intro h
    exact (hRmem _ h).2 (Or.inr rfl)
  have hclean : ∀ e ∈ trackEdges R, e ∉ X := by
    rintro e ⟨k, hk, rfl⟩ heX
    have heC := (SimpleGraph.deleteEdges_adj.mp (hRd.1.2.2 k hk)).2
    rcases houtside ⟨heX, heC⟩ with he | he
    · rcases Sym2.mem_iff.mp he.2 with h | h
      · exact hiR (h ▸ List.getElem_mem (by omega))
      · exact hiR (h ▸ List.getElem_mem hk)
    · rcases Sym2.mem_iff.mp he.2 with h | h
      · exact hjR (h ▸ List.getElem_mem (by omega))
      · exact hjR (h ▸ List.getElem_mem hk)
  have hP := pair_track hadj₁
  have hcommon : ∀ w ∈ [B[i]'(by omega), a₁], w ∈ R → w = a₁ := by
    intro w hw hwR
    rcases List.mem_cons.mp hw with h | h
    · exact (hiR (h ▸ hwR)).elim
    · exact List.mem_singleton.mp h
  have hjP : B[j]'hj ∉ [B[i]'(by omega), a₁] := by
    simp [hcne.symm, ha₁j.symm]
  have hodd := clean_join_odd hnotrack hP hR (by simp) hRlen hcommon hjP hjR
    hadj₂.symm hA₁.1.2 (by simpa only [Sym2.eq_swap] using hA₂.1.2)
    (fun e he _ => head_edge_unique hP.1 (by simp) he (by
      obtain ⟨k, hk, rfl⟩ := he
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp)) hclean
  obtain ⟨hglue, hmem⟩ := Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
    H [B[i]'(by omega), a₁] R B[i] a₁ a₂ hP hR hcommon
  have hjglue : B[j]'hj ∉ [B[i]'(by omega), a₁] ++ R.tail := by
    intro h
    rcases hmem _ h with h | h
    · exact hjP h
    · exact hjR h
  have heven := hsame _ (isTrackFrom_concat hglue hadj₂.symm hjglue)
  simp only [trackLength, List.length_append, List.length_cons, List.length_nil,
    List.length_tail, Nat.even_iff, Nat.odd_iff] at heven hodd
  omega

/-- PAPER: *"We deduce that there is a vertex `a` ... such that `Aᵢ = {cᵢa}` for `i = 1,2`."* -/
theorem common_outer_neighbor (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hnotrack : NoEvenTrack57 H X) {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hA₁ : (ASet H X (slice B i j) B[i]).Nonempty)
    (hA₂ : (ASet H X (slice B i j) B[j]).Nonempty)
    (houtside : X \ trackEdges (slice B i j) ⊆ incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hsame : SameBiparity H B[i] B[j]) :
    ∃ a : W, ASet H X (slice B i j) B[i] = {s(B[i], a)} ∧
      ASet H X (slice B i j) B[j] = {s(B[j], a)} := by
  obtain ⟨e, he⟩ := hA₁
  obtain ⟨f, hf⟩ := hA₂
  obtain ⟨a, hea⟩ := Sym2.mem_iff_exists.mp he.1.1.2
  obtain ⟨b, hfb⟩ := Sym2.mem_iff_exists.mp hf.1.1.2
  subst e
  subst f
  have hab := outer_neighbors_equal H hc3 X hnotrack hB hij hj houtside hsame he hf
  subst b
  refine ⟨a, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro e he'
      obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp he'.1.1.2
      have h := outer_neighbors_equal H hc3 X hnotrack hB hij hj houtside hsame he' hf
      simpa [h]
    · exact Set.singleton_subset_iff.mpr he
  · apply Set.Subset.antisymm
    · intro e he'
      obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp he'.1.1.2
      have h := outer_neighbors_equal H hc3 X hnotrack hB hij hj houtside hsame he he'
      simpa [← h]
    · exact Set.singleton_subset_iff.mpr hf

end Workspace.ProofLemmas.Thm57Claim2SameEnds
