import Workspace.ProofLemmas.Thm61EvenFinalTracks
import Workspace.ProofLemmas.Thm85Five8Transported

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenFinalK4

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-- Two branch-vertices joined by one branch. The list fixes the direction of that branch. -/
def Linked {W : Type*} (H : SimpleGraph W) (a b : W) : Prop :=
  ∃ B, IsBranch H B ∧ IsTrackFrom H B a b ∧ 1 ≤ trackLength B

theorem linked_of_adj {W : Type*} {H : SimpleGraph W} {a b : W}
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H) (hab : H.Adj a b) : Linked H a b := by
  have hfrom := HPrimeTracks.isTrackFrom_pair hab
  exact ⟨[a, b], Thm82BranchDelta.isBranch_of_ends_branch hfrom hab.ne
    (by simp [trackInterior]) ha hb, hfrom, by simp [trackLength]⟩

theorem linked_symm {W : Type*} {H : SimpleGraph W} {a b : W} (h : Linked H a b) :
    Linked H b a := by
  obtain ⟨B, hB, hfrom, hpos⟩ := h
  exact ⟨B.reverse, isBranch_reverse hB, TrackSlice.isTrackFrom_reverse hfrom,
    by simpa [trackLength] using hpos⟩

/-- The connectivity step used in (13). Two adjacent vertices of degree three with the
same two other neighbors exhaust a 3-connected graph. Applied before suppressing the
branches, this identifies the original graph with `K₄` and names all its branch-vertices. -/
theorem k4_of_two_triads
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    {a b c d : Fin n} (hnd : [a, b, c, d].Nodup)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H)
    (hc : c ∈ branchVertices H) (hd : d ∈ branchVertices H)
    (hdegA : (H.neighborSet a).ncard = 3) (hdegB : (H.neighborSet b).ncard = 3)
    (hAB : Linked H a b) (hAC : Linked H a c) (hAD : Linked H a d)
    (hBC : Linked H b c) (hBD : Linked H b d) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ branchVertices H = {a, b, c, d} := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrng := SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  obtain ⟨u₀, h0⟩ := hrng ha
  obtain ⟨u₁, h1⟩ := hrng hb
  obtain ⟨u₂, h2⟩ := hrng hc
  obtain ⟨u₃, h3⟩ := hrng hd
  have hij : [u₀, u₁, u₂, u₃].Nodup := by
    have hm : ([u₀, u₁, u₂, u₃].map ι).Nodup := by simpa [h0, h1, h2, h3] using hnd
    exact List.Nodup.of_map ι hm
  have h01 : u₀ ≠ u₁ := by intro h; simp [h] at hij
  have h02 : u₀ ≠ u₂ := by intro h; simp [h] at hij
  have h03 : u₀ ≠ u₃ := by intro h; simp [h] at hij
  have h12 : u₁ ≠ u₂ := by intro h; simp [h] at hij
  have h13 : u₁ ≠ u₃ := by intro h; simp [h] at hij
  have h23 : u₂ ≠ u₃ := by intro h; simp [h] at hij
  have lift_link : ∀ {p q : Fin m} {x y : Fin n},
      ι p = x → ι q = y → Linked H x y → J.Adj p q := by
    rintro p q x y hx hy ⟨B, hB, hfrom, hpos⟩
    exact original_adj_of_branch_ends hι htrack hlen hrev hdisj hnew hcover hedges hdeg
      hB hfrom hpos hx.symm hy.symm
  have j01 := lift_link h0 h1 hAB
  have j02 := lift_link h0 h2 hAC
  have j03 := lift_link h0 h3 hAD
  have j12 := lift_link h1 h2 hBC
  have j13 := lift_link h1 h3 hBD
  have jd0 : (J.neighborSet u₀).ncard = 3 := by
    have h := original_degree_le_subdivision_degree hι htrack hlen hdisj hnew u₀
    rw [h0, hdegA] at h
    exact le_antisymm h (hdeg u₀)
  have jd1 : (J.neighborSet u₁).ncard = 3 := by
    have h := original_degree_le_subdivision_degree hι htrack hlen hdisj hnew u₁
    rw [h1, hdegB] at h
    exact le_antisymm h (hdeg u₁)
  have hall := four_vertices_of_two_degree_three hJ j01 j02 j03 j12 j13 h23 jd0 jd1
  have j23 : J.Adj u₂ u₃ := by
    by_contra hn
    have hs : J.neighborSet u₂ ⊆ ({u₀, u₁} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (J.irrefl hx)
      · exact False.elim (hn hx)
    have hle := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_pair h01] at hle
    have := hdeg u₂
    omega
  refine ⟨iso_top_of_four_vertices h01 h02 h03 h12 h13 h23 hall j01 j02 j03 j12 j13 j23, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hu⟩ := hrng hx
    rcases hall u with rfl | rfl | rfl | rfl <;> simp_all
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

/-- In a subdivision of `K₄`, every two distinct branch-vertices are joined by a branch. -/
theorem linked_of_k4
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    (hiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    {a b : Fin n} (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H) (hne : a ≠ b) :
    Linked H a b := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrng := SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  obtain ⟨u, hu⟩ := hrng ha
  obtain ⟨v, hv⟩ := hrng hb
  obtain ⟨ψ⟩ := hiso
  have huv : J.Adj u v := ψ.map_rel_iff.mp (by
    simp only [SimpleGraph.top_adj]
    intro h
    exact hne (hu.symm.trans ((congrArg ι (ψ.injective h)).trans hv)))
  refine ⟨T u v, subdivision_track_isBranch hι htrack hlen hrev hdisj hnew hcover hedges hdeg huv,
    ?_, hlen u v huv⟩
  simpa only [hu, hv] using htrack u v huv

/-- Four distinct branch-vertices exhaust a subdivision of `K₄`. -/
theorem branchVertices_eq_four
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    (hiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    {a b c d : Fin n} (hnd : [a, b, c, d].Nodup)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H)
    (hc : c ∈ branchVertices H) (hd : d ∈ branchVertices H) :
    branchVertices H = {a, b, c, d} := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have heq : branchVertices H = Set.range ι := Set.Subset.antisymm
    (SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges)
    (SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdeg)
  obtain ⟨ψ⟩ := hiso
  have hm : m = 4 := by simpa using Fintype.card_congr ψ.toEquiv
  have hcard : (branchVertices H).ncard = 4 := by
    rw [heq, Set.ncard_range_of_injective hι, Nat.card_eq_fintype_card]
    simpa using hm
  have hab : a ≠ b := by intro h; simp [h] at hnd
  have hac : a ≠ c := by intro h; simp [h] at hnd
  have had : a ≠ d := by intro h; simp [h] at hnd
  have hbc : b ≠ c := by intro h; simp [h] at hnd
  have hbd : b ≠ d := by intro h; simp [h] at hnd
  have hcd : c ≠ d := by intro h; simp [h] at hnd
  have hs : ({a, b, c, d} : Set (Fin n)) ⊆ branchVertices H := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  apply (Set.eq_of_subset_of_ncard_le hs _ (Set.toFinite _)).symm
  rw [hcard]
  simp [Set.ncard_insert_of_notMem, hab, hac, had, hbc, hbd, hcd]

/-- A wrapper for the uniqueness of the branch joining two named ends. -/
theorem same_branch_edges
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    {B C : List (Fin n)} {a b : Fin n}
    (hB : IsBranch H B) (hBfrom : IsTrackFrom H B a b) (hBpos : 1 ≤ trackLength B)
    (hC : IsBranch H C) (hCfrom : IsTrackFrom H C a b) (hCpos : 1 ≤ trackLength C)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H) : trackEdges B = trackEdges C := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  exact BranchClassification.trackEdges_eq_of_same_ends hι htrack hlen hrev hdisj hnew hcover hedges
    hdeg hB (by simp only [trackLength] at hBpos; omega) hBfrom hC
    (by simp only [trackLength] at hCpos; omega) hCfrom ha hb (Or.inl ⟨rfl, rfl⟩)

/-- Subdivision of a 3-connected graph creates no isolated vertex. -/
theorem exists_neighbor
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H) : ∀ w, ∃ x, H.Adj w x := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  intro w
  rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
  · have hb := SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdeg ⟨a, rfl⟩
    have h3 : 3 ≤ (H.neighborSet (ι a)).ncard := hb
    obtain ⟨x, hx⟩ : (H.neighborSet (ι a)).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]
      omega
    exact ⟨x, hx⟩
  · obtain ⟨j, hj, hjw⟩ := (SubdivisionCounting.mem_trackInterior_iff _ _).mp hw
    refine ⟨(T a b)[j + 2]'(by omega), ?_⟩
    rw [← hjw]
    exact (htrack a b hab).1.2.2 (j + 1) (by omega)

end Workspace.ProofLemmas.Thm61EvenFinalK4
