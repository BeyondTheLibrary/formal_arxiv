import Workspace.ProofLemmas.Thm61EvenFinalK4

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenFinalDiagonals

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm61EvenFinalK4 Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61Claim1Helpers

/-- An internal vertex of a track differs from its named ends. -/
theorem interior_ne_ends {W : Type*} {H : SimpleGraph W} {B : List W} {a b w : W}
    (hB : IsTrackFrom H B a b) (hw : w ∈ trackInterior B) : w ≠ a ∧ w ≠ b := by
  obtain ⟨i, hi, hiw⟩ := (SubdivisionCounting.mem_trackInterior_iff _ _).mp hw
  constructor
  · intro h
    have he : B[i + 1]'(by omega) = B[0]'(by omega) :=
      hiw.trans (h.trans (head_getElem hB.2.1 (by omega)).symm)
    have := hB.1.2.1.getElem_inj_iff.mp he
    omega
  · intro h
    have he : B[i + 1]'(by omega) = B[B.length - 1]'(by omega) :=
      hiw.trans (h.trans (last_getElem hB.2.2 (by omega)).symm)
    have := hB.1.2.1.getElem_inj_iff.mp he
    omega

/-- The two diagonal branches of the four-cycle `b-b₂-b₁-b₃-b`. -/
structure Diagonals {n : ℕ} (H : SimpleGraph (Fin n)) (b b₁ b₂ b₃ : Fin n)
    (C₁ C₄ : List (Fin n)) : Prop where
  track₁ : IsTrackFrom H C₁ b b₁
  track₄ : IsTrackFrom H C₄ b₂ b₃
  branch₁ : IsBranch H C₁
  branch₄ : IsBranch H C₄
  pos₁ : 2 ≤ trackLength C₁
  pos₄ : 2 ≤ trackLength C₄
  even₁ : Even (trackLength C₁)
  even₄ : Even (trackLength C₄)
  disjoint : ∀ x ∈ C₁, x ∉ C₄
  avoids₁ : ∀ x ∈ C₁, x ≠ b₂ ∧ x ≠ b₃
  avoids₄ : ∀ x ∈ C₄, x ≠ b ∧ x ≠ b₁
  edges : H.edgeSet = ({s(b, b₂), s(b₂, b₁), s(b₁, b₃), s(b₃, b)} : Set (Sym2 (Fin n))) ∪
    trackEdges C₄ ∪ trackEdges C₁

/-- Once `B₅` has length one, the four-cycle and its two diagonal branches cover `H`. -/
theorem exists_diagonals
    {m n : ℕ} {J : SimpleGraph (Fin m)} {H : SimpleGraph (Fin n)}
    (hsub : IsSubdivision J H) (hbip : H.IsBipartite)
    (hiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    {b b₁ b₂ b₃ : Fin n} (hnd : [b, b₂, b₁, b₃].Nodup)
    (hbv : branchVertices H = {b, b₂, b₁, b₃})
    (h02 : H.Adj b b₂) (h21 : H.Adj b₂ b₁) (h13 : H.Adj b₁ b₃) (h30 : H.Adj b₃ b) :
    ∃ C₁ C₄, Diagonals H b b₁ b₂ b₃ C₁ C₄ := by
  obtain ⟨ψ⟩ := hiso
  have hsub4 := Thm85Five8Transported.isSubdivision_of_iso ψ hsub
  obtain ⟨P, R, hP, hR, hPpos, hRpos, hPeven, hReven, hPR, hPavoids, hRavoids, hedges⟩ :=
    k4_structure hsub4 hbip b b₂ b₁ b₃ hnd hbv h02 h21 h13 h30
  have h01 : b ≠ b₁ := by intro h; simp [h] at hnd
  have h23 : b₂ ≠ b₃ := by intro h; simp [h] at hnd
  have hv0 : b ∈ branchVertices H := by rw [hbv]; simp
  have hv1 : b₁ ∈ branchVertices H := by rw [hbv]; simp
  have hv2 : b₂ ∈ branchVertices H := by rw [hbv]; simp
  have hv3 : b₃ ∈ branchVertices H := by rw [hbv]; simp
  have hPBr : IsBranch H P := by
    refine Thm82BranchDelta.isBranch_of_ends_branch hP h23 ?_ hv2 hv3
    intro w hw hwbv
    have hmem : w ∈ P := PathBasics.interior_subset hw
    have hne := interior_ne_ends hP hw
    rw [hbv] at hwbv
    rcases hwbv with h | h | h | h
    · exact (hPavoids w hmem).1 h
    · exact hne.1 h
    · exact (hPavoids w hmem).2 h
    · exact hne.2 h
  have hRBr : IsBranch H R := by
    refine Thm82BranchDelta.isBranch_of_ends_branch hR h01.symm ?_ hv1 hv0
    intro w hw hwbv
    have hmem : w ∈ R := PathBasics.interior_subset hw
    have hne := interior_ne_ends hR hw
    rw [hbv] at hwbv
    rcases hwbv with h | h | h | h
    · exact hne.2 h
    · exact (hRavoids w hmem).1 h
    · exact hne.1 h
    · exact (hRavoids w hmem).2 h
  refine ⟨R.reverse, P, TrackSlice.isTrackFrom_reverse hR, hP, isBranch_reverse hRBr, hPBr,
    ?_, hPpos, ?_, hPeven, ?_, ?_, hPavoids, ?_⟩
  · simpa [trackLength] using hRpos
  · simpa [trackLength] using hReven
  · intro w hw hw'
    exact hPR w hw' (List.mem_reverse.mp hw)
  · intro w hw
    exact hRavoids w (List.mem_reverse.mp hw)
  · rwa [SubdivisionCounting.trackEdges_reverse]

/-- A two-edge track has a unique internal vertex. -/
theorem eq_three_of_length_two {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W}
    (hB : IsTrackFrom H B a b) (hlen : trackLength B = 2) : ∃ x, B = [a, x, b] := by
  have hlen3 : B.length = 3 := by simp only [trackLength] at hlen; omega
  obtain ⟨u, x, v, rfl⟩ := List.length_eq_three.mp hlen3
  have hu : u = a := by simpa using hB.2.1
  have hv : v = b := by simpa using hB.2.2
  exact ⟨x, by rw [hu, hv]⟩

/-- The final count: the four-cycle and two two-edge diagonals have six vertices. -/
theorem six_vertices
    {n : ℕ} {H : SimpleGraph (Fin n)} {b b₁ b₂ b₃ : Fin n} {C₁ C₄ : List (Fin n)}
    (hnd : [b, b₂, b₁, b₃].Nodup) (hD : Diagonals H b b₁ b₂ b₃ C₁ C₄)
    (hnbr : ∀ w, ∃ x, H.Adj w x)
    (hlen₁ : trackLength C₁ = 2) (hlen₄ : trackLength C₄ = 2) : Fintype.card (Fin n) = 6 := by
  classical
  obtain ⟨x, hx⟩ := eq_three_of_length_two hD.track₁ hlen₁
  obtain ⟨y, hy⟩ := eq_three_of_length_two hD.track₄ hlen₄
  have h6 : [b, x, b₁, b₂, y, b₃].Nodup := by
    have hcat : (C₁ ++ C₄).Nodup := List.nodup_append.mpr
      ⟨hD.track₁.1.2.1, hD.track₄.1.2.1, fun w hw z hz heq => hD.disjoint w hw (heq ▸ hz)⟩
    simpa only [hx, hy, List.cons_append, List.nil_append] using hcat
  have hcover : ∀ w : Fin n, w ∈ [b, x, b₁, b₂, y, b₃] := by
    intro w
    obtain ⟨z, hwz⟩ := hnbr w
    have he : s(w, z) ∈ H.edgeSet := hwz
    rw [hD.edges] at he
    rcases he with (he | he) | he
    · have hm : w ∈ s(w, z) := by simp
      rcases he with he | he | he | he <;> rw [he] at hm <;>
        simp only [Sym2.mem_iff] at hm <;> rcases hm with h | h <;> simp [h]
    · have hm := NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges he
        (show w ∈ s(w, z) by simp)
      rw [hy] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      tauto
    · have hm := NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges he
        (show w ∈ s(w, z) by simp)
      rw [hx] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      tauto
  let F : Finset (Fin n) := [b, x, b₁, b₂, y, b₃].toFinset
  have hF : F = Finset.univ := by
    ext w
    simp only [F, List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcover w
  have hcard : F.card = 6 := by
    dsimp [F]
    rw [List.toFinset_card_of_nodup h6]
    rfl
  rwa [hF, Finset.card_univ] at hcard

end Workspace.ProofLemmas.Thm61EvenFinalDiagonals
