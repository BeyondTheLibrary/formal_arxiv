import Mathlib
import Workspace.ProofLemmas.Thm61Claim1Geometry

/-!
# The six-vertex alternative in 6.1(1)

When both diagonal branches of the degenerate `K₄` subdivision have two edges, its vertices
are the four branch vertices and the two diagonal internal vertices.  This file isolates that
finite counting step from the adjacency argument of claim (1).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Claim1Card

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm61Claim1Helpers

/-- Every vertex of a subdivision of `K₄` lies on an edge. -/
theorem vertex_incident_of_k4_subdivision
    {n : ℕ} {H : SimpleGraph (Fin n)}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (z : Fin n) :
    ∃ e : Sym2 (Fin n), e ∈ H.edgeSet ∧ z ∈ e := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  rcases hcover z with ⟨a, rfl⟩ | ⟨a, b, hab, hz⟩
  · obtain ⟨b, hab⟩ := SubdivisionCounting.exists_adj_of_three_connected
      (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected a
    have hT := htrack a b hab
    have h2 : 2 ≤ (T a b).length := by
      have := hlen a b hab
      simp only [trackLength] at this
      omega
    let e := s((T a b)[0]'(by omega), (T a b)[1]'(by omega))
    refine ⟨e, TrackToRungPath.trackEdge_mem_edgeSet hT.1 0 (by omega), ?_⟩
    have hh := head_getElem hT.2.1 (show 0 < (T a b).length by omega)
    simp only [e, Sym2.mem_iff]
    exact Or.inl hh.symm
  · obtain ⟨j, hj, hjz⟩ := (SubdivisionCounting.mem_trackInterior_iff (T a b) z).mp hz
    let e := s((T a b)[j]'(by omega), (T a b)[j + 1]'(by omega))
    refine ⟨e, TrackToRungPath.trackEdge_mem_edgeSet (htrack a b hab).1 j (by omega), ?_⟩
    simp only [e, Sym2.mem_iff]
    exact Or.inr hjz.symm

/-- If the two non-cycle branches both have two edges, the `K₄` subdivision has six
vertices.  This is the fourth outcome invoked in the middle of claim (1). -/
theorem card_six_of_short_diagonals
    {n : ℕ} {H : SimpleGraph (Fin n)}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (Bp Bq : List (Fin n))
    (hBp : IsTrackFrom H Bp w₂ w₄) (hBq : IsTrackFrom H Bq w₃ w₁)
    (hlenP : trackLength Bp = 2) (hlenQ : trackLength Bq = 2)
    (hdisj : ∀ x ∈ Bp, x ∉ Bq)
    (havoidP : ∀ x ∈ Bp, x ≠ w₁ ∧ x ≠ w₃)
    (havoidQ : ∀ x ∈ Bq, x ≠ w₂ ∧ x ≠ w₄)
    (hedges : H.edgeSet =
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))) ∪ trackEdges Bp ∪ trackEdges Bq) :
    Fintype.card (Fin n) = 6 := by
  classical
  have hlenP' : Bp.length = 3 := by simp only [trackLength] at hlenP; omega
  have hlenQ' : Bq.length = 3 := by simp only [trackLength] at hlenQ; omega
  let zp := Bp[1]'(by omega)
  let zq := Bq[1]'(by omega)
  have hp0 : Bp[0]'(by omega) = w₂ := head_getElem hBp.2.1 (by omega)
  have hp2 : Bp[2]'(by omega) = w₄ := by
    have h := last_getElem hBp.2.2 (by omega)
    convert h using 1 <;> apply geq <;> omega
  have hq0 : Bq[0]'(by omega) = w₃ := head_getElem hBq.2.1 (by omega)
  have hq2 : Bq[2]'(by omega) = w₁ := by
    have h := last_getElem hBq.2.2 (by omega)
    convert h using 1 <;> apply geq <;> omega
  have hall : ∀ z : Fin n, z ∈ ({w₁, w₂, w₃, w₄, zp, zq} : Set (Fin n)) := by
    intro z
    obtain ⟨e, he, hze⟩ := vertex_incident_of_k4_subdivision hsub z
    rw [hedges] at he
    rcases he with (he | he) | he
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he ⊢
      rcases he with rfl | rfl | rfl | rfl
      · rcases Sym2.mem_iff.mp hze with h | h <;> simp [h]
      · rcases Sym2.mem_iff.mp hze with h | h <;> simp [h]
      · rcases Sym2.mem_iff.mp hze with h | h <;> simp [h]
      · rcases Sym2.mem_iff.mp hze with h | h <;> simp [h]
    · obtain ⟨i, hi, hie⟩ := he
      rw [hie] at hze
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simp only [Sym2.mem_iff] at hze
        rcases hze with h | h
        · rw [h, hp0]; simp
        · rw [h]; simp [zp]
      · simp only [Sym2.mem_iff] at hze
        rcases hze with h | h
        · rw [h]; simp [zp]
        · rw [h, hp2]; simp
    · obtain ⟨i, hi, hie⟩ := he
      rw [hie] at hze
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simp only [Sym2.mem_iff] at hze
        rcases hze with h | h
        · rw [h, hq0]; simp
        · rw [h]; simp [zq]
      · simp only [Sym2.mem_iff] at hze
        rcases hze with h | h
        · rw [h]; simp [zq]
        · rw [h, hq2]; simp
  have h12 : w₁ ≠ w₂ := by rintro rfl; simp at hnd
  have h13 : w₁ ≠ w₃ := by rintro rfl; simp at hnd
  have h14 : w₁ ≠ w₄ := by rintro rfl; simp at hnd
  have h23 : w₂ ≠ w₃ := by rintro rfl; simp at hnd
  have h24 : w₂ ≠ w₄ := by rintro rfl; simp at hnd
  have h34 : w₃ ≠ w₄ := by rintro rfl; simp at hnd
  have hzp2 : zp ≠ w₂ := by
    intro h
    have hi := hBp.1.2.1.getElem_inj_iff.mp (h.trans hp0.symm)
    omega
  have hzp4 : zp ≠ w₄ := by
    intro h
    have hi := hBp.1.2.1.getElem_inj_iff.mp (h.trans hp2.symm)
    omega
  have hzp1 : zp ≠ w₁ := (havoidP zp (by simp [zp])).1
  have hzp3 : zp ≠ w₃ := (havoidP zp (by simp [zp])).2
  have hzq3 : zq ≠ w₃ := by
    intro h
    have hi := hBq.1.2.1.getElem_inj_iff.mp (h.trans hq0.symm)
    omega
  have hzq1 : zq ≠ w₁ := by
    intro h
    have hi := hBq.1.2.1.getElem_inj_iff.mp (h.trans hq2.symm)
    omega
  have hzq2 : zq ≠ w₂ := (havoidQ zq (by simp [zq])).1
  have hzq4 : zq ≠ w₄ := (havoidQ zq (by simp [zq])).2
  have hzpzq : zp ≠ zq := by
    intro h
    exact hdisj zp (by simp [zp]) (h ▸ (by simp [zq]))
  have hcardSet : ({w₁, w₂, w₃, w₄, zp, zq} : Set (Fin n)).ncard = 6 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14, Ne.symm hzp1, Ne.symm hzq1]),
      Set.ncard_insert_of_notMem (by simp [h23, h24, Ne.symm hzp2, Ne.symm hzq2]),
      Set.ncard_insert_of_notMem (by simp [h34, Ne.symm hzp3, Ne.symm hzq3]),
      Set.ncard_insert_of_notMem (by simp [Ne.symm hzp4, Ne.symm hzq4]),
      Set.ncard_pair hzpzq]
  have hsubUniv : ({w₁, w₂, w₃, w₄, zp, zq} : Set (Fin n)) = Set.univ := by
    ext z
    simp only [Set.mem_univ, iff_true]
    exact hall z
  rw [hsubUniv, Set.ncard_univ, Nat.card_eq_fintype_card] at hcardSet
  exact hcardSet

end Workspace.ProofLemmas.Thm61Claim1Card
