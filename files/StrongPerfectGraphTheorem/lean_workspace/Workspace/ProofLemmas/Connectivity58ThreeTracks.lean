import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The three tracks out of `w`

PAPER (proof of 5.8 (6), printed p. 28): *"Hence in `L(H)` there are three vertex-disjoint
paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`."*

The three tracks behind those three paths are the two arcs of the cycle out of `w` — that is,
the two pieces into which the return track `D` is cut at its internal vertex `w` — together
with the minimal track back to `c`, reversed so that it too starts at `w`.  This file packages
them, with the only fact that needs proving: they meet only at `w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Connectivity58ThreeTracks

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

/-- The two arcs of `D` out of its internal vertex `w`, together with the minimal track back to
`c`: three tracks starting at `w` which pairwise meet only there. -/
theorem exists_three_tracks {D Sm : List W} {v₁ v₂ c w : W} {k : ℕ}
    (hD : IsTrackFrom H D v₁ v₂) (hk0 : 0 < k) (hklt : k + 1 < D.length)
    (hkw : D[k]? = some w) (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) :
    ∃ (b : Fin 3 → W) (S : Fin 3 → List W),
      b 0 = v₁ ∧ b 1 = v₂ ∧ b 2 = c ∧
      (∀ i, IsTrackFrom H (S i) w (b i)) ∧ (∀ i, 2 ≤ (S i).length) ∧
      (∀ i j : Fin 3, i ≠ j → ∀ z ∈ S i, z ∈ S j → z = w) ∧
      (∀ z ∈ S 0, z ∈ D) ∧ (∀ z ∈ S 1, z ∈ D) ∧ S 2 = Sm.reverse := by
  classical
  have hDpos : 0 < D.length := by omega
  have hDk : D[k]'(by omega) = w := by
    rw [List.getElem?_eq_getElem (by omega : k < D.length)] at hkw
    exact Option.some_injective _ hkw
  have hD0 : D[0]'hDpos = v₁ := track_head hD hDpos
  have hDl : D[D.length - 1]'(by omega) = v₂ := by
    have h' := hD.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : D.length - 1 < D.length)] at h'
    exact Option.some_injective _ h'
  have hnd : D.Nodup := hD.1.2.1
  -- the two arcs
  have harc0 : IsTrackFrom H (TrackSlice.slice D 0 k).reverse w v₁ := by
    have := TrackSlice.isTrackFrom_slice hD.1 (by omega : k < D.length) (by omega : 0 ≤ k)
    rw [hD0, hDk] at this
    exact TrackSlice.isTrackFrom_reverse this
  have harc1 : IsTrackFrom H (TrackSlice.slice D k (D.length - 1)) w v₂ := by
    have := TrackSlice.isTrackFrom_slice hD.1 (by omega : D.length - 1 < D.length)
      (by omega : k ≤ D.length - 1)
    rw [hDk, hDl] at this
    exact this
  refine ⟨![v₁, v₂, c], ![(TrackSlice.slice D 0 k).reverse,
    TrackSlice.slice D k (D.length - 1), Sm.reverse], rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · exact harc0
    · exact harc1
    · exact TrackSlice.isTrackFrom_reverse hSm
  · intro i
    fin_cases i
    · show 2 ≤ (TrackSlice.slice D 0 k).reverse.length
      rw [List.length_reverse,
        TrackSlice.length_slice D (by omega : k < D.length) (by omega : 0 ≤ k)]
      omega
    · show 2 ≤ (TrackSlice.slice D k (D.length - 1)).length
      rw [TrackSlice.length_slice D (by omega : D.length - 1 < D.length)
        (by omega : k ≤ D.length - 1)]
      omega
    · show 2 ≤ Sm.reverse.length
      simpa using hSm2
  · -- the three tracks meet only at `w`
    have hslice0 : ∀ z ∈ (TrackSlice.slice D 0 k).reverse,
        ∃ (i : ℕ) (h : i < D.length), i ≤ k ∧ D[i]'h = z := by
      intro z hz
      obtain ⟨i, hi, -, hik, hiz⟩ :=
        (TrackSlice.mem_slice_iff (by omega : k < D.length) (by omega : 0 ≤ k)).mp
          (List.mem_reverse.mp hz)
      exact ⟨i, hi, hik, hiz⟩
    have hslice1 : ∀ z ∈ TrackSlice.slice D k (D.length - 1),
        ∃ (i : ℕ) (h : i < D.length), k ≤ i ∧ D[i]'h = z := by
      intro z hz
      obtain ⟨i, hi, hki, -, hiz⟩ :=
        (TrackSlice.mem_slice_iff (by omega : D.length - 1 < D.length)
          (by omega : k ≤ D.length - 1)).mp hz
      exact ⟨i, hi, hki, hiz⟩
    have hsub0 : ∀ z ∈ (TrackSlice.slice D 0 k).reverse, z ∈ D := by
      intro z hz
      obtain ⟨i, hi, -, rfl⟩ := hslice0 z hz
      exact List.getElem_mem _
    have hsub1 : ∀ z ∈ TrackSlice.slice D k (D.length - 1), z ∈ D := by
      intro z hz
      obtain ⟨i, hi, -, rfl⟩ := hslice1 z hz
      exact List.getElem_mem _
    have hcross : ∀ z ∈ (TrackSlice.slice D 0 k).reverse,
        z ∈ TrackSlice.slice D k (D.length - 1) → z = w := by
      intro z hz hz'
      obtain ⟨i, hi, hik, hiz⟩ := hslice0 z hz
      obtain ⟨j, hj, hkj, hjz⟩ := hslice1 z hz'
      have hij : i = j := hnd.getElem_inj_iff (hi := hi) (hj := hj) |>.mp (by rw [hiz, hjz])
      rw [← hiz, getElem_eq_of_index_eq D (show i = k by omega) hi (by omega), hDk]
    intro i j hij z hz hz'
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcross z hz hz'
    · exact hSmD z (List.mem_reverse.mp hz') (hsub0 z hz)
    · exact hcross z hz' hz
    · exact absurd rfl hij
    · exact hSmD z (List.mem_reverse.mp hz') (hsub1 z hz)
    · exact hSmD z (List.mem_reverse.mp hz) (hsub0 z hz')
    · exact hSmD z (List.mem_reverse.mp hz) (hsub1 z hz')
    · exact absurd rfl hij
  · intro z hz
    obtain ⟨i, hi, -, -, rfl⟩ :=
      (TrackSlice.mem_slice_iff (by omega : k < D.length) (by omega : 0 ≤ k)).mp
        (List.mem_reverse.mp hz)
    exact List.getElem_mem _
  · intro z hz
    obtain ⟨i, hi, -, -, rfl⟩ :=
      (TrackSlice.mem_slice_iff (by omega : D.length - 1 < D.length)
        (by omega : k ≤ D.length - 1)).mp hz
    exact List.getElem_mem _

end Workspace.ProofLemmas.Connectivity58ThreeTracks
