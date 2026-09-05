import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Minimal tracks to a set, and tracks that cannot enter a branch

PAPER (proof of 5.8 (6), printed p. 28): *"choose a minimal track `S` in `H \ {v₁,v₂}` between
`u` and `V(C₁)`.  Let the ends of `S` be `u` and `w` say."*

Two elementary facts.  The first is the truncation that makes a track minimal: cut a track at
the first vertex that lies in the target set.  The second is the reason such a track never
meets the branch between `v₁` and `v₂`: an internal vertex of a branch has exactly two
neighbours and both lie on the branch, so a track avoiding both ends of the branch can never
enter it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Connectivity58Minimal

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}

/-- Cutting a track at the first vertex lying in a target set. -/
theorem exists_first_hit {R : List W} {c z : W} (hR : IsTrackFrom H R c z)
    (A : Set W) (hz : z ∈ A) (hc : c ∉ A) :
    ∃ (S : List W) (w : W), IsTrackFrom H S c w ∧ w ∈ A ∧
      (∀ x ∈ S, x ∈ A → x = w) ∧ (∀ x ∈ S, x ∈ R) ∧ 2 ≤ S.length := by
  classical
  have hpos : 0 < R.length := List.length_pos_of_ne_nil hR.1.1
  have hR0 : R[0]'hpos = c := track_head hR hpos
  have hRl : R[R.length - 1]'(by omega) = z := by
    have h' := hR.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : R.length - 1 < R.length)] at h'
    exact Option.some_injective _ h'
  have hex : ∃ j, ∃ h : j < R.length, R[j]'h ∈ A := ⟨R.length - 1, by omega, by rw [hRl]; exact hz⟩
  obtain ⟨k, hk, hkA, hmin⟩ :
      ∃ k, ∃ h : k < R.length, R[k]'h ∈ A ∧ ∀ j < k, ∀ h : j < R.length, R[j]'h ∉ A := by
    refine ⟨Nat.find hex, ?_, ?_, ?_⟩
    · exact (Nat.find_spec hex).1
    · exact (Nat.find_spec hex).2
    · intro j hj hjlt hjA
      exact Nat.find_min hex hj ⟨hjlt, hjA⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (by rw [hR0] at hkA; exact hkA) hc
    · omega
  refine ⟨TrackSlice.slice R 0 k, R[k]'hk, ?_, hkA, ?_, ?_, ?_⟩
  · have := TrackSlice.isTrackFrom_slice hR.1 hk (by omega : 0 ≤ k)
    rwa [hR0] at this
  · intro x hx hxA
    obtain ⟨j, hj, -, hjk, rfl⟩ := (TrackSlice.mem_slice_iff hk (by omega)).mp hx
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact absurd hxA (hmin j hlt hj)
    · exact getElem_eq_of_index_eq R (show j = k by omega) hj hk
  · intro x hx
    exact TrackSlice.mem_of_mem_slice hx
  · rw [TrackSlice.length_slice R hk (by omega)]
    omega


/-- **Shortcutting a track at the last neighbour of its first vertex.**  Every track can be
replaced by one with the same ends, using only its own vertices, on which the first vertex has
exactly one neighbour, namely the second vertex.  This is the part of the paper's *"minimal
track"* that the extension through the star at `c` needs: the extra vertex of the star that
carries the neighbour of `p₁` must not see the rung of `S` twice. -/
theorem exists_no_chord_at_head {S : List W} {c w : W} (hS : IsTrackFrom H S c w)
    (hS2 : 2 ≤ S.length) :
    ∃ S' : List W, IsTrackFrom H S' c w ∧ 2 ≤ S'.length ∧ (∀ x ∈ S', x ∈ S) ∧
      ∀ y ∈ S', H.Adj c y → S'[1]? = some y := by
  classical
  have hS0 : S[0]'(by omega) = c := track_head hS (by omega)
  have hSl : S[S.length - 1]'(by omega) = w := by
    have h' := hS.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : S.length - 1 < S.length)] at h'
    exact Option.some_injective _ h'
  set Q : ℕ → Prop := fun j => ∃ h : j < S.length, H.Adj c (S[j]'h) with hQ
  have hQ1 : Q 1 := ⟨by omega, by
    have := hS.1.2.2 0 (by omega)
    rwa [hS0] at this⟩
  set j : ℕ := Nat.findGreatest Q (S.length - 1) with hj
  have hj1 : 1 ≤ j := Nat.le_findGreatest (by omega) hQ1
  have hjle : j ≤ S.length - 1 := Nat.findGreatest_le _
  obtain ⟨hjlt, hjadj⟩ : Q j := Nat.findGreatest_spec (m := 1) (by omega) hQ1
  have hgreat : ∀ k, j < k → k ≤ S.length - 1 → ¬ Q k := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hcnot : c ∉ TrackSlice.slice S j (S.length - 1) := by
    intro hmem
    obtain ⟨k, hk, hjk, -, hkc⟩ := (TrackSlice.mem_slice_iff (by omega) (by omega)).mp hmem
    have : k = 0 := hS.1.2.1.getElem_inj_iff (hi := hk) (hj := (by omega : 0 < S.length))
      |>.mp (by rw [hkc, hS0])
    omega
  have hslice : IsTrackFrom H (TrackSlice.slice S j (S.length - 1))
      (S[j]'hjlt) (S[S.length - 1]'(by omega)) :=
    TrackSlice.isTrackFrom_slice hS.1 (by omega) (by omega)
  have htrack : IsTrackFrom H (c :: TrackSlice.slice S j (S.length - 1)) c w := by
    have h1 := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hslice)
      hjadj.symm (by simpa using hcnot)
    have h2 := TrackSlice.isTrackFrom_reverse h1
    rw [hSl] at h2
    simpa using h2
  refine ⟨c :: TrackSlice.slice S j (S.length - 1), htrack, ?_, ?_, ?_⟩
  · have := TrackSlice.length_slice S (by omega : S.length - 1 < S.length) (by omega : j ≤ S.length - 1)
    simp only [List.length_cons]
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hS0 ▸ List.getElem_mem _
    · exact TrackSlice.mem_of_mem_slice hx'
  · intro y hy hadj
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact (H.irrefl hadj).elim
    · obtain ⟨k, hk, hjk, hkl, hky⟩ := (TrackSlice.mem_slice_iff (by omega) (by omega)).mp hy'
      have hkj : k ≤ j := by
        by_contra hh
        exact hgreat k (by omega) (by omega) ⟨hk, by rw [hky]; exact hadj⟩
      have hkeq : k = j := by omega
      rw [List.getElem?_cons_succ]
      have h0 : (TrackSlice.slice S j (S.length - 1))[0]?
          = some (S[j]'hjlt) := by
        rw [← List.head?_eq_getElem?]
        exact hslice.2.1
      rw [h0, ← hky, getElem_eq_of_index_eq S hkeq hk hjlt]

/-- An internal vertex of a branch has both its neighbours on the branch. -/
theorem neighbors_of_branch_interior (hdeg2 : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    {q : List W} (hq : IsBranch H q) {x : W} (hx : x ∈ trackInterior q) :
    ∀ y, H.Adj x y → y ∈ q := by
  classical
  obtain ⟨j, hj, rfl⟩ := (mem_trackInterior_iff q x).mp hx
  have hnd : q.Nodup := hq.1.2.1
  have h1 : q[j]'(by omega) ∈ H.neighborSet (q[j + 1]'(by omega)) :=
    (hq.1.2.2 j (by omega)).symm
  have h2 : q[j + 2]'(by omega) ∈ H.neighborSet (q[j + 1]'(by omega)) := by
    have := hq.1.2.2 (j + 1) (by omega)
    exact this
  have hne : q[j]'(by omega) ≠ q[j + 2]'(by omega) := by
    intro hh
    have := hnd.getElem_inj_iff (hi := (by omega : j < q.length))
      (hj := (by omega : j + 2 < q.length)) |>.mp hh
    omega
  have hsub : ({q[j]'(by omega), q[j + 2]'(by omega)} : Set W) ⊆
      H.neighborSet (q[j + 1]'(by omega)) := by
    rintro y (rfl | hy)
    · exact h1
    · have : y = q[j + 2]'(by omega) := hy
      exact this ▸ h2
  have hcard : ({q[j]'(by omega), q[j + 2]'(by omega)} : Set W).ncard = 2 :=
    Set.ncard_pair hne
  have hle : (H.neighborSet (q[j + 1]'(by omega))).ncard ≤ 2 := by
    by_contra hh
    exact hq.2.1 _ hx (by simp only [branchVertices, Set.mem_setOf_eq]; omega)
  have heq : ({q[j]'(by omega), q[j + 2]'(by omega)} : Set W) =
      H.neighborSet (q[j + 1]'(by omega)) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  intro y hy
  have hymem : y ∈ ({q[j]'(by omega), q[j + 2]'(by omega)} : Set W) := by
    rw [heq]; exact hy
  rcases hymem with hh | hh
  · exact hh ▸ List.getElem_mem _
  · have : y = q[j + 2]'(by omega) := hh
    exact this ▸ List.getElem_mem _

/-- A track avoiding both ends of a branch never meets the branch, provided it starts off it. -/
theorem track_avoids_branch (hdeg2 : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    {q : List W} (hq : IsBranch H q) {v₁ v₂ : W} (hqe : IsTrackFrom H q v₁ v₂)
    (hq2 : 2 ≤ q.length) {S : List W} {c w : W} (hS : IsTrackFrom H S c w)
    (hcq : c ∉ q) (hv₁ : v₁ ∉ S) (hv₂ : v₂ ∉ S) : ∀ x ∈ S, x ∉ q := by
  classical
  have hpos : 0 < S.length := List.length_pos_of_ne_nil hS.1.1
  have hS0 : S[0]'hpos = c := track_head hS hpos
  have hq0 : q[0]'(by omega) = v₁ := track_head hqe (by omega)
  have hql : q[q.length - 1]'(by omega) = v₂ := by
    have h' := hqe.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : q.length - 1 < q.length)] at h'
    exact Option.some_injective _ h'
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0S, hx0q⟩ := hcon
  have hex : ∃ j, ∃ h : j < S.length, S[j]'h ∈ q := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx0S
    exact ⟨j, hj, hx0q⟩
  obtain ⟨k, hk, hkq, hmin⟩ :
      ∃ k, ∃ h : k < S.length, S[k]'h ∈ q ∧ ∀ j < k, ∀ h : j < S.length, S[j]'h ∉ q := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro j hj hjlt hjq
    exact Nat.find_min hex hj ⟨hjlt, hjq⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (by rw [hS0] at hkq; exact hkq) hcq
    · omega
  -- the first vertex of `S` on the branch is internal to the branch
  have hint : S[k]'hk ∈ trackInterior q := by
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hkq
    have hj0 : j ≠ 0 := by
      intro hh
      apply hv₁
      have hv : q[j]'hj = v₁ := by
        rw [getElem_eq_of_index_eq q hh hj (by omega), hq0]
      rw [← hv, hje]
      exact List.getElem_mem _
    have hjl : j ≠ q.length - 1 := by
      intro hh
      apply hv₂
      have hv : q[j]'hj = v₂ := by
        rw [getElem_eq_of_index_eq q hh hj (by omega), hql]
      rw [← hv, hje]
      exact List.getElem_mem _
    refine (mem_trackInterior_iff q _).mpr ⟨j - 1, by omega, ?_⟩
    rw [getElem_eq_of_index_eq q (show j - 1 + 1 = j by omega) (by omega) hj]
    exact hje
  have hprev : H.Adj (S[k]'hk) (S[k - 1]'(by omega)) := by
    have := hS.1.2.2 (k - 1) (by omega)
    rw [getElem_eq_of_index_eq S (show k - 1 + 1 = k by omega) (by omega) hk] at this
    exact this.symm
  exact hmin (k - 1) (by omega) (by omega)
    (neighbors_of_branch_interior hdeg2 hq hint _ hprev)

end Workspace.ProofLemmas.Connectivity58Minimal
