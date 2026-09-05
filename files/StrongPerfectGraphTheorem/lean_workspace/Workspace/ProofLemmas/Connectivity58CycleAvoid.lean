import Workspace.ProofLemmas.Connectivity58Minimal

/-!
# A track that misses one end of a branch misses the whole interior of that branch

PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the branch between `u₁` and
`v₁`, and using `u₂` and not `v₂`."*

The reason the cycle of that sentence uses no edge of the branch `R_{u₂v₂}` is purely local: an
internal vertex of a branch has exactly two neighbours and both lie on the branch, so a track
entering the interior of a branch has to follow the branch until it leaves at an end.  A track
whose own ends are branch-vertices therefore has to contain *both* ends of any branch whose
interior it meets.  Contrapositively, missing one end means missing the whole interior, and then
also every edge of the branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Connectivity58CycleAvoid

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}

/-- The two neighbours of an internal vertex of a branch are its two neighbours *on* the
branch.  This is `Connectivity58Minimal.neighbors_of_branch_interior` with the position of the
neighbour pinned down. -/
theorem nbr_of_branch_interior (hdeg2 : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    {q : List W} (hq : IsBranch H q) {j : ℕ} (hj : j + 2 < q.length)
    {y : W} (hy : H.Adj (q[j + 1]'(by omega)) y) :
    y = q[j]'(by omega) ∨ y = q[j + 2]'hj := by
  classical
  have hnd : q.Nodup := hq.1.2.1
  have hint : q[j + 1]'(by omega) ∈ trackInterior q :=
    (mem_trackInterior_iff q _).mpr ⟨j, by omega, rfl⟩
  have h1 : q[j]'(by omega) ∈ H.neighborSet (q[j + 1]'(by omega)) :=
    (hq.1.2.2 j (by omega)).symm
  have h2 : q[j + 2]'hj ∈ H.neighborSet (q[j + 1]'(by omega)) := hq.1.2.2 (j + 1) (by omega)
  have hne : q[j]'(by omega) ≠ q[j + 2]'hj := by
    intro hh
    have := hnd.getElem_inj_iff (hi := (by omega : j < q.length)) (hj := hj) |>.mp hh
    omega
  have hsub : ({q[j]'(by omega), q[j + 2]'hj} : Set W) ⊆ H.neighborSet (q[j + 1]'(by omega)) := by
    rintro y (rfl | hy')
    · exact h1
    · have : y = q[j + 2]'hj := hy'
      exact this ▸ h2
  have hcard : ({q[j]'(by omega), q[j + 2]'hj} : Set W).ncard = 2 := Set.ncard_pair hne
  have hle : (H.neighborSet (q[j + 1]'(by omega))).ncard ≤ 2 := by
    by_contra hh
    exact hq.2.1 _ hint (by simp only [branchVertices, Set.mem_setOf_eq]; omega)
  have heq : ({q[j]'(by omega), q[j + 2]'hj} : Set W) = H.neighborSet (q[j + 1]'(by omega)) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hymem : y ∈ ({q[j]'(by omega), q[j + 2]'hj} : Set W) := by rw [heq]; exact hy
  rcases hymem with hh | hh
  · exact Or.inl hh
  · exact Or.inr hh

/-- **A track missing the far end of a branch misses the branch's interior.** -/
theorem interior_disjoint_of_last_not_mem (hdeg2 : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length)
    {D : List W} (hD : IsTrackList H D)
    (hends : ∀ x ∈ D, (D.head? = some x ∨ D.getLast? = some x) → x ∉ trackInterior q)
    (hlast : q[q.length - 1]'(by omega) ∉ D) :
    ∀ x ∈ trackInterior q, x ∉ D := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxq, hxD⟩ := hcon
  obtain ⟨j₀, hj₀, rfl⟩ := (mem_trackInterior_iff q x).mp hxq
  set Q : ℕ → Prop := fun j => ∃ h : j + 2 < q.length, (q[j + 1]'(by omega)) ∈ D with hQ
  have hQj₀ : Q j₀ := ⟨hj₀, hxD⟩
  set M : ℕ := Nat.findGreatest Q q.length with hM
  have hMle : M ≤ q.length := Nat.findGreatest_le _
  obtain ⟨hMlt, hMD⟩ : Q M := Nat.findGreatest_spec (m := j₀) (by omega) hQj₀
  have hgreat : ∀ k, M < k → k ≤ q.length → ¬ Q k := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  -- the vertex `q[M+1]` sits inside `D`, and is not an end of `D`
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hMD
  have hint : q[M + 1]'(by omega) ∈ trackInterior q :=
    (mem_trackInterior_iff q _).mpr ⟨M, by omega, rfl⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (hends _ hMD (Or.inl (by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, hkeq]))) (by
        simpa using hint)
    · exact h
  have hklt : k + 1 < D.length := by
    rcases Nat.lt_or_ge (k + 1) D.length with h | h
    · exact h
    · exfalso
      refine hends _ hMD (Or.inr ?_) hint
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : D.length - 1 < D.length),
        getElem_eq_of_index_eq D (show D.length - 1 = k by omega) (by omega) hk, hkeq]
  have hadj1 : H.Adj (q[M + 1]'(by omega)) (D[k - 1]'(by omega)) := by
    have := hD.2.2 (k - 1) (by omega)
    rw [getElem_eq_of_index_eq D (show k - 1 + 1 = k by omega) (by omega) hk, hkeq] at this
    exact this.symm
  have hadj2 : H.Adj (q[M + 1]'(by omega)) (D[k + 1]'hklt) := by
    have := hD.2.2 k hklt
    rw [hkeq] at this
    exact this
  have hne : D[k - 1]'(by omega : k - 1 < D.length) ≠ D[k + 1]'hklt := by
    intro hh
    have := hD.2.1.getElem_inj_iff (hi := (by omega : k - 1 < D.length)) (hj := hklt) |>.mp hh
    omega
  have h1 := nbr_of_branch_interior hdeg2 hq hMlt hadj1
  have h2 := nbr_of_branch_interior hdeg2 hq hMlt hadj2
  have hMem : q[M + 2]'hMlt ∈ D := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · exact h2 ▸ List.getElem_mem hklt
    · exact h1 ▸ List.getElem_mem (by omega)
  rcases Nat.lt_or_ge (M + 3) q.length with hcase | hcase
  · exact hgreat (M + 1) (by omega) (by omega) ⟨by omega, hMem⟩
  · exact hlast (by
      rw [getElem_eq_of_index_eq q (show q.length - 1 = M + 2 by omega) (by omega) hMlt]
      exact hMem)

/-- **A track missing the far end of a branch uses no edge of the branch.** -/
theorem trackEdges_disjoint_of_last_not_mem (hdeg2 : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length)
    {D : List W} (hD : IsTrackList H D)
    (hends : ∀ x ∈ D, (D.head? = some x ∨ D.getLast? = some x) → x ∉ trackInterior q)
    (hlast : q[q.length - 1]'(by omega) ∉ D) :
    ∀ e ∈ trackEdges q, e ∉ trackEdges D := by
  intro e he heD
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨l, hl, hle⟩ := heD
  have hmem : q[i + 1]'hi ∈ D := by
    have : q[i + 1]'hi ∈ s(D[l]'(by omega), D[l + 1]'hl) := by
      rw [← hle]; exact Sym2.mem_mk_right _ _
    rcases Sym2.mem_iff.mp this with hh | hh
    · exact hh ▸ List.getElem_mem _
    · exact hh ▸ List.getElem_mem _
  rcases Nat.lt_or_ge (i + 2) q.length with hcase | hcase
  · exact interior_disjoint_of_last_not_mem hdeg2 hq hq2 hD hends hlast _
      ((mem_trackInterior_iff q _).mpr ⟨i, hcase, rfl⟩) hmem
  · exact hlast (by
      rw [getElem_eq_of_index_eq q (show q.length - 1 = i + 1 by omega) (by omega) hi]
      exact hmem)

end Workspace.ProofLemmas.Connectivity58CycleAvoid
