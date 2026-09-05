import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim2Window
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.BranchExternalEdge

/-!
# Structural bookkeeping for 5.7 (2)

This file proves the branch facts used on both sides of the parity split in printed claim (2).
In particular, an edge of `X` outside the chosen window must meet one of its ends.  It also
packages the final elementary case split which gives alternatives 3, 4, or 5 once the two
sets of missing end-edges are empty.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Structure

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A subtrack uses only edges of the original track. -/
theorem trackEdges_slice_subset (B : List W) {i j : ℕ} (hj : j < B.length) (hij : i ≤ j) :
    trackEdges (slice B i j) ⊆ trackEdges B := by
  rintro e ⟨k, hk, rfl⟩
  have hlen := length_slice B hj hij
  have hk' : k < (slice B i j).length := by omega
  refine ⟨i + k, by omega, ?_⟩
  rw [getElem_slice B hk' (show i + k < B.length by omega),
    getElem_slice B hk (show i + (k + 1) < B.length by omega),
    SubdivisionCounting.getElem_eq_of_index_eq B
      (show i + (k + 1) = i + k + 1 by omega) _ _]

/-- Reversing a branch does not change the branch subgraph. -/
theorem isBranch_reverse {H : SimpleGraph W} {q : List W} (hq : IsBranch H q) :
    IsBranch H q.reverse := by
  refine ⟨isTrackList_reverse hq.1, ?_, ?_⟩
  · intro v hv
    exact hq.2.1 v (mem_trackInterior_reverse.mp hv)
  · intro q' hq' hq'int hsub hverts
    have hsub' : trackEdges q ⊆ trackEdges q' := by
      simpa [SubdivisionCounting.trackEdges_reverse] using hsub
    have hverts' : ∀ v ∈ q, v ∈ q' := by
      intro v hv
      exact hverts v (by simpa using hv)
    have heq := hq.2.2 q' hq' hq'int hsub' hverts'
    simpa [SubdivisionCounting.trackEdges_reverse] using heq

/-- A branch with at least one edge, named from its first to its last vertex. -/
theorem branch_from_ends {H : SimpleGraph W} {B : List W} (hB : IsBranch H B)
    (h2 : 2 ≤ B.length) :
    IsTrackFrom H B B[0] B[B.length - 1] := by
  refine ⟨hB.1, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]

/-- Every edge at a non-end vertex of a branch belongs to that branch. -/
theorem incidentEdges_internal_subset {H : SimpleGraph W} {B : List W}
    (hB : IsBranch H B) {k : ℕ} (hk₀ : 0 < k) (hkL : k + 1 < B.length) :
    incidentEdges H B[k] ⊆ trackEdges B := by
  intro e he
  by_contra heB
  let d : Sym2 W := s(B[k - 1]'(by omega), B[k]'(by omega))
  have hdB : d ∈ trackEdges B := by
    refine ⟨k - 1, by omega, ?_⟩
    dsimp [d]
    rw [SubdivisionCounting.getElem_eq_of_index_eq B (show k - 1 + 1 = k by omega) _ _]
  have hdE : d ∈ H.edgeSet := by
    dsimp [d]
    have hadj := hB.1.2.2 (k - 1) (by omega)
    rw [SubdivisionCounting.getElem_eq_of_index_eq B (show k - 1 + 1 = k by omega) _ _]
      at hadj
    exact hadj
  have hkd : B[k]'(by omega) ∈ d := by
    dsimp [d]
    exact Sym2.mem_mk_right _ _
  have hends := Workspace.ProofLemmas.BranchExternalEdge.external_edge_meets_branch_only_at_ends
    hB (branch_from_ends hB (by omega)) hdB he.1 heB he.2 hkd
  rcases hends with h | h
  · have hi := hB.1.2.1.getElem_inj_iff.mp h
    omega
  · have hi := hB.1.2.1.getElem_inj_iff.mp h
    omega

/-- PAPER: *"every edge in `X` either belongs to `C` or is incident with one of `c₁,c₂`"*.

Here `C` is the interval of `B` from positions `i` to `j`. -/
theorem edges_outside_window_meet_an_end (H : SimpleGraph W) (X : Set (Sym2 W))
    (hXE : X ⊆ H.edgeSet) {B : List W} (hB : IsBranch H B) {i j : ℕ}
    (hij : i < j) (hj : j < B.length) (hmeet : MeetsEveryEdge X (slice B i j)) :
    X \ trackEdges (slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j] := by
  intro e he
  obtain ⟨w, hwC, hwe⟩ := hmeet e he.1
  by_cases hwi : w = B[i]'(by omega)
  · exact Or.inl ⟨hXE he.1, hwi ▸ hwe⟩
  by_cases hwj : w = B[j]'hj
  · exact Or.inr ⟨hXE he.1, hwj ▸ hwe⟩
  obtain ⟨k, hk, hik, hkj, hBkw⟩ := (mem_slice_iff hj (by omega)).mp hwC
  have hik' : i < k := by
    by_contra h
    have hki : k = i := by omega
    apply hwi
    rw [← hBkw]
    exact SubdivisionCounting.getElem_eq_of_index_eq B hki _ _
  have hkj' : k < j := by
    by_contra h
    have hkjEq : k = j := by omega
    apply hwj
    rw [← hBkw]
    exact SubdivisionCounting.getElem_eq_of_index_eq B hkjEq _ _
  have hk₀ : 0 < k := lt_of_le_of_lt (Nat.zero_le i) hik'
  have hkL : k + 1 < B.length := lt_of_le_of_lt (Nat.succ_le_iff.mpr hkj') hj
  have heB : e ∈ trackEdges B := incidentEdges_internal_subset hB hk₀ hkL
    ⟨hXE he.1, by rw [hBkw]; exact hwe⟩
  obtain ⟨l, hl, hel⟩ := heB
  have hwedge : w ∈ s(B[l]'(by omega), B[l + 1]'hl) := hel ▸ hwe
  have hlcase : k = l ∨ k = l + 1 := by
    rcases Sym2.mem_iff.mp hwedge with h | h
    · left
      apply hB.1.2.1.getElem_inj_iff.mp
      exact hBkw.trans h
    · right
      apply hB.1.2.1.getElem_inj_iff.mp
      exact hBkw.trans h
  exfalso
  apply he.2
  rcases hlcase with hkl | hkl
  · refine ⟨l - i, ?_, ?_⟩
    · rw [length_slice B hj (by omega)]
      omega
    · rw [getElem_slice B (by rw [length_slice B hj (by omega)]; omega) (by omega),
        getElem_slice B (by rw [length_slice B hj (by omega)]; omega) (by omega),
        SubdivisionCounting.getElem_eq_of_index_eq B (show i + (l - i) = l by omega) _ _,
        SubdivisionCounting.getElem_eq_of_index_eq B
          (show i + (l - i + 1) = l + 1 by omega) _ _]
      exact hel
  · refine ⟨l - i, ?_, ?_⟩
    · rw [length_slice B hj (by omega)]
      omega
    · rw [getElem_slice B (by rw [length_slice B hj (by omega)]; omega) (by omega),
        getElem_slice B (by rw [length_slice B hj (by omega)]; omega) (by omega),
        SubdivisionCounting.getElem_eq_of_index_eq B (show i + (l - i) = l by omega) _ _,
        SubdivisionCounting.getElem_eq_of_index_eq B
          (show i + (l - i + 1) = l + 1 by omega) _ _]
      exact hel

/-- Once neither end of the minimal window has a non-`X` edge outside the window, the four
possible positions of the window inside its branch give alternatives 3, 4, or 5 of 5.7. -/
theorem classify_after_exhaustion (H : SimpleGraph W) (X : Set (Sym2 W))
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hdiff : DifferentBiparity H B[i] B[j])
    (houtside : X \ trackEdges (slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hempty : BSet H X (slice B i j) B[i] ∪
      BSet H X (slice B i j) B[j] = ∅) :
    Stmt57_3 H X ∨ Stmt57_4 H X ∨ Stmt57_5 H X := by
  classical
  have hB₂ : 2 ≤ B.length := by omega
  have hBfrom : IsTrackFrom H B B[0] B[B.length - 1] := branch_from_ends hB hB₂
  have hCfrom : IsTrackFrom H (slice B i j) B[i] B[j] :=
    isTrackFrom_slice hB.1 hj (by omega)
  have hCsub : trackEdges (slice B i j) ⊆ trackEdges B :=
    trackEdges_slice_subset B hj (by omega)
  have hfull₁ : incidentEdges H B[i] \ trackEdges (slice B i j) ⊆ X := by
    intro e he
    by_contra heX
    have heB : e ∈ BSet H X (slice B i j) B[i] := ⟨⟨he.1, heX⟩, he.2⟩
    have hu : e ∈ BSet H X (slice B i j) B[i] ∪
        BSet H X (slice B i j) B[j] := Or.inl heB
    rw [hempty] at hu
    exact hu
  have hfull₂ : incidentEdges H B[j] \ trackEdges (slice B i j) ⊆ X := by
    intro e he
    by_contra heX
    have heB : e ∈ BSet H X (slice B i j) B[j] := ⟨⟨he.1, heX⟩, he.2⟩
    have hu : e ∈ BSet H X (slice B i j) B[i] ∪
        BSet H X (slice B i j) B[j] := Or.inr heB
    rw [hempty] at hu
    exact hu
  have hEqC : X \ trackEdges (slice B i j) =
      (incidentEdges H B[i] ∪ incidentEdges H B[j]) \ trackEdges (slice B i j) := by
    apply Set.Subset.antisymm
    · intro e he
      exact ⟨houtside he, he.2⟩
    · intro e he
      rcases he.1 with he₁ | he₂
      · exact ⟨hfull₁ ⟨he₁, he.2⟩, he.2⟩
      · exact ⟨hfull₂ ⟨he₂, he.2⟩, he.2⟩
  by_cases hi₀ : i = 0
  · by_cases hjL : j = B.length - 1
    · right
      right
      have hCeq : slice B i j = B := by
        subst i
        rw [hjL]
        simp only [slice, List.drop_zero, Nat.sub_zero]
        rw [show B.length - 1 + 1 = B.length by omega, List.take_length]
      have hodd : Odd (trackLength B) := by
        rw [← hCeq]
        exact hdiff (slice B i j) hCfrom
      refine ⟨B, B[0], B[B.length - 1], hB, hBfrom, hodd, ?_⟩
      have hEqC' := hEqC
      simp only [hi₀, hjL] at hEqC'
      have hfullSlice : slice B 0 (B.length - 1) = B := by
        simpa only [hi₀, hjL] using hCeq
      rw [hfullSlice] at hEqC'
      exact hEqC'
    · right
      left
      have hjInt : j + 1 < B.length := by omega
      refine ⟨B, B[0], B[B.length - 1], hB, hBfrom, ?_⟩
      apply Set.Subset.antisymm
      · intro e he
        have heC : e ∉ trackEdges (slice B i j) := fun hc ↦ he.2 (hCsub hc)
        rcases houtside ⟨he.1, heC⟩ with he₁ | he₂
        · have hv : B[i]'(by omega) = B[0]'(by omega) :=
            SubdivisionCounting.getElem_eq_of_index_eq B hi₀ _ _
          rw [← hv]
          exact ⟨he₁, he.2⟩
        · exact (he.2 (incidentEdges_internal_subset hB (by omega) hjInt he₂)).elim
      · intro e he
        have heC : e ∉ trackEdges (slice B i j) := fun hc ↦ he.2 (hCsub hc)
        have heI : e ∈ incidentEdges H B[i] := by simpa [hi₀] using he.1
        exact ⟨hfull₁ ⟨heI, heC⟩, he.2⟩
  · by_cases hjL : j = B.length - 1
    · right
      left
      have hiInt₀ : 0 < i := by omega
      have hiIntL : i + 1 < B.length := by omega
      have hBrev : IsBranch H B.reverse := isBranch_reverse hB
      have hfromRev : IsTrackFrom H B.reverse B[B.length - 1] B[0] :=
        isTrackFrom_reverse hBfrom
      refine ⟨B.reverse, B[B.length - 1], B[0], hBrev, hfromRev, ?_⟩
      have hEq : X \ trackEdges B = incidentEdges H B[B.length - 1] \ trackEdges B := by
        apply Set.Subset.antisymm
        · intro e he
          have heC : e ∉ trackEdges (slice B i j) := fun hc ↦ he.2 (hCsub hc)
          rcases houtside ⟨he.1, heC⟩ with he₁ | he₂
          · exact (he.2 (incidentEdges_internal_subset hB hiInt₀ hiIntL he₁)).elim
          · have hv : B[j]'hj = B[B.length - 1]'(by omega) :=
              SubdivisionCounting.getElem_eq_of_index_eq B hjL _ _
            rw [← hv]
            exact ⟨he₂, he.2⟩
        · intro e he
          have heC : e ∉ trackEdges (slice B i j) := fun hc ↦ he.2 (hCsub hc)
          have heJ : e ∈ incidentEdges H B[j] := by simpa [hjL] using he.1
          exact ⟨hfull₂ ⟨heJ, heC⟩, he.2⟩
      simpa [SubdivisionCounting.trackEdges_reverse] using hEq
    · left
      have hiInt₀ : 0 < i := by omega
      have hiIntL : i + 1 < B.length := by omega
      have hjInt₀ : 0 < j := by omega
      have hjIntL : j + 1 < B.length := by omega
      refine ⟨B, hB, ?_⟩
      intro e heX
      by_cases heC : e ∈ trackEdges (slice B i j)
      · exact hCsub heC
      · rcases houtside ⟨heX, heC⟩ with he₁ | he₂
        · exact incidentEdges_internal_subset hB hiInt₀ hiIntL he₁
        · exact incidentEdges_internal_subset hB hjInt₀ hjIntL he₂

end Workspace.ProofLemmas.Thm57Claim2Structure
