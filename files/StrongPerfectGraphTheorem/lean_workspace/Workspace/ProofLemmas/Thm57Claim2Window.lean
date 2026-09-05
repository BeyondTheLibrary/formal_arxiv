import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The minimal subtrack in 5.7 (2)

This file formalizes the first paragraph of printed claim (2).  Starting from a branch which
meets every edge of `X`, we choose a shortest interval of that branch which still meets every
edge.  Two disjoint edges force the interval to have positive length.  Its two end vertices
each have an edge of `X` leaving the interval, since otherwise that end could be removed.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Window

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Every edge in `X` has an end on the list `C`. -/
def MeetsEveryEdge (X : Set (Sym2 W)) (C : List W) : Prop :=
  ∀ e ∈ X, ∃ v : W, v ∈ C ∧ v ∈ e

/-- The `X`-edges at `c` which are not edges of `C`. -/
def ASet (H : SimpleGraph W) (X : Set (Sym2 W)) (C : List W) (c : W) : Set (Sym2 W) :=
  (incidentEdges H c ∩ X) \ trackEdges C

/-- The non-`X` edges at `c` which are not edges of `C`. -/
def BSet (H : SimpleGraph W) (X : Set (Sym2 W)) (C : List W) (c : W) : Set (Sym2 W) :=
  (incidentEdges H c \ X) \ trackEdges C

/-- The only edge of a track incident with its first vertex is its first edge. -/
theorem head_edge_unique {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (h2 : 2 ≤ q.length) {e : Sym2 W} (he : e ∈ trackEdges q)
    (hmem : q[0]'(by omega) ∈ e) :
    e = s(q[0]'(by omega), q[1]'(by omega)) := by
  obtain ⟨k, hk, rfl⟩ := he
  rcases Sym2.mem_iff.mp hmem with h | h
  · have hki : (0 : ℕ) = k := hq.2.1.getElem_inj_iff.mp h
    subst k
    rfl
  · have hki : (0 : ℕ) = k + 1 := hq.2.1.getElem_inj_iff.mp h
    omega

/-- The only edge of a track incident with its last vertex is its last edge. -/
theorem last_edge_unique {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (h2 : 2 ≤ q.length) {e : Sym2 W} (he : e ∈ trackEdges q)
    (hmem : q[q.length - 1]'(by omega) ∈ e) :
    e = s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) := by
  obtain ⟨k, hk, rfl⟩ := he
  rcases Sym2.mem_iff.mp hmem with h | h
  · have hki : q.length - 1 = k := hq.2.1.getElem_inj_iff.mp h
    omega
  · have hki : q.length - 1 = k + 1 := hq.2.1.getElem_inj_iff.mp h
    have hk' : k = q.length - 2 := by omega
    subst k
    rfl

/-- A shortest interval of `B` which meets every edge of `X`. -/
theorem exists_minimal_window (H : SimpleGraph W) (X : Set (Sym2 W))
    (hXE : X ⊆ H.edgeSet) (hdisj : TwoDisjointEdges H X)
    (hB : SomeBranchMeetsAll H X) :
    ∃ (B : List W) (i j : ℕ), ∃ (hi : i < B.length) (hj : j < B.length),
      IsBranch H B ∧ i < j ∧
      MeetsEveryEdge X (slice B i j) ∧
      (ASet H X (slice B i j) (B[i]'hi)).Nonempty ∧
      (ASet H X (slice B i j) (B[j]'hj)).Nonempty ∧
      ∀ (i' j' : ℕ), i' ≤ j' → j' < B.length →
        MeetsEveryEdge X (slice B i' j') →
        (slice B i j).length ≤ (slice B i' j').length := by
  classical
  obtain ⟨B, hbranch, hmeetB⟩ := hB
  have hBne : B ≠ [] := hbranch.1.1
  have hBpos : 0 < B.length := List.length_pos_of_ne_nil hBne
  let P : ℕ → Prop := fun n ↦
    ∃ i j : ℕ, i ≤ j ∧ j < B.length ∧
      (slice B i j).length = n ∧ MeetsEveryEdge X (slice B i j)
  have hPB : P B.length := by
    refine ⟨0, B.length - 1, by omega, by omega, ?_, ?_⟩
    · rw [length_slice B (by omega) (by omega)]
      omega
    · intro e he
      obtain ⟨v, hvB, hve⟩ := hmeetB e he
      refine ⟨v, ?_, hve⟩
      obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hvB
      exact (mem_slice_iff (show B.length - 1 < B.length by omega) (by omega)).mpr
        ⟨k, hk, by omega, by omega, hkv⟩
  have hPex : ∃ n, P n := ⟨B.length, hPB⟩
  obtain ⟨i, j, hij, hj, hlen, hmeet⟩ := Nat.find_spec hPex
  have hmin : ∀ (i' j' : ℕ), i' ≤ j' → j' < B.length →
      MeetsEveryEdge X (slice B i' j') →
      (slice B i j).length ≤ (slice B i' j').length := by
    intro i' j' hi'j' hj' hmeet'
    have hp : P (slice B i' j').length := ⟨i', j', hi'j', hj', rfl, hmeet'⟩
    have hf := Nat.find_min' hPex hp
    omega
  have hlt : i < j := by
    by_contra hnlt
    have hji : j = i := by omega
    obtain ⟨e, heX, f, hfX, hef⟩ := hdisj
    obtain ⟨x, hxC, hxe⟩ := hmeet e heX
    obtain ⟨y, hyC, hyf⟩ := hmeet f hfX
    obtain ⟨kx, hkx, hikx, hkxj, hBx⟩ := (mem_slice_iff hj hij).mp hxC
    obtain ⟨ky, hky, hiky, hkyj, hBy⟩ := (mem_slice_iff hj hij).mp hyC
    have hkxy : kx = ky := by omega
    have hxy : x = y := by
      rw [← hBx, ← hBy]
      exact SubdivisionCounting.getElem_eq_of_index_eq B hkxy _ _
    exact hef x ⟨hxe, hxy ▸ hyf⟩
  have hCtrack : IsTrackList H (slice B i j) :=
    isTrackList_slice hbranch.1 hj (by omega)
  have hClen : (slice B i j).length = j - i + 1 := length_slice B hj (by omega)
  have hc₁ : (slice B i j)[0]'(by omega) = B[i]'(by omega) := by
    exact getElem_slice B (by omega) (by omega)
  have hc₂ : (slice B i j)[(slice B i j).length - 1]'(by omega) = B[j]'hj := by
    rw [getElem_slice B (by omega) (show i + ((slice B i j).length - 1) < B.length by omega)]
    exact SubdivisionCounting.getElem_eq_of_index_eq B (by omega) _ _
  have hA₁ : (ASet H X (slice B i j) B[i]).Nonempty := by
    by_contra hA
    have hmeet' : MeetsEveryEdge X (slice B (i + 1) j) := by
      intro e heX
      obtain ⟨v, hvC, hve⟩ := hmeet e heX
      obtain ⟨k, hk, hik, hkj, hBv⟩ := (mem_slice_iff hj (by omega)).mp hvC
      by_cases hki : k = i
      · have hc₁e : B[i]'(by omega) ∈ e := by
          have hvEq : B[k]'hk = B[i]'(by omega) :=
            SubdivisionCounting.getElem_eq_of_index_eq B hki _ _
          rw [← hvEq, hBv]
          exact hve
        have heC : e ∈ trackEdges (slice B i j) := by
          by_contra heC
          exact hA ⟨e, ⟨⟨hXE heX, hc₁e⟩, heX⟩, heC⟩
        have heq := head_edge_unique hCtrack (by omega) heC (hc₁ ▸ hc₁e)
        let z := B[i + 1]'(by omega)
        refine ⟨z, ?_, ?_⟩
        · apply (mem_slice_iff hj (by omega)).mpr
          exact ⟨i + 1, by omega, le_rfl, by omega, rfl⟩
        · have hzC : (slice B i j)[1]'(by omega) = z := by
            exact getElem_slice B (by omega) (by omega)
          rw [heq, hzC]
          exact Sym2.mem_mk_right _ _
      · refine ⟨v, (mem_slice_iff hj (by omega)).mpr ?_, hve⟩
        exact ⟨k, hk, by omega, hkj, hBv⟩
    have hm := hmin (i + 1) j (by omega) hj hmeet'
    have hnewlen : (slice B (i + 1) j).length = j - (i + 1) + 1 :=
      length_slice B hj (by omega)
    rw [hClen, hnewlen] at hm
    omega
  have hA₂ : (ASet H X (slice B i j) B[j]).Nonempty := by
    by_contra hA
    have hmeet' : MeetsEveryEdge X (slice B i (j - 1)) := by
      intro e heX
      obtain ⟨v, hvC, hve⟩ := hmeet e heX
      obtain ⟨k, hk, hik, hkj, hBv⟩ := (mem_slice_iff hj (by omega)).mp hvC
      by_cases hkj' : k = j
      · have hc₂e : B[j]'hj ∈ e := by
          have hvEq : B[k]'hk = B[j]'hj :=
            SubdivisionCounting.getElem_eq_of_index_eq B hkj' _ _
          rw [← hvEq, hBv]
          exact hve
        have heC : e ∈ trackEdges (slice B i j) := by
          by_contra heC
          exact hA ⟨e, ⟨⟨hXE heX, hc₂e⟩, heX⟩, heC⟩
        have heq := last_edge_unique hCtrack (by omega) heC (hc₂ ▸ hc₂e)
        let z := B[j - 1]'(by omega)
        refine ⟨z, ?_, ?_⟩
        · apply (mem_slice_iff (show j - 1 < B.length by omega) (by omega)).mpr
          exact ⟨j - 1, by omega, by omega, le_rfl, rfl⟩
        · have hzC : (slice B i j)[(slice B i j).length - 2]'(by omega) = z := by
            rw [getElem_slice B (by omega)
              (show i + ((slice B i j).length - 2) < B.length by omega)]
            exact SubdivisionCounting.getElem_eq_of_index_eq B (by omega) _ _
          rw [heq, hzC]
          exact Sym2.mem_mk_left _ _
      · refine ⟨v, (mem_slice_iff (show j - 1 < B.length by omega) (by omega)).mpr ?_, hve⟩
        exact ⟨k, hk, hik, by omega, hBv⟩
    have hm := hmin i (j - 1) (by omega) (by omega) hmeet'
    have hnewlen : (slice B i (j - 1)).length = (j - 1) - i + 1 :=
      length_slice B (show j - 1 < B.length by omega) (by omega)
    rw [hClen, hnewlen] at hm
    omega
  exact ⟨B, i, j, by omega, hj, hbranch, hlt, hmeet, hA₁, hA₂, hmin⟩

end Workspace.ProofLemmas.Thm57Claim2Window
