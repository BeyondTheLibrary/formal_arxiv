import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A globally shortest induced path from an attachment set `A` to a disjoint
attachment set `B` meets each attachment set only at its prescribed endpoint. -/
theorem MinimumAttachmentPathInternalVerticesAvoidAttachments
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (X A B : Set W) (a b : W) (P : List W)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hAB : Disjoint A B)
    (ha : a ∈ A) (hb : b ∈ B)
    (hP : SPGT.IsPathFrom K P a b)
    (hPX : ∀ v ∈ P, v ∈ X)
    (hmin : ∀ a' ∈ A, ∀ b' ∈ B, ∀ R : List W,
      SPGT.IsPathFrom K R a' b' → (∀ v ∈ R, v ∈ X) →
        SPGT.pathLength P ≤ SPGT.pathLength R) :
    a ≠ b ∧
      1 ≤ SPGT.pathLength P ∧
        (∀ v ∈ SPGT.interior P, v ∉ A ∪ B) ∧
          (∀ x ∈ P, x ∈ A ↔ x = a) ∧
            (∀ x ∈ P, x ∈ B ↔ x = b) := by
  have hdisj : ∀ x, x ∈ A → x ∈ B → False := by
    intro x hxA hxB
    exact (Set.disjoint_left.mp hAB hxA) hxB
  have hab : a ≠ b := by
    intro h
    exact hdisj a ha (h ▸ hb)
  have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
  have h0 : P[0]'hpos = a := PathBasics.getElem_zero_of_head? hP.2.1 hpos
  have hlast : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  have hmemA : a ∈ P := PathBasics.head_mem hP.2.1
  have hmemB : b ∈ P := PathBasics.getLast_mem hP.2.2
  have hlen2 : 2 ≤ P.length := by
    by_contra hcon
    have hL : P.length = 1 := by omega
    rw [List.length_eq_one_iff] at hL
    obtain ⟨x, hx⟩ := hL
    rw [hx] at hmemA hmemB
    simp only [List.mem_singleton] at hmemA hmemB
    exact hab (hmemA.trans hmemB.symm)
  have hplen : SPGT.pathLength P = P.length - 1 := rfl
  have hone : 1 ≤ SPGT.pathLength P := by rw [hplen]; omega
  have hint : ∀ v ∈ SPGT.interior P, v ∉ A ∪ B := by
    intro v hv hvAB
    obtain ⟨k, hk, hk1, hk2, hkv⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hv
    rcases hvAB with hvA | hvB
    · -- the suffix from position `k` to the end is a shorter `A`-to-`B` path
      have hij : k < P.length - 1 := by omega
      have hj : P.length - 1 < P.length := by omega
      have hRpath : SPGT.IsPathFrom K ((P.drop k).take (P.length - 1 - k + 1)) v b := by
        refine ⟨PathBasics.isPathList_slice hP.1 hij hj, ?_, ?_⟩
        · rw [PathBasics.head?_slice P (le_of_lt hij) hj]
          exact congrArg some hkv
        · rw [PathBasics.getLast?_slice P (le_of_lt hij) hj]
          exact congrArg some hlast
      have hRX : ∀ w ∈ (P.drop k).take (P.length - 1 - k + 1), w ∈ X := by
        intro w hw
        rw [PathBasics.mem_slice_iff P (le_of_lt hij) hj] at hw
        obtain ⟨m, hm, _, _, rfl⟩ := hw
        exact hPX _ (List.getElem_mem hm)
      have hle := hmin v hvA b hb _ hRpath hRX
      have hRlen := PathBasics.length_slice P (le_of_lt hij) hj
      have hRp : SPGT.pathLength ((P.drop k).take (P.length - 1 - k + 1))
          = (P.length - 1 - k + 1) - 1 := by
        rw [PathBasics.pathLength_eq, hRlen]
      rw [hplen, hRp] at hle
      omega
    · -- the prefix from the start to position `k` is a shorter `A`-to-`B` path
      have hij : (0 : ℕ) < k := hk1
      have hj : k < P.length := hk
      have hRpath : SPGT.IsPathFrom K ((P.drop 0).take (k - 0 + 1)) a v := by
        refine ⟨PathBasics.isPathList_slice hP.1 hij hj, ?_, ?_⟩
        · rw [PathBasics.head?_slice P (le_of_lt hij) hj]
          exact congrArg some h0
        · rw [PathBasics.getLast?_slice P (le_of_lt hij) hj]
          exact congrArg some hkv
      have hRX : ∀ w ∈ (P.drop 0).take (k - 0 + 1), w ∈ X := by
        intro w hw
        rw [PathBasics.mem_slice_iff P (le_of_lt hij) hj] at hw
        obtain ⟨m, hm, _, _, rfl⟩ := hw
        exact hPX _ (List.getElem_mem hm)
      have hle := hmin a ha v hvB _ hRpath hRX
      have hRlen := PathBasics.length_slice P (le_of_lt hij) hj
      have hRp : SPGT.pathLength ((P.drop 0).take (k - 0 + 1)) = (k - 0 + 1) - 1 := by
        rw [PathBasics.pathLength_eq, hRlen]
      rw [hplen, hRp] at hle
      omega
  refine ⟨hab, hone, hint, ?_, ?_⟩
  · intro x hxP
    constructor
    · intro hxA
      by_contra hxa
      by_cases hxb : x = b
      · exact hdisj x hxA (hxb ▸ hb)
      · exact hint x ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hxP, hxa, hxb⟩)
          (Or.inl hxA)
    · rintro rfl
      exact ha
  · intro x hxP
    constructor
    · intro hxB
      by_contra hxb
      by_cases hxa : x = a
      · exact hdisj x (hxa ▸ ha) hxB
      · exact hint x ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hxP, hxa, hxb⟩)
          (Or.inr hxB)
    · rintro rfl
      exact hb

end Workspace.ProofLemmas
