import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Joining two tracks that meet only at a common end

The third path of 5.8 (7) runs from the cycle of `H` to the branch `R_{u₂v₂}` and then along
that branch to an attachment of `p₂`.  It is therefore the concatenation of two tracks meeting
only at the junction, and this file provides that concatenation together with the two index
dictionaries needed to read its edges.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Connectivity58Concat

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

theorem length_append (T₁ T₂ : List W) :
    (T₁ ++ T₂.tail).length = T₁.length + (T₂.length - 1) := by
  simp only [List.length_append, List.length_tail]

theorem mem_append {T₁ T₂ : List W} {z : W} :
    z ∈ T₁ ++ T₂.tail ↔ z ∈ T₁ ∨ z ∈ T₂.tail := List.mem_append

theorem append_getElem_left (T₁ T₂ : List W) (i : ℕ) (hi : i < T₁.length)
    (h : i < (T₁ ++ T₂.tail).length) : (T₁ ++ T₂.tail)[i] = T₁[i] :=
  List.getElem_append_left hi

/-- Reading the second half: position `|T₁| - 1 + k` of the concatenation is position `k` of
`T₂`.  For `k = 0` this is the junction, which belongs to both halves. -/
theorem append_getElem_right {T₁ T₂ : List W} {a b d : W}
    (h₁ : IsTrackFrom H T₁ a b) (h₂ : IsTrackFrom H T₂ b d) (k : ℕ) (hk : k < T₂.length)
    (h : T₁.length - 1 + k < (T₁ ++ T₂.tail).length) :
    (T₁ ++ T₂.tail)[T₁.length - 1 + k] = T₂[k] := by
  have h1pos : 0 < T₁.length := List.length_pos_of_ne_nil h₁.1.1
  have h2pos : 0 < T₂.length := List.length_pos_of_ne_nil h₂.1.1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hb1 : T₁[T₁.length - 1]'(by omega) = b := by
      have h' := h₁.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : T₁.length - 1 < T₁.length)] at h'
      exact Option.some_injective _ h'
    have hb2 : T₂[0]'(by omega) = b := by
      have h' := h₂.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < T₂.length)] at h'
      exact Option.some_injective _ h'
    simp only [Nat.add_zero] at h ⊢
    rw [append_getElem_left T₁ T₂ _ (by omega) h, hb1, hb2]
  · have hge : T₁.length ≤ T₁.length - 1 + k := by omega
    rw [List.getElem_append_right hge]
    have : T₁.length - 1 + k - T₁.length < T₂.tail.length := by
      rw [List.length_tail]; omega
    rw [List.getElem_tail]
    exact getElem_eq_of_index_eq T₂ (by omega) _ _

/-- **Two tracks meeting only at a common end concatenate to a track.** -/
theorem isTrackFrom_append {T₁ T₂ : List W} {a b d : W}
    (h₁ : IsTrackFrom H T₁ a b) (h₂ : IsTrackFrom H T₂ b d)
    (hdisj : ∀ z ∈ T₁, z ∈ T₂ → z = b) :
    IsTrackFrom H (T₁ ++ T₂.tail) a d := by
  classical
  have h1pos : 0 < T₁.length := List.length_pos_of_ne_nil h₁.1.1
  have h2pos : 0 < T₂.length := List.length_pos_of_ne_nil h₂.1.1
  have hlen := length_append T₁ T₂
  have hb1 : T₁[T₁.length - 1]'(by omega) = b := by
    have h' := h₁.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : T₁.length - 1 < T₁.length)] at h'
    exact Option.some_injective _ h'
  have hb2 : T₂[0]'(by omega) = b := by
    have h' := h₂.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < T₂.length)] at h'
    exact Option.some_injective _ h'
  have hbtail : b ∉ T₂.tail := by
    intro hmem
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_tail] at hi
    rw [List.getElem_tail] at hie
    have := h₂.1.2.1.getElem_inj_iff (hi := (by omega : i + 1 < T₂.length))
      (hj := (by omega : 0 < T₂.length)) |>.mp (hie.trans hb2.symm)
    omega
  have htailsub : ∀ z ∈ T₂.tail, z ∈ T₂ := fun z hz => List.mem_of_mem_tail hz
  refine ⟨⟨by simp [h₁.1.1], ?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨h₁.1.2.1, List.Nodup.sublist (List.tail_sublist _) h₂.1.2.1, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact hbtail (hdisj x hx (htailsub x hy) ▸ hy)
  · intro i hi
    rw [hlen] at hi
    rcases Nat.lt_or_ge (i + 1) T₁.length with hcase | hcase
    · rw [append_getElem_left T₁ T₂ i (by omega) (by rw [hlen]; omega),
        append_getElem_left T₁ T₂ (i + 1) hcase (by rw [hlen]; omega)]
      exact h₁.1.2.2 i hcase
    · have hi1 : i = T₁.length - 1 + (i + 1 - T₁.length) := by omega
      have he1 : (T₁ ++ T₂.tail)[i]'(by rw [hlen]; omega)
          = T₂[i + 1 - T₁.length]'(by omega) := by
        rw [getElem_eq_of_index_eq (T₁ ++ T₂.tail) hi1 (by rw [hlen]; omega)
          (by rw [hlen]; omega)]
        exact append_getElem_right h₁ h₂ _ (by omega) (by rw [hlen]; omega)
      have hi2 : i + 1 = T₁.length - 1 + (i + 2 - T₁.length) := by omega
      have he2 : (T₁ ++ T₂.tail)[i + 1]'(by rw [hlen]; omega)
          = T₂[i + 2 - T₁.length]'(by omega) := by
        rw [getElem_eq_of_index_eq (T₁ ++ T₂.tail) hi2 (by rw [hlen]; omega)
          (by rw [hlen]; omega)]
        exact append_getElem_right h₁ h₂ _ (by omega) (by rw [hlen]; omega)
      rw [he1, he2]
      have := h₂.1.2.2 (i + 1 - T₁.length) (by omega)
      rw [getElem_eq_of_index_eq T₂ (show i + 1 - T₁.length + 1 = i + 2 - T₁.length by omega)
        (by omega) (by omega)] at this
      exact this
  · rw [List.head?_append, h₁.2.1]
    rfl
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    have hidx : (T₁ ++ T₂.tail).length - 1 = T₁.length - 1 + (T₂.length - 1) := by
      rw [hlen]; omega
    have hd : T₂[T₂.length - 1]'(by omega) = d := by
      have h' := h₂.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : T₂.length - 1 < T₂.length)] at h'
      exact Option.some_injective _ h'
    rw [getElem_eq_of_index_eq (T₁ ++ T₂.tail) hidx (by rw [hlen]; omega) (by rw [hlen]; omega),
      append_getElem_right h₁ h₂ _ (by omega) (by rw [hlen]; omega), hd]

end Workspace.ProofLemmas.Connectivity58Concat
