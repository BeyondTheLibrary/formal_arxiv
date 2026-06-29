import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_DenomEq

open BigOperators

namespace Workspace.Lemmas.LambdaHSumEqWRelation

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

/-- Auxiliary lemma: the sum of λ_H over W ∩ H relates to the fractional cover w.
    This is equation (4.2) in the paper proof.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
lemma lambdaH_sum_eq_w_relation {X : Type} [Fintype X] [DecidableEq X]
    (t : ℕ) (ℋ : Set (Finset X)) (cov : FractionalCover X ℋ)
    (H : Finset X) (hH : H ∈ ℋ) (W : Finset X)
    (_h_supp : ∀ W' : Finset X, t < W'.card → cov.w W' = 0) :
    ∑ x ∈ W ∩ H, lambdaH cov H hH x =
    (∑ W' ∈ H.powerset, cov.w W' -
     ∑ W' ∈ H.powerset, if W' ⊆ W then 0 else cov.w W' * ((W'.card - (W' ∩ W).card : ℝ) / W'.card)) /
    (∑ W' ∈ H.powerset, cov.w W') := by
  have h_denom_eq := Workspace.Lemmas.LambdaH_DenomEq.lambdaH_denom_eq cov H hH
  -- Step 1: Unfold λ_H and factor out the constant denominator
  show (∑ x ∈ W ∩ H,
        (∑ W' ∈ H.powerset, if x ∈ W' then cov.w W' / (W'.card : ℝ) else 0) /
        (∑ y ∈ H, ∑ W' ∈ H.powerset, if y ∈ W' then cov.w W' / (W'.card : ℝ) else 0)) = _
  rw [← Finset.sum_div, h_denom_eq]
  -- Now goal: (∑ x ∈ W ∩ H, num(x)) / total = (total - conditional_sum) / total
  congr 1
  -- Goal: ∑ x ∈ W ∩ H, num(x) = total - conditional_sum
  -- Equivalently: ∑ x ∈ W ∩ H, num(x) + conditional_sum = total
  rw [eq_sub_iff_add_eq]
  -- Step 2: Combine the inner sums
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro W' hW'
  rw [Finset.mem_powerset] at hW'
  -- For each W' ⊆ H, show:
  --   (∑ x ∈ W ∩ H, if x ∈ W' then w(W')/|W'| else 0) +
  --   (if W' ⊆ W then 0 else w(W') * (|W'| - |W' ∩ W|)/|W'|) = w(W')
  -- Step 3: Convert the if-sum to a sum over a filtered set
  rw [← Finset.sum_filter]
  -- {x ∈ W ∩ H | x ∈ W'} = W' ∩ W (since W' ⊆ H)
  have h_filter : (W ∩ H).filter (· ∈ W') = W' ∩ W := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨hxW, _⟩, hxW'⟩; exact ⟨hxW', hxW⟩
    · rintro ⟨hxW', hxW⟩; exact ⟨⟨hxW, hW' hxW'⟩, hxW'⟩
  rw [h_filter, Finset.sum_const, nsmul_eq_mul]
  -- Goal: ↑(W' ∩ W).card * (w(W')/|W'|) +
  --       (if W' ⊆ W then 0 else w(W') * ((|W'| - |W' ∩ W|)/|W'|)) = w(W')
  by_cases hW'_sub : W' ⊆ W
  · -- Case: W' ⊆ W. Then W' ∩ W = W' and the conditional gives 0.
    rw [if_pos hW'_sub, add_zero]
    have h_inter : W' ∩ W = W' := Finset.inter_eq_left.mpr hW'_sub
    rw [h_inter]
    rcases Nat.eq_zero_or_pos W'.card with h | h
    · -- W' = ∅: w(∅) = 0, so both sides vanish
      have hempty : W' = ∅ := Finset.card_eq_zero.mp h
      rw [hempty, cov.w_empty]; simp
    · -- W' nonempty: |W'| * (w(W')/|W'|) = w(W')
      have hc : (W'.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
      field_simp
  · -- Case: W' ⊄ W. Then W' must be nonempty (else ∅ ⊆ W).
    rw [if_neg hW'_sub]
    have hpos : 0 < W'.card := by
      rcases Nat.eq_zero_or_pos W'.card with h | h
      · exfalso; apply hW'_sub
        rw [Finset.card_eq_zero.mp h]; exact Finset.empty_subset _
      · exact h
    have hc : (W'.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    -- Algebraic identity: |W'∩W|·(w/|W'|) + w·(|W'|-|W'∩W|)/|W'| = w
    field_simp
    ring

end Workspace.Lemmas.LambdaHSumEqWRelation
