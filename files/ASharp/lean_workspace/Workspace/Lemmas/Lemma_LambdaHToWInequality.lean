import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaHSumEqWRelation
import Workspace.Lemmas.Lemma_LambdaHToWInequality_TermBound

open BigOperators

namespace Workspace.Lemmas.LambdaHToWInequality

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

/-- The key inequality relating λ_H to w.
    When λ_H is heavy on W ∩ H, then w is heavy on subsets of H ∩ W.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem lambdaH_to_w_inequality {X : Type} [Fintype X] [DecidableEq X]
    (t : ℕ) (ℋ : Set (Finset X)) (cov : FractionalCover X ℋ)
    (H : Finset X) (hH : H ∈ ℋ) (W : Finset X)
    (h_supp : ∀ W' : Finset X, t < W'.card → cov.w W' = 0)
    (h_lambda : (1 : ℝ) - (2 : ℝ) ^ (-(Nat.ceil (Real.log (2 * t) / Real.log 2) : ℝ)) ≤
                ∑ x ∈ W ∩ H, lambdaH cov H hH x)
    (h_heavy_le : (1 : ℝ) - (2 : ℝ) ^ (-(Nat.ceil (Real.log (2 * t) / Real.log 2) : ℝ)) ≥
                  1 - 1 / (2 * (t : ℝ))) :
    1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W' := by
  -- Abbreviations
  set S : ℝ := ∑ W' ∈ H.powerset, cov.w W' with hS_def
  set P : ℝ := ∑ W' ∈ (H ∩ W).powerset, cov.w W' with hP_def
  set T : ℝ := ∑ W' ∈ H.powerset,
      if W' ⊆ W then 0 else cov.w W' * (((W'.card : ℝ) - (W' ∩ W).card) / W'.card) with hT_def
  -- (1) S ≥ 1 (from cover) and S > 0
  have hS_ge_one : (1 : ℝ) ≤ S := cov.is_cover H hH
  have hS_pos : (0 : ℝ) < S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hS_ge_one
  -- (2) Combine h_lambda and h_heavy_le to get 1 - 1/(2t) ≤ ∑ λ_H
  have h_sum_lambda_lb : (1 : ℝ) - 1 / (2 * (t : ℝ)) ≤ ∑ x ∈ W ∩ H, lambdaH cov H hH x := by
    linarith
  -- (3) Apply lambdaH_sum_eq_w_relation
  have h_eq := Workspace.Lemmas.LambdaHSumEqWRelation.lambdaH_sum_eq_w_relation
                t ℋ cov H hH W h_supp
  -- The RHS of h_eq is (S - T) / S
  have h_eq' : ∑ x ∈ W ∩ H, lambdaH cov H hH x = (S - T) / S := h_eq
  -- (4) Establish t ≥ 1: otherwise h_supp + w_empty implies S = 0, contradiction.
  have ht_pos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with ht0 | ht_pos
    · exfalso
      -- t = 0: every W' has cov.w W' = 0
      have h_all_zero : ∀ W' ∈ H.powerset, cov.w W' = 0 := by
        intro W' _
        rcases Nat.eq_zero_or_pos W'.card with hc | hc
        · rw [Finset.card_eq_zero.mp hc]; exact cov.w_empty
        · apply h_supp W'
          rw [ht0]; exact hc
      have hS_zero : S = 0 := by
        rw [hS_def]
        exact Finset.sum_eq_zero h_all_zero
      linarith
    · exact ht_pos
  have ht_pos_real : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  -- (5) Decompose S - P as ∑ W' ∈ H.powerset, if W' ⊆ W then 0 else cov.w W'
  -- Since (H ∩ W).powerset corresponds exactly to subsets W' of H with W' ⊆ W.
  have h_S_minus_P : S - P =
      ∑ W' ∈ H.powerset, if W' ⊆ W then 0 else cov.w W' := by
    -- S = ∑ W' ∈ H.powerset, cov.w W'
    --   = ∑ W' ∈ H.powerset, (if W' ⊆ W then cov.w W' else 0) +
    --     ∑ W' ∈ H.powerset, (if W' ⊆ W then 0 else cov.w W')
    have h_split : S =
        (∑ W' ∈ H.powerset, if W' ⊆ W then cov.w W' else 0) +
        (∑ W' ∈ H.powerset, if W' ⊆ W then 0 else cov.w W') := by
      rw [hS_def, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro W' _
      by_cases hWW : W' ⊆ W
      · simp [hWW]
      · simp [hWW]
    -- ∑ W' ∈ H.powerset, (if W' ⊆ W then cov.w W' else 0) = P
    have h_P_eq : (∑ W' ∈ H.powerset, if W' ⊆ W then cov.w W' else 0) = P := by
      rw [hP_def]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext W'
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hH', hW'⟩
        exact Finset.subset_inter hH' hW'
      · intro hHW
        refine ⟨hHW.trans Finset.inter_subset_left, hHW.trans Finset.inter_subset_right⟩
    linarith
  -- (6) Apply the term-by-term bound: T ≥ (S - P)/t
  have h_T_lb : (S - P) / (t : ℝ) ≤ T := by
    rw [h_S_minus_P]
    rw [hT_def]
    -- Need: ∑ (if W' ⊆ W then 0 else cov.w W') / t ≤ ∑ (if W' ⊆ W then 0 else cov.w W' * ((|W'|-|W'∩W|)/|W'|))
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro W' _
    exact Workspace.Lemmas.LambdaHToWInequality_TermBound.term_bound
            cov t W h_supp ht_pos W'
  -- (7) Combine: 1 - 1/(2t) ≤ (S - T)/S
  have h_sum_eq_lb : (1 : ℝ) - 1 / (2 * (t : ℝ)) ≤ (S - T) / S := by
    rw [← h_eq']; exact h_sum_lambda_lb
  -- Multiply by S > 0: (1 - 1/(2t)) * S ≤ S - T
  have h_mul_S : (1 - 1 / (2 * (t : ℝ))) * S ≤ S - T := by
    have := mul_le_mul_of_nonneg_right h_sum_eq_lb hS_pos.le
    rwa [div_mul_cancel₀ _ hS_pos.ne'] at this
  -- So T ≤ S - (1 - 1/(2t)) * S = S/(2t)
  have h_T_ub : T ≤ S / (2 * (t : ℝ)) := by
    have h2t_pos : (0 : ℝ) < 2 * (t : ℝ) := by linarith
    have : T ≤ S - (1 - 1 / (2 * (t : ℝ))) * S := by linarith
    have hS_eq : S - (1 - 1 / (2 * (t : ℝ))) * S = S / (2 * (t : ℝ)) := by
      field_simp; ring
    linarith
  -- (8) Combine h_T_lb and h_T_ub: (S-P)/t ≤ S/(2t)
  have h_combined : (S - P) / (t : ℝ) ≤ S / (2 * (t : ℝ)) := le_trans h_T_lb h_T_ub
  -- Multiply both sides by t > 0: S - P ≤ S/2
  have h_SP_bound : S - P ≤ S / 2 := by
    have : (S - P) / (t : ℝ) * (t : ℝ) ≤ S / (2 * (t : ℝ)) * (t : ℝ) :=
      mul_le_mul_of_nonneg_right h_combined ht_pos_real.le
    rwa [div_mul_cancel₀ _ ht_pos_real.ne',
         show S / (2 * (t : ℝ)) * (t : ℝ) = S / 2 by field_simp] at this
  -- (9) Conclude: P ≥ S/2 ≥ 1/2
  have hP_ge : S / 2 ≤ P := by linarith
  have h_half : (1 : ℝ) / 2 ≤ S / 2 := by linarith
  linarith

end Workspace.Lemmas.LambdaHToWInequality
