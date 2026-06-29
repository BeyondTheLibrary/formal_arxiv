import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Workspace.Types.FractionalCover

open BigOperators

namespace Workspace.Lemmas.LambdaHToWInequality_TermBound

open Workspace.Types.FractionalCover

/-- Term-by-term bound used in the proof of `lambdaH_to_w_inequality`.

For any `W' : Finset X` and any `W : Finset X`, under the support condition
`h_supp` (`cov.w W' = 0` for `|W'| > t`) and `1 ≤ t`, we have:

  (if W' ⊆ W then 0 else cov.w W') / t
    ≤ (if W' ⊆ W then 0 else cov.w W' * ((W'.card - (W' ∩ W).card) / W'.card))

The intuition: when `W' ⊄ W`, there is at least one element of `W'` outside `W`,
so `|W' ∩ W| ≤ |W'| - 1`, hence `(|W'| - |W' ∩ W|)/|W'| ≥ 1/|W'| ≥ 1/t`
(the last using `cov.w W' > 0 ⇒ |W'| ≤ t`).

This lemma is broken out as a helper to keep the main proof readable.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
lemma term_bound {X : Type} [Fintype X] [DecidableEq X]
    {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)
    (t : ℕ) (W : Finset X)
    (h_supp : ∀ W' : Finset X, t < W'.card → cov.w W' = 0)
    (ht_pos : 1 ≤ t)
    (W' : Finset X) :
    (if W' ⊆ W then 0 else cov.w W') / (t : ℝ)
    ≤ (if W' ⊆ W then 0
       else cov.w W' * (((W'.card : ℝ) - (W' ∩ W).card) / W'.card)) := by
  have ht_pos_real : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  by_cases hsub : W' ⊆ W
  · simp [hsub]
  · simp only [if_neg hsub]
    -- W' ⊄ W ⇒ W' ≠ ∅
    have hW'_ne : W'.Nonempty := by
      rcases Finset.eq_empty_or_nonempty W' with h | h
      · exfalso; apply hsub; rw [h]; exact Finset.empty_subset _
      · exact h
    have hW'_card_pos : 0 < W'.card := Finset.card_pos.mpr hW'_ne
    have hW'_card_real_pos : (0 : ℝ) < (W'.card : ℝ) := by exact_mod_cast hW'_card_pos
    -- W' ⊄ W ⇒ |W' ∩ W| < |W'|
    have h_inter_ssubset : W' ∩ W ⊂ W' := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      apply hsub
      intro x hx
      have hin : x ∈ W' ∩ W := heq.ge hx
      exact (Finset.mem_inter.mp hin).2
    have h_inter_lt : (W' ∩ W).card < W'.card := Finset.card_lt_card h_inter_ssubset
    have h_inter_le : (W' ∩ W).card + 1 ≤ W'.card := h_inter_lt
    have h_diff_ge_one : (1 : ℝ) ≤ (W'.card : ℝ) - ((W' ∩ W).card : ℝ) := by
      have : ((W' ∩ W).card : ℝ) + 1 ≤ (W'.card : ℝ) := by exact_mod_cast h_inter_le
      linarith
    have hcov_nn : 0 ≤ cov.w W' := cov.nonneg W'
    -- Split on whether cov.w W' = 0
    rcases eq_or_lt_of_le hcov_nn with h0 | hpos
    · -- cov.w W' = 0: both sides zero
      rw [← h0, zero_div, zero_mul]
    · -- cov.w W' > 0 ⇒ |W'| ≤ t
      have hW'_le_t : W'.card ≤ t := by
        by_contra h
        push_neg at h
        have := h_supp W' h
        linarith
      have hW'_le_t_real : (W'.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hW'_le_t
      -- Key inequality: 1/t ≤ (|W'| - |W' ∩ W|)/|W'|
      -- Proof: (|W'| - |W' ∩ W|)/|W'| ≥ 1/|W'| ≥ 1/t
      have h_div_ge : (1 : ℝ) / (t : ℝ) ≤ ((W'.card : ℝ) - (W' ∩ W).card) / W'.card := by
        have h1 : (1 : ℝ) / (t : ℝ) ≤ 1 / (W'.card : ℝ) :=
          one_div_le_one_div_of_le hW'_card_real_pos hW'_le_t_real
        have h2 : (1 : ℝ) / (W'.card : ℝ) ≤
              ((W'.card : ℝ) - (W' ∩ W).card) / W'.card :=
          div_le_div_of_nonneg_right h_diff_ge_one hW'_card_real_pos.le
        linarith
      -- Now conclude: cov.w W' / t = cov.w W' * (1/t) ≤ cov.w W' * (...)
      have step : cov.w W' / (t : ℝ) = cov.w W' * (1 / (t : ℝ)) := by
        rw [mul_one_div]
      rw [step]
      exact mul_le_mul_of_nonneg_left h_div_ge hcov_nn

end Workspace.Lemmas.LambdaHToWInequality_TermBound
