import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Workspace.Lemmas.QLeOne

/-- **Theorem: q_le_one**
For p ≤ 1, t ≥ 2, and c_sel ≤ 100 * log(2), we have q = (c_sel/100000) * p / log(t) ≤ 1.

**Mathematical Proof**:
- We have (c_sel/100000) * p ≤ c_sel/100000 since p ≤ 1
- For t ≥ 2: log(t) ≥ log(2)
- So q ≤ (c_sel/100000) / log(2)
- If c_sel ≤ 100 * log(2), then (c_sel/100000) / log(2) ≤ (100 * log(2) / 100000) / log(2) = 1/1000 ≤ 1

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem q_le_one (p c_sel : ℝ) (t : ℕ)
    (hp_le1 : p ≤ 1) (_hp_nonneg : 0 ≤ p)
    (hc_sel_pos : 0 < c_sel) (hc_sel_le : c_sel ≤ 100 * log 2)
    (ht : 2 ≤ t) :
    (c_sel / 100000) * p / log t ≤ 1 := by
  -- Step 1: (c_sel/100000) * p ≤ c_sel/100000
  have step1 : (c_sel / 100000) * p ≤ c_sel / 100000 := by
    have : (c_sel / 100000) * p ≤ (c_sel / 100000) * 1 := by
      apply mul_le_mul_of_nonneg_left hp_le1
      apply div_nonneg (le_of_lt hc_sel_pos) (by norm_num : (0 : ℝ) ≤ 100000)
    rw [mul_one] at this
    exact this

  -- Step 2: log 2 ≤ log t
  have step2 : log 2 ≤ log t := by
    apply log_le_log
    · norm_num
    · have : 2 ≤ (t : ℝ) := by exact Nat.cast_le.mpr ht
      linarith

  have hlog2_pos : 0 < log 2 := log_pos (by norm_num : 1 < (2 : ℝ))
  have hlogt_pos : 0 < log t := by
    apply log_pos
    have : 1 < (t : ℝ) := by simp only [Nat.one_lt_cast]; omega
    exact this

  -- Main calculation
  calc (c_sel / 100000) * p / log t
      ≤ (c_sel / 100000) / log t := by
        apply div_le_div_of_nonneg_right step1 (le_of_lt hlogt_pos)
    _ ≤ (c_sel / 100000) / log 2 := by
        apply div_le_div_of_nonneg_left _ hlog2_pos step2
        apply div_nonneg (le_of_lt hc_sel_pos)
        norm_num
    _ ≤ (100 * log 2 / 100000) / log 2 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hlog2_pos)
        apply div_le_div_of_nonneg_right hc_sel_le
        norm_num
    _ = 100 / 100000 := by
        field_simp [ne_of_gt hlog2_pos]
    _ ≤ 1 := by norm_num

end Workspace.Lemmas.QLeOne
