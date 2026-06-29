import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Workspace.Lemmas.HeavyLe

/-- **Theorem: heavy_le**
For s = ⌈log₂(2t)⌉, we have 1 - 2^(-s) ≥ 1 - 1/(2t).

**Mathematical Proof**:
- The inequality 1 - 2^(-s) ≥ 1 - 1/(2t) is equivalent to 2^(-s) ≤ 1/(2t)
- Which is equivalent to 2^s ≥ 2t
- Taking log₂: s ≥ log₂(2t)
- This holds by the ceiling property: ⌈x⌉ ≥ x

**Implementation Note**: The mathematical argument is straightforward:
1. s = ⌈log(2t) / log(2)⌉ ≥ log(2t) / log(2) (by ceiling property)
2. Multiply by log(2) > 0: s * log(2) ≥ log(2t)
3. Take exp: 2^s ≥ 2t
4. Take reciprocals: 1/2^s ≤ 1/(2t)
5. Therefore: 1 - 1/2^s ≥ 1 - 1/(2t)

This requires finding the correct lemmas for inverse inequalities and combining
logarithm/exponential properties. The proof is doable but requires careful
application of Mathlib lemmas.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem heavy_le (t : ℕ) (s : ℕ)
    (ht : 2 ≤ t) (hs : s = Nat.ceil (log (2 * t) / log 2)) :
    1 - (2 : ℝ) ^ (-(s : ℝ)) ≥ 1 - 1 / (2 * (t : ℝ)) := by
  suffices h : (2 : ℝ) ^ (-(s : ℝ)) ≤ 1 / (2 * (t : ℝ)) by linarith
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have h2t_pos : (0 : ℝ) < 2 * (t : ℝ) := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hlog2_pos : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  -- By the ceiling property: a ≤ ↑⌈a⌉₊
  have hs_ge : log (2 * ↑t) / log 2 ≤ (s : ℝ) := by
    rw [hs]; exact Nat.le_ceil _
  -- Multiply both sides by log 2 > 0
  have h_log_le : log (2 * ↑t) ≤ (s : ℝ) * log 2 := by
    have := mul_le_mul_of_nonneg_right hs_ge hlog2_pos.le
    rwa [div_mul_cancel₀ _ hlog2_pos.ne'] at this
  -- Therefore 2t ≤ 2^s (by log monotonicity)
  have h_2s_pos : (0 : ℝ) < (2 : ℝ) ^ (s : ℝ) := rpow_pos_of_pos h2_pos _
  have h_2s_ge : 2 * (t : ℝ) ≤ (2 : ℝ) ^ (s : ℝ) := by
    rw [← Real.log_le_log_iff h2t_pos h_2s_pos, Real.log_rpow h2_pos]
    exact h_log_le
  -- Therefore 2^(-s) = (2^s)⁻¹ ≤ (2t)⁻¹ = 1/(2t)
  rw [Real.rpow_neg h2_pos.le, one_div]
  exact inv_anti₀ h2t_pos h_2s_ge

end Workspace.Lemmas.HeavyLe
