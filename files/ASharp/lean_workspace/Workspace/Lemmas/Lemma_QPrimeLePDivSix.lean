import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Real

namespace Workspace.Lemmas.QPrimeLePDivSix

/-- **Theorem: q'_le_p_div_6**
Under the conditions of the main theorem with c_sel ≤ 100 * log(2),
we have q' = 16 * s * q ≤ p/6.

**Mathematical Argument**:
- q = (c_sel/100000) * p / log(t)
- q' = 16 * s * q = 16 * s * (c_sel/100000) * p / log(t)
- For s = ⌈log₂(2t)⌉ ≈ log(2t) / log(2) ≈ log(t) / log(2) + 1 (for large t)
- We can bound: s ≤ log(2t)/log(2) + 1 = 1 + log(t)/log(2) + 1 = 2 + log(t)/log(2)
- So: q' ≤ 16 * (2 + log(t)/log(2)) * (c_sel/100000) * p / log(t)
-     = 16 * c_sel/100000 * p * (2/log(t) + 1/log(2))
- For c_sel ≤ 100 * log(2) and t ≥ 2 (so log(t) ≥ log(2)):
-     q' ≤ 16 * (100*log(2))/100000 * p * (2/log(2) + 1/log(2))
-        = (1600*log(2)/100000) * p * (3/log(2))
-        = (1600/100000) * 3 * p
-        = 4800/100000 * p
-        = 0.048 * p < p/6 ≈ 0.167 * p

**Implementation Note**: This proof requires careful arithmetic with the ceiling bound.
The key insight is that the factor 16 * s * c_sel / (100000 * log t) is bounded by a
small constant (< 1/6) when c_sel ≤ 100 * log 2 and t ≥ 2.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem q_prime_le_p_div_6 (p c_sel : ℝ) (t : ℕ) (s : ℕ) (q q' : ℝ)
    (hp_pos : 0 < p) (hp_le1 : p ≤ 1)
    (hc_sel : 0 < c_sel) (hc_sel_le : c_sel ≤ 100 * log 2)
    (ht : 2 ≤ t) (hs : s = Nat.ceil (log (2 * t) / log 2))
    (hq : q = (c_sel / 100000) * p / log t)
    (hq' : q' = 16 * s * q) :
    q' ≤ p / 6 := by
  have hlog2_pos : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hlogt_pos : (0 : ℝ) < log ↑t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hlogt_ge_log2 : log 2 ≤ log ↑t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have h_nonneg_arg : 0 ≤ log (2 * ↑t) / log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * t by omega))) hlog2_pos.le
  -- s < log(2t)/log(2) + 1 by ceiling property
  have hs_lt : (↑s : ℝ) < log (2 * ↑t) / log 2 + 1 := by
    rw [hs]; exact Nat.ceil_lt_add_one h_nonneg_arg
  have h_log_2t : log (2 * ↑t) = log 2 + log ↑t :=
    Real.log_mul (by norm_num) ht_pos.ne'
  -- Therefore s < 2 + log(t)/log(2)
  have h_s_lt : (↑s : ℝ) < 2 + log ↑t / log 2 := by
    have := hs_lt
    rw [h_log_2t, add_div, div_self hlog2_pos.ne'] at this
    linarith
  -- s * log(2) < 2 * log(2) + log(t)
  have hs_mul : (↑s : ℝ) * log 2 < 2 * log 2 + log ↑t := by
    have h := mul_lt_mul_of_pos_right h_s_lt hlog2_pos
    rw [show (2 + log ↑t / log 2) * log 2 = 2 * log 2 + log ↑t by
      rw [add_mul, div_mul_cancel₀ _ hlog2_pos.ne']] at h
    linarith
  -- Key bound: 96 * s * c_sel ≤ 100000 * log(t)
  have h_key : 96 * (↑s : ℝ) * c_sel ≤ 100000 * log ↑t := by
    have hs_nonneg : 0 ≤ (↑s : ℝ) := Nat.cast_nonneg _
    calc 96 * (↑s : ℝ) * c_sel
        ≤ 96 * ((↑s : ℝ) * (100 * log 2)) := by nlinarith [hc_sel_le, hs_nonneg]
      _ = 9600 * ((↑s : ℝ) * log 2) := by ring
      _ ≤ 9600 * (2 * log 2 + log ↑t) := by nlinarith [hs_mul.le]
      _ = 19200 * log 2 + 9600 * log ↑t := by ring
      _ ≤ 19200 * log ↑t + 9600 * log ↑t := by nlinarith [hlogt_ge_log2]
      _ = 28800 * log ↑t := by ring
      _ ≤ 100000 * log ↑t := by nlinarith [hlogt_pos.le]
  -- Conclude q' ≤ p/6
  rw [hq', hq]
  have h_denom_pos : (0 : ℝ) < 6 * (100000 * log ↑t) := by positivity
  rw [show (16 : ℝ) * ↑s * ((c_sel / 100000) * p / log ↑t) =
      (96 * (↑s : ℝ) * c_sel * p) / (6 * (100000 * log ↑t)) by ring]
  apply (div_le_div_iff₀ h_denom_pos (by norm_num : (0 : ℝ) < 6)).mpr
  nlinarith [h_key, hp_pos, hlogt_pos]

end Workspace.Lemmas.QPrimeLePDivSix
