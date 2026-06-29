import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Workspace.Lemmas.QPos

/-- **Theorem: q_pos**
For p > 0, c_sel > 0, and t ≥ 2, we have q = (c_sel/100000) * p / log(t) > 0.

**Mathematical Proof**:
- Numerator: (c_sel/100000) * p > 0 since both c_sel > 0 and p > 0
- Denominator: log(t) > 0 for t ≥ 2, since t ≥ 2 > 1 and log is strictly increasing
- Ratio of two positive numbers is positive

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem q_pos (p c_sel : ℝ) (t : ℕ)
    (hp : 0 < p) (hc_sel : 0 < c_sel) (ht : 2 ≤ t) :
    0 < (c_sel / 100000) * p / log t := by
  apply div_pos
  · apply mul_pos
    · apply div_pos hc_sel (by norm_num : (0 : ℝ) < 100000)
    · exact hp
  · have ht_pos : 1 < (t : ℝ) := by
      simp only [Nat.one_lt_cast]
      omega
    exact log_pos ht_pos

end Workspace.Lemmas.QPos
