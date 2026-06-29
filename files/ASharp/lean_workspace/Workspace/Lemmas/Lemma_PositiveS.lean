import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open Real

namespace Workspace.Lemmas.PositiveS

/-- **Theorem: s_pos**
For t ≥ 2, we have s = ⌈log₂(2t)⌉ > 0.

**Mathematical Proof**:
- For t ≥ 2, we have 2t ≥ 4
- Since log₂ is strictly increasing and log₂(4) = 2
- We get log₂(2t) ≥ 2
- By ceiling property: s = ⌈log₂(2t)⌉ ≥ log₂(2t) ≥ 2 > 0

**Implementation Note**: This theorem requires:
1. log₂(x) = log(x) / log(2) in Lean
2. Properties: log is strictly increasing for x > 0
3. log(4) / log(2) = 2 (computable)
4. Ceiling function properties: ⌈x⌉ ≥ x
These are available in Mathlib but require careful chaining of lemmas.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem s_pos (t : ℕ) (ht : 2 ≤ t) : 0 < Nat.ceil (log (2 * t) / log 2) := by
  -- Show that 2t ≥ 4, so 2*t > 1 as a real
  have h2t_pos : 1 < (2 * t : ℝ) := by
    have : 4 ≤ 2 * t := by omega
    have : (4 : ℝ) ≤ (2 * t : ℝ) := by norm_cast
    linarith

  -- log(2t) / log(2) > 0
  have hlog_pos : 0 < log (2 * t) / log 2 := by
    apply div_pos
    · exact log_pos h2t_pos
    · exact log_pos (by norm_num : 1 < (2 : ℝ))

  -- Ceiling of positive number is positive
  exact Nat.ceil_pos.mpr hlog_pos

end Workspace.Lemmas.PositiveS
