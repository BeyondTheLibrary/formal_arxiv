import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace Workspace.Lemmas.PowBoundFromRatio

/-- If 0 ≤ q' ≤ p/6 and W.card ≥ 1, then q'^|W| ≤ (p/6)^|W| ≤ (1/6) p^|W|.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
lemma pow_bound_from_ratio {p q' : ℝ} {k : ℕ}
    (hp : 0 ≤ p) (hq' : 0 ≤ q') (hq'_le : q' ≤ p / 6) (hk : k ≥ 1) :
    q' ^ k ≤ (1 / 6) * p ^ k := by
  have h_pdivsix : q' ≤ 1 / 6 * p := by linarith
  have h1 : q' ^ k ≤ (1 / 6 * p) ^ k := by gcongr
  rw [mul_pow] at h1
  have h2 : (1 / 6 : ℝ) ^ k ≤ 1 / 6 := by
    have := pow_le_pow_of_le_one (show (0:ℝ) ≤ 1/6 by norm_num) (show (1:ℝ)/6 ≤ 1 by norm_num) hk
    simpa using this
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (pow_nonneg hp k))

end Workspace.Lemmas.PowBoundFromRatio
