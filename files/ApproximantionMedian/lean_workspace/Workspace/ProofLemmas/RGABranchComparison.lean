import Mathlib
import Workspace.ProofLemmas.RGDefs

open Workspace.ProofLemmas.RGDefs

namespace Workspace.ProofLemmas.RGABranchComparison

/-- **RGABranchComparison** (proof_detailed.md Step 13; appendix.tex 294, `a₂'` vs
`(1+c)/2`; the `c → −c` image of `CGABranchComparison`).

SINGLE BRANCH: for EVERY `c ∈ [0,1)`, with
`a₂' = (2 − c − √(3−2c))/2 = a2' c`:
`a₂' ≤ (1+c)/2`.

(Proof: `a₂' − (1+c)/2 = (1 − 2c − √(3−2c))/2`, so the inequality is
`√(3−2c) ≥ 1 − 2c`. If `1 − 2c ≤ 0` this is immediate; else squaring both
nonneg sides gives `0 ≥ 2(2c+1)(c−1) ⟺ (2c+1)(c−1) ≤ 0`, which holds on
`[0,1)` since `2c+1 > 0` and `c−1 < 0`. Unlike consistency's two-branch factor
`(2c−1)(c+1)`, here `(2c+1)(c−1) ≤ 0` on the WHOLE interval — no phase
transition.) -/
theorem RGABranchComparison_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    a2' c ≤ (1 + c) / 2 := by
  unfold a2'
  rw [div_le_div_iff_of_pos_right (show (0:ℝ) < 2 by norm_num)]
  -- Goal: 2 - c - √(3 - 2*c) ≤ 1 + c
  -- ⟺ 1 - 2*c ≤ √(3 - 2*c)
  have hsqnn : (0:ℝ) ≤ Real.sqrt (3 - 2 * c) := Real.sqrt_nonneg _
  have h32 : (0:ℝ) ≤ 3 - 2 * c := by linarith
  by_cases hcase : c < 1 / 2
  · -- c < 1/2, so 1 - 2c > 0; need to square
    have h12c_nn : (0:ℝ) ≤ 1 - 2 * c := by linarith
    -- (1-2c)^2 = 4c^2 - 4c + 1 ≤ 3 - 2c iff 4c^2 - 2c - 2 ≤ 0 iff 2(2c+1)(c-1) ≤ 0
    nlinarith [Real.sq_sqrt h32, Real.sqrt_nonneg (3 - 2 * c),
               Real.sqrt_le_sqrt (show (1 - 2*c)^2 ≤ 3 - 2*c by nlinarith),
               Real.sqrt_sq h12c_nn]
  · -- c ≥ 1/2, so 1 - 2c ≤ 0 ≤ √(3 - 2c)
    have hc12 : 1 / 2 ≤ c := not_lt.mp hcase
    nlinarith [Real.sqrt_nonneg (3 - 2 * c)]

/-- Consequently the optimal `a₂` is the interior root for ALL `c ∈ [0,1)`:
`a₂ = a₂'`. The constraint boundary `(1+c)/2` never binds (single branch — this
is the definitional content of `a2`, justified by `RGABranchComparison_le`). -/
theorem RGABranchComparison_value (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    a2 c = a2' c := by
  unfold a2
  rfl

end Workspace.ProofLemmas.RGABranchComparison
