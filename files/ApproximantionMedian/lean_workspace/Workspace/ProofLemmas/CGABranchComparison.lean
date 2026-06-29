import Mathlib
import Workspace.ProofLemmas.CGDefs

open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.CGABranchComparison

/-- **CGABranchComparison** (prediction.tex line 197; appendix `a₁'` vs `(1-c)/2`).
For `c ≥ 0`, with `a₁' = (2 + c − √(3+2c))/2 = a1' c`:
`a₁' ≤ (1-c)/2 ⟺ c ≤ 1/2`.
(Proof: `a₁' − (1-c)/2 = (1 + 2c − √(3+2c))/2`, so the inequality is
`√(3+2c) ≥ 1 + 2c`; squaring both nonnegative sides gives
`0 ≥ 2(2c−1)(c+1) ⟺ c ≤ 1/2`.) -/
theorem CGABranchComparison_iff (c : ℝ) (hc : 0 ≤ c) :
    a1' c ≤ (1 - c) / 2 ↔ c ≤ 1 / 2 := by
  unfold a1'
  rw [div_le_div_iff_of_pos_right (show (0:ℝ) < 2 by norm_num)]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 + 2 * c by linarith),
      Real.sqrt_nonneg (3 + 2 * c)]
  · intro h
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 + 2 * c by linarith),
      Real.sqrt_nonneg (3 + 2 * c),
      Real.sqrt_le_sqrt (show (1 + 2 * c) ^ 2 ≤ 3 + 2 * c by nlinarith),
      Real.sqrt_sq (show (0:ℝ) ≤ 1 + 2 * c by linarith)]

/-- Consequently the branched optimum `a1 c` is the interior root for `c < 1/2`
and the constraint boundary `(1-c)/2` for `c ≥ 1/2` — i.e. `a1` agrees with its
definition, which is the content of the branch selection from
`CGOptimalSolutionForA1` (`a₁ = a₁'` when the interior point is feasible, i.e.
`a₁' ≤ (1-c)/2`; otherwise `a₁ = (1-c)/2`). -/
theorem CGABranchComparison_value (c : ℝ) (hc : 0 ≤ c) :
    (c < 1 / 2 → a1 c = a1' c) ∧ (1 / 2 ≤ c → a1 c = (1 - c) / 2) := by
  exact ⟨fun h => by unfold a1; rw [if_pos h],
    fun h => by unfold a1; rw [if_neg (by linarith)]⟩

end Workspace.ProofLemmas.CGABranchComparison
