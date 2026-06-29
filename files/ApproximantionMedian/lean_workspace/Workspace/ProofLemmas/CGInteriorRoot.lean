import Mathlib
import Workspace.ProofLemmas.CGDefs

open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.CGInteriorRoot

/-- **CGInteriorRoot** (appendix.tex 190–196). For `c ≥ 0` the quadratic factor
`2t² + 2t − (1+c) = 0` has a unique nonnegative root `t₁ = (−1 + √(3+2c))/2`
(the other root `(−1 − √(3+2c))/2 < 0` is rejected since `t₁ = √(a₁') ≥ 0`).
Consequently the interior critical point of `u₁` is
`a₁' = t₁² = (2 + c − √(3+2c))/2 = a1' c`.

The statement bundles: (a) `t₁` is a root of the quadratic, (b) `t₁ ≥ 0`,
(c) the negative root is `< 0`, (d) `a₁' = t₁²` matches `a1' c`. -/
theorem CGInteriorRoot (c : ℝ) (hc : 0 ≤ c) :
    let t1 : ℝ := (-1 + Real.sqrt (3 + 2 * c)) / 2
    (2 * t1 ^ 2 + 2 * t1 - (1 + c) = 0) ∧
    (0 ≤ t1) ∧
    ((-1 - Real.sqrt (3 + 2 * c)) / 2 < 0) ∧
    (a1' c = t1 ^ 2) := by
  intro t1
  have h3 : (0:ℝ) ≤ 3 + 2 * c := by linarith
  set s := Real.sqrt (3 + 2 * c) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 3 + 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt h3]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have ht1 : t1 = (-1 + s) / 2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht1]; nlinarith [hs_sq]
  · rw [ht1]; linarith
  · linarith
  · rw [ht1]
    show a1' c = ((-1 + s) / 2) ^ 2
    rw [a1']; nlinarith [hs_sq]

end Workspace.ProofLemmas.CGInteriorRoot
