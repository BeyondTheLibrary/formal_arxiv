import Mathlib
import Workspace.ProofLemmas.RGDefs

open Workspace.ProofLemmas.RGDefs

namespace Workspace.ProofLemmas.RGInteriorRoot

/-- **RGInteriorRoot** (appendix.tex 292–294; `c → −c` mirror of `CGInteriorRoot`).
For `c ∈ [0,1)` the quadratic factor `2t² + 2t − (1−c) = 0` has a unique nonnegative
root `t₂ = (−1 + √(3−2c))/2` (the other root `(−1 − √(3−2c))/2 < 0` is rejected since
`t₂ = √(a₂') ≥ 0`). Consequently the interior critical point of `u₂` is
`a₂' = t₂² = (2 − c − √(3−2c))/2 = a2' c`.

The statement bundles: (a) `t₂` is a root of the quadratic, (b) `t₂ ≥ 0`,
(c) the negative root is `< 0`, (d) `a₂' = t₂²` matches `a2' c`. -/
theorem RGInteriorRoot (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    let t2 : ℝ := (-1 + Real.sqrt (3 - 2 * c)) / 2
    (2 * t2 ^ 2 + 2 * t2 - (1 - c) = 0) ∧
    (0 ≤ t2) ∧
    ((-1 - Real.sqrt (3 - 2 * c)) / 2 < 0) ∧
    (a2' c = t2 ^ 2) := by
  intro t2
  have h3 : (0:ℝ) ≤ 3 - 2 * c := by linarith
  set s := Real.sqrt (3 - 2 * c) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 3 - 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt h3]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have ht2 : t2 = (-1 + s) / 2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht2]; nlinarith [hs_sq]
  · rw [ht2]; linarith
  · linarith
  · rw [ht2]
    show a2' c = ((-1 + s) / 2) ^ 2
    rw [a2']; nlinarith [hs_sq]

end Workspace.ProofLemmas.RGInteriorRoot
