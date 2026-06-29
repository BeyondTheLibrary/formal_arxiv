import Mathlib
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.CGDeltaLambdaLowBranch
import Workspace.ProofLemmas.CGDeltaLambdaHighBranch

open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.CGLambda1InUnitInterval

/-- **CGLambda1InUnitInterval** (prediction.tex 89–95; proof_nlp.md §5.5).
For every `c ∈ [0,1)`, the constant `λ₁ = lambda1 c` given by the two-branch
closed form satisfies `0 < λ₁ ∧ λ₁ < 1`; equivalently `CG c = 1/λ₁ > 1`.

* For `c < 1/2`: `4√(2c+3)c + 6√(2c+3) − 10c − 8 > (c+1)² > 0` (e.g. at `c = 0`,
  `6√3 − 8 > 1`, the `SixSqrtThreeMinusEightPos`-style bound), so `λ₁ < 1`.
* For `c ≥ 1/2`: `λ₁ = √((c+1)/2)` with `(c+1)/2 > 0` and `(c+1)/2 < 1 ⟺ c < 1`.

We state both `0 < λ₁ < 1` and `1 < CG c`. -/
theorem CGLambda1InUnitInterval (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < lambda1 c ∧ lambda1 c < 1 ∧ 1 < Workspace.ConsistencyTheorem.CG c := by
  unfold lambda1 Workspace.ConsistencyTheorem.CG
  by_cases hcase : c < 1 / 2
  · -- Low branch c ∈ [0, 1/2): λ₁ = (c+1)·(√D)⁻¹, CG = √D/(c+1), with
    -- D = 4√(2c+3)·c + 6√(2c+3) − 10c − 8.  We show (c+1)² < D, hence 0 < D and
    -- c+1 < √D, which yields all three conjuncts.
    rw [if_pos hcase, if_pos hcase]
    set s := Real.sqrt (2 * c + 3) with hs_def
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 2 * c + 3 := by rw [hs_def, sq, Real.mul_self_sqrt (by linarith)]
    have hs_ge : (1 : ℝ) ≤ s := by nlinarith [hs2, hs_nonneg]
    set D := 4 * s * c + 6 * s - 10 * c - 8 with hD_def
    have hc1pos : (0 : ℝ) < c + 1 := by linarith
    have hDgt : (c + 1) ^ 2 < D := by
      nlinarith [hs2, hs_nonneg, hs_ge, hc0, hcase, sq_nonneg (s - 1),
        mul_nonneg hs_nonneg hc0]
    have hDpos : 0 < D := lt_trans (by positivity) hDgt
    have hsqrtD : c + 1 < Real.sqrt D := by
      rw [Real.lt_sqrt hc1pos.le]; exact hDgt
    have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
    refine ⟨?_, ?_, ?_⟩
    · positivity
    · rw [mul_inv_lt_iff₀ hsqrtDpos]; linarith
    · rw [lt_div_iff₀ hc1pos]; linarith
  · -- High branch c ∈ [1/2, 1): λ₁ = √((c+1)/2), CG = √(2/(c+1)).
    rw [if_neg hcase, if_neg hcase]
    have hpos : (0 : ℝ) < (c + 1) / 2 := by linarith
    refine ⟨Real.sqrt_pos.mpr hpos, ?_, ?_⟩
    · rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]; nlinarith
    · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1),
        lt_div_iff₀ (by linarith : (0 : ℝ) < c + 1)]
      linarith

end Workspace.ProofLemmas.CGLambda1InUnitInterval
