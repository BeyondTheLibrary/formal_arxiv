import Mathlib
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGDefs

open Workspace.ProofLemmas.RGDefs

namespace Workspace.ProofLemmas.RGLambda2InUnitInterval

theorem RGLambda2InUnitInterval (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < lambda2 c ∧ lambda2 c < 1 ∧ 1 < Workspace.RobustnessTheorem.RG c := by
  unfold lambda2 Workspace.RobustnessTheorem.RG
  -- D₂ = −4√(3−2c)·c + 6√(3−2c) + 10c − 8.  We show (1−c)² < D₂, hence 0 < D₂ and
  -- 1−c < √D₂, which yields all three conjuncts.
  set s := Real.sqrt (3 - 2 * c) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 - 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt (by linarith)]
  have hs_ge : (1 : ℝ) ≤ s := by nlinarith [hs2, hs_nonneg]
  set D := -4 * s * c + 6 * s + 10 * c - 8 with hD_def
  have hc1pos : (0 : ℝ) < 1 - c := by linarith
  have hDgt : (1 - c) ^ 2 < D := by
    nlinarith [hs2, hs_nonneg, hs_ge, hc0, hc1, sq_nonneg (s - 1),
      mul_nonneg hs_nonneg hc0]
  have hDpos : 0 < D := lt_trans (by positivity) hDgt
  have hsqrtD : 1 - c < Real.sqrt D := by
    rw [Real.lt_sqrt hc1pos.le]; exact hDgt
  have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · rw [mul_inv_lt_iff₀ hsqrtDpos]; linarith
  · rw [lt_div_iff₀ hc1pos]; linarith

end Workspace.ProofLemmas.RGLambda2InUnitInterval
