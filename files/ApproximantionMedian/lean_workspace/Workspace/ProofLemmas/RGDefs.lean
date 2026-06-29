import Mathlib
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.ZeqInHalfRange
import Workspace.ProofLemmas.CGDefs

open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.ZeqInHalfRange
open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.RGDefs

/-!
# Robustness-specific constants for Theorem 4 (CMP(c))

These are the genuinely new objects of the robustness proof
(`appendix.tex` 257–311), all at the fixed exponent `q = 2` (Euclidean L₂).
They are the exact `c → −c` images of the consistency constants of
`Workspace.ProofLemmas.CGDefs`.

We follow appendix.tex exactly:

* `a2' c = (2 − c − √(3−2c))/2`        (the interior critical point `a₂'`, line 294)
* `a2  c = a2' c`  for ALL `c ∈ [0,1)`  (the *single-branch* optimum `a₂`, line 294)
* `lambda2 c`                           (the optimal `λ₂` closed form, line 310)
* `delta2 c  = δ(λ₂) = (λ₂⁻² − 1)^{1/2}`  (the `δ₂`)
* `u2 c a    = (1−c)(δ₂(1−a)^{1/2} − a^{1/2}) − 1 + 2a − c`  (the objective, line 257)

Unlike consistency's two-branch `a1`, the robustness `a2` is single-branch:
`a₂' ≤ (1+c)/2` on the whole interval `c ∈ [0,1)`, so the boundary never binds.

The closed form for `λ₂` mirrors `Workspace.RobustnessTheorem.RG c = 1/λ₂`.
-/

/-- Interior critical point `a₂' = (2 − c − √(3−2c))/2` (appendix 294). -/
noncomputable def a2' (c : ℝ) : ℝ := (2 - c - Real.sqrt (3 - 2 * c)) / 2

/-- The optimal `a₂`. SINGLE BRANCH: `a₂ = a₂'` for ALL `c ∈ [0,1)` (unlike the
two-branch `a1`), because `a₂' ≤ (1+c)/2` on the whole interval (appendix 294). -/
noncomputable def a2 (c : ℝ) : ℝ := a2' c

/-- Optimal `λ₂` closed form (single branch, appendix 310):
`λ₂ = (1−c)·(−4√(3−2c)·c + 6√(3−2c) + 10c − 8)^{-1/2}`. By construction `RG c = 1/λ₂`. -/
noncomputable def lambda2 (c : ℝ) : ℝ :=
  (1 - c) * (Real.sqrt (-4 * Real.sqrt (3 - 2 * c) * c + 6 * Real.sqrt (3 - 2 * c) + 10 * c - 8))⁻¹

/-- `δ₂ = δ(λ₂) = (λ₂^{-2} − 1)^{1/2}` — the `q=2` instance of `delta_of_lambda` at `λ₂`. -/
noncomputable def delta2 (c : ℝ) : ℝ := delta_of_lambda 2 (lambda2 c)

/-- Per-capita objective `u₂(a) = (1−c)(δ₂(1−a)^{1/2} − a^{1/2}) − 1 + 2a − c` (appendix 257). -/
noncomputable def u2 (c a : ℝ) : ℝ :=
  (1 - c) * (delta2 c * (1 - a) ^ ((1 : ℝ) / 2) - a ^ ((1 : ℝ) / 2)) - 1 + 2 * a - c

/-- `u₂` with explicit `δ`. -/
noncomputable def u2delta (c delta a : ℝ) : ℝ :=
  (1 - c) * (delta * (1 - a) ^ ((1 : ℝ) / 2) - a ^ ((1 : ℝ) / 2)) - 1 + 2 * a - c

/-- `u₂'(a) = ½(1−c)(−δ(1−a)^{-1/2} − a^{-1/2}) + 2` (c→−c image of `u1deriv`). -/
noncomputable def u2deriv (c delta a : ℝ) : ℝ :=
  (1 / 2) * (1 - c) * (-delta * (1 - a) ^ (-(1 : ℝ) / 2) - a ^ (-(1 : ℝ) / 2)) + 2

end Workspace.ProofLemmas.RGDefs

open Workspace.ProofLemmas.RGDefs

/-- `RG c = 1 / λ₂` (single branch, appendix 310). -/
theorem RG_eq_inv_lambda2 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Workspace.RobustnessTheorem.RG c = 1 / lambda2 c := by
  unfold Workspace.RobustnessTheorem.RG lambda2
  set s := Real.sqrt (3 - 2 * c) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 - 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt (by linarith)]
  have hs_ge : (1 : ℝ) ≤ s := by nlinarith [hs2, hs_nonneg]
  set D := -4 * s * c + 6 * s + 10 * c - 8 with hD_def
  have hc1pos : (0 : ℝ) < 1 - c := by linarith
  have hDpos : 0 < D := by
    nlinarith [hs2, hs_nonneg, hs_ge, hc0, hc1, sq_nonneg (s - 1), mul_nonneg hs_nonneg hc0]
  have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  rw [one_div, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
