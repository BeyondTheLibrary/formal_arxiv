import Mathlib
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.ZeqInHalfRange

open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.ZeqInHalfRange

namespace Workspace.ProofLemmas.CGDefs

/-!
# Consistency-specific constants for Theorem 3 (CMP(c))

These are the genuinely new objects of the consistency proof (proof_nlp.md §3–§5,
`appendix.tex` 116–225), all at the fixed exponent `q = 2` (Euclidean L₂).

We follow proof_nlp.md exactly:

* `a1' c = (2 + c − √(3+2c))/2`         (the interior critical point `a₁'`, §5.1)
* `a1  c = a1' c` if `c < 1/2`, else `(1-c)/2`   (the branched optimum `a₁`, §5.2)
* `lambda1 c`                            (the optimal `λ₁` closed form, §5.3/§5.4)
* `delta1 c  = δ(λ₁) = (λ₁⁻² − 1)^{1/2}`  (the `δ₁`, §2.1)
* `u1 c a    = (1+c)(δ₁(1−a)^{1/2} − a^{1/2}) − 1 + 2a + c`  (the objective, §2.4)

The closed form for `λ₁` mirrors `Workspace.ConsistencyTheorem.CG c = 1/λ₁`.
-/

/-- The interior critical point `a₁' = (2 + c − √(3+2c))/2` (proof_nlp.md §5.1). -/
noncomputable def a1' (c : ℝ) : ℝ :=
  (2 + c - Real.sqrt (3 + 2 * c)) / 2

/-- The branched optimal `a₁`: the interior root `a₁'` on `c < 1/2`, the
constraint boundary `(1-c)/2` on `c ≥ 1/2` (proof_nlp.md §5.2). -/
noncomputable def a1 (c : ℝ) : ℝ :=
  if c < 1 / 2 then a1' c else (1 - c) / 2

/-- The optimal constant `λ₁` in closed form (proof_nlp.md §5.3, §5.4):

* `c < 1/2`:  `λ₁ = (c+1)·(4√(2c+3)·c + 6√(2c+3) − 10c − 8)^{-1/2}`
* `c ≥ 1/2`:  `λ₁ = √((c+1)/2)`

By construction `CG c = 1/λ₁` (see `CG_eq_inv_lambda1`). -/
noncomputable def lambda1 (c : ℝ) : ℝ :=
  if c < 1 / 2 then
    (c + 1) *
      (Real.sqrt (4 * Real.sqrt (2 * c + 3) * c + 6 * Real.sqrt (2 * c + 3) - 10 * c - 8))⁻¹
  else
    Real.sqrt ((c + 1) / 2)

/-- The associated `δ₁ = δ(λ₁) = (λ₁^{-2} − 1)^{1/2}`, i.e. the `q = 2` instance
of `delta_of_lambda` at `λ = λ₁` (proof_nlp.md §2.1). -/
noncomputable def delta1 (c : ℝ) : ℝ :=
  delta_of_lambda 2 (lambda1 c)

/-- The per-capita objective `u₁(a)` of proof_nlp.md §2.4:
`u₁(a) = (1+c)·(δ₁·(1−a)^{1/2} − a^{1/2}) − 1 + 2a + c`,
where `δ₁ = delta1 c` is the `δ` of the chosen `λ₁`. -/
noncomputable def u1 (c a : ℝ) : ℝ :=
  (1 + c) * (delta1 c * (1 - a) ^ ((1 : ℝ) / 2) - a ^ ((1 : ℝ) / 2)) - 1 + 2 * a + c

/-- `u₁(a)` with an *explicit* `δ`, for sub-lemmas that pin `δ` separately
(e.g. `CGOneParamReduction`, `CGOptimalSolutionForA1`). -/
noncomputable def u1delta (c delta a : ℝ) : ℝ :=
  (1 + c) * (delta * (1 - a) ^ ((1 : ℝ) / 2) - a ^ ((1 : ℝ) / 2)) - 1 + 2 * a + c

/-- The derivative `u₁'(a) = ½(1+c)(−δ(1−a)^{-1/2} − a^{-1/2}) + 2`
(proof_nlp.md §3, appendix line 121; with the corrected `−δ` sign). -/
noncomputable def u1deriv (c delta a : ℝ) : ℝ :=
  (1 / 2) * (1 + c) *
    (-delta * (1 - a) ^ (-(1 : ℝ) / 2) - a ^ (-(1 : ℝ) / 2)) + 2

/-- The inflection point `z = δ^{-2/3}/(δ^{-2/3}+1)`, the `q = 2` instance of
`z_func` (sign-change of `h''`). -/
noncomputable def zCG (delta : ℝ) : ℝ :=
  delta ^ (-(2 : ℝ) / 3) / (delta ^ (-(2 : ℝ) / 3) + 1)

end Workspace.ProofLemmas.CGDefs

open Workspace.ProofLemmas.CGDefs

/-- The relation pinning the closed form to `CG`: `CG c = 1 / λ₁`.
For `c < 1/2`, `1/λ₁ = √(4√(2c+3)c + 6√(2c+3) − 10c − 8)/(c+1)`; for `c ≥ 1/2`,
`1/λ₁ = √(2/(c+1))`. (proof_nlp.md §6.) -/
theorem CG_eq_inv_lambda1 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Workspace.ConsistencyTheorem.CG c = 1 / lambda1 c := by
  unfold lambda1 Workspace.ConsistencyTheorem.CG
  by_cases hcase : c < 1 / 2
  · rw [if_pos hcase, if_pos hcase]
    set D := 4 * Real.sqrt (2 * c + 3) * c + 6 * Real.sqrt (2 * c + 3) - 10 * c - 8 with hD_def
    have hDpos : 0 < D := by
      have hs_nonneg : 0 ≤ Real.sqrt (2 * c + 3) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (2 * c + 3)) ^ 2 = 2 * c + 3 := by
        rw [sq, Real.mul_self_sqrt (by linarith)]
      have hs_ge : (1 : ℝ) ≤ Real.sqrt (2 * c + 3) := by nlinarith [hs2, hs_nonneg]
      rw [hD_def]
      nlinarith [hs2, hs_nonneg, hs_ge, hc0, hcase, sq_nonneg (Real.sqrt (2 * c + 3) - 1),
        mul_nonneg hs_nonneg hc0]
    have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
    have hc1pos : (0 : ℝ) < c + 1 := by linarith
    field_simp
  · rw [if_neg hcase, if_neg hcase]
    have hc1pos : (0 : ℝ) < c + 1 := by linarith
    have hhalf_pos : (0 : ℝ) < (c + 1) / 2 := by linarith
    have hsqrt_pos : 0 < Real.sqrt ((c + 1) / 2) := Real.sqrt_pos.mpr hhalf_pos
    rw [eq_div_iff (ne_of_gt hsqrt_pos)]
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 / (c + 1)) * ((c + 1) / 2) = 1 by field_simp]
    exact Real.sqrt_one
