import Mathlib
import Workspace.Types.GaussianPDF

namespace Workspace.ProofLemmas

open Real

/-- Key inequality: `u · exp(-u²/2) ≤ 1` for all real `u ≥ 0`. -/
private lemma key_bound_simple (u : ℝ) (hu : 0 ≤ u) : u * Real.exp (-(u^2 / 2)) ≤ 1 := by
  have h1 : 1 + u^2 / 2 ≤ Real.exp (u^2 / 2) := by
    have := Real.add_one_le_exp (u^2 / 2)
    linarith
  have h2 : 0 < Real.exp (u^2 / 2) := Real.exp_pos _
  have h4 : u ≤ 1 + u^2 / 2 := by nlinarith [sq_nonneg (u - 1)]
  have hexp_neg : Real.exp (-(u^2 / 2)) = 1 / Real.exp (u^2 / 2) := by
    rw [Real.exp_neg, one_div]
  rw [hexp_neg, mul_one_div, div_le_one h2]
  exact le_trans h4 h1

/-- For any `V > 0`, `|y| · exp(-y²/(2V)) ≤ √V`. -/
private lemma key_bound_general (y V : ℝ) (hV : 0 < V) :
    |y| * Real.exp (-(y^2 / (2 * V))) ≤ Real.sqrt V := by
  set σ := Real.sqrt V with hσ_def
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hV
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
  have hσ_sq : σ^2 = V := Real.sq_sqrt hV.le
  -- Rewrite the exp argument: y²/(2V) = (|y|/σ)²/2
  have h_eq : y^2 / (2 * V) = (|y| / σ)^2 / 2 := by
    rw [div_pow, sq_abs, hσ_sq]; ring
  -- Rewrite LHS as ((|y|/σ) * exp(...)) * σ
  have h_lhs : |y| * Real.exp (-(y^2 / (2 * V)))
             = ((|y| / σ) * Real.exp (-((|y| / σ)^2 / 2))) * σ := by
    rw [h_eq]
    field_simp
  rw [h_lhs]
  have key := key_bound_simple (|y| / σ) (by positivity)
  calc ((|y| / σ) * Real.exp (-((|y| / σ) ^ 2 / 2))) * σ
      ≤ 1 * σ := mul_le_mul_of_nonneg_right key hσ_pos.le
    _ = σ := one_mul σ

theorem GaussianDensityDerivBound
    (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Differentiable ℝ G.density
    ∧ ∀ x : ℝ, |deriv G.density x| ≤ 1 / G.varSq := by
  set V := G.varSq with hV_def
  set μ := G.mean with hμ_def
  have hV_pos : 0 < V := G.varSq_pos
  have h2V_pos : 0 < 2 * V := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have h2piV_pos : 0 < 2 * Real.pi * V := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * V) := Real.sqrt_pos.mpr h2piV_pos
  have hsqrtV_pos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV_pos
  have h2pi_ge_one : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  -- Differentiability
  have h_inner_diff : Differentiable ℝ (fun x : ℝ => -(x - μ)^2 / (2 * V)) := by
    apply Differentiable.div_const
    exact (((differentiable_id.sub_const μ).pow 2).neg)
  have h_exp_diff : Differentiable ℝ (fun x : ℝ => Real.exp (-(x - μ)^2 / (2 * V))) :=
    Real.differentiable_exp.comp h_inner_diff
  have h_diff : Differentiable ℝ G.density := by
    show Differentiable ℝ (fun x =>
      (1 / Real.sqrt (2 * Real.pi * V)) * Real.exp (-(x - μ)^2 / (2 * V)))
    exact h_exp_diff.const_mul _
  refine ⟨h_diff, ?_⟩
  intro x
  -- Compute derivative via HasDerivAt
  have h_sq_deriv : HasDerivAt (fun x : ℝ => (x - μ)^2) (2 * (x - μ)) x := by
    simpa using ((hasDerivAt_id x).sub_const μ).pow 2
  have h_inner_deriv : HasDerivAt (fun x : ℝ => -(x - μ)^2 / (2 * V))
      (-(2 * (x - μ)) / (2 * V)) x :=
    (h_sq_deriv.neg).div_const (2 * V)
  have h_exp_deriv : HasDerivAt (fun x : ℝ => Real.exp (-(x - μ)^2 / (2 * V)))
      (Real.exp (-(x - μ)^2 / (2 * V)) * (-(2 * (x - μ)) / (2 * V))) x :=
    h_inner_deriv.exp
  have h_dens_deriv : HasDerivAt G.density
      ((1 / Real.sqrt (2 * Real.pi * V)) *
        (Real.exp (-(x - μ)^2 / (2 * V)) * (-(2 * (x - μ)) / (2 * V)))) x := by
    show HasDerivAt (fun x =>
      (1 / Real.sqrt (2 * Real.pi * V)) * Real.exp (-(x - μ)^2 / (2 * V))) _ x
    exact h_exp_deriv.const_mul _
  rw [h_dens_deriv.deriv]
  set y := x - μ with hy_def
  -- Algebraic manipulation
  have h_simp : (1 / Real.sqrt (2 * Real.pi * V)) *
      (Real.exp (-y^2 / (2 * V)) * (-(2 * y) / (2 * V))) =
      -((1 / Real.sqrt (2 * Real.pi * V)) * Real.exp (-y^2 / (2 * V)) * (y / V)) := by
    have h2V_ne : (2 : ℝ) * V ≠ 0 := ne_of_gt h2V_pos
    have hV_ne : V ≠ 0 := ne_of_gt hV_pos
    have hsqrt_ne : Real.sqrt (2 * Real.pi * V) ≠ 0 := ne_of_gt hsqrt_pos
    field_simp
  rw [h_simp, abs_neg]
  rw [show -y^2 / (2*V) = -(y^2 / (2*V)) by ring]
  have h_exp_pos : 0 < Real.exp (-(y^2 / (2 * V))) := Real.exp_pos _
  have h_inv_sqrt_pos : 0 < 1 / Real.sqrt (2 * Real.pi * V) := by positivity
  rw [abs_mul, abs_mul, abs_of_pos h_inv_sqrt_pos, abs_of_pos h_exp_pos,
      abs_div, abs_of_pos hV_pos]
  have key := key_bound_general y V hV_pos
  have hsqrt_factor : Real.sqrt (2 * Real.pi * V) = Real.sqrt (2 * Real.pi) * Real.sqrt V := by
    rw [← Real.sqrt_mul h2pi_pos.le]
  have hsqrt_2pi_ge : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt h2pi_ge_one
  have key2 : |y| * Real.exp (-(y^2 / (2*V))) ≤ Real.sqrt (2 * Real.pi * V) := by
    calc |y| * Real.exp (-(y^2 / (2*V)))
        ≤ Real.sqrt V := key
      _ = 1 * Real.sqrt V := (one_mul _).symm
      _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt V :=
          mul_le_mul_of_nonneg_right hsqrt_2pi_ge hsqrtV_pos.le
      _ = Real.sqrt (2 * Real.pi * V) := hsqrt_factor.symm
  -- Now turn the goal into (|y|*exp) / (V*√(2πV)) ≤ 1/V
  have h_rearrange : (1 / Real.sqrt (2 * Real.pi * V)) * Real.exp (-(y^2 / (2*V))) * (|y|/V)
        = (|y| * Real.exp (-(y^2/(2*V)))) / (V * Real.sqrt (2 * Real.pi * V)) := by
    have hV_ne : V ≠ 0 := ne_of_gt hV_pos
    have hsqrt_ne : Real.sqrt (2 * Real.pi * V) ≠ 0 := ne_of_gt hsqrt_pos
    field_simp
  rw [h_rearrange]
  rw [div_le_div_iff₀ (by positivity) hV_pos]
  -- Goal: |y| * exp(-(y²/(2V))) * V ≤ 1 * (V * √(2πV))
  have hVsqrt_pos : 0 ≤ V * Real.sqrt (2 * Real.pi * V) := by positivity
  have key3 : |y| * Real.exp (-(y^2 / (2*V))) * V ≤ Real.sqrt (2 * Real.pi * V) * V :=
    mul_le_mul_of_nonneg_right key2 hV_pos.le
  linarith [key3]

end Workspace.ProofLemmas
