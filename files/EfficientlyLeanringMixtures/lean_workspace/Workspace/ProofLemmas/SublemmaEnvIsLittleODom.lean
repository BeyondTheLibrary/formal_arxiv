import Mathlib

namespace Workspace.ProofLemmas

open Filter Asymptotics
open scoped Topology

/--
The envelope Gaussian with the smaller variance `v_env` is little-o of the
dominant Gaussian with the larger variance `v_dom`, both at `atTop` and `atBot`.

Proof strategy: write the ratio as `exp(a·x² + b·x + c)` with
`a = 1/(2 v_dom) - 1/(2 v_env) < 0`, which tends to 0 as `|x| → ∞`.
-/
theorem SublemmaEnvIsLittleODom
    (v_env v_dom μ_dom : ℝ) (h_env : 0 < v_env) (h_dom : 0 < v_dom)
    (h_lt : v_env < v_dom) :
    (fun x : ℝ => Real.exp (-x^2 / (2 * v_env))) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v_dom))) ∧
    (fun x : ℝ => Real.exp (-x^2 / (2 * v_env))) =o[Filter.atBot]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v_dom))) := by
  -- Define the quadratic coefficients.
  let a : ℝ := 1 / (2 * v_dom) - 1 / (2 * v_env)
  let b : ℝ := -μ_dom / v_dom
  let c : ℝ := μ_dom^2 / (2 * v_dom)
  have h2env_pos : (0 : ℝ) < 2 * v_env := by positivity
  have h2dom_pos : (0 : ℝ) < 2 * v_dom := by positivity
  have h_lt_2 : 2 * v_env < 2 * v_dom := by linarith
  have ha_neg : a < 0 := by
    have h1 : 1 / (2 * v_dom) < 1 / (2 * v_env) :=
      one_div_lt_one_div_of_lt h2env_pos h_lt_2
    show 1 / (2 * v_dom) - 1 / (2 * v_env) < 0
    linarith
  -- Pointwise identity: ratio = exp(a x² + b x + c).
  have ratio_eq : ∀ x : ℝ,
      Real.exp (-x^2 / (2 * v_env)) / Real.exp (-(x - μ_dom)^2 / (2 * v_dom))
        = Real.exp (a * x^2 + b * x + c) := by
    intro x
    rw [← Real.exp_sub]
    congr 1
    show -x^2 / (2 * v_env) - -(x - μ_dom)^2 / (2 * v_dom)
        = (1 / (2 * v_dom) - 1 / (2 * v_env)) * x^2
            + (-μ_dom / v_dom) * x + μ_dom^2 / (2 * v_dom)
    have hv1 : (2 * v_env) ≠ 0 := ne_of_gt h2env_pos
    have hv2 : (2 * v_dom) ≠ 0 := ne_of_gt h2dom_pos
    have hv_dom : v_dom ≠ 0 := ne_of_gt h_dom
    field_simp
    ring
  -- Helper: the inner quadratic tends to -∞ at atTop.
  have h_atTop : Tendsto (fun x : ℝ => a * x^2 + b * x + c) atTop atBot := by
    have h1 : Tendsto (fun x : ℝ => a * x + b) atTop atBot :=
      (Filter.tendsto_id.const_mul_atTop_of_neg ha_neg).atBot_add tendsto_const_nhds
    have h2 : Tendsto (fun x : ℝ => x * (a * x + b)) atTop atBot :=
      Filter.tendsto_id.atTop_mul_atBot₀ h1
    have h3 : Tendsto (fun x : ℝ => x * (a * x + b) + c) atTop atBot :=
      h2.atBot_add tendsto_const_nhds
    apply h3.congr
    intro x; ring
  -- Helper: the inner quadratic tends to -∞ at atBot.
  have h_atBot : Tendsto (fun x : ℝ => a * x^2 + b * x + c) atBot atBot := by
    have h1 : Tendsto (fun x : ℝ => a * x + b) atBot atTop :=
      (Filter.tendsto_id.const_mul_atBot_of_neg ha_neg).atTop_add tendsto_const_nhds
    have h2 : Tendsto (fun x : ℝ => x * (a * x + b)) atBot atBot :=
      Filter.tendsto_id.atBot_mul_atTop₀ h1
    have h3 : Tendsto (fun x : ℝ => x * (a * x + b) + c) atBot atBot :=
      h2.atBot_add tendsto_const_nhds
    apply h3.congr
    intro x; ring
  -- Compose with exp to get exp(quadratic) → 0.
  have h_exp_atTop : Tendsto (fun x : ℝ => Real.exp (a * x^2 + b * x + c)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_atTop
  have h_exp_atBot : Tendsto (fun x : ℝ => Real.exp (a * x^2 + b * x + c)) atBot (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_atBot
  -- Now use isLittleO_iff_tendsto: ratio → 0.
  refine ⟨?_, ?_⟩
  · -- atTop part.
    have hne : ∀ x : ℝ, Real.exp (-(x - μ_dom)^2 / (2 * v_dom)) = 0 →
        Real.exp (-x^2 / (2 * v_env)) = 0 := fun x hx =>
      absurd hx (ne_of_gt (Real.exp_pos _))
    rw [Asymptotics.isLittleO_iff_tendsto hne]
    refine h_exp_atTop.congr ?_
    intro x
    exact (ratio_eq x).symm
  · -- atBot part.
    have hne : ∀ x : ℝ, Real.exp (-(x - μ_dom)^2 / (2 * v_dom)) = 0 →
        Real.exp (-x^2 / (2 * v_env)) = 0 := fun x hx =>
      absurd hx (ne_of_gt (Real.exp_pos _))
    rw [Asymptotics.isLittleO_iff_tendsto hne]
    refine h_exp_atBot.congr ?_
    intro x
    exact (ratio_eq x).symm

end Workspace.ProofLemmas
