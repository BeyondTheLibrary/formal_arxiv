import Mathlib

namespace Workspace.ProofLemmas.LambdaDeltaIdentity

open Real

noncomputable def delta_of_lambda (q lambda : ℝ) : ℝ :=
  (lambda ^ (-(q / (q - 1))) - 1) ^ ((q - 1) / q)

end Workspace.ProofLemmas.LambdaDeltaIdentity

open Workspace.ProofLemmas.LambdaDeltaIdentity

theorem LambdaDeltaIdentity
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam_pos : 0 < lambda) (hlam_le : lambda ≤ 1) :
    lambda * delta_of_lambda q lambda
      = (1 - lambda ^ (q / (q - 1))) ^ ((q - 1) / q) := by
  unfold delta_of_lambda
  -- Set up positivity facts
  set r : ℝ := q / (q - 1) with hr_def
  have hq_sub_pos : 0 < q - 1 := by linarith
  have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hq_sub_pos
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hr_pos : 0 < r := by
    simp [hr_def]; exact div_pos hq_pos hq_sub_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hlam_nn : (0 : ℝ) ≤ lambda := le_of_lt hlam_pos
  have hlam_ne : lambda ≠ 0 := ne_of_gt hlam_pos
  -- lambda^r > 0
  have hlam_r_pos : 0 < lambda ^ r := Real.rpow_pos_of_pos hlam_pos _
  have hlam_r_nn : 0 ≤ lambda ^ r := le_of_lt hlam_r_pos
  have hlam_r_ne : lambda ^ r ≠ 0 := ne_of_gt hlam_r_pos
  -- Rewrite lambda^(-r) - 1 = (1 - lambda^r) / lambda^r
  have h_neg : lambda ^ (-r) = (lambda ^ r)⁻¹ := Real.rpow_neg hlam_nn r
  -- Compute 1 - lambda^r ≥ 0 since lambda ≤ 1 and r > 0
  have h_lam_r_le_one : lambda ^ r ≤ 1 := by
    have : lambda ^ r ≤ lambda ^ (0 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam_le
      linarith
    simpa using this
  have h_one_sub_nn : 0 ≤ 1 - lambda ^ r := by linarith
  -- Substitute lambda^(-r) = (lambda^r)⁻¹
  rw [h_neg]
  -- Now: lambda * ((lambda^r)⁻¹ - 1)^((q-1)/q) = (1 - lambda^r)^((q-1)/q)
  have h_step1 : (lambda ^ r)⁻¹ - 1 = (1 - lambda ^ r) / (lambda ^ r) := by
    field_simp
  rw [h_step1]
  -- Goal: lambda * ((1 - lambda^r) / lambda^r)^((q-1)/q) = (1 - lambda^r)^((q-1)/q)
  rw [Real.div_rpow h_one_sub_nn hlam_r_nn]
  -- Goal: lambda * ((1 - lambda^r)^((q-1)/q) / (lambda^r)^((q-1)/q)) = ...
  -- We want to show (lambda^r)^((q-1)/q) = lambda
  have h_inner : (lambda ^ r) ^ ((q - 1) / q) = lambda := by
    rw [← Real.rpow_mul hlam_nn]
    have h_prod : r * ((q - 1) / q) = 1 := by
      simp [hr_def]
      field_simp
    rw [h_prod, Real.rpow_one]
  rw [h_inner]
  -- Goal: lambda * ((1 - lambda^r)^((q-1)/q) / lambda) = (1 - lambda^r)^((q-1)/q)
  field_simp
