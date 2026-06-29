import Mathlib
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.DeltaStarAsymptotic

open Workspace.ProofLemmas.LambdaStarDef
open Workspace.ProofLemmas.DeltaStarDef

theorem LambdaStarAsymptotic :
    Filter.Tendsto lambda_star Filter.atTop (nhds ((1:ℝ)/3)) := by
  -- Step 1: q/(q-1) → 1 as q → ∞.
  -- We have q/(q-1) = 1 + 1/(q-1).
  have h_tendsto_id : Filter.Tendsto (fun q : ℝ => q) Filter.atTop Filter.atTop :=
    Filter.tendsto_id
  have h_tendsto_qm1_atTop : Filter.Tendsto (fun q : ℝ => q - 1) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) h_tendsto_id
  have h_tendsto_inv_qm1 : Filter.Tendsto (fun q : ℝ => (q - 1)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    Filter.Tendsto.comp tendsto_inv_atTop_zero h_tendsto_qm1_atTop
  -- q/(q-1) = 1 + 1/(q-1) for q ≠ 1
  have h_q_div_qm1 : Filter.Tendsto (fun q : ℝ => q / (q - 1)) Filter.atTop (nhds (1 : ℝ)) := by
    have : Filter.Tendsto (fun q : ℝ => 1 + (q - 1)⁻¹) Filter.atTop (nhds ((1 : ℝ) + 0)) :=
      Filter.Tendsto.const_add 1 h_tendsto_inv_qm1
    have h_eq : ∀ᶠ q : ℝ in Filter.atTop, 1 + (q - 1)⁻¹ = q / (q - 1) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with q hq
      have hqm1_ne : q - 1 ≠ 0 := by
        intro h
        have : q = 1 := by linarith
        linarith
      field_simp
      ring
    have h1 : Filter.Tendsto (fun q : ℝ => 1 + (q - 1)⁻¹) Filter.atTop (nhds (1 : ℝ)) := by
      simpa using this
    exact h1.congr' h_eq
  -- Step 2: (q-1)/q → 1, so -((q-1)/q) → -1.
  have h_inv_q : Filter.Tendsto (fun q : ℝ => q⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have h_qm1_div_q : Filter.Tendsto (fun q : ℝ => (q - 1) / q) Filter.atTop (nhds (1 : ℝ)) := by
    have h0 : Filter.Tendsto (fun q : ℝ => 1 - q⁻¹) Filter.atTop (nhds ((1 : ℝ) - 0)) :=
      Filter.Tendsto.const_sub 1 h_inv_q
    have h_eq : ∀ᶠ q : ℝ in Filter.atTop, 1 - q⁻¹ = (q - 1) / q := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with q hq
      have hq_ne : q ≠ 0 := ne_of_gt hq
      field_simp
    have h1 : Filter.Tendsto (fun q : ℝ => 1 - q⁻¹) Filter.atTop (nhds (1 : ℝ)) := by
      simpa using h0
    exact h1.congr' h_eq
  have h_neg_qm1_div_q : Filter.Tendsto (fun q : ℝ => -((q - 1) / q)) Filter.atTop (nhds (-1 : ℝ)) := by
    have := h_qm1_div_q.neg
    simpa using this
  -- Step 3: delta_star q → 2.
  have h_delta : Filter.Tendsto delta_star Filter.atTop (nhds (2 : ℝ)) := DeltaStarAsymptotic
  -- Step 4: (delta_star q)^(q/(q-1)) → 2^1 = 2.
  have h_dpow : Filter.Tendsto (fun q : ℝ => (delta_star q) ^ (q / (q - 1))) Filter.atTop
      (nhds ((2 : ℝ) ^ (1 : ℝ))) :=
    h_delta.rpow h_q_div_qm1 (Or.inl (by norm_num : (2 : ℝ) ≠ 0))
  have h_two_pow_one : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
  have h_dpow' : Filter.Tendsto (fun q : ℝ => (delta_star q) ^ (q / (q - 1))) Filter.atTop
      (nhds (2 : ℝ)) := by
    rw [← h_two_pow_one]; exact h_dpow
  -- Step 5: 1 + (delta_star q)^(q/(q-1)) → 3.
  have h_sum : Filter.Tendsto (fun q : ℝ => 1 + (delta_star q) ^ (q / (q - 1))) Filter.atTop
      (nhds ((1 : ℝ) + 2)) :=
    Filter.Tendsto.const_add 1 h_dpow'
  have h_sum' : Filter.Tendsto (fun q : ℝ => 1 + (delta_star q) ^ (q / (q - 1))) Filter.atTop
      (nhds (3 : ℝ)) := by
    have : (1 : ℝ) + 2 = 3 := by norm_num
    rw [← this]; exact h_sum
  -- Step 6: (1 + ...)^(-((q-1)/q)) → 3^(-1).
  have h_full : Filter.Tendsto
      (fun q : ℝ => (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)))
      Filter.atTop (nhds ((3 : ℝ) ^ (-1 : ℝ))) :=
    h_sum'.rpow h_neg_qm1_div_q (Or.inl (by norm_num : (3 : ℝ) ≠ 0))
  have h_three_inv : (3 : ℝ) ^ (-1 : ℝ) = 1/3 := by
    rw [Real.rpow_neg_one]
    norm_num
  have h_full' : Filter.Tendsto
      (fun q : ℝ => (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)))
      Filter.atTop (nhds ((1 : ℝ)/3)) := by
    rw [← h_three_inv]; exact h_full
  -- Step 7: lambda_star q = (1 + ...)^(-((q-1)/q)) eventually.
  have h_eq : ∀ᶠ q : ℝ in Filter.atTop, lambda_star q =
      (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with q hq
    have hq_ne1 : q ≠ 1 := ne_of_gt hq
    unfold lambda_star
    rw [if_neg hq_ne1, if_pos hq]
  exact h_full'.congr' (Filter.EventuallyEq.symm h_eq)
