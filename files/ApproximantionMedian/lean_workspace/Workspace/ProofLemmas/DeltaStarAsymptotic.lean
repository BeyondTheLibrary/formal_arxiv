import Mathlib
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.AStarAsymptotic
import Workspace.ProofLemmas.AStarLessThanOneHalf
import Workspace.ProofLemmas.FqHasUniqueInteriorZero

open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.FqHasUniqueInteriorZero

theorem DeltaStarAsymptotic :
    Filter.Tendsto delta_star Filter.atTop (nhds (2 : ℝ)) := by
  -- Step 0: q * a_star q → 1/2.
  have hq_astar : Filter.Tendsto (fun q : ℝ => q * a_star q) Filter.atTop (nhds ((1:ℝ)/2)) :=
    AStarAsymptotic

  -- Step 1: 1/q → 0 (and q⁻¹ → 0).
  have h_inv_q : Filter.Tendsto (fun q : ℝ => q⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have h_one_div_q : Filter.Tendsto (fun q : ℝ => (1 : ℝ) / q) Filter.atTop (nhds (0 : ℝ)) := by
    have h1 : (fun q : ℝ => (1 : ℝ) / q) = (fun q : ℝ => q⁻¹) := by
      funext q; rw [one_div]
    rw [h1]; exact h_inv_q

  -- Step 2: a_star q → 0.
  have h_astar_zero : Filter.Tendsto (fun q : ℝ => a_star q) Filter.atTop (nhds (0 : ℝ)) := by
    have h_prod : Filter.Tendsto (fun q : ℝ => (q * a_star q) * q⁻¹) Filter.atTop
        (nhds (((1:ℝ)/2) * 0)) := hq_astar.mul h_inv_q
    have h_target : ((1:ℝ)/2) * (0 : ℝ) = 0 := by ring
    rw [h_target] at h_prod
    have h_eq : ∀ᶠ q : ℝ in Filter.atTop, (q * a_star q) * q⁻¹ = a_star q := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with q hq
      have hq_ne : q ≠ 0 := ne_of_gt hq
      field_simp
    exact h_prod.congr' h_eq

  -- Step 3: 1 - a_star q → 1.
  have h_one_minus : Filter.Tendsto (fun q : ℝ => 1 - a_star q) Filter.atTop (nhds (1 : ℝ)) := by
    have h := Filter.Tendsto.const_sub (1:ℝ) h_astar_zero
    simpa using h

  -- Step 4: (1 - a_star q)^(1/q) → 1.
  have h_denom_aux : Filter.Tendsto (fun q : ℝ => (1 - a_star q) ^ ((1:ℝ)/q)) Filter.atTop
      (nhds ((1:ℝ) ^ (0:ℝ))) :=
    h_one_minus.rpow h_one_div_q (Or.inl one_ne_zero)
  have h_denom : Filter.Tendsto (fun q : ℝ => (1 - a_star q) ^ ((1:ℝ)/q)) Filter.atTop
      (nhds (1 : ℝ)) := by
    have h_pow : (1:ℝ) ^ (0:ℝ) = 1 := Real.rpow_zero 1
    rw [h_pow] at h_denom_aux
    exact h_denom_aux

  -- Step 5: (a_star q)^(1/q) → 1.
  have h_log_id : Real.log =o[Filter.atTop] (id : ℝ → ℝ) := Real.isLittleO_log_id_atTop
  have h_log_div : Filter.Tendsto (fun q : ℝ => Real.log q / q) Filter.atTop (nhds 0) := by
    have h := h_log_id.tendsto_div_nhds_zero
    simpa [Function.id_def] using h

  have h_evt_q_gt_one : ∀ᶠ q : ℝ in Filter.atTop, 1 < q := Filter.eventually_gt_atTop 1
  have h_qastar_gt : ∀ᶠ q : ℝ in Filter.atTop, (1:ℝ)/4 < q * a_star q := by
    have : ∀ᶠ x in nhds ((1:ℝ)/2), (1:ℝ)/4 < x := eventually_gt_nhds (by norm_num : (1:ℝ)/4 < 1/2)
    exact hq_astar.eventually this
  have h_qastar_lt : ∀ᶠ q : ℝ in Filter.atTop, q * a_star q < (1:ℝ) := by
    have : ∀ᶠ x in nhds ((1:ℝ)/2), x < (1:ℝ) := eventually_lt_nhds (by norm_num : (1:ℝ)/2 < 1)
    exact hq_astar.eventually this

  have h_evt_main : ∀ᶠ q : ℝ in Filter.atTop,
      0 < a_star q ∧ a_star q < 1/q ∧ 1/(4*q) < a_star q ∧ 1 < q := by
    filter_upwards [h_evt_q_gt_one, h_qastar_gt, h_qastar_lt] with q hq hgt hlt
    have hq_pos : 0 < q := lt_trans zero_lt_one hq
    have h_astar_lt_half := AStarLessThanOneHalf q hq
    have ha_pos : 0 < a_star q := h_astar_lt_half.1
    have ha_lt_inv_q : a_star q < 1/q := by
      rw [lt_div_iff₀ hq_pos]
      linarith [hlt]
    have ha_gt_qtr : 1/(4*q) < a_star q := by
      have h4q_pos : 0 < 4 * q := by linarith
      rw [div_lt_iff₀ h4q_pos]
      nlinarith [hgt, hq_pos, ha_pos]
    exact ⟨ha_pos, ha_lt_inv_q, ha_gt_qtr, hq⟩

  -- Show g(q) := (1/q) * log(a_star q) → 0.
  have h_log_div_g : Filter.Tendsto (fun q : ℝ => (1/q) * Real.log (a_star q)) Filter.atTop
      (nhds (0 : ℝ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h3 : 0 < ε / 3 := by linarith
    rw [Metric.tendsto_atTop] at h_log_div
    obtain ⟨N1, hN1⟩ := h_log_div (ε / 3) h3
    have h_const_div_q : Filter.Tendsto (fun q : ℝ => Real.log 4 / q) Filter.atTop (nhds (0:ℝ)) := by
      have hh : Filter.Tendsto (fun q : ℝ => Real.log 4 * q⁻¹) Filter.atTop
          (nhds (Real.log 4 * 0)) := h_inv_q.const_mul (Real.log 4)
      have ht : Real.log 4 * (0 : ℝ) = 0 := by ring
      rw [ht] at hh
      have h_eq : (fun q : ℝ => Real.log 4 * q⁻¹) = (fun q : ℝ => Real.log 4 / q) := by
        funext q; rw [div_eq_mul_inv]
      rw [h_eq] at hh
      exact hh
    rw [Metric.tendsto_atTop] at h_const_div_q
    obtain ⟨N2, hN2⟩ := h_const_div_q (ε / 3) h3
    rw [Filter.eventually_atTop] at h_evt_main
    obtain ⟨N3, hN3⟩ := h_evt_main
    refine ⟨max (max N1 N2) N3, ?_⟩
    intro q hq_ge
    have hq_ge_N1 : q ≥ N1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq_ge
    have hq_ge_N2 : q ≥ N2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq_ge
    have hq_ge_N3 : q ≥ N3 := le_trans (le_max_right _ _) hq_ge
    have h_log_div_close := hN1 q hq_ge_N1
    have h_const_close := hN2 q hq_ge_N2
    obtain ⟨ha_pos, ha_lt_inv_q, ha_gt_qtr, hq_gt_one⟩ := hN3 q hq_ge_N3
    have hq_pos : 0 < q := lt_trans zero_lt_one hq_gt_one
    have hq_inv_pos : 0 < 1/q := by positivity
    have h_log_upper : Real.log (a_star q) < -Real.log q := by
      have h_log_lt : Real.log (a_star q) < Real.log (1/q) :=
        Real.log_lt_log ha_pos ha_lt_inv_q
      have h_log_inv : Real.log (1/q) = -Real.log q := by
        rw [Real.log_div one_ne_zero (ne_of_gt hq_pos), Real.log_one]
        ring
      linarith
    have h_log_lower : Real.log (a_star q) > -(Real.log 4 + Real.log q) := by
      have h4q_pos : (0:ℝ) < 4 * q := by linarith
      have h_log_lt : Real.log (1/(4*q)) < Real.log (a_star q) :=
        Real.log_lt_log (by positivity) ha_gt_qtr
      have h_log_inv : Real.log (1/(4*q)) = -(Real.log 4 + Real.log q) := by
        rw [Real.log_div one_ne_zero (ne_of_gt h4q_pos), Real.log_one]
        rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hq_pos)]
        ring
      linarith
    have h_g_upper : (1/q) * Real.log (a_star q) < -Real.log q / q := by
      have h := mul_lt_mul_of_pos_left h_log_upper hq_inv_pos
      rw [show (1/q) * (-Real.log q) = -Real.log q / q by ring] at h
      exact h
    have h_g_lower : (1/q) * Real.log (a_star q) > -((Real.log 4 + Real.log q)/q) := by
      have h := mul_lt_mul_of_pos_left h_log_lower hq_inv_pos
      have heq : (1/q) * (-(Real.log 4 + Real.log q)) = -((Real.log 4 + Real.log q) / q) := by
        ring
      rw [heq] at h
      exact h
    rw [Real.dist_eq, sub_zero] at h_log_div_close
    rw [Real.dist_eq, sub_zero] at h_const_close
    rw [Real.dist_eq, sub_zero]
    -- Need |1/q * log(a_star q)| < ε.
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · -- -ε < 1/q * log(a_star q)
      -- We have 1/q * log(a_star q) > -((log 4 + log q)/q)
      -- = -(log 4 / q + log q / q)
      -- ≥ -(|log 4 / q| + |log q / q|)
      -- > -(ε/3 + ε/3) = -2ε/3 > -ε
      have h1 : -((Real.log 4 + Real.log q)/q) = -(Real.log 4 / q) - (Real.log q / q) := by
        have hq_ne : q ≠ 0 := ne_of_gt hq_pos
        field_simp
        ring
      rw [h1] at h_g_lower
      have h_abs1 : -(Real.log 4 / q) ≥ -|Real.log 4 / q| := neg_le_neg (le_abs_self _)
      have h_abs2 : -(Real.log q / q) ≥ -|Real.log q / q| := neg_le_neg (le_abs_self _)
      have h_combined : -(Real.log 4 / q) - (Real.log q / q) ≥ -|Real.log 4 / q| - |Real.log q / q| := by
        linarith
      have h_bound : -|Real.log 4 / q| - |Real.log q / q| > -(ε/3) - (ε/3) := by linarith
      have h_eps : -(ε/3) - (ε/3) ≥ -ε := by linarith
      linarith
    · -- 1/q * log(a_star q) < ε
      -- 1/q * log(a_star q) < -log q / q ≤ |log q / q| < ε/3 < ε
      have h_abs : -(Real.log q / q) ≤ |Real.log q / q| := neg_le_abs _
      have heq : -Real.log q / q = -(Real.log q / q) := by ring
      rw [heq] at h_g_upper
      linarith

  -- 6e: (a_star q)^(1/q) = exp((1/q) * log(a_star q)) eventually.
  have h_astar_pow : Filter.Tendsto (fun q : ℝ => (a_star q) ^ ((1:ℝ)/q)) Filter.atTop
      (nhds (1 : ℝ)) := by
    have h_exp_tendsto : Filter.Tendsto (fun q : ℝ => Real.exp ((1/q) * Real.log (a_star q)))
        Filter.atTop (nhds (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto.comp h_log_div_g
    have h_exp_zero : Real.exp 0 = 1 := Real.exp_zero
    rw [h_exp_zero] at h_exp_tendsto
    have h_eq : ∀ᶠ q : ℝ in Filter.atTop,
        Real.exp ((1/q) * Real.log (a_star q)) = (a_star q) ^ ((1:ℝ)/q) := by
      filter_upwards [h_evt_main] with q hq_data
      obtain ⟨ha_pos, _, _, _⟩ := hq_data
      rw [Real.rpow_def_of_pos ha_pos]
      ring_nf
    exact h_exp_tendsto.congr' h_eq

  -- Step 7: Numerator → 2.
  have h_num : Filter.Tendsto (fun q : ℝ => (a_star q) ^ ((1:ℝ)/q) + 1 - 2 * (a_star q))
      Filter.atTop (nhds (2 : ℝ)) := by
    have h1 : Filter.Tendsto (fun q : ℝ => (a_star q) ^ ((1:ℝ)/q) + 1) Filter.atTop
        (nhds ((1:ℝ) + 1)) := h_astar_pow.add_const 1
    have h2 : Filter.Tendsto (fun q : ℝ => 2 * a_star q) Filter.atTop (nhds (0 : ℝ)) := by
      have h := h_astar_zero.const_mul (2 : ℝ)
      have ht : (2 : ℝ) * 0 = 0 := by ring
      rw [ht] at h
      exact h
    have h3 : Filter.Tendsto (fun q : ℝ => ((a_star q) ^ ((1:ℝ)/q) + 1) - 2 * a_star q) Filter.atTop
        (nhds ((1 + 1) - 0)) := h1.sub h2
    have ht : ((1:ℝ) + 1) - 0 = 2 := by ring
    rw [ht] at h3
    have h_fun_eq : (fun q : ℝ => ((a_star q) ^ ((1:ℝ)/q) + 1) - 2 * a_star q) =
        (fun q : ℝ => (a_star q) ^ ((1:ℝ)/q) + 1 - 2 * (a_star q)) := by
      funext q; ring
    rw [h_fun_eq] at h3
    exact h3

  -- Step 8: delta_star q → 2/1 = 2.
  have h_div_aux : Filter.Tendsto
      (fun q : ℝ => ((a_star q) ^ ((1:ℝ)/q) + 1 - 2 * (a_star q)) /
        (1 - a_star q) ^ ((1:ℝ)/q))
      Filter.atTop (nhds ((2:ℝ) / 1)) :=
    h_num.div h_denom one_ne_zero
  have h_div : Filter.Tendsto
      (fun q : ℝ => ((a_star q) ^ ((1:ℝ)/q) + 1 - 2 * (a_star q)) /
        (1 - a_star q) ^ ((1:ℝ)/q))
      Filter.atTop (nhds (2 : ℝ)) := by
    have ht : (2:ℝ) / 1 = 2 := by norm_num
    rw [ht] at h_div_aux
    exact h_div_aux

  -- delta_star q is the fraction.
  have h_eq_final : delta_star = (fun q : ℝ => ((a_star q) ^ ((1:ℝ)/q) + 1 - 2 * (a_star q)) /
        (1 - a_star q) ^ ((1:ℝ)/q)) := by
    funext q; rfl
  rw [h_eq_final]
  exact h_div
