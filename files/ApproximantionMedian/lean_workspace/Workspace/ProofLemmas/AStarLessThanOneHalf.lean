import Mathlib
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.FqStrictConvex

open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.FqSignAt0Pos

theorem AStarLessThanOneHalf (q : ℝ) (hq : 1 < q) :
    0 < a_star q ∧ a_star q < 1/2 := by
  -- Get IsAStar info from FqHasUniqueInteriorZero
  obtain ⟨_, hIs⟩ := FqHasUniqueInteriorZero q hq
  obtain ⟨ha_pos, ha_lt_one, hFa⟩ := hIs
  refine ⟨ha_pos, ?_⟩
  -- Basic positivity facts
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
  have hqp1_pos : (0 : ℝ) < q + 1 := by linarith
  -- F_q q 1 = 0
  have hF_one : F_q q 1 = 0 := by
    simp only [F_q, Real.one_rpow]
    field_simp
    ring
  -- log 2 < 1
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  -- 0 < log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- 2 * (q - 1) / (q + 1) < log q
  have hlogq_lower : 2 * (q - 1) / (q + 1) < Real.log q := by
    have h := Real.lt_log_one_add_of_pos (x := q - 1) hqm1_pos
    have h1 : (q - 1 : ℝ) + 2 = q + 1 := by ring
    have h2 : (1 : ℝ) + (q - 1) = q := by ring
    rw [h1, h2] at h
    exact h
  -- Key inequality: log 2 * (q - 1) < q * log q
  have h_key : Real.log 2 * (q - 1) < q * Real.log q := by
    have h_step1 : Real.log 2 * (q - 1) ≤ q * (2 * (q - 1) / (q + 1)) := by
      have h_aux : Real.log 2 * (q + 1) ≤ 2 * q := by
        have hq_ge_one : (1 : ℝ) ≤ q := le_of_lt hq
        nlinarith [hlog2_lt_one, hq_ge_one, hlog2_pos]
      have h_lhs : Real.log 2 * (q - 1) * (q + 1) ≤ 2 * q * (q - 1) := by
        nlinarith [hqm1_pos, h_aux]
      have h_rhs_eq : q * (2 * (q - 1) / (q + 1)) = (2 * q * (q - 1)) / (q + 1) := by
        field_simp
      rw [h_rhs_eq, le_div_iff₀ hqp1_pos]
      linarith
    have h_step2 : q * (2 * (q - 1) / (q + 1)) < q * Real.log q := by
      exact mul_lt_mul_of_pos_left hlogq_lower hq_pos
    linarith
  -- F_q q (1/2) < 0
  have hF_half : F_q q (1/2) < 0 := by
    have h_half_rpow : ((1:ℝ)/2) ^ ((1 - q) / q) = Real.exp (((q - 1) / q) * Real.log 2) := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ by norm_num]
      rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
      rw [show ((2 : ℝ)^((1 - q) / q))⁻¹ = (2 : ℝ)^(-(((1 - q) / q))) by
        rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]]
      rw [show -((1 - q) / q) = (q - 1) / q by ring]
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      ring_nf
    -- Derive: (1/2)^((1-q)/q) < q
    have h_rpow_lt_q : ((1:ℝ)/2) ^ ((1 - q) / q) < q := by
      rw [h_half_rpow]
      have hexp_lt : ((q - 1) / q) * Real.log 2 < Real.log q := by
        rw [div_mul_eq_mul_div]
        rw [div_lt_iff₀ hq_pos]
        linarith [h_key]
      calc Real.exp (((q - 1) / q) * Real.log 2)
          < Real.exp (Real.log q) := Real.exp_lt_exp.mpr hexp_lt
        _ = q := Real.exp_log hq_pos
    -- Now F_q(1/2) = -1 + (1/q) * (1/2)^((1-q)/q) < -1 + (1/q) * q = 0
    have h_inv_pos : 0 < (1 : ℝ) / q := by positivity
    have h_mul : (1/q) * ((1:ℝ)/2) ^ ((1 - q) / q) < (1/q) * q := by
      exact mul_lt_mul_of_pos_left h_rpow_lt_q h_inv_pos
    have h_inv_q : (1/q) * q = 1 := by field_simp
    rw [h_inv_q] at h_mul
    have hFq_half_eq : F_q q (1/2) = -1 + (1/q) * ((1:ℝ)/2) ^ ((1 - q) / q) := by
      simp only [F_q]
      field_simp
      ring
    rw [hFq_half_eq]
    linarith
  -- Apply secant_strict_mono via FqStrictConvex
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : 1/2 ≤ a_star q
  have hSC := FqStrictConvex q hq
  rcases eq_or_lt_of_le h_neg with heq | hlt
  · -- 1/2 = a_star q
    rw [← heq] at hFa
    linarith
  · -- 1/2 < a_star q
    have h_half_in : (1 : ℝ)/2 ∈ Set.Ioi (0 : ℝ) := by
      simp only [Set.mem_Ioi]; norm_num
    have h_one_in : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      simp only [Set.mem_Ioi]; norm_num
    have h_astar_in : a_star q ∈ Set.Ioi (0 : ℝ) := ha_pos
    have hxa : (1 : ℝ)/2 ≠ 1 := by norm_num
    have hya : a_star q ≠ 1 := ne_of_lt ha_lt_one
    -- secant_strict_mono : a ∈ s → x ∈ s → y ∈ s → x ≠ a → y ≠ a → x < y →
    --   (f x - f a) / (x - a) < (f y - f a) / (y - a)
    have hSecant := hSC.secant_strict_mono h_one_in h_half_in h_astar_in hxa hya hlt
    rw [hFa, hF_one] at hSecant
    -- hSecant : (F_q q (1/2) - 0) / (1/2 - 1) < (0 - 0) / (a_star q - 1)
    -- Simplify: F_q q (1/2) / (1/2 - 1) < 0
    have h_rhs_zero : (0 - (0 : ℝ)) / (a_star q - 1) = 0 := by
      simp
    have h_lhs_simp : (F_q q (1/2) - 0) / ((1:ℝ)/2 - 1) = F_q q (1/2) / ((1:ℝ)/2 - 1) := by
      ring
    rw [h_rhs_zero, h_lhs_simp] at hSecant
    -- hSecant : F_q q (1/2) / (1/2 - 1) < 0
    have hdenom_neg : ((1:ℝ)/2 - 1) < 0 := by norm_num
    -- F_q q (1/2) / (negative) < 0 means F_q q (1/2) > 0, contradicting hF_half
    have hF_pos : 0 < F_q q (1/2) := by
      rcases div_neg_iff.mp hSecant with ⟨hp, hn⟩ | ⟨hn, hp⟩
      · linarith
      · linarith
    linarith
