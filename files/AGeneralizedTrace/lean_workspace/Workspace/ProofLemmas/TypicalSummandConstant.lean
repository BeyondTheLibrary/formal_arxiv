import Mathlib
import Workspace.Types.AlternatingSumExpression

set_option maxHeartbeats 800000

open Real

theorem TypicalSummandConstant :
    ∀ (n : ℕ), (10 : ℕ) ^ 12 ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt (n : ℝ) ≤ δ → δ ≤ 1/2 →
    ∀ (zMinus zPlus : ℕ),
      (n : ℝ) / 16 ≤ (zMinus : ℝ) →
      (n : ℝ) / 16 ≤ (zPlus : ℝ) →
      let B_exp : ℕ → ℝ → ℕ → ℕ → ℝ := fun n' δ' zM zP =>
        ((n' : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ') ^ 2 *
          max (max (Real.exp (-(δ' * (zM : ℝ) / 20)) / (1 - δ'))
                   (Real.exp (-(δ' * (zP : ℝ) / 20)) / (1 - δ')))
              (Real.exp (-((n' : ℝ) / 150)))
      let B_Fou : ℕ → ℝ → ℝ := fun n' δ' =>
        4 * (2 * Real.pi) ^ 2 / (1 - δ') ^ 2 * Real.exp (-Real.sqrt (n' : ℝ))
      let C_star : ℝ := 16 * (2 * Real.pi) ^ 4
      B_exp n δ zMinus zPlus + B_Fou n δ
        ≤ C_star * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
  intro n hn_lb hn_mod δ hδ_lb hδ_ub zMinus zPlus hzM hzP
  simp only
  -- Basic positivity / ordering facts
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by
    have h1 : 0 < (10 : ℕ) ^ 12 := by positivity
    have h2 : 0 < n := lt_of_lt_of_le h1 hn_lb
    exact_mod_cast h2
  have h_n_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    have h1 : 0 < (10 : ℕ) ^ 12 := by positivity
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have h_n_ge : (10 : ℝ)^12 ≤ (n : ℝ) := by exact_mod_cast hn_lb
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr h_n_pos
  have h_sqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt h_sqrt_n_pos
  -- sqrt n ≥ 10^6
  have h_sqrt_n_ge : (10 : ℝ)^6 ≤ Real.sqrt (n : ℝ) := by
    have h1 : ((10 : ℝ)^6)^2 = (10 : ℝ)^12 := by norm_num
    have h2 : ((10 : ℝ)^6)^2 ≤ (n : ℝ) := by rw [h1]; exact h_n_ge
    have h3 : (0 : ℝ) ≤ (10 : ℝ)^6 := by positivity
    calc (10 : ℝ)^6 = Real.sqrt (((10 : ℝ)^6)^2) := by rw [Real.sqrt_sq h3]
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h2
  -- δ positive
  have h320_pos : (0 : ℝ) < 320 / Real.sqrt (n : ℝ) := by
    apply div_pos; · norm_num
    · exact h_sqrt_n_pos
  have hδ_pos : 0 < δ := lt_of_lt_of_le h320_pos hδ_lb
  -- 1 - δ bounds
  have h_one_sub_δ_pos : 0 < 1 - δ := by linarith
  have h_one_sub_δ_ge : 1/2 ≤ 1 - δ := by linarith
  have h_one_sub_δ_le : 1 - δ ≤ 1 := by linarith
  have h_one_sub_δ_nonneg : 0 ≤ 1 - δ := le_of_lt h_one_sub_δ_pos
  -- (1-δ)^2 ≥ 1/4
  have h_sq_ge : (1/4 : ℝ) ≤ (1 - δ)^2 := by
    have : (1/2 : ℝ)^2 = 1/4 := by norm_num
    rw [← this]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h_one_sub_δ_ge 2
  have h_sq_pos : 0 < (1 - δ)^2 := by positivity
  -- 1/(1-δ)^2 ≤ 4
  have h_recip_sq_le : 1 / (1 - δ)^2 ≤ 4 := by
    rw [div_le_iff₀ h_sq_pos]
    linarith
  -- 1/(1-δ) ≤ 2
  have h_recip_le : 1 / (1 - δ) ≤ 2 := by
    rw [div_le_iff₀ h_one_sub_δ_pos]
    linarith
  -- π bounds
  have h_pi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_two_pi_pos : 0 < 2 * Real.pi := by linarith
  have h_two_pi_ge_one : 1 ≤ 2 * Real.pi := by linarith
  have h_two_pi_ge_six : 6 ≤ 2 * Real.pi := by linarith
  -- (2π)^k positivity
  have h_pi2_pos : 0 < (2 * Real.pi)^2 := by positivity
  have h_pi3_pos : 0 < (2 * Real.pi)^3 := by positivity
  have h_pi4_pos : 0 < (2 * Real.pi)^4 := by positivity
  have h_pi2_ge_one : 1 ≤ (2 * Real.pi)^2 := by
    nlinarith [h_two_pi_ge_one, h_two_pi_pos]
  have h_pi3_le_pi4 : (2 * Real.pi)^3 ≤ (2 * Real.pi)^4 := by
    have heq : (2 * Real.pi)^4 = (2 * Real.pi)^3 * (2 * Real.pi) := by ring
    rw [heq]
    nlinarith [h_pi3_pos, h_two_pi_ge_one]
  have h_2pi_minus_2_pos : 0 < 2 * Real.pi - 2 := by linarith
  have h_2pi_minus_2_le : 2 * Real.pi - 2 ≤ 2 * Real.pi := by linarith
  -- exp(-√n) bounds
  have h_exp_pos : 0 < Real.exp (-Real.sqrt (n : ℝ)) := Real.exp_pos _
  have h_exp_nonneg : 0 ≤ Real.exp (-Real.sqrt (n : ℝ)) := le_of_lt h_exp_pos
  -- δ z₋ / 20 ≥ √n
  have h_zM_nn : 0 ≤ (zMinus : ℝ) := by
    have h_n_div_16_nn : 0 ≤ (n : ℝ) / 16 := by positivity
    linarith
  have h_zP_nn : 0 ≤ (zPlus : ℝ) := by
    have h_n_div_16_nn : 0 ≤ (n : ℝ) / 16 := by positivity
    linarith
  have h_δzM_ge_sqrtN : Real.sqrt (n : ℝ) ≤ δ * (zMinus : ℝ) / 20 := by
    have h1 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16) ≤ δ * (zMinus : ℝ) := by
      apply mul_le_mul hδ_lb hzM
      · positivity
      · linarith
    have h2 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16) = 20 * ((n : ℝ) / Real.sqrt (n : ℝ)) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
      have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (le_of_lt h_n_pos)
      field_simp
      linarith
    rw [h3] at h1
    linarith
  have h_δzP_ge_sqrtN : Real.sqrt (n : ℝ) ≤ δ * (zPlus : ℝ) / 20 := by
    have h1 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16) ≤ δ * (zPlus : ℝ) := by
      apply mul_le_mul hδ_lb hzP
      · positivity
      · linarith
    have h2 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16) = 20 * ((n : ℝ) / Real.sqrt (n : ℝ)) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
      have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (le_of_lt h_n_pos)
      field_simp
      linarith
    rw [h3] at h1
    linarith
  -- n/150 ≥ √n since √n ≥ 10^6 ≥ 150
  have h_nDiv150_ge_sqrtN : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 150 := by
    have h_sqrt_ge_150 : (150 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have h150 : (150 : ℝ) ≤ (10 : ℝ)^6 := by norm_num
      linarith
    have h1 : 150 * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      nlinarith [h_sqrt_ge_150, h_sqrt_n_pos]
    have h2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (le_of_lt h_n_pos)
    rw [h2] at h1
    linarith
  -- exp(-δzM/20) ≤ exp(-√n) etc
  have h_exp_zM : Real.exp (-(δ * (zMinus : ℝ) / 20)) ≤ Real.exp (-Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h_exp_zP : Real.exp (-(δ * (zPlus : ℝ) / 20)) ≤ Real.exp (-Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h_exp_n150 : Real.exp (-((n : ℝ) / 150)) ≤ Real.exp (-Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h_exp_zM_pos : 0 < Real.exp (-(δ * (zMinus : ℝ) / 20)) := Real.exp_pos _
  have h_exp_zP_pos : 0 < Real.exp (-(δ * (zPlus : ℝ) / 20)) := Real.exp_pos _
  have h_exp_n150_pos : 0 < Real.exp (-((n : ℝ) / 150)) := Real.exp_pos _
  -- Bound each ratio in the max by 2 * exp(-√n)
  -- exp(-δzM/20)/(1-δ): denominator ≥ 1/2, so ratio ≤ 2 * exp(-δzM/20) ≤ 2 * exp(-√n)
  have h_frac_zM : Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ) ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    -- exp(-δzM/20)/(1-δ) ≤ exp(-δzM/20) * 2 since 1/(1-δ) ≤ 2
    have h1 : Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ) =
              Real.exp (-(δ * (zMinus : ℝ) / 20)) * (1 / (1 - δ)) := by
      rw [mul_one_div]
    rw [h1]
    calc Real.exp (-(δ * (zMinus : ℝ) / 20)) * (1 / (1 - δ))
        ≤ Real.exp (-(δ * (zMinus : ℝ) / 20)) * 2 := by
          apply mul_le_mul_of_nonneg_left h_recip_le (le_of_lt h_exp_zM_pos)
      _ ≤ Real.exp (-Real.sqrt (n : ℝ)) * 2 := by
          apply mul_le_mul_of_nonneg_right h_exp_zM (by norm_num : (0:ℝ) ≤ 2)
      _ = 2 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
  have h_frac_zP : Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ) ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    have h1 : Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ) =
              Real.exp (-(δ * (zPlus : ℝ) / 20)) * (1 / (1 - δ)) := by
      rw [mul_one_div]
    rw [h1]
    calc Real.exp (-(δ * (zPlus : ℝ) / 20)) * (1 / (1 - δ))
        ≤ Real.exp (-(δ * (zPlus : ℝ) / 20)) * 2 := by
          apply mul_le_mul_of_nonneg_left h_recip_le (le_of_lt h_exp_zP_pos)
      _ ≤ Real.exp (-Real.sqrt (n : ℝ)) * 2 := by
          apply mul_le_mul_of_nonneg_right h_exp_zP (by norm_num : (0:ℝ) ≤ 2)
      _ = 2 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
  -- exp(-n/150) ≤ exp(-√n) ≤ 2 * exp(-√n)
  have h_exp_n150_bound : Real.exp (-((n : ℝ) / 150)) ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    calc Real.exp (-((n : ℝ) / 150))
        ≤ Real.exp (-Real.sqrt (n : ℝ)) := h_exp_n150
      _ ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by linarith
  -- max(max(...), ...) ≤ 2 * exp(-√n)
  have h_max_inner : max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                         (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ))
                     ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := max_le h_frac_zM h_frac_zP
  have h_max_outer : max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                              (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                         (Real.exp (-((n : ℝ) / 150)))
                     ≤ 2 * Real.exp (-Real.sqrt (n : ℝ)) := max_le h_max_inner h_exp_n150_bound
  have h_max_nn : 0 ≤ max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                               (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                          (Real.exp (-((n : ℝ) / 150))) := by
    apply le_max_of_le_right; exact le_of_lt h_exp_n150_pos
  -- Now bound B_exp
  -- B_exp = (n+1)(2π-2)(2π)² / (1-δ)² * max(...)
  -- ≤ (n+1)(2π)(2π)² · 4 · 2 exp(-√n)
  -- = 8(2π)³(n+1) exp(-√n)
  -- ≤ 16(2π)³ n exp(-√n)
  -- The factor (2π-2) ≤ 2π
  -- The factor 1/(1-δ)² ≤ 4
  -- Coefficient: (n+1)(2π-2)(2π)² / (1-δ)² ≤ (n+1)·2π·(2π)²·4 = 8π(n+1)(2π)² = 4(n+1)(2π)³
  -- Then multiply by max which is ≤ 2 exp(-√n):
  -- B_exp ≤ 4(n+1)(2π)³ · 2 exp(-√n) = 8(n+1)(2π)³ exp(-√n) ≤ 16 n (2π)³ exp(-√n)
  -- Then since (2π)³ ≤ (2π)⁴:
  -- B_exp ≤ 16 n (2π)⁴ exp(-√n)
  -- Let's compute step by step.
  have h_n_plus_1_pos : 0 < (n : ℝ) + 1 := by linarith
  have h_n_plus_1_nn : 0 ≤ (n : ℝ) + 1 := le_of_lt h_n_plus_1_pos
  have h_n_plus_1_le_2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  -- Coefficient bound: (n+1)(2π-2)(2π)² / (1-δ)²
  -- We expand using 1/(1-δ)² ≤ 4 and (2π-2) ≤ 2π
  have h_coef_pos : 0 ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 := by
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg h_n_plus_1_nn (le_of_lt h_2pi_minus_2_pos)
      · exact le_of_lt h_pi2_pos
    · exact le_of_lt h_sq_pos
  -- B_exp = coef * max(...) ≤ coef * (2 exp(-√n)) since max ≥ 0 and coef ≥ 0
  -- Actually we apply: a*b ≤ a*c when a ≥ 0 and b ≤ c
  -- Now bound coef ≤ 8π(n+1)(2π)² = 4(n+1)(2π)³
  -- Use: 1/(1-δ)² ≤ 4 and (2π-2)*1 ≤ 2π*1
  -- Step: ((n+1)(2π-2)(2π)²) / (1-δ)² = ((n+1)(2π-2)(2π)²) * (1/(1-δ)²)
  --                                  ≤ ((n+1)(2π-2)(2π)²) * 4
  --                                  ≤ ((n+1)(2π)(2π)²) * 4   (since 2π-2 ≤ 2π)
  --                                  = 4(n+1)(2π)³
  have h_coef_le : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2
                   ≤ 4 * ((n : ℝ) + 1) * (2 * Real.pi)^3 := by
    have h_num_nn : 0 ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 := by
      apply mul_nonneg
      · apply mul_nonneg h_n_plus_1_nn (le_of_lt h_2pi_minus_2_pos)
      · exact le_of_lt h_pi2_pos
    have h_denom : (1 - δ)^2 ≥ 1/4 := h_sq_ge
    -- numerator/denominator ≤ numerator/(1/4) = 4*numerator
    have step1 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2
                 ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1/4) := by
      apply div_le_div_of_nonneg_left h_num_nn (by norm_num : (0:ℝ) < 1/4) h_denom
    have step2 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1/4)
                 = 4 * (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2) := by
      ring
    rw [step2] at step1
    -- Now bound 4 * ((n+1) (2π-2) (2π)²) ≤ 4 * ((n+1) (2π) (2π)²) = 4 (n+1) (2π)³
    have step3 : 4 * (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2)
                 ≤ 4 * (((n : ℝ) + 1) * (2 * Real.pi) * (2 * Real.pi)^2) := by
      have hfactor : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2
                     ≤ ((n : ℝ) + 1) * (2 * Real.pi) * (2 * Real.pi)^2 := by
        have hh : ((n : ℝ) + 1) * (2 * Real.pi - 2) ≤ ((n : ℝ) + 1) * (2 * Real.pi) := by
          apply mul_le_mul_of_nonneg_left h_2pi_minus_2_le h_n_plus_1_nn
        apply mul_le_mul_of_nonneg_right hh (le_of_lt h_pi2_pos)
      linarith
    have step4 : 4 * (((n : ℝ) + 1) * (2 * Real.pi) * (2 * Real.pi)^2)
                 = 4 * ((n : ℝ) + 1) * (2 * Real.pi)^3 := by ring
    linarith
  -- Then B_exp ≤ (4 (n+1) (2π)³) * (2 exp(-√n)) = 8 (n+1) (2π)³ exp(-√n)
  --             ≤ 16 n (2π)³ exp(-√n)   (using n+1 ≤ 2n)
  --             ≤ 16 n (2π)⁴ exp(-√n)   (using (2π)³ ≤ (2π)⁴)
  have h_4_n1_2pi3_nn : 0 ≤ 4 * ((n : ℝ) + 1) * (2 * Real.pi)^3 := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 4) h_n_plus_1_nn
    · exact le_of_lt h_pi3_pos
  -- B_exp = coef * max(...)
  set Mxx := max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                       (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                  (Real.exp (-((n : ℝ) / 150))) with hMxx_def
  -- Combine:
  have h_Bexp_step1 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 * Mxx
                     ≤ (4 * ((n : ℝ) + 1) * (2 * Real.pi)^3) * (2 * Real.exp (-Real.sqrt (n : ℝ))) := by
    apply mul_le_mul h_coef_le h_max_outer h_max_nn h_4_n1_2pi3_nn
  -- Now 4*(n+1)*(2π)³ * 2 * exp(-√n) = 8*(n+1)*(2π)³*exp(-√n)
  -- ≤ 16*n*(2π)³*exp(-√n) since n+1 ≤ 2n
  have h_Bexp_step2 : (4 * ((n : ℝ) + 1) * (2 * Real.pi)^3) * (2 * Real.exp (-Real.sqrt (n : ℝ)))
                     ≤ 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ)) := by
    -- LHS = 8(n+1)(2π)³ exp(-√n)
    -- RHS = 16 n (2π)³ exp(-√n)
    -- 8(n+1) ≤ 16 n iff n+1 ≤ 2n iff n ≥ 1
    have hh : 8 * ((n : ℝ) + 1) ≤ 16 * (n : ℝ) := by linarith
    have key : 8 * ((n : ℝ) + 1) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ))
              ≤ 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ)) := by
      have : 8 * ((n : ℝ) + 1) * (2 * Real.pi)^3 ≤ 16 * (n : ℝ) * (2 * Real.pi)^3 := by
        apply mul_le_mul_of_nonneg_right hh (le_of_lt h_pi3_pos)
      apply mul_le_mul_of_nonneg_right this h_exp_nonneg
    have eq1 : (4 * ((n : ℝ) + 1) * (2 * Real.pi)^3) * (2 * Real.exp (-Real.sqrt (n : ℝ)))
               = 8 * ((n : ℝ) + 1) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    linarith [key, eq1.symm.le, eq1.le]
  -- 16 n (2π)³ exp(-√n) ≤ 16 n (2π)⁴ exp(-√n)
  have h_Bexp_step3 : 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ))
                     ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 * Real.exp (-Real.sqrt (n : ℝ)) := by
    have h_n_nn : 0 ≤ (n : ℝ) := le_of_lt h_n_pos
    have h_16n_nn : 0 ≤ 16 * (n : ℝ) := by linarith
    have key : 16 * (n : ℝ) * (2 * Real.pi)^3 ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 := by
      apply mul_le_mul_of_nonneg_left h_pi3_le_pi4 h_16n_nn
    apply mul_le_mul_of_nonneg_right key h_exp_nonneg
  -- Combine these to get B_exp ≤ 16 n (2π)^4 exp(-√n) (this is C_star * n * exp(-√n))
  have h_Bexp_total : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 * Mxx
                     ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 * Real.exp (-Real.sqrt (n : ℝ)) := by
    linarith [h_Bexp_step1, h_Bexp_step2, h_Bexp_step3]
  -- Now bound B_Fou: 4 (2π)² / (1-δ)² * exp(-√n)
  -- 4 / (1-δ)² ≤ 4 * 4 = 16
  -- So B_Fou ≤ 16 (2π)² exp(-√n)
  -- We need: 16 (2π)² exp(-√n) ≤ ε * (16 n (2π)⁴ exp(-√n)) ... actually we want sum ≤ C_star n exp(-√n)
  -- Idea: B_Fou ≤ 16 (2π)² exp(-√n) ≤ 16 (n (2π)⁴ - n (2π)³) exp(-√n) ... too tight
  -- Let me reconsider. The hint says:
  -- B_Fou ≤ 16 (2π)² exp(-√n) ≤ 16 (2π)⁴ n exp(-√n) (for n ≥ 1, (2π)² ≤ (2π)⁴ and 1 ≤ n)
  -- So B_exp + B_Fou ≤ 16 n (2π)⁴ exp + 16 n (2π)⁴ exp ≠ 16 n (2π)⁴ exp...
  -- Hmm, we need the sum ≤ 16 n (2π)⁴ exp, not 32.
  -- The right bound: B_exp ≤ 8(n+1)(2π)³ exp(-√n) ≤ 16 n (2π)³ exp(-√n)
  -- B_Fou ≤ 16 (2π)² exp(-√n)
  -- Sum: 16 n (2π)³ + 16 (2π)² ≤ 16 n (2π)⁴   for n ≥ 1
  -- 16 (2π)² (n (2π) + 1) ≤ 16 n (2π)⁴
  -- (2π)n + 1 ≤ n (2π)²
  -- For n ≥ 1: n (2π)² - (2π)n = n (2π) (2π - 1) ≥ 1·(2π)·(2π-1) = (2π)² - 2π ≈ 39.5 - 6.28 = 33.2 ≥ 1.
  -- So (2π)² n ≥ (2π) n + 1 holds for n ≥ 1.
  have h_Bfou_nn : 0 ≤ 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (le_of_lt h_pi2_pos)
      · exact le_of_lt h_sq_pos
    · exact h_exp_nonneg
  -- B_Fou = 4 (2π)² / (1-δ)² * exp(-√n) ≤ 4 (2π)² * 4 * exp(-√n) = 16 (2π)² exp(-√n)
  have h_Bfou_le_simple : 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ))
                         ≤ 16 * (2 * Real.pi)^2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    have h_num_nn : 0 ≤ 4 * (2 * Real.pi)^2 := by
      apply mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (le_of_lt h_pi2_pos)
    have step1 : 4 * (2 * Real.pi)^2 / (1 - δ)^2 ≤ 4 * (2 * Real.pi)^2 / (1/4) := by
      apply div_le_div_of_nonneg_left h_num_nn (by norm_num : (0:ℝ) < 1/4) h_sq_ge
    have step2 : 4 * (2 * Real.pi)^2 / (1/4) = 16 * (2 * Real.pi)^2 := by ring
    rw [step2] at step1
    apply mul_le_mul_of_nonneg_right step1 h_exp_nonneg
  -- Now we need B_exp + B_Fou ≤ 16 n (2π)⁴ exp(-√n)
  -- We have B_exp ≤ 8(n+1)(2π)³ exp(-√n)
  -- We have B_Fou ≤ 16 (2π)² exp(-√n)
  -- Want: 8(n+1)(2π)³ + 16 (2π)² ≤ 16 n (2π)⁴
  -- = 8 (2π)² ((n+1)(2π) + 2)
  -- ≤ 16 n (2π)⁴
  -- So need (n+1)(2π) + 2 ≤ 2 n (2π)²
  -- Equivalent: 2π n + 2π + 2 ≤ 2 (2π)² n
  -- For n ≥ 1: 2(2π)² n - 2π n = 2π n (2(2π) - 1) ≥ 2π (2(2π) - 1) ≈ 6.28 * 11.56 ≈ 72.6
  -- 2π + 2 ≈ 8.28. So 2(2π)² n - 2π n ≥ 72 ≥ 2π + 2.
  -- Cleaner: just bound stronger. B_exp ≤ 16 n (2π)³ exp.
  -- Need: 16 n (2π)³ + 16 (2π)² ≤ 16 n (2π)⁴
  -- i.e., n (2π)³ + (2π)² ≤ n (2π)⁴
  -- Divide by (2π)²: n (2π) + 1 ≤ n (2π)²
  -- i.e., 1 ≤ n (2π)² - n (2π) = n(2π)((2π) - 1)
  -- Since n ≥ 1, (2π) ≥ 6, (2π)-1 ≥ 5, RHS ≥ 30 ≥ 1.
  -- Let's prove: n (2π) + 1 ≤ n (2π)²
  have h_key_ineq : (n : ℝ) * (2 * Real.pi) + 1 ≤ (n : ℝ) * (2 * Real.pi)^2 := by
    have h_diff : (n : ℝ) * (2 * Real.pi)^2 - (n : ℝ) * (2 * Real.pi)
                  = (n : ℝ) * (2 * Real.pi) * ((2 * Real.pi) - 1) := by ring
    have h_2pi_minus_1_pos : 0 < 2 * Real.pi - 1 := by linarith
    have h_prod_nn : 0 ≤ (n : ℝ) * (2 * Real.pi) := by
      apply mul_nonneg (le_of_lt h_n_pos) (le_of_lt h_two_pi_pos)
    -- n * (2π) * (2π - 1) ≥ 1 * 6 * 5 = 30 ≥ 1
    have h_nn_le_n : (1 : ℝ) ≤ (n : ℝ) := h_n_ge_one
    have h_30 : (30 : ℝ) ≤ (n : ℝ) * (2 * Real.pi) * ((2 * Real.pi) - 1) := by
      have step1 : (1 : ℝ) * 6 * 5 ≤ (n : ℝ) * (2 * Real.pi) * ((2 * Real.pi) - 1) := by
        apply mul_le_mul
        · apply mul_le_mul h_nn_le_n h_two_pi_ge_six (by norm_num) (le_of_lt h_n_pos)
        · linarith
        · linarith
        · apply mul_nonneg (le_of_lt h_n_pos) (le_of_lt h_two_pi_pos)
      linarith
    linarith
  -- Now derive 16 n (2π)³ + 16 (2π)² ≤ 16 n (2π)⁴
  have h_sum_coef : 16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2
                   ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 := by
    have h1 : 16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2
              = 16 * (2 * Real.pi)^2 * ((n : ℝ) * (2 * Real.pi) + 1) := by ring
    have h2 : 16 * (n : ℝ) * (2 * Real.pi)^4
              = 16 * (2 * Real.pi)^2 * ((n : ℝ) * (2 * Real.pi)^2) := by ring
    rw [h1, h2]
    have h16pi2_nn : 0 ≤ 16 * (2 * Real.pi)^2 := by
      apply mul_nonneg (by norm_num) (le_of_lt h_pi2_pos)
    apply mul_le_mul_of_nonneg_left h_key_ineq h16pi2_nn
  -- Multiply by exp(-√n)
  have h_sum_full : (16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2) * Real.exp (-Real.sqrt (n : ℝ))
                   ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 * Real.exp (-Real.sqrt (n : ℝ)) := by
    apply mul_le_mul_of_nonneg_right h_sum_coef h_exp_nonneg
  -- Distribute on LHS
  have h_distribute : (16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2) * Real.exp (-Real.sqrt (n : ℝ))
                     = 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ)) +
                       16 * (2 * Real.pi)^2 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
  -- Final assembly
  -- LHS of goal = B_exp n δ zMinus zPlus + B_Fou n δ
  --     B_exp n δ zMinus zPlus = ((n+1)(2π-2)(2π)²/(1-δ)²) * Mxx ≤ 16 n (2π)³ exp(-√n)
  --     B_Fou n δ = 4(2π)²/(1-δ)² exp(-√n) ≤ 16 (2π)² exp(-√n)
  -- Sum ≤ 16 n (2π)³ exp + 16 (2π)² exp ≤ 16 n (2π)⁴ exp = C_star * n * exp(-√n)
  -- Use linarith with all the pieces.
  -- Goal still has the lets unfolded by simp only [].
  -- After simp only, goal is: B_exp n δ zMinus zPlus + B_Fou n δ ≤ C_star * n * exp(-√n)
  -- where B_exp etc. are unfolded (since they were lets).
  -- The unfolded form:
  --   ((n+1)(2π-2)(2π)²/(1-δ)²) * Mxx + 4(2π)²/(1-δ)² * exp(-√n) ≤ 16 (2π)⁴ * n * exp(-√n)
  -- We have h_Bexp_total and h_Bfou_le_simple.
  -- 16 n (2π)³ exp + 16 (2π)² exp ≤ 16 n (2π)⁴ exp from h_sum_coef (multiplied by exp).
  show ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 *
        max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                 (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
            (Real.exp (-((n : ℝ) / 150)))
       + 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ))
       ≤ 16 * (2 * Real.pi)^4 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
  -- Rewrite to use Mxx.
  rw [show max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                    (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                (Real.exp (-((n : ℝ) / 150))) = Mxx from rfl]
  -- Now: B_exp_expr + B_Fou_expr ≤ 16 (2π)⁴ n exp(-√n)
  -- We have:
  --   h_Bexp_total : (n+1)(2π-2)(2π)²/(1-δ)² * Mxx ≤ 16 n (2π)⁴ exp(-√n)
  -- Wait, h_Bexp_total bounds B_exp by 16 n (2π)⁴ exp directly (we did the (2π)³ ≤ (2π)⁴ step).
  -- That's too strong! We need B_exp + B_Fou ≤ 16 n (2π)⁴ exp.
  -- Recompute: B_exp ≤ 16 n (2π)³ exp, B_Fou ≤ 16 (2π)² exp.
  -- Then B_exp + B_Fou ≤ 16 n (2π)³ exp + 16 (2π)² exp ≤ 16 n (2π)⁴ exp.
  -- The issue: h_Bexp_total did chain to (2π)⁴, but we want (2π)³ for the sum step.
  -- Let me extract the (2π)³ bound:
  have h_Bexp_pi3 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 * Mxx
                   ≤ 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ)) := by
    linarith [h_Bexp_step1, h_Bexp_step2]
  -- Sum:
  have h_final : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 * Mxx
                 + 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ))
                 ≤ 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ))
                 + 16 * (2 * Real.pi)^2 * Real.exp (-Real.sqrt (n : ℝ)) := by
    linarith [h_Bexp_pi3, h_Bfou_le_simple]
  -- And RHS ≤ goal RHS
  have h_RHS : 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ))
               + 16 * (2 * Real.pi)^2 * Real.exp (-Real.sqrt (n : ℝ))
               ≤ 16 * (2 * Real.pi)^4 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
    have hh : (16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2) * Real.exp (-Real.sqrt (n : ℝ))
             ≤ 16 * (n : ℝ) * (2 * Real.pi)^4 * Real.exp (-Real.sqrt (n : ℝ)) := h_sum_full
    have eq1 : (16 * (n : ℝ) * (2 * Real.pi)^3 + 16 * (2 * Real.pi)^2) * Real.exp (-Real.sqrt (n : ℝ))
              = 16 * (n : ℝ) * (2 * Real.pi)^3 * Real.exp (-Real.sqrt (n : ℝ))
                + 16 * (2 * Real.pi)^2 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    have eq2 : 16 * (n : ℝ) * (2 * Real.pi)^4 * Real.exp (-Real.sqrt (n : ℝ))
              = 16 * (2 * Real.pi)^4 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    linarith [hh, eq1.le, eq1.symm.le, eq2.le, eq2.symm.le]
  linarith [h_final, h_RHS]
