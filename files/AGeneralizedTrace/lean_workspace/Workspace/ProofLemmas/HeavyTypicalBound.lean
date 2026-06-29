import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.HeavyEllCount
import Workspace.ProofLemmas.SublemmaPerSummandBound
import Workspace.ProofLemmas.TypicalSummandConstant

set_option maxHeartbeats 8000000

open Classical

theorem HeavyTypicalBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt (n : ℝ) ≤ δ → δ ≤ 1 / 2 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j))
      let allEll : Finset (Finset ℕ) :=
        ((Finset.Icc 1 (n / 2)).powerset).filter
          Workspace.Types.AlternatingSumExpression.sameParity
      let P_H : Finset (Finset ℕ) :=
        allEll.filter (fun ℓ =>
          ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ)
      let T_I : ℝ :=
        ∑ ℓ ∈ P_H,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
      T_I ≤ (1 : ℝ) / 4 * Real.exp (-(Real.sqrt n / 4)) := by
  intro n hn hmod δ hδ_lb hδ_ub
  simp only
  -- Set up shorthand
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  set α : ℝ := c' * Real.sqrt n with hα_def
  set n_h : ℕ := n / 2 with hn_h_def
  set S_er : ℤ → ℕ → ℝ := fun r j =>
        α * Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ)) with hS_er_def
  set widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j)) with hwidetildeMu_def
  set allEll : Finset (Finset ℕ) :=
        ((Finset.Icc 1 (n / 2)).powerset).filter
          Workspace.Types.AlternatingSumExpression.sameParity with hallEll_def
  set P_H : Finset (Finset ℕ) :=
        allEll.filter (fun ℓ =>
          ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ) with hP_H_def
  set P_H' : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
            ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ) with hP_H'_def
  -- Basic positivity facts
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by
    have h1 : 0 < (10 ^ 12 : ℕ) := by positivity
    have h2 : 0 < n := lt_of_lt_of_le h1 hn
    exact_mod_cast h2
  have h_n_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by
      have h1 : 0 < (10 ^ 12 : ℕ) := by positivity
      omega
    exact_mod_cast this
  have h_n_ge : (10 : ℝ)^12 ≤ (n : ℝ) := by exact_mod_cast hn
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr h_n_pos
  have h_sqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := h_sqrt_n_pos.le
  have h_sqrt_n_ge : (10 : ℝ)^6 ≤ Real.sqrt (n : ℝ) := by
    have h1 : ((10 : ℝ)^6)^2 = (10 : ℝ)^12 := by norm_num
    have h2 : ((10 : ℝ)^6)^2 ≤ (n : ℝ) := by rw [h1]; exact h_n_ge
    have h3 : (0 : ℝ) ≤ (10 : ℝ)^6 := by positivity
    calc (10 : ℝ)^6 = Real.sqrt (((10 : ℝ)^6)^2) := by rw [Real.sqrt_sq h3]
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h2
  -- δ positive
  have h320_pos : (0 : ℝ) < 320 / Real.sqrt (n : ℝ) := by
    apply div_pos
    · norm_num
    · exact h_sqrt_n_pos
  have hδ_pos : 0 < δ := lt_of_lt_of_le h320_pos hδ_lb
  -- π bounds
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_two_pi_pos : 0 < 2 * Real.pi := by linarith
  -- exp(-√n) is positive
  have h_exp_neg_sqrt_pos : 0 < Real.exp (-Real.sqrt (n : ℝ)) := Real.exp_pos _
  have h_exp_neg_sqrt_nonneg : 0 ≤ Real.exp (-Real.sqrt (n : ℝ)) := h_exp_neg_sqrt_pos.le
  -- Floor bound: zMinus ≥ n/16 (Nat) ⟹ (n : ℝ)/16 - 1 ≤ zMinus
  have h_floor_bound : ∀ (z : ℕ), z ≥ n / 16 → (n : ℝ) / 16 - 1 ≤ (z : ℝ) := by
    intro z hz
    have h1 : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
    have h2 : n % 16 ≤ 15 := by omega
    have h_n_ge_15 : 15 ≤ n := by
      have h0 : 0 < (10 ^ 12 : ℕ) := by positivity
      omega
    have h4 : 16 * z ≥ n - 15 := by
      have hh : 16 * (n / 16) ≤ 16 * z := by
        apply Nat.mul_le_mul_left; exact hz
      omega
    have hcast : ((16 * z : ℕ) : ℝ) ≥ ((n - 15 : ℕ) : ℝ) := by exact_mod_cast h4
    have h_eq : ((n - 15 : ℕ) : ℝ) = (n : ℝ) - 15 := by
      rw [Nat.cast_sub h_n_ge_15]; norm_num
    rw [h_eq] at hcast
    push_cast at hcast
    linarith
  -- Define M (a generous constant)
  set M : ℝ := 100000 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; norm_num
  -- Helper: (n : ℝ) / sqrt n = sqrt n
  have h_n_div_sqrt : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
    rw [div_eq_iff (ne_of_gt h_sqrt_n_pos)]
    exact (Real.mul_self_sqrt h_n_pos.le).symm
  -- Per-summand "typical" bound:
  have h_per_summand_typical :
      ∀ (ℓ : Finset ℕ), ℓ ⊆ Finset.Icc 1 (n / 2) →
        Workspace.Types.AlternatingSumExpression.sameParity ℓ →
      ∀ (zMinus zPlus : ℕ),
        zMinus ∈ Finset.Ico (n / 16) (n_h + 1) →
        zPlus ∈ Finset.Ico (n / 16) (n_h + 1) →
        |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
          ≤ M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
    intro ℓ hℓ_sub hℓ_par zMinus zPlus hzM_mem hzP_mem
    rw [Finset.mem_Ico] at hzM_mem hzP_mem
    obtain ⟨hzM_lo, hzM_hi⟩ := hzM_mem
    obtain ⟨hzP_lo, hzP_hi⟩ := hzP_mem
    have hzM_range : zMinus ∈ Finset.range (n / 2 + 1) := by
      rw [Finset.mem_range]; omega
    have hzP_range : zPlus ∈ Finset.range (n / 2 + 1) := by
      rw [Finset.mem_range]; omega
    -- Apply SublemmaPerSummandBound
    have hPSB := SublemmaPerSummandBound n hn hmod δ hδ_pos hδ_ub ℓ hℓ_sub hℓ_par
                  zMinus zPlus hzM_range hzP_range
    simp only at hPSB
    have h_zM_real : (n : ℝ) / 16 - 1 ≤ (zMinus : ℝ) := h_floor_bound zMinus hzM_lo
    have h_zP_real : (n : ℝ) / 16 - 1 ≤ (zPlus : ℝ) := h_floor_bound zPlus hzP_lo
    have h_zM_nn : 0 ≤ (zMinus : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_zP_nn : 0 ≤ (zPlus : ℝ) := by exact_mod_cast Nat.zero_le _
    -- (1 - δ) bounds
    have h_one_sub_δ_ge : 1/2 ≤ 1 - δ := by linarith
    have h_one_sub_δ_pos : 0 < 1 - δ := by linarith
    have h_sq_ge : (1/4 : ℝ) ≤ (1 - δ)^2 := by
      have : (1/2 : ℝ)^2 = 1/4 := by norm_num
      rw [← this]
      exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h_one_sub_δ_ge 2
    have h_sq_pos : 0 < (1 - δ)^2 := by positivity
    have h_recip_le : 1 / (1 - δ) ≤ 2 := by
      rw [div_le_iff₀ h_one_sub_δ_pos]; linarith
    -- 16 / sqrt n ≤ 1
    have h_16_over_sqrt_le_1 : (16 : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ h_sqrt_n_pos]
      linarith
    -- δ * zMinus / 20 ≥ √n - 1
    have h_n16m1_nn : 0 ≤ (n : ℝ) / 16 - 1 := by
      have h_n_ge_16 : (16 : ℝ) ≤ (n : ℝ) := by linarith
      linarith
    have h_δzM_ge : Real.sqrt (n : ℝ) - 1 ≤ δ * (zMinus : ℝ) / 20 := by
      have step1 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16 - 1) ≤ δ * (zMinus : ℝ) := by
        apply mul_le_mul hδ_lb h_zM_real h_n16m1_nn hδ_pos.le
      have step2 : (320 / Real.sqrt (n : ℝ)) * ((n : ℝ) / 16 - 1)
                   = 20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ) := by
        have h_eq : (320 / Real.sqrt (n : ℝ)) * ((n : ℝ) / 16 - 1)
                   = 20 * ((n : ℝ) / Real.sqrt (n : ℝ)) - 320 / Real.sqrt (n : ℝ) := by
          field_simp; ring
        rw [h_eq, h_n_div_sqrt]
      rw [step2] at step1
      have h_div : (20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ)) / 20
                   = Real.sqrt (n : ℝ) - 16 / Real.sqrt (n : ℝ) := by
        field_simp; ring
      have step3 : Real.sqrt (n : ℝ) - 16 / Real.sqrt (n : ℝ) ≤ δ * (zMinus : ℝ) / 20 := by
        have hgoal : (20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ)) / 20
                      ≤ δ * (zMinus : ℝ) / 20 := by
          apply div_le_div_of_nonneg_right step1 (by norm_num : (0:ℝ) ≤ 20)
        rwa [h_div] at hgoal
      linarith
    have h_δzP_ge : Real.sqrt (n : ℝ) - 1 ≤ δ * (zPlus : ℝ) / 20 := by
      have step1 : 320 / Real.sqrt (n : ℝ) * ((n : ℝ) / 16 - 1) ≤ δ * (zPlus : ℝ) := by
        apply mul_le_mul hδ_lb h_zP_real h_n16m1_nn hδ_pos.le
      have step2 : (320 / Real.sqrt (n : ℝ)) * ((n : ℝ) / 16 - 1)
                   = 20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ) := by
        have h_eq : (320 / Real.sqrt (n : ℝ)) * ((n : ℝ) / 16 - 1)
                   = 20 * ((n : ℝ) / Real.sqrt (n : ℝ)) - 320 / Real.sqrt (n : ℝ) := by
          field_simp; ring
        rw [h_eq, h_n_div_sqrt]
      rw [step2] at step1
      have h_div : (20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ)) / 20
                   = Real.sqrt (n : ℝ) - 16 / Real.sqrt (n : ℝ) := by
        field_simp; ring
      have step3 : Real.sqrt (n : ℝ) - 16 / Real.sqrt (n : ℝ) ≤ δ * (zPlus : ℝ) / 20 := by
        have hgoal : (20 * Real.sqrt (n : ℝ) - 320 / Real.sqrt (n : ℝ)) / 20
                      ≤ δ * (zPlus : ℝ) / 20 := by
          apply div_le_div_of_nonneg_right step1 (by norm_num : (0:ℝ) ≤ 20)
        rwa [h_div] at hgoal
      linarith
    -- n/150 ≥ √n
    have h_n150_ge : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 150 := by
      have h_sqrt_ge_150 : (150 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have : (150 : ℝ) ≤ (10 : ℝ)^6 := by norm_num
        linarith
      have h1 : 150 * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
        nlinarith [h_sqrt_ge_150, h_sqrt_n_pos]
      have h2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt h_n_pos.le
      rw [h2] at h1
      linarith
    -- exp bounds
    have h_exp_zM : Real.exp (-(δ * (zMinus : ℝ) / 20))
                    ≤ Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_le : -(δ * (zMinus : ℝ) / 20) ≤ -(Real.sqrt (n : ℝ) - 1) := by linarith
      calc Real.exp (-(δ * (zMinus : ℝ) / 20))
          ≤ Real.exp (-(Real.sqrt (n : ℝ) - 1)) := Real.exp_le_exp.mpr h_le
        _ = Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ)) := by
            rw [show -(Real.sqrt (n : ℝ) - 1) = 1 + (-Real.sqrt (n : ℝ)) from by ring,
                Real.exp_add]
    have h_exp_zP : Real.exp (-(δ * (zPlus : ℝ) / 20))
                    ≤ Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_le : -(δ * (zPlus : ℝ) / 20) ≤ -(Real.sqrt (n : ℝ) - 1) := by linarith
      calc Real.exp (-(δ * (zPlus : ℝ) / 20))
          ≤ Real.exp (-(Real.sqrt (n : ℝ) - 1)) := Real.exp_le_exp.mpr h_le
        _ = Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ)) := by
            rw [show -(Real.sqrt (n : ℝ) - 1) = 1 + (-Real.sqrt (n : ℝ)) from by ring,
                Real.exp_add]
    have h_exp_n150 : Real.exp (-((n : ℝ) / 150))
                       ≤ Real.exp (-Real.sqrt (n : ℝ)) := by
      apply Real.exp_le_exp.mpr; linarith
    have h_e_le_3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h_frac_zM : Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ)
                     ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_exp_pos : 0 < Real.exp (-(δ * (zMinus : ℝ) / 20)) := Real.exp_pos _
      rw [div_eq_mul_one_div]
      calc Real.exp (-(δ * (zMinus : ℝ) / 20)) * (1 / (1 - δ))
          ≤ Real.exp (-(δ * (zMinus : ℝ) / 20)) * 2 := by
            apply mul_le_mul_of_nonneg_left h_recip_le h_exp_pos.le
        _ ≤ (Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ))) * 2 := by
            apply mul_le_mul_of_nonneg_right h_exp_zM (by norm_num : (0:ℝ) ≤ 2)
        _ ≤ (3 * Real.exp (-Real.sqrt (n : ℝ))) * 2 := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right h_e_le_3 h_exp_neg_sqrt_nonneg
            · norm_num
        _ = 6 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    have h_frac_zP : Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)
                     ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_exp_pos : 0 < Real.exp (-(δ * (zPlus : ℝ) / 20)) := Real.exp_pos _
      rw [div_eq_mul_one_div]
      calc Real.exp (-(δ * (zPlus : ℝ) / 20)) * (1 / (1 - δ))
          ≤ Real.exp (-(δ * (zPlus : ℝ) / 20)) * 2 := by
            apply mul_le_mul_of_nonneg_left h_recip_le h_exp_pos.le
        _ ≤ (Real.exp 1 * Real.exp (-Real.sqrt (n : ℝ))) * 2 := by
            apply mul_le_mul_of_nonneg_right h_exp_zP (by norm_num : (0:ℝ) ≤ 2)
        _ ≤ (3 * Real.exp (-Real.sqrt (n : ℝ))) * 2 := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right h_e_le_3 h_exp_neg_sqrt_nonneg
            · norm_num
        _ = 6 * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    have h_exp_n150_bound : Real.exp (-((n : ℝ) / 150))
                             ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) := by
      calc Real.exp (-((n : ℝ) / 150))
          ≤ Real.exp (-Real.sqrt (n : ℝ)) := h_exp_n150
        _ ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) := by linarith
    have h_max_inner : max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                            (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ))
                       ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) := max_le h_frac_zM h_frac_zP
    have h_max_outer : max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                                  (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                              (Real.exp (-((n : ℝ) / 150)))
                       ≤ 6 * Real.exp (-Real.sqrt (n : ℝ)) :=
      max_le h_max_inner h_exp_n150_bound
    have h_max_nn : 0 ≤ max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                                  (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                              (Real.exp (-((n : ℝ) / 150))) := by
      apply le_max_of_le_right; exact (Real.exp_pos _).le
    have h_2pi_minus_2_pos : 0 < 2 * Real.pi - 2 := by
      have : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      linarith
    have h_2pi_minus_2_le : 2 * Real.pi - 2 ≤ 2 * Real.pi := by linarith
    have h_two_pi_le_7 : 2 * Real.pi ≤ 7 := by
      have : Real.pi < 3.15 := Real.pi_lt_d2; linarith
    have h_pi2_pos : 0 < (2 * Real.pi)^2 := by positivity
    have h_2pi_sq_le_49 : (2 * Real.pi)^2 ≤ 49 := by
      nlinarith [h_two_pi_pos, h_two_pi_le_7]
    have h_n_plus_1_le_2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have h_n_plus_1_nn : 0 ≤ (n : ℝ) + 1 := by linarith
    -- Coefficient bound: (n+1)(2π-2)(2π)² / (1-δ)² ≤ 2744 n
    have h_coef_le : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2
                     ≤ 2744 * (n : ℝ) := by
      have h_num_nn : 0 ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 := by
        apply mul_nonneg
        · apply mul_nonneg h_n_plus_1_nn h_2pi_minus_2_pos.le
        · exact h_pi2_pos.le
      have step1 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2
                   ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1/4) := by
        apply div_le_div_of_nonneg_left h_num_nn (by norm_num : (0:ℝ) < 1/4) h_sq_ge
      have step2 : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1/4)
                   = 4 * (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2) := by ring
      rw [step2] at step1
      have h_n_pos' : 0 ≤ (n : ℝ) := h_n_pos.le
      have step3 : 4 * (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2)
                   ≤ 4 * (2 * (n : ℝ) * 7 * 49) := by
        have hh : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2
                  ≤ 2 * (n : ℝ) * 7 * 49 := by
          have h1 : ((n : ℝ) + 1) * (2 * Real.pi - 2) ≤ 2 * (n : ℝ) * 7 := by
            have h11 : ((n : ℝ) + 1) * (2 * Real.pi - 2) ≤ ((n : ℝ) + 1) * (2 * Real.pi) := by
              apply mul_le_mul_of_nonneg_left h_2pi_minus_2_le h_n_plus_1_nn
            have h12 : ((n : ℝ) + 1) * (2 * Real.pi) ≤ 2 * (n : ℝ) * 7 := by
              have h121 : ((n : ℝ) + 1) * (2 * Real.pi) ≤ 2 * (n : ℝ) * (2 * Real.pi) := by
                apply mul_le_mul_of_nonneg_right h_n_plus_1_le_2n h_two_pi_pos.le
              have h122 : 2 * (n : ℝ) * (2 * Real.pi) ≤ 2 * (n : ℝ) * 7 := by
                apply mul_le_mul_of_nonneg_left h_two_pi_le_7
                linarith
              linarith
            linarith
          have h_rhs_nn : 0 ≤ 2 * (n : ℝ) * 7 := by
            apply mul_nonneg (by linarith) (by norm_num : (0:ℝ) ≤ 7)
          calc ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2
              ≤ 2 * (n : ℝ) * 7 * (2 * Real.pi)^2 := by
                apply mul_le_mul_of_nonneg_right h1 h_pi2_pos.le
            _ ≤ 2 * (n : ℝ) * 7 * 49 := by
                apply mul_le_mul_of_nonneg_left h_2pi_sq_le_49 h_rhs_nn
        linarith
      have step4 : 4 * (2 * (n : ℝ) * 7 * 49) = 2744 * (n : ℝ) := by ring
      linarith
    have h_2744n_nn : 0 ≤ 2744 * (n : ℝ) := by
      apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2744) h_n_pos.le
    -- B_exp bound
    have h_Bexp_bound : ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 *
        max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                  (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
              (Real.exp (-((n : ℝ) / 150)))
        ≤ 16464 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
      calc ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 *
            max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                  (Real.exp (-((n : ℝ) / 150)))
          ≤ (2744 * (n : ℝ)) * (6 * Real.exp (-Real.sqrt (n : ℝ))) := by
            apply mul_le_mul h_coef_le h_max_outer h_max_nn h_2744n_nn
        _ = 16464 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by ring
    -- B_Fou bound
    have h_Bfou_bound : 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ))
                        ≤ 784 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_num_nn : 0 ≤ 4 * (2 * Real.pi)^2 := by
        apply mul_nonneg (by norm_num) h_pi2_pos.le
      have step1 : 4 * (2 * Real.pi)^2 / (1 - δ)^2 ≤ 4 * (2 * Real.pi)^2 / (1/4) := by
        apply div_le_div_of_nonneg_left h_num_nn (by norm_num : (0:ℝ) < 1/4) h_sq_ge
      have step2 : 4 * (2 * Real.pi)^2 / (1/4) = 16 * (2 * Real.pi)^2 := by ring
      rw [step2] at step1
      have step3 : 16 * (2 * Real.pi)^2 ≤ 16 * 49 := by
        apply mul_le_mul_of_nonneg_left h_2pi_sq_le_49 (by norm_num)
      have h_chain : 4 * (2 * Real.pi)^2 / (1 - δ)^2 ≤ 784 := by linarith
      calc 4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ))
          ≤ 784 * Real.exp (-Real.sqrt (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_right h_chain h_exp_neg_sqrt_nonneg
        _ ≤ 784 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
            have h_le : (784 : ℝ) ≤ 784 * (n : ℝ) := by linarith
            have h2 : 784 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
                      = (784 * (n : ℝ)) * Real.exp (-Real.sqrt (n : ℝ)) := by ring
            rw [h2]
            apply mul_le_mul_of_nonneg_right h_le h_exp_neg_sqrt_nonneg
    -- Sum bound
    have h_sum_bound : (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi)^2 / (1 - δ)^2 *
        max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                  (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
              (Real.exp (-((n : ℝ) / 150))))
        + (4 * (2 * Real.pi)^2 / (1 - δ)^2 * Real.exp (-Real.sqrt (n : ℝ)))
        ≤ M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
      have h_M_ge : (17248 : ℝ) ≤ M := by rw [hM_def]; norm_num
      have hn_exp_nn : 0 ≤ (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
        apply mul_nonneg h_n_pos.le h_exp_neg_sqrt_nonneg
      have h_step : 17248 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
                    ≤ M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
        have h1 : 17248 * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
                  = 17248 * ((n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by ring
        have h2 : M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
                  = M * ((n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by ring
        rw [h1, h2]
        apply mul_le_mul_of_nonneg_right h_M_ge hn_exp_nn
      linarith
    linarith
  -- Inner bound: ∑_zM ∑_zP |...| ≤ n² · M n exp(-√n)
  have h_inner_bound : ∀ (ℓ : Finset ℕ), ℓ ⊆ Finset.Icc 1 (n / 2) →
      Workspace.Types.AlternatingSumExpression.sameParity ℓ →
      (∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
        ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
          |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
      ≤ (n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by
    intro ℓ hℓ_sub hℓ_par
    have h_Ico_card_le_n : (Finset.Ico (n / 16) (n_h + 1)).card ≤ n := by
      rw [Nat.card_Ico]
      have hh : n_h ≤ n := by rw [hn_h_def]; exact Nat.div_le_self n 2
      omega
    have h_Ico_card_real : ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h_Ico_card_le_n
    -- Apply per-summand bound
    have h_zM_sum :
        ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
        ≤ ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
              M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro zMinus hzM
      apply Finset.sum_le_sum
      intro zPlus hzP
      exact h_per_summand_typical ℓ hℓ_sub hℓ_par zMinus zPlus hzM hzP
    -- Sum-of-constants
    have h_outer_const :
        ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
            M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))
        = ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
          (((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
            (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    rw [h_outer_const] at h_zM_sum
    -- Now bound by n * n * (M n exp)
    have h_M_n_exp_nn : 0 ≤ M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
      apply mul_nonneg
      · apply mul_nonneg hM_pos.le h_n_pos.le
      · exact h_exp_neg_sqrt_nonneg
    have h_card_nn : 0 ≤ ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have h_inner_n : ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
                       (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))
                     ≤ (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_right h_Ico_card_real h_M_n_exp_nn
    have h_inner_n_nn : 0 ≤ (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by
      apply mul_nonneg h_n_pos.le h_M_n_exp_nn
    have h_outer_n : ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
                       ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
                     ≤ (n : ℝ) * ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
      apply mul_le_mul_of_nonneg_right h_Ico_card_real h_inner_n_nn
    have h_chain : ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
              (((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
                (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
            ≤ (n : ℝ) * ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
      calc ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
              (((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
                (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
          ≤ ((Finset.Ico (n / 16) (n_h + 1)).card : ℝ) *
              ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left h_inner_n h_card_nn
        _ ≤ (n : ℝ) * ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := h_outer_n
    have h_eq_assoc : (n : ℝ) * ((n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
                      = (n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by
      ring
    linarith
  -- P_H = P_H'
  have h_PH_eq : P_H = P_H' := by
    apply Finset.ext
    intro ℓ
    rw [hP_H_def, hP_H'_def, hallEll_def]
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hHeavy := HeavyEllCount n hn hmod
  simp only at hHeavy
  have h_PH_card_eq : P_H.card = P_H'.card := by rw [h_PH_eq]
  have h_PH_bound : (P_H.card : ℝ) ≤ (n : ℝ) * Real.exp (Real.sqrt n / 2) := by
    have heq : (P_H.card : ℝ) = (P_H'.card : ℝ) := by exact_mod_cast h_PH_card_eq
    rw [heq]
    convert hHeavy using 2
  -- Outer sum over P_H
  have h_outer_le :
      ∑ ℓ ∈ P_H,
        ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
      ≤ ∑ ℓ ∈ P_H, ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    have hℓ' : ℓ ∈ allEll := by
      rw [hP_H_def] at hℓ
      simp only [Finset.mem_filter] at hℓ
      exact hℓ.1
    rw [hallEll_def] at hℓ'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hℓ'
    exact h_inner_bound ℓ hℓ'.1 hℓ'.2
  have h_sum_const :
      ∑ _ℓ ∈ P_H, ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
      = (P_H.card : ℝ) * ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  rw [h_sum_const] at h_outer_le
  have h_const_nn : 0 ≤ (n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))) := by
    apply mul_nonneg
    · apply mul_nonneg h_n_pos.le h_n_pos.le
    · apply mul_nonneg
      · apply mul_nonneg hM_pos.le h_n_pos.le
      · exact h_exp_neg_sqrt_nonneg
  have h_PH_step : (P_H.card : ℝ) *
                    ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
                  ≤ ((n : ℝ) * Real.exp (Real.sqrt n / 2)) *
                    ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := by
    apply mul_le_mul_of_nonneg_right h_PH_bound h_const_nn
  -- Simplify the RHS
  have h_simplify : ((n : ℝ) * Real.exp (Real.sqrt n / 2)) *
                     ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
                    = M * (n : ℝ)^4 * Real.exp (-(Real.sqrt n / 2)) := by
    have h_exp_combine : Real.exp (Real.sqrt n / 2) * Real.exp (-Real.sqrt (n : ℝ))
                         = Real.exp (-(Real.sqrt n / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_eq : ((n : ℝ) * Real.exp (Real.sqrt n / 2)) *
                  ((n : ℝ) * (n : ℝ) * (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ))))
                = M * (n : ℝ)^4 *
                    (Real.exp (Real.sqrt n / 2) * Real.exp (-Real.sqrt (n : ℝ))) := by ring
    rw [h_eq, h_exp_combine]
  -- Final numerical step: M * n^4 * exp(-√n/2) ≤ (1/4) * exp(-√n/4)
  have h_final : M * (n : ℝ)^4 * Real.exp (-(Real.sqrt n / 2))
                  ≤ (1 : ℝ) / 4 * Real.exp (-(Real.sqrt n / 4)) := by
    have h_sqrtN_div4_nn : 0 ≤ Real.sqrt (n : ℝ) / 4 := by linarith
    -- Use Taylor (√n/4)^14 / 14! ≤ exp(√n/4)
    have h_taylor : (Real.sqrt (n : ℝ) / 4) ^ 14 / (Nat.factorial 14 : ℝ)
                    ≤ Real.exp (Real.sqrt (n : ℝ) / 4) :=
      Real.pow_div_factorial_le_exp _ h_sqrtN_div4_nn 14
    have h_fact14 : (Nat.factorial 14 : ℝ) = 87178291200 := by
      norm_num [Nat.factorial]
    rw [h_fact14] at h_taylor
    have h_pow_eq : (Real.sqrt (n : ℝ) / 4) ^ 14 = (Real.sqrt (n : ℝ))^14 / (4:ℝ)^14 := by
      rw [div_pow]
    have h_sqrt14 : (Real.sqrt (n : ℝ))^14 = (n : ℝ)^7 := by
      have h_sqrt2 : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt h_n_pos.le
      calc (Real.sqrt (n : ℝ))^14 = ((Real.sqrt (n : ℝ))^2)^7 := by ring
        _ = (n : ℝ)^7 := by rw [h_sqrt2]
    rw [h_pow_eq, h_sqrt14] at h_taylor
    have h_4_14 : (4:ℝ)^14 = 268435456 := by norm_num
    rw [h_4_14] at h_taylor
    have h_combine : (n : ℝ)^7 / 268435456 / 87178291200
                     = (n : ℝ)^7 / (268435456 * 87178291200) := by
      rw [div_div]
    rw [h_combine] at h_taylor
    have h_n_cube_ge : (10 : ℝ)^36 ≤ (n : ℝ)^3 := by
      have h1 : ((10 : ℝ)^12)^3 ≤ (n : ℝ)^3 := by
        apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10^12) h_n_ge 3
      have h2 : ((10 : ℝ)^12)^3 = (10 : ℝ)^36 := by ring
      linarith
    have h_4M_n4_bound : 4 * M * (n : ℝ)^4 ≤ (n : ℝ)^7 / (268435456 * 87178291200) := by
      have hM_val : M = 100000 := hM_def
      rw [hM_val]
      have h_const : (4 : ℝ) * 100000 * (268435456 * 87178291200) ≤ 10^36 := by norm_num
      have h_le_n3 : (4 : ℝ) * 100000 * (268435456 * 87178291200) ≤ (n : ℝ)^3 := by linarith
      have h_pos : (0 : ℝ) < 268435456 * 87178291200 := by norm_num
      rw [le_div_iff₀ h_pos]
      have h_n_pow_eq : (n : ℝ)^7 = (n : ℝ)^4 * (n : ℝ)^3 := by ring
      rw [show 4 * (100000 : ℝ) * (n : ℝ)^4 * (268435456 * 87178291200)
              = (n : ℝ)^4 * (4 * 100000 * (268435456 * 87178291200)) from by ring]
      rw [h_n_pow_eq]
      have h_n4_nn : 0 ≤ (n : ℝ)^4 := by positivity
      apply mul_le_mul_of_nonneg_left h_le_n3 h_n4_nn
    have h_4M_le_exp : 4 * M * (n : ℝ)^4 ≤ Real.exp (Real.sqrt (n : ℝ) / 4) := by linarith
    have h_exp_neg_half_pos : 0 < Real.exp (-(Real.sqrt (n : ℝ) / 2)) := Real.exp_pos _
    have h_mult : 4 * M * (n : ℝ)^4 * Real.exp (-(Real.sqrt (n : ℝ) / 2))
                  ≤ Real.exp (Real.sqrt (n : ℝ) / 4) * Real.exp (-(Real.sqrt (n : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_right h_4M_le_exp h_exp_neg_half_pos.le
    have h_exp_combine : Real.exp (Real.sqrt (n : ℝ) / 4) * Real.exp (-(Real.sqrt (n : ℝ) / 2))
                         = Real.exp (-(Real.sqrt (n : ℝ) / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h_exp_combine] at h_mult
    linarith
  -- Combine
  calc ∑ ℓ ∈ P_H,
        ∑ zMinus ∈ Finset.Ico (n / 16) (n_h + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n_h + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
      ≤ (P_H.card : ℝ) * ((n : ℝ) * (n : ℝ) *
            (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := h_outer_le
    _ ≤ ((n : ℝ) * Real.exp (Real.sqrt n / 2)) *
            ((n : ℝ) * (n : ℝ) *
              (M * (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)))) := h_PH_step
    _ = M * (n : ℝ)^4 * Real.exp (-(Real.sqrt n / 2)) := h_simplify
    _ ≤ (1 : ℝ) / 4 * Real.exp (-(Real.sqrt n / 4)) := h_final
