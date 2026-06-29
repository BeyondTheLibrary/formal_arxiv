import Mathlib

open Real

theorem SharpeningInequalityCheck :
    ∀ (n : ℕ), 1 ≤ n →
      Real.pi * Real.sqrt (n : ℝ) *
          Real.exp (-(Real.sqrt (n : ℝ) * (Real.pi - 1)))
        ≤ 1 - Real.exp (-(Real.sqrt (n : ℝ) * (Real.pi - 1))) := by
  intro n hn
  -- Let s = √n. Then s ≥ 1.
  set s : ℝ := Real.sqrt (n : ℝ) with hs_def
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs_one : 1 ≤ s := by
    rw [hs_def]
    have : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt hn_pos
    simpa using this
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_one
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  -- π > 3, so π - 1 > 2.
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi1 : (2 : ℝ) < Real.pi - 1 := by linarith
  have hpi1_pos : 0 < Real.pi - 1 := by linarith
  have hpi1_nonneg : 0 ≤ Real.pi - 1 := le_of_lt hpi1_pos
  -- Let x = s * (π - 1). Then x ≥ 0.
  set x : ℝ := s * (Real.pi - 1) with hx_def
  have hx_nonneg : 0 ≤ x := mul_nonneg hs_nonneg hpi1_nonneg
  have hx_pos : 0 < x := mul_pos hs_pos hpi1_pos
  -- exp(x) ≥ 1 + x + x²/2
  have hexp : 1 + x + x^2 / 2 ≤ Real.exp x :=
    Real.quadratic_le_exp_of_nonneg hx_nonneg
  -- Note: -x = -(s * (π - 1))
  -- We want to show: π * s * exp(-x) ≤ 1 - exp(-x)
  -- Equivalently (multiplying by exp(x) > 0): π * s ≤ exp(x) - 1
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hexp_neg_pos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  -- Compute exp(-x) * exp(x) = 1
  have hexp_inv : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  -- It suffices to show π * s ≤ exp(x) - 1.
  -- From quadratic bound: exp(x) - 1 ≥ x + x²/2 = s*(π-1) + s²*(π-1)²/2
  -- Need π * s ≤ s*(π-1) + s²*(π-1)²/2
  -- ⟺ s ≤ s²*(π-1)²/2
  -- ⟺ 2 ≤ s*(π-1)²  (divide by s ≥ 1 > 0)
  -- Since s ≥ 1 and (π-1)² > 4, we have s*(π-1)² > 4 > 2.
  -- Step 1: π * s ≤ exp(x) - 1
  have hpi_s_le : Real.pi * s ≤ Real.exp x - 1 := by
    have h1 : Real.pi * s ≤ 1 + x + x^2/2 - 1 := by
      have : 1 + x + x^2/2 - 1 = x + x^2/2 := by ring
      rw [this]
      -- Need: π * s ≤ x + x²/2 = s*(π-1) + s²*(π-1)²/2
      have hx_eq : x = s * (Real.pi - 1) := hx_def
      have hx2 : x^2 = s^2 * (Real.pi - 1)^2 := by rw [hx_eq]; ring
      rw [hx_eq, hx2]
      -- Goal: π * s ≤ s*(π-1) + s²*(π-1)²/2
      -- ⟺ π * s - s*(π-1) ≤ s²*(π-1)²/2
      -- ⟺ s ≤ s²*(π-1)²/2
      -- ⟺ 2 ≤ s*(π-1)²
      have h_pi1_sq : 4 < (Real.pi - 1)^2 := by nlinarith [hpi]
      have h_s_pi1_sq : 4 ≤ s * (Real.pi - 1)^2 := by
        have := mul_le_mul_of_nonneg_right hs_one (sq_nonneg (Real.pi - 1))
        nlinarith [h_pi1_sq, hs_one, sq_nonneg (Real.pi - 1)]
      nlinarith [h_s_pi1_sq, hs_one, hs_pos, hpi1_pos, sq_nonneg (Real.pi - 1), sq_nonneg s, mul_pos hs_pos hpi1_pos]
    linarith [hexp]
  -- Now multiply through by exp(-x).
  -- π * s * exp(-x) ≤ (exp(x) - 1) * exp(-x) = exp(x)*exp(-x) - exp(-x) = 1 - exp(-x)
  have key : Real.pi * s * Real.exp (-x) ≤ (Real.exp x - 1) * Real.exp (-x) := by
    exact mul_le_mul_of_nonneg_right hpi_s_le (le_of_lt hexp_neg_pos)
  have rhs_eq : (Real.exp x - 1) * Real.exp (-x) = 1 - Real.exp (-x) := by
    have hcomm : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    have : (Real.exp x - 1) * Real.exp (-x) = Real.exp x * Real.exp (-x) - Real.exp (-x) := by ring
    rw [this, hcomm]
  rw [rhs_eq] at key
  exact key
