import Mathlib

/--
**MGF calibration at √n.** With `c' := 1 / (4 · exp(2) · √(2π))` and
`α := c' · √n`, for every `n ≥ 1`,
`α · √(8π/n) · exp(2) = 1/2`.
-/
theorem MGFCalibrationAtSqrtN :
    ∀ (n : ℕ), 1 ≤ n →
      (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ) *
          Real.sqrt (8 * Real.pi / (n : ℝ)) * Real.exp 2 = 1 / 2 := by
  intro n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h8pi_pos : (0 : ℝ) < 8 * Real.pi := by positivity
  have h8pi_div_n_nonneg : (0 : ℝ) ≤ 8 * Real.pi / (n : ℝ) := by positivity
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have h8pi_nonneg : (0 : ℝ) ≤ 8 * Real.pi := le_of_lt h8pi_pos
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hsqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos 2
  have hexp_ne : Real.exp 2 ≠ 0 := ne_of_gt hexp_pos
  -- Combine √n · √(8π/n) = √(8π)
  have h1 : Real.sqrt (n : ℝ) * Real.sqrt (8 * Real.pi / (n : ℝ)) =
      Real.sqrt (8 * Real.pi) := by
    rw [← Real.sqrt_mul hn_nonneg]
    congr 1
    field_simp
  -- 8π = 4 * (2π), so √(8π) = √4 * √(2π) = 2 * √(2π)
  have h2 : Real.sqrt (8 * Real.pi) = 2 * Real.sqrt (2 * Real.pi) := by
    have : (8 : ℝ) * Real.pi = 4 * (2 * Real.pi) := by ring
    rw [this, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    have : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [this]
  -- Now rewrite the LHS
  calc (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ) *
          Real.sqrt (8 * Real.pi / (n : ℝ)) * Real.exp 2
      = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
          (Real.sqrt (n : ℝ) * Real.sqrt (8 * Real.pi / (n : ℝ))) * Real.exp 2 := by ring
    _ = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
          Real.sqrt (8 * Real.pi) * Real.exp 2 := by rw [h1]
    _ = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
          (2 * Real.sqrt (2 * Real.pi)) * Real.exp 2 := by rw [h2]
    _ = 1 / 2 := by
        field_simp
        ring
