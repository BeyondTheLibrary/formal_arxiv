import Mathlib

theorem SixSqrtThreeMinusEightPos : 6 * Real.sqrt 3 - 8 > 0 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
