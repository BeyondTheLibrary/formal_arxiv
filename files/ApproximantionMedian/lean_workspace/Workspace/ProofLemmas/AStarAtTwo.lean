import Mathlib
import Workspace.ProofLemmas.FqHasUniqueInteriorZero

open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.FqSignAt0Pos

theorem AStarAtTwo : a_star 2 = 1 - Real.sqrt 3 / 2 := by
  -- Get existence + uniqueness of the interior zero from FqHasUniqueInteriorZero.
  have h := FqHasUniqueInteriorZero 2 one_lt_two
  obtain ⟨hUnique, hStar⟩ := h
  -- Destructure IsAStar 2 (a_star 2): 0 < a_star 2, a_star 2 < 1, F_q 2 (a_star 2) = 0
  obtain ⟨h1, h2, h3⟩ := hStar
  -- Build the algebraic facts about 1 - √3/2.
  set a : ℝ := 1 - Real.sqrt 3 / 2 with ha_def
  -- 0 ≤ √3
  have h_sqrt3_nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  -- √3 < 2 since 3 < 4
  have h_sqrt3_lt_two : Real.sqrt 3 < 2 := by
    have : Real.sqrt 3 < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num] at this
    rw [Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)] at this
    exact this
  -- 1 < √3
  have h_one_lt_sqrt3 : 1 < Real.sqrt 3 := by
    have : Real.sqrt 1 < Real.sqrt 3 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    rwa [Real.sqrt_one] at this
  -- a > 0
  have ha_pos : 0 < a := by
    simp only [ha_def]
    linarith
  -- a < 1
  have ha_lt_one : a < 1 := by
    simp only [ha_def]
    linarith
  -- a = ((√3 - 1)/2)^2
  have h3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  have ha_eq_sq : a = ((Real.sqrt 3 - 1) / 2) ^ 2 := by
    simp only [ha_def]
    field_simp
    ring_nf
    nlinarith [h3_sq]
  -- (√3 - 1)/2 > 0
  have h_half_pos : 0 < (Real.sqrt 3 - 1) / 2 := by linarith
  -- √a = (√3 - 1)/2
  have h_sqrt_a : Real.sqrt a = (Real.sqrt 3 - 1) / 2 := by
    rw [ha_eq_sq]
    rw [Real.sqrt_sq (le_of_lt h_half_pos)]
  -- The exponent (1 - 2)/2 simplifies to -(1/2)
  have h_exp_eq : ((1 - 2) / 2 : ℝ) = -(1/2 : ℝ) := by norm_num
  -- a^(1/2) = √a
  have h_a_half : a ^ ((1:ℝ)/2) = Real.sqrt a := by
    rw [Real.sqrt_eq_rpow]
  -- a^(-1/2) = (a^(1/2))⁻¹
  have h_a_neg_half : a ^ (-(1:ℝ)/2) = (a ^ ((1:ℝ)/2))⁻¹ := by
    rw [show -(1:ℝ)/2 = -(1/2:ℝ) from by ring]
    rw [Real.rpow_neg (le_of_lt ha_pos)]
  -- Combine
  have h_a_pow : a ^ ((1 - 2) / 2 : ℝ) = (Real.sqrt a)⁻¹ := by
    rw [h_exp_eq]
    rw [show -(1/2:ℝ) = -(1:ℝ)/2 from by ring]
    rw [h_a_neg_half, h_a_half]
  -- Compute F_q 2 a = 0
  have hF_zero : F_q 2 a = 0 := by
    unfold F_q
    rw [h_a_pow, h_sqrt_a]
    have h_ne : Real.sqrt 3 - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    nlinarith [h3_sq, h_one_lt_sqrt3, h_sqrt3_lt_two, h_sqrt3_nn]
  -- Use uniqueness to identify a_star 2 with a.
  exact (hUnique.unique
    (show 0 < a_star 2 ∧ a_star 2 < 1 ∧ F_q 2 (a_star 2) = 0 from ⟨h1, h2, h3⟩)
    (show 0 < a ∧ a < 1 ∧ F_q 2 a = 0 from ⟨ha_pos, ha_lt_one, hF_zero⟩))
