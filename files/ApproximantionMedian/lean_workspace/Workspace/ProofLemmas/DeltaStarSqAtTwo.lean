import Mathlib
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.AStarAtTwo

open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.FqHasUniqueInteriorZero

theorem DeltaStarSqAtTwo :
    (delta_star 2) ^ 2 = 6 * Real.sqrt 3 - 9 := by
  have hAStar : a_star 2 = 1 - Real.sqrt 3 / 2 := AStarAtTwo
  -- basic sqrt 3 facts
  have h3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3lt2 : Real.sqrt 3 < 2 := by
    have hh : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]
    linarith
  have h3gt1 : 1 < Real.sqrt 3 := by
    have hh : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at hh
    exact hh
  -- 1 - √3 / 2 > 0 and √3/2 > 0
  have h_a_pos : 0 < 1 - Real.sqrt 3 / 2 := by linarith
  have h_one_minus_a : 1 - (1 - Real.sqrt 3 / 2) = Real.sqrt 3 / 2 := by ring
  have h_one_minus_a_pos : 0 < Real.sqrt 3 / 2 := by linarith
  -- key identity: √(1 - √3/2) = (√3 - 1)/2
  have hkey : Real.sqrt (1 - Real.sqrt 3 / 2) = (Real.sqrt 3 - 1) / 2 := by
    have hnonneg : 0 ≤ (Real.sqrt 3 - 1) / 2 := by linarith
    rw [show (1 - Real.sqrt 3 / 2) = ((Real.sqrt 3 - 1) / 2)^2 by nlinarith [h3sq]]
    exact Real.sqrt_sq hnonneg
  -- unfold delta_star and substitute a_star 2
  unfold delta_star
  rw [hAStar]
  -- Convert rpow ((1:ℝ)/2) to sqrt
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [h_one_minus_a, hkey]
  -- denominator √(√3/2) is positive, with square equal to √3/2
  have hden : Real.sqrt (Real.sqrt 3 / 2) > 0 := Real.sqrt_pos.mpr h_one_minus_a_pos
  have hden_sq : (Real.sqrt (Real.sqrt 3 / 2))^2 = Real.sqrt 3 / 2 :=
    Real.sq_sqrt (le_of_lt h_one_minus_a_pos)
  field_simp
  rw [hden_sq]
  ring_nf
  nlinarith [h3sq, h3pos, sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3)]
