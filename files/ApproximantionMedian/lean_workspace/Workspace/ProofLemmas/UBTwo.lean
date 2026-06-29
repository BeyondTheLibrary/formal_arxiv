import Mathlib
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.DeltaStarSqAtTwo
import Workspace.ProofLemmas.SixSqrtThreeMinusEightPos

open Workspace.ProofLemmas.UBDef
open Workspace.ProofLemmas.LambdaStarDef
open Workspace.ProofLemmas.DeltaStarDef

theorem UBTwo : UB 2 = Real.sqrt (6 * Real.sqrt 3 - 8) := by
  have h1le2 : (1 : ℝ) ≤ 2 := by norm_num
  have h1lt2 : (1 : ℝ) < 2 := by norm_num
  have h2ne1 : (2 : ℝ) ≠ 1 := by norm_num
  have hpos : (0 : ℝ) < 6 * Real.sqrt 3 - 8 := SixSqrtThreeMinusEightPos
  have hd2 : (delta_star 2) ^ 2 = 6 * Real.sqrt 3 - 9 := DeltaStarSqAtTwo
  -- (delta_star 2) ^ ((2:ℝ)/(2-1)) = (delta_star 2)^2 (as real number)
  have hexp : ((2 : ℝ) / (2 - 1)) = (2 : ℕ) := by norm_num
  have h_rpow_eq : (delta_star 2) ^ ((2 : ℝ) / (2 - 1)) = (delta_star 2) ^ 2 := by
    rw [hexp, Real.rpow_natCast]
  -- 1 + (delta_star 2)^(2/(2-1)) = 6 * sqrt 3 - 8
  have h_sum : 1 + (delta_star 2) ^ ((2 : ℝ) / (2 - 1)) = 6 * Real.sqrt 3 - 8 := by
    rw [h_rpow_eq, hd2]; ring
  -- lambda_star 2 = (6*sqrt 3 - 8) ^ (-1/2)
  have h_exponent : -((2 - 1 : ℝ)/2) = -(1/2 : ℝ) := by norm_num
  have h_lambda : lambda_star 2 = (6 * Real.sqrt 3 - 8) ^ (-(1/2 : ℝ)) := by
    unfold lambda_star
    rw [if_neg h2ne1, if_pos h1lt2, h_sum, h_exponent]
  -- UB 2 = 1 / lambda_star 2
  have h_UB : UB 2 = 1 / lambda_star 2 := by
    unfold UB
    rw [if_pos h1le2]
  rw [h_UB, h_lambda]
  -- 1 / x^(-1/2) = sqrt(x)
  rw [Real.rpow_neg (le_of_lt hpos), one_div, inv_inv, ← Real.sqrt_eq_rpow]
