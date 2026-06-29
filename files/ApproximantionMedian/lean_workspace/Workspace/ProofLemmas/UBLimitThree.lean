import Mathlib
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LambdaStarAsymptotic

open Workspace.ProofLemmas.UBDef
open Workspace.ProofLemmas.LambdaStarDef

theorem UBLimitThree :
    Filter.Tendsto UB Filter.atTop (nhds (3 : ℝ)) := by
  have h_lam : Filter.Tendsto lambda_star Filter.atTop (nhds ((1:ℝ)/3)) :=
    LambdaStarAsymptotic
  -- 1 / lambda_star q tends to 1 / (1/3) = 3
  have h_inv : Filter.Tendsto (fun q => 1 / lambda_star q) Filter.atTop (nhds (3 : ℝ)) := by
    have h_ne : ((1:ℝ)/3) ≠ 0 := by norm_num
    have h_div : Filter.Tendsto (fun q => 1 / lambda_star q) Filter.atTop (nhds (1 / ((1:ℝ)/3))) :=
      Filter.Tendsto.div tendsto_const_nhds h_lam h_ne
    have h_eq : (1 : ℝ) / ((1:ℝ)/3) = 3 := by norm_num
    rw [h_eq] at h_div
    exact h_div
  -- UB q = 1 / lambda_star q for q ≥ 1
  apply h_inv.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with q hq
  simp only [UB, if_pos hq]
