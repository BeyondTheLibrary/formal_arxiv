import Mathlib
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.LBConstruction

open Workspace.ProofLemmas.LambdaStarDef Workspace.ProofLemmas.LBConstruction

namespace Workspace.ProofLemmas.LBLambdaStarLtOne

theorem LBLambdaStarLtOne (q : ℝ) (hq : 1 < q) :
    (0 < lambda_star q ∧ lambda_star q < 1) ∧
    (0 < mu q ∧ mu q < 1) ∧
    (0 < 1 - mu q ∧ 1 - mu q < 1) := by
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
  have hq_ne1 : q ≠ 1 := ne_of_gt hq
  -- From LambdaStarDef: 0 < lambda_star q ≤ 1.
  have hLam := (LambdaStarDef.1 q hq_le)
  have hlam_pos : 0 < lambda_star q := hLam.1
  -- Strict < 1 at q > 1, reusing the NormalizedCoreInequality pattern.
  have hlam_lt_one : lambda_star q < 1 := by
    have h_unfold : lambda_star q =
        (1 + (Workspace.ProofLemmas.DeltaStarDef.delta_star q) ^ (q / (q - 1)))
          ^ (-((q - 1) / q)) := by
      unfold lambda_star
      rw [if_neg hq_ne1, if_pos hq]
    have hD_ge_one : 1 ≤ Workspace.ProofLemmas.DeltaStarDef.delta_star q :=
      (Workspace.ProofLemmas.DeltaStarDef.DeltaStarDef q hq).1
    have hD_pos : 0 < Workspace.ProofLemmas.DeltaStarDef.delta_star q :=
      lt_of_lt_of_le one_pos hD_ge_one
    have h_exp1_pos : 0 < q / (q - 1) := div_pos hq_pos hqm1_pos
    have h_dpow_ge_one :
        1 ≤ (Workspace.ProofLemmas.DeltaStarDef.delta_star q) ^ (q / (q - 1)) :=
      Real.one_le_rpow hD_ge_one (le_of_lt h_exp1_pos)
    have h_sum_gt_one :
        1 < 1 + (Workspace.ProofLemmas.DeltaStarDef.delta_star q) ^ (q / (q - 1)) := by
      linarith
    have h_exp2_neg : -((q - 1) / q) < 0 := by
      have hp : 0 < (q - 1) / q := div_pos hqm1_pos hq_pos
      linarith
    rw [h_unfold]
    exact Real.rpow_lt_one_of_one_lt_of_neg h_sum_gt_one h_exp2_neg
  -- mu q = (lambda_star q)^(q/(q-1)) with base in (0,1) and exponent > 0.
  have h_exp_mu_pos : 0 < q / (q - 1) := div_pos hq_pos hqm1_pos
  have hmu_eq : mu q = (lambda_star q) ^ (q / (q - 1)) := rfl
  have hmu_pos : 0 < mu q := by
    rw [hmu_eq]
    exact Real.rpow_pos_of_pos hlam_pos _
  have hmu_lt_one : mu q < 1 := by
    rw [hmu_eq]
    exact Real.rpow_lt_one (le_of_lt hlam_pos) hlam_lt_one h_exp_mu_pos
  exact ⟨⟨hlam_pos, hlam_lt_one⟩, ⟨hmu_pos, hmu_lt_one⟩,
    ⟨by linarith, by linarith⟩⟩

end Workspace.ProofLemmas.LBLambdaStarLtOne
