import Mathlib
import Workspace.ProofLemmas.DeltaStarDef

open Workspace.ProofLemmas.DeltaStarDef

namespace Workspace.ProofLemmas.LambdaStarDef

noncomputable def lambda_star (q : ℝ) : ℝ :=
  if q = 1 then 1
  else if 1 < q then
    (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q))
  else 1

theorem LambdaStarDef :
    (∀ q : ℝ, 1 ≤ q → 0 < lambda_star q ∧ lambda_star q ≤ 1) ∧ lambda_star 1 = 1 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    by_cases hq1 : q = 1
    · subst hq1
      simp [lambda_star]
    · have hq' : 1 < q := lt_of_le_of_ne hq (Ne.symm hq1)
      have hq_pos : (0 : ℝ) < q := by linarith
      have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
      have hD := DeltaStarDef q hq'
      obtain ⟨hD_ge_one, _⟩ := hD
      have hD_pos : 0 < delta_star q := by linarith
      -- exponent q/(q-1) > 0
      have h_exp1_pos : 0 < q / (q - 1) := div_pos hq_pos hqm1_pos
      -- (delta_star q)^(q/(q-1)) ≥ 1 since delta_star q ≥ 1 and exponent ≥ 0
      have h_dpow_ge_one : 1 ≤ (delta_star q) ^ (q / (q - 1)) :=
        Real.one_le_rpow hD_ge_one (le_of_lt h_exp1_pos)
      -- 1 + (delta_star q)^(q/(q-1)) ≥ 2 > 0
      have h_sum_pos : 0 < 1 + (delta_star q) ^ (q / (q - 1)) := by linarith
      have h_sum_ge_one : 1 ≤ 1 + (delta_star q) ^ (q / (q - 1)) := by linarith
      -- exponent -(q-1)/q
      have h_exp2_nonpos : -((q - 1) / q) ≤ 0 := by
        have : 0 ≤ (q - 1) / q := le_of_lt (div_pos hqm1_pos hq_pos)
        linarith
      -- Now goal: 0 < lambda_star q ∧ lambda_star q ≤ 1
      have h_unfold : lambda_star q =
          (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)) := by
        unfold lambda_star
        rw [if_neg hq1, if_pos hq']
      rw [h_unfold]
      refine ⟨Real.rpow_pos_of_pos h_sum_pos _, ?_⟩
      -- (≥ 1)^(≤ 0) ≤ 1
      have h_le : (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)) ≤
                  (1 + (delta_star q) ^ (q / (q - 1))) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le h_sum_ge_one h_exp2_nonpos
      rw [Real.rpow_zero] at h_le
      exact h_le
  · simp [lambda_star]

end Workspace.ProofLemmas.LambdaStarDef
