import Mathlib
import Workspace.ConsistencyDefs

open Workspace.ConsistencyTheorem
open Classical

namespace Workspace.ProofLemmas.RGRelaxedConstraint

theorem RGRelaxedConstraint
    {n d : ℕ} (c : ℝ)
    (hcn : (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ))
    (f : Fin d → ℝ) (hf_sum : (∑ j, (f j) ^ (2 : ℝ)) = 1)
    (sigma : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma i j = 1 ∨ sigma i j = -1)
    (hbalance : ∀ j,
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ)
        = ((n : ℝ) + ⌊c * (n : ℝ)⌋₊) / 2) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j => sigma i j = 1),
        (f j) ^ (2 : ℝ))
      = (1 + c) / 2 * (n : ℝ) := by
  classical
  have step1 :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j => sigma i j = 1),
          (f j) ^ (2 : ℝ)) =
      ∑ i, ∑ j, (if sigma i j = 1 then (f j) ^ (2 : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_filter]
  rw [step1, Finset.sum_comm]
  have step2 : ∀ j : Fin d,
      (∑ i, (if sigma i j = 1 then (f j) ^ (2 : ℝ) else 0)) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ)
        * (f j) ^ (2 : ℝ) := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const]
    ring
  simp_rw [step2]
  simp_rw [hbalance]
  rw [← Finset.mul_sum, hf_sum, mul_one]
  rw [hcn]
  ring

end Workspace.ProofLemmas.RGRelaxedConstraint
