import Mathlib
import Workspace.ConsistencyDefs

open Workspace.ConsistencyTheorem
open Classical

namespace Workspace.ProofLemmas.CGRelaxedConstraint

/-- **CGRelaxedConstraint** (prediction.tex 48–54, `eq: consistency
relaxed_median_constraint`; consistency analog of `MedianConstraintToSumX`).
Gap (ii).

In the normalized setting (`f j > 0`, `∑ⱼ (fⱼ)² = 1`), with the signature `σ` of
`CGMedianConstraintFromAugment` — so for each coordinate `j` exactly
`(n − ⌊cn⌋)/2` of the original agents have `σⱼ(pᵢ) = +1` — and
`xᵢ := Δ_{S(pᵢ)} = ∑_{j : σⱼ(pᵢ)=1} (fⱼ)²`, one has
`∑_{i∈[n]} xᵢ = (1−c)/2 · n`.

(Proof: swap the order of summation; `∑ᵢ xᵢ = ∑ⱼ (fⱼ)² · #{i : j∈S(pᵢ)}
= ∑ⱼ (fⱼ)² · (n − cn)/2 = (1−c)/2 · n · ∑ⱼ (fⱼ)² = (1−c)/2 · n`.)

We take the per-coordinate balance count as a hypothesis (the conclusion of
`CGMedianConstraintFromAugment`), written real-valued as
`#{i : σⱼ = 1} = (n − ⌊cn⌋)/2`. -/
theorem CGRelaxedConstraint
    {n d : ℕ} (c : ℝ)
    (hcn : (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ))
    (f : Fin d → ℝ) (hf_sum : (∑ j, (f j) ^ (2 : ℝ)) = 1)
    (sigma : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma i j = 1 ∨ sigma i j = -1)
    (hbalance : ∀ j,
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ)
        = ((n : ℝ) - ⌊c * (n : ℝ)⌋₊) / 2) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j => sigma i j = 1),
        (f j) ^ (2 : ℝ))
      = (1 - c) / 2 * (n : ℝ) := by
  classical
  -- Swap the order of summation: ∑ᵢ ∑_{j∈S(pᵢ)} (fⱼ)² = ∑ⱼ (#{i : σⱼ(pᵢ)=1}) · (fⱼ)².
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
  -- Each per-coordinate count equals (n − ⌊cn⌋)/2 by `hbalance`.
  simp_rw [hbalance]
  -- ∑ⱼ ((n − ⌊cn⌋)/2) · (fⱼ)² = (n − ⌊cn⌋)/2 · ∑ⱼ (fⱼ)² = (n − ⌊cn⌋)/2.
  rw [← Finset.mul_sum, hf_sum, mul_one]
  -- Finally `hcn` rewrites ⌊cn⌋ = cn, so (n − cn)/2 = (1 − c)/2 · n.
  rw [hcn]
  ring

end Workspace.ProofLemmas.CGRelaxedConstraint
