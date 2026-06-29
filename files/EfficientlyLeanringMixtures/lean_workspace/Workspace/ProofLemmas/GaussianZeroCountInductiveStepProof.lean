import Mathlib
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.PositiveSmallestVarianceInductiveStep

/-!
# GaussianZeroCountInductiveStepProof

The distinct-variance `k → k+1` inductive step of Moitra–Valiant Proposition 7,
assembled from its already-formalized sub-lemmas.  This theorem is intended to
replace the prior-work axiom
`Workspace.PriorWork.GaussianZeroCountInductiveStep` on the live induction path.

## Restriction to positive variances (2026-06-05 pivot)

The live induction path (`Prop7Induction`) only ever instantiates this step with
strictly positive variances (`GaussianPDF.varSq_pos`).  We therefore require
`0 < τ_sq i` (and, in the inductive hypothesis, positivity of the `k`-component
variances).  This avoids the negative-variance "global shift" / "variance
degeneration crossing" Step 8 entirely: with all variances positive we land in
the all-positive regime and conclude directly via
`PositiveSmallestVarianceInductiveStep` (Steps 1–7).
-/

namespace Workspace.ProofLemmas

theorem GaussianZeroCountInductiveStepProof
    (k : ℕ) (hk : 1 ≤ k)
    (IH : ∀ (a' : Fin k → ℝ)
            (μ' : Fin k → ℝ)
            (τ_sq' : Fin k → ℝ),
          (∀ i : Fin k, 0 < τ_sq' i) →
          (∀ i j : Fin k, i ≠ j → τ_sq' i ≠ τ_sq' j) →
          (∃ i : Fin k, a' i ≠ 0) →
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => a' i * Real.exp (-(x - μ' i)^2 / (2 * τ_sq' i))))
            (2 * (k - 1)))
    (a : Fin (k + 1) → ℝ)
    (μ : Fin (k + 1) → ℝ)
    (τ_sq : Fin (k + 1) → ℝ)
    (h_τ_pos : ∀ i : Fin (k + 1), 0 < τ_sq i)
    (h_τ_distinct : ∀ i j : Fin (k + 1), i ≠ j → τ_sq i ≠ τ_sq j)
    (h_a_nonzero : ∃ i : Fin (k + 1), a i ≠ 0) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      (2 * ((k + 1) - 1)) := by
  -- Reduce the exponent `2 * ((k+1) - 1)` to `2 * k`.
  have hexp : 2 * ((k + 1) - 1) = 2 * k := by omega
  rw [hexp]
  -- Nonzero variances follow from positivity.
  have h_τ_nonzero : ∀ i : Fin (k + 1), τ_sq i ≠ 0 := fun i => ne_of_gt (h_τ_pos i)
  -- The all-positive-variance case (Steps 1–7) gives the `≤ 2k` bound directly.
  exact PositiveSmallestVarianceInductiveStep k hk IH a μ τ_sq
    h_τ_nonzero h_τ_distinct h_a_nonzero h_τ_pos

end Workspace.ProofLemmas
