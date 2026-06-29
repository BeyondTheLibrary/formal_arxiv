import Mathlib
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.SublemmaFormalGaussianIHExtensionPaper

namespace Workspace.ProofLemmas

/-- §6.1 strengthened IH: a finite signed combination of formal Gaussians with
    possibly-NEGATIVE variances and pairwise-distinct nonzero variances has at
    most `2(k − 1)` real zeros. The Lean `Prop7Induction` is a corollary
    (specialization to the all-`τ_sq i > 0` case after absorbing normalization
    into `a_i`). -/
theorem SublemmaFormalGaussianIHExtension
    (k : ℕ) (hk : 1 ≤ k)
    (a : Fin k → ℝ)
    (μ : Fin k → ℝ)
    (τ_sq : Fin k → ℝ)
    (h_τ_pos : ∀ i : Fin k, 0 < τ_sq i)
    (h_τ_distinct : ∀ i j : Fin k, i ≠ j → τ_sq i ≠ τ_sq j)
    (h_a_nonzero : ∃ i : Fin k, a i ≠ 0) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      (2 * (k - 1)) :=
  Workspace.ProofLemmas.SublemmaFormalGaussianIHExtensionPaper
    k hk a μ τ_sq h_τ_pos h_τ_distinct h_a_nonzero

end Workspace.ProofLemmas
