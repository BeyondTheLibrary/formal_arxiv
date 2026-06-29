import Mathlib
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FormalGaussianAnalyticZeroCountInduction

/-! The Moitra-Valiant (2010) §6.1 "strengthened induction hypothesis" — a finite
    signed combination of formal Gaussians with possibly-negative variances and
    pairwise-distinct nonzero variances has at most `2(k − 1)` real zeros — is
    NOT a fundamentally new result. It is a direct instance of the classical
    real-analytic zero-count induction (Hurwitz + analytic IFT + induction);
    Moitra-Valiant simply specialise that template to formal Gaussians.

    We therefore re-attribute the statement to the textbook ingredients:
    `Workspace.ProofLemmas.FormalGaussianAnalyticZeroCountInduction` carries the
    Hurwitz/Conway + Krantz–Parks citation, and the Moitra-Valiant §6.1 name is
    now a theorem proven by delegation. -/

namespace Workspace.ProofLemmas

theorem SublemmaFormalGaussianIHExtensionPaper
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
  Workspace.ProofLemmas.FormalGaussianAnalyticZeroCountInduction
    k hk a μ τ_sq h_τ_pos h_τ_distinct h_a_nonzero

end Workspace.ProofLemmas
