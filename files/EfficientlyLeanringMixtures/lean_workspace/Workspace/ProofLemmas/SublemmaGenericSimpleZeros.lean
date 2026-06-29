import Mathlib
import Workspace.ProofLemmas.SublemmaGenericSimpleZerosPaper

namespace Workspace.ProofLemmas

/-- Paper §6.1 — the set of coefficient perturbations producing a non-simple
    zero of a finite formal Gaussian combination is countable. This is the
    "generic" simple-zeros property used in the first reduction. -/
theorem SublemmaGenericSimpleZeros
    (n : ℕ) (hn : 1 ≤ n)
    (μ τ : Fin n → ℝ)
    (h_τ_ne : ∀ i : Fin n, τ i ≠ 0)
    (a_rest : Fin (n - 1) → ℝ) :
    Set.Countable
      {a_1 : ℝ |
        let g : ℝ → ℝ := fun x =>
          a_1 * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
          + (Finset.univ : Finset (Fin (n - 1))).sum
              (fun i => a_rest i *
                Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                          (2 * τ ⟨i.val + 1, by omega⟩)))
        ∃ x : ℝ, g x = 0 ∧ deriv g x = 0} :=
  Workspace.ProofLemmas.SublemmaGenericSimpleZerosPaper n hn μ τ h_τ_ne a_rest

end Workspace.ProofLemmas
