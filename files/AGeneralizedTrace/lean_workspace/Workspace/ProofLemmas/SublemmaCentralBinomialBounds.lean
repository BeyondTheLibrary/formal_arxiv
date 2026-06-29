import Workspace.Types.StirlingAxioms
import Mathlib

/-!
# Central Binomial Bounds (Sublemma)

For every `n ≥ 1`, the central binomial pmf `bin(n, 1/2, i) := C(n,i) * 2^(-n)`
satisfies the two-sided bound:

* (a) `bin(n, 1/2, i) ≤ √(2 / (π · n))` for every `i`;
* (b) `bin(n, 1/2, n/2) ≥ 1 / (2 √n)`,
  equivalently `C(n, n/2) ≥ 2^n / (2 √n)`.

Both are corollaries of Stirling's formula bounds.
-/

namespace Workspace.ProofLemmas

theorem SublemmaCentralBinomialBounds :
    ∀ n : ℕ, 1 ≤ n →
      (∀ i : ℕ,
          ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤
            Real.sqrt (2 / (Real.pi * n))) ∧
        ((Nat.choose n (n / 2) : ℝ) * (2 ^ n : ℝ)⁻¹ ≥
          1 / (2 * Real.sqrt n)) := by
  intro n hn
  refine ⟨?_, ?_⟩
  · intro i
    exact Workspace.Types.StirlingAxioms.central_binomial_pmf_upper_bound hn i
  · exact Workspace.Types.StirlingAxioms.central_binomial_pmf_lower_bound hn

end Workspace.ProofLemmas
