import Mathlib
import Workspace.Types.StirlingAxioms

/--
**Centered binomial pmf maximum bound.** For every `n ∈ ℕ` with `n ≥ 1` and every
`m ∈ ℕ`, the centered binomial pmf with parameter `1/2` satisfies
`bin(n, 1/2, m) := C(n, m) · 2^(-n) ≤ √(2 / (π · n))`.
-/
theorem BinomialPmfMaxBound :
    ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ),
      ((Nat.choose n m : ℝ) * (2 ^ n : ℝ)⁻¹) ≤
        Real.sqrt (2 / (Real.pi * n)) := by
  intro n hn m
  exact Workspace.Types.StirlingAxioms.central_binomial_pmf_upper_bound hn m
