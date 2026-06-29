-- Cited from: Krantz, S. G. and Parks, H. R. (2002). "A Primer of Real Analytic
--              Functions" (2nd ed.), Birkhäuser. Specifically the classical fact
--              (Chapter 4, on zero sets of real-analytic functions) that the
--              non-simple-zero locus of a real-analytic family of functions
--              depending real-analytically on a one-dimensional parameter is, in
--              the parameter, countable: a real-analytic function of one real
--              variable either vanishes identically or has a discrete (hence
--              countable) zero set, and the non-simple-zero condition for an
--              analytic family `g(x; a) = a · φ(x) + h(x)` reduces to an
--              analytic equation in the parameter via elimination of `x`.
-- Paper label: Classical (Krantz–Parks, "Real Analytic Functions", Ch. 4)
-- NL statement: Let n ≥ 1, fix mean parameters μ : Fin n → ℝ and variance
-- parameters τ : Fin n → ℝ with every τ i ≠ 0, and fix a_rest : Fin (n-1) → ℝ.
-- For a real parameter a_1, define the real-analytic function
--   g(x) = a_1 · exp(-(x - μ₀)² / (2 τ₀)) +
--          Σ_{i : Fin (n-1)} a_rest i · exp(-(x - μ_{i+1})² / (2 τ_{i+1})).
-- Then the set of parameter values a_1 for which g has a non-simple real zero
-- (i.e. some x ∈ ℝ with g(x) = 0 and g'(x) = 0) is countable.

import Mathlib

namespace Workspace.PriorWork

axiom AnalyticParameterFamilySimpleZeroGenericity
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
        ∃ x : ℝ, g x = 0 ∧ deriv g x = 0}

end Workspace.PriorWork
