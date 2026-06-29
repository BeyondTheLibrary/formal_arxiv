import Mathlib

open MeasureTheory Real

/--
**Gaussian integral value.** For every `a ∈ ℝ` with `a > 0`,
`∫_ℝ exp(-a · ξ²) dξ = √(π/a)`.

This is a real-line restatement of `integral_gaussian` (Mathlib).
-/
theorem GaussianIntegralValue :
    ∀ (a : ℝ), 0 < a →
      ∫ (ξ : ℝ), Real.exp (-a * ξ ^ 2) = Real.sqrt (Real.pi / a) := by
  intro a _
  exact integral_gaussian a
