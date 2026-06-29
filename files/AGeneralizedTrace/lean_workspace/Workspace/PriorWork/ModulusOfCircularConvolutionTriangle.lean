-- Cited from: Folland, G. B. (1999). Real Analysis: Modern Techniques and Their Applications (2nd ed.). Wiley. §6.2 (convolution and Lp spaces) and §8.2 (Fourier series and convolutions on the torus).
-- Paper label: Standard circular-convolution triangle inequality
-- NL statement: For every pair of 2π-periodic integrable functions f, g : ℝ → ℂ and every ξ ∈ ℝ, the circular convolution satisfies |(f ⊛ g)(ξ)| ≤ (|f| ⊛ |g|)(ξ).
import Mathlib

/--
**Triangle (modulus) inequality for circular convolution on `ℝ/(2πℤ)`.**

For `2π`-periodic integrable functions `f, g : ℝ → ℂ`, the circular
convolution
`(f ⊛ g)(ξ) := (1/(2π)) ∫_{-π}^{π} f(η) · g(ξ - η) dη`
satisfies the pointwise modulus bound
`|(f ⊛ g)(ξ)| ≤ (|f| ⊛ |g|)(ξ)`,
where on the right we convolve the moduli `|f|, |g| : ℝ → ℝ` (still
`2π`-periodic, integrable, non-negative).

This is the standard triangle inequality applied inside the integral
defining the circular convolution.
-/
theorem ModulusOfCircularConvolutionTriangle :
    ∀ (f g : ℝ → ℂ),
      (∀ x, f (x + 2 * Real.pi) = f x) →
      (∀ x, g (x + 2 * Real.pi) = g x) →
      MeasureTheory.IntegrableOn f (Set.Icc (-Real.pi) Real.pi) →
      MeasureTheory.IntegrableOn g (Set.Icc (-Real.pi) Real.pi) →
      ∀ ξ : ℝ,
        ‖(1 / (2 * Real.pi : ℂ)) *
            ∫ η in (-Real.pi)..Real.pi, f η * g (ξ - η)‖
          ≤ (1 / (2 * Real.pi)) *
              ∫ η in (-Real.pi)..Real.pi, ‖f η‖ * ‖g (ξ - η)‖ := by
  intro f g hf hg hfint hgint ξ
  have hpi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hle : (-Real.pi) ≤ Real.pi := by
    have := Real.pi_pos; linarith
  rw [norm_mul]
  have hcnorm : ‖(1 / (2 * Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    exact abs_of_nonneg hpi
  rw [hcnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∫ η in (-Real.pi)..Real.pi, f η * g (ξ - η)‖
      ≤ ∫ η in (-Real.pi)..Real.pi, ‖f η * g (ξ - η)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ = ∫ η in (-Real.pi)..Real.pi, ‖f η‖ * ‖g (ξ - η)‖ := by
        simp only [norm_mul]
