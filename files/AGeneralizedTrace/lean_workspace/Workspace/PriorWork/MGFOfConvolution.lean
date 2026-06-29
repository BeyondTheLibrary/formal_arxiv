-- Cited from: Billingsley, P. (1995). Probability and Measure (3rd ed.). Wiley. Theorem 26.2 (moment generating function of a sum of independent random variables; equivalently, MGF of a convolution).
-- Paper label: Standard MGF-of-convolution identity
-- NL statement: For every pair of non-negative integrable functions f, g : ℝ → ℝ with compact support, and every t ∈ ℝ, ∫_ℝ exp(t·η) · (f * g)(η) dη = (∫_ℝ exp(t·η) · f(η) dη) · (∫_ℝ exp(t·η) · g(η) dη).
import Mathlib

open MeasureTheory Real

/--
**MGF-of-convolution identity.**

For non-negative integrable `f, g : ℝ → ℝ` with compact support, the
moment generating function of the convolution `(f * g)(η) := ∫ y, f y · g (η - y)`
factors:
  `∫ exp(t·η) · (f * g)(η) dη
     = (∫ exp(t·η) · f η dη) · (∫ exp(t·η) · g η dη)`
for every `t ∈ ℝ`.

The compact-support hypothesis is encoded via the existence of `R > 0` such
that `f` and `g` vanish outside `[-R, R]`.
-/
theorem MGFOfConvolution :
    ∀ (f g : ℝ → ℝ),
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      MeasureTheory.Integrable f →
      MeasureTheory.Integrable g →
      (∃ R : ℝ, 0 < R ∧
        (∀ x, |x| > R → f x = 0) ∧
        (∀ x, |x| > R → g x = 0)) →
      ∀ t : ℝ,
        (∫ η, Real.exp (t * η) * (∫ y, f y * g (η - y)))
          = (∫ η, Real.exp (t * η) * f η) *
            (∫ η, Real.exp (t * η) * g η) := by
  intro f g hf0 hg0 hfi hgi hsupp t
  obtain ⟨R, hR, hfR, hgR⟩ := hsupp
  -- Integrability of the (unweighted) convolution integrand on the product.
  have hconv0 : Integrable
      (fun p : ℝ × ℝ => (ContinuousLinearMap.mul ℝ ℝ) (|f| p.2) (|g| (p.1 - p.2)))
      (volume.prod volume) :=
    (hfi.abs).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (hgi.abs)
  have hconv : Integrable
      (fun p : ℝ × ℝ => |f p.2| * |g (p.1 - p.2)|) (volume.prod volume) := by
    simpa [ContinuousLinearMap.mul_apply'] using hconv0
  -- Weighted integrand integrability, via domination by the unweighted one.
  set C : ℝ := Real.exp (|t| * (2 * R)) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have hwint : Integrable
      (fun p : ℝ × ℝ => Real.exp (t * p.1) * (f p.2 * g (p.1 - p.2)))
      (volume.prod volume) := by
    apply Integrable.mono' (g := fun p : ℝ × ℝ => C * (|f p.2| * |g (p.1 - p.2)|))
        (hconv.const_mul C)
    · -- AEStronglyMeasurable of the weighted integrand
      have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp (t * p.1)) (volume.prod volume) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).aestronglyMeasurable
      have hmfg0 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => (ContinuousLinearMap.mul ℝ ℝ) (f p.2) (g (p.1 - p.2)))
          (volume.prod volume) :=
        hfi.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
          hgi.aestronglyMeasurable
      have hmfg : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2))
          (volume.prod volume) := by
        simpa [ContinuousLinearMap.mul_apply'] using hmfg0
      exact hm1.mul hmfg
    · -- the pointwise norm bound
      filter_upwards with p
      rcases eq_or_ne (f p.2) 0 with hfz | hfnz
      · simp [hfz]
      rcases eq_or_ne (g (p.1 - p.2)) 0 with hgz | hgnz
      · simp [hgz]
      -- both nonzero ⇒ |p.2| ≤ R and |p.1 - p.2| ≤ R ⇒ |p.1| ≤ 2R ⇒ exp bound
      have hy : |p.2| ≤ R := by
        by_contra h
        exact hfnz (hfR _ (lt_of_not_ge h))
      have hxy : |p.1 - p.2| ≤ R := by
        by_contra h
        exact hgnz (hgR _ (lt_of_not_ge h))
      have hx : |p.1| ≤ 2 * R := by
        have hsub : |p.1| ≤ |p.1 - p.2| + |p.2| := by
          calc |p.1| = |(p.1 - p.2) + p.2| := by ring_nf
            _ ≤ |p.1 - p.2| + |p.2| := abs_add_le (p.1 - p.2) p.2
        linarith
      have hexp : Real.exp (t * p.1) ≤ C := by
        rw [hC]
        apply Real.exp_le_exp.mpr
        calc t * p.1 ≤ |t * p.1| := le_abs_self _
          _ = |t| * |p.1| := abs_mul _ _
          _ ≤ |t| * (2 * R) := by
              apply mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_right hexp
      positivity
  set Mg : ℝ := ∫ η, Real.exp (t * η) * g η with hMg
  -- Step A: pull exp(t*η) into the inner integral, giving a double integral.
  have stepA : (∫ η, Real.exp (t * η) * (∫ y, f y * g (η - y)))
      = ∫ η, ∫ y, Real.exp (t * η) * (f y * g (η - y)) := by
    apply integral_congr_ae
    filter_upwards with η
    rw [integral_const_mul]
  rw [stepA]
  -- Step B: Fubini swap the order of integration.
  rw [integral_integral_swap hwint]
  -- Step D (as a lemma): the inner η-integral evaluates to exp(t*y) * Mg.
  have stepD : ∀ y : ℝ, (∫ η, Real.exp (t * η) * g (η - y)) = Real.exp (t * y) * Mg := by
    intro y
    have hshift : (∫ η, (fun η => Real.exp (t * η) * g (η - y)) (η + y))
        = ∫ η, (fun η => Real.exp (t * η) * g (η - y)) η :=
      integral_add_right_eq_self (fun η => Real.exp (t * η) * g (η - y)) y
    simp only [add_sub_cancel_right] at hshift
    rw [← hshift]
    have hcongr : (∫ η, Real.exp (t * (η + y)) * g η)
        = ∫ η, Real.exp (t * y) * (Real.exp (t * η) * g η) := by
      apply integral_congr_ae
      filter_upwards with η
      rw [mul_add, Real.exp_add]
      ring
    rw [hcongr, integral_const_mul, hMg]
  -- Step C + E: factor f y, apply Step D, then pull out Mg.
  have stepCE : (∫ y, ∫ η, Real.exp (t * η) * (f y * g (η - y)))
      = ∫ y, (Real.exp (t * y) * f y) * Mg := by
    apply integral_congr_ae
    filter_upwards with y
    have : (∫ η, Real.exp (t * η) * (f y * g (η - y)))
        = f y * ∫ η, Real.exp (t * η) * g (η - y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with η
      ring
    rw [this, stepD y]
    ring
  rw [stepCE, integral_mul_const]
