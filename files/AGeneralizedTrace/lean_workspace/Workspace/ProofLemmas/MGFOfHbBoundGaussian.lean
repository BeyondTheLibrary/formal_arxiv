import Mathlib
import Workspace.ProofLemmas.GaussianCosBound
import Workspace.ProofLemmas.GaussianIntegralValue

open MeasureTheory Real

/--
**MGF of `H_b` bounded by a Gaussian MGF.**

Let `n ≥ 1`, and let
`H_b(ξ) := cos(ξ/2)^n` for `ξ ∈ [-π, π]`, `0` otherwise.
Then for every `t ∈ ℝ`,
`∫_ℝ H_b(ξ) · exp(t · ξ) dξ ≤ √(8π/n) · exp(2 t² / n)`.

The proof combines the pointwise Gaussian cosine bound (`GaussianCosBound`)
with the value of the standard Gaussian integral (`GaussianIntegralValue`).
-/
theorem MGFOfHbBoundGaussian :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (t : ℝ),
        (∫ ξ : ℝ,
            (if |ξ| ≤ Real.pi then (Real.cos (ξ / 2)) ^ n else 0)
              * Real.exp (t * ξ))
          ≤ Real.sqrt (8 * Real.pi / (n : ℝ)) *
              Real.exp (2 * t ^ 2 / (n : ℝ)) := by
  intro n hn t
  -- First, set up positivity facts for n.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := hn
    exact_mod_cast this
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have hn8_pos : (0 : ℝ) < (n : ℝ) / 8 := by positivity
  -- Step 1: pointwise bound on the integrand.
  -- The integrand is `≤ exp(-n·ξ²/8 + t·ξ)`.
  set f : ℝ → ℝ :=
    fun ξ =>
      (if |ξ| ≤ Real.pi then (Real.cos (ξ / 2)) ^ n else 0)
        * Real.exp (t * ξ) with hf_def
  set g : ℝ → ℝ :=
    fun ξ => Real.exp (-((n : ℝ) / 8) * ξ ^ 2 + t * ξ) with hg_def
  have hpw : ∀ ξ : ℝ, f ξ ≤ g ξ := by
    intro ξ
    simp only [hf_def, hg_def]
    by_cases hξ : |ξ| ≤ Real.pi
    · -- on |ξ| ≤ π
      simp only [if_pos hξ]
      -- cos(ξ/2) ≥ 0
      have habs2 : |ξ / 2| ≤ Real.pi / 2 := by
        rw [abs_div]; simp; linarith [hξ]
      have habs2' : -(Real.pi / 2) ≤ ξ / 2 ∧ ξ / 2 ≤ Real.pi / 2 := by
        rw [abs_le] at habs2; exact habs2
      have hcos_nn : 0 ≤ Real.cos (ξ / 2) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [habs2'.1]) habs2'.2
      have hcos_bound : Real.cos (ξ / 2) ≤ Real.exp (-((ξ / 2) ^ 2 / 2)) := by
        apply GaussianCosBound (ξ / 2)
        · linarith [habs2'.1]
        · exact habs2'.2
      -- raise to the n-th power
      have hpow : (Real.cos (ξ / 2)) ^ n ≤
          (Real.exp (-((ξ / 2) ^ 2 / 2))) ^ n :=
        pow_le_pow_left₀ hcos_nn hcos_bound n
      -- exp(...)^n = exp(n * ...)
      have hexp_pow : (Real.exp (-((ξ / 2) ^ 2 / 2))) ^ n =
          Real.exp ((n : ℝ) * (-((ξ / 2) ^ 2 / 2))) := by
        rw [← Real.exp_nat_mul]
      -- Simplify the exponent: n·(-(ξ/2)²/2) = -n·ξ²/8
      have hexp_eq : (n : ℝ) * (-((ξ / 2) ^ 2 / 2)) = -((n : ℝ) / 8) * ξ ^ 2 := by
        ring
      rw [hexp_pow, hexp_eq] at hpow
      -- Now multiply by exp(t·ξ) > 0
      have hexp_t_pos : 0 < Real.exp (t * ξ) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hpow (le_of_lt hexp_t_pos)
      -- exp(-n·ξ²/8) * exp(t·ξ) = exp(-n·ξ²/8 + t·ξ)
      rw [← Real.exp_add] at hmul
      exact hmul
    · -- |ξ| > π: LHS is 0, RHS is positive
      simp only [if_neg hξ, zero_mul]
      exact (Real.exp_pos _).le
  -- Step 2: Integrability of g.
  -- Observe: g(ξ) = exp(-(n/8)·(ξ - 4t/n)² + 2t²/n)
  --        = exp(2t²/n) * exp(-(n/8)·(ξ - 4t/n)²)
  set α : ℝ := (n : ℝ) / 8 with hα_def
  set β : ℝ := 4 * t / (n : ℝ) with hβ_def
  set C : ℝ := 2 * t ^ 2 / (n : ℝ) with hC_def
  have hα_pos : 0 < α := hn8_pos
  have hg_eq : ∀ ξ : ℝ,
      g ξ = Real.exp C * Real.exp (-α * (ξ - β) ^ 2) := by
    intro ξ
    simp only [hg_def, hα_def, hβ_def, hC_def]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  -- Integrability: g is integrable
  have h_int_shifted : Integrable (fun ξ : ℝ => Real.exp (-α * (ξ - β) ^ 2)) := by
    -- shifted Gaussian is integrable
    have h_orig : Integrable (fun ξ : ℝ => Real.exp (-α * ξ ^ 2)) :=
      integrable_exp_neg_mul_sq hα_pos
    -- shift by -β
    have := h_orig.comp_sub_right β
    convert this using 1
  have h_int_g : Integrable g := by
    have : Integrable (fun ξ => Real.exp C * Real.exp (-α * (ξ - β) ^ 2)) :=
      h_int_shifted.const_mul (Real.exp C)
    convert this using 1
    funext ξ
    exact hg_eq ξ
  -- Step 3: Integrability of f.
  have h_int_f : Integrable f := by
    -- f is bounded by g almost everywhere, and f is measurable
    refine Integrable.mono' h_int_g ?_ ?_
    · -- measurability of f
      apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · apply Measurable.ite
        · -- {ξ | |ξ| ≤ π} is measurable
          exact measurableSet_le measurable_norm measurable_const
        · exact (Real.continuous_cos.measurable.comp (measurable_id.div_const 2)).pow_const n
        · exact measurable_const
      · exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
    · -- |f ξ| ≤ g ξ
      refine ae_of_all _ (fun ξ => ?_)
      have hg_pos : 0 < g ξ := by
        simp only [hg_def]; exact Real.exp_pos _
      have hg_nn : 0 ≤ g ξ := le_of_lt hg_pos
      -- f ξ = (if ...) * exp(t·ξ); the if-part is in [0, cos^n] which is in [0,1]; exp(t·ξ) > 0.
      simp only [Real.norm_eq_abs]
      by_cases hξ : |ξ| ≤ Real.pi
      · simp only [hf_def, if_pos hξ]
        have habs2' : -(Real.pi / 2) ≤ ξ / 2 ∧ ξ / 2 ≤ Real.pi / 2 := by
          have habs2 : |ξ / 2| ≤ Real.pi / 2 := by
            rw [abs_div]; simp; linarith [hξ]
          rw [abs_le] at habs2; exact habs2
        have hcos_nn : 0 ≤ Real.cos (ξ / 2) :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le
            (by linarith [habs2'.1]) habs2'.2
        have hcos_pow_nn : 0 ≤ (Real.cos (ξ / 2)) ^ n := pow_nonneg hcos_nn n
        have hexp_pos : 0 ≤ Real.exp (t * ξ) := (Real.exp_pos _).le
        have hf_nn : 0 ≤ (Real.cos (ξ / 2)) ^ n * Real.exp (t * ξ) :=
          mul_nonneg hcos_pow_nn hexp_pos
        rw [abs_of_nonneg hf_nn]
        have := hpw ξ
        simp only [hf_def, hg_def, if_pos hξ] at this
        exact this
      · simp only [hf_def, if_neg hξ, zero_mul, abs_zero]
        exact hg_nn
  -- Step 4: ∫ f ≤ ∫ g.
  have h_mono : (∫ ξ, f ξ) ≤ ∫ ξ, g ξ :=
    integral_mono h_int_f h_int_g hpw
  -- Step 5: Compute ∫ g.
  have h_int_g_eq :
      (∫ ξ, g ξ) = Real.exp C * Real.sqrt (Real.pi / α) := by
    have h1 : (∫ ξ, g ξ) =
        ∫ ξ, Real.exp C * Real.exp (-α * (ξ - β) ^ 2) := by
      apply integral_congr_ae
      refine ae_of_all _ (fun ξ => ?_)
      exact hg_eq ξ
    rw [h1]
    rw [integral_const_mul]
    -- Translation: ∫ exp(-α(ξ - β)²) dξ = ∫ exp(-α ξ²) dξ
    have h_shift :
        (∫ ξ : ℝ, Real.exp (-α * (ξ - β) ^ 2)) =
        ∫ ξ : ℝ, Real.exp (-α * ξ ^ 2) :=
      MeasureTheory.integral_sub_right_eq_self
        (μ := (volume : Measure ℝ))
        (fun ξ : ℝ => Real.exp (-α * ξ ^ 2)) β
    rw [h_shift]
    rw [GaussianIntegralValue α hα_pos]
  -- Step 6: Simplify √(π/α) = √(8π/n).
  have hsqrt_eq : Real.sqrt (Real.pi / α) = Real.sqrt (8 * Real.pi / (n : ℝ)) := by
    congr 1
    simp only [hα_def]
    field_simp
  -- Conclude.
  calc (∫ ξ : ℝ,
            (if |ξ| ≤ Real.pi then (Real.cos (ξ / 2)) ^ n else 0)
              * Real.exp (t * ξ))
      = ∫ ξ, f ξ := by simp only [hf_def]
    _ ≤ ∫ ξ, g ξ := h_mono
    _ = Real.exp C * Real.sqrt (Real.pi / α) := h_int_g_eq
    _ = Real.exp C * Real.sqrt (8 * Real.pi / (n : ℝ)) := by rw [hsqrt_eq]
    _ = Real.sqrt (8 * Real.pi / (n : ℝ)) * Real.exp C := by ring
    _ = Real.sqrt (8 * Real.pi / (n : ℝ)) *
            Real.exp (2 * t ^ 2 / (n : ℝ)) := by simp only [hC_def]
