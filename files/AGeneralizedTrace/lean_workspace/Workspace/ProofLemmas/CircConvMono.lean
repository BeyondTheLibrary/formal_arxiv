import Mathlib
import Workspace.ProofLemmas.CircConvInfra

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Monotonicity of the real circular convolution (Lemma 7, step G4 building block)

The G4 step of the paper's Lemma 7 (arXiv:2412.00674v1, lines 331-339) compares the
iterated *circular* convolution envelope `kModEnv` (the k-fold circular convolution
of the per-factor Fourier-transform moduli `‖FT(f j)‖`) against the iterated
circular convolution of a single dominating envelope `e`.  To carry that comparison
through the `kModEnv` recurrence one needs the elementary fact that the real
circular convolution `circConvR` is **monotone** in both arguments when the
functions involved are non-negative.

This file lands that monotonicity, sorry-free:

* `circConvR_mono_right` — fix the (non-negative) left factor `f`; if `g₁ ≤ g₂`
  pointwise (and all functions continuous), then `circConvR f g₁ ξ ≤ circConvR f g₂ ξ`.
* `circConvR_mono_left` — symmetric, fixing the right factor.
* `circConvR_mono` — both factors at once: `f₁ ≤ f₂`, `g₁ ≤ g₂`, all non-negative
  and continuous, gives `circConvR f₁ g₁ ξ ≤ circConvR f₂ g₂ ξ`.

These are the per-step monotonicity facts the G4 induction iterates over the
`kModEnv` recurrence (`kModEnv f (k+2) = circConvR (kModEnv f (k+1)) ‖FT(f (k+1))‖`).
Everything here is proved sorry-free.
-/

namespace CircConvMono

open CircConvInfra

/-- IntervalIntegrability on `[-π, π]` of `η ↦ f η * g (ξ - η)` for continuous `f g`. -/
theorem intIntegrable_circConv_integrand (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (ξ : ℝ) :
    IntervalIntegrable (fun η => f η * g (ξ - η)) MeasureTheory.volume
      (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  exact hf.mul (hg.comp (continuous_const.sub continuous_id))

/-- **Monotonicity of `circConvR` in the RIGHT argument.** For a non-negative
continuous left factor `f` and continuous right factors `g₁ ≤ g₂` *on `[-π, π]`*,
the circular convolution is monotone: `circConvR f g₁ ξ ≤ circConvR f g₂ ξ`.

The pointwise domination is only required on `[-π, π]`, because the integral that
defines `circConvR f g ξ = (1/2π)∫_{-π}^{π} f(η)·g(ξ-η)` only ever samples the
integration variable `η ∈ [-π, π]`. Concretely, `intervalIntegral.integral_mono_on`
needs the integrand comparison only on the integration interval `[-π, π]`, and there
the argument `ξ - η` ranges over `[ξ-π, ξ+π]`; we phrase the hypothesis directly in
terms of the values `g₁ (ξ - η) ≤ g₂ (ξ - η)` for `η ∈ [-π, π]`. -/
theorem circConvR_mono_right (f g₁ g₂ : ℝ → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x) (hf : Continuous f)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (ξ : ℝ)
    (hle : ∀ η ∈ Set.Icc (-Real.pi) Real.pi, g₁ (ξ - η) ≤ g₂ (ξ - η)) :
    circConvR f g₁ ξ ≤ circConvR f g₂ ξ := by
  unfold circConvR
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (intIntegrable_circConv_integrand f g₁ hf hg₁ ξ)
    (intIntegrable_circConv_integrand f g₂ hf hg₂ ξ)
  intro η hη
  exact mul_le_mul_of_nonneg_left (hle η hη) (hf_nn η)

/-- **Monotonicity of `circConvR` in the LEFT argument.** For continuous left
factors `f₁ ≤ f₂` *on `[-π, π]`* and a non-negative continuous right factor `g`,
the circular convolution is monotone: `circConvR f₁ g ξ ≤ circConvR f₂ g ξ`.

As with `circConvR_mono_right`, the pointwise domination `f₁ ≤ f₂` is only required
on the integration interval `[-π, π]`, the only place the defining integral samples
its left argument. -/
theorem circConvR_mono_left (f₁ f₂ g : ℝ → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg_nn : ∀ x, 0 ≤ g x) (hg : Continuous g)
    (hle : ∀ η ∈ Set.Icc (-Real.pi) Real.pi, f₁ η ≤ f₂ η) (ξ : ℝ) :
    circConvR f₁ g ξ ≤ circConvR f₂ g ξ := by
  unfold circConvR
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (intIntegrable_circConv_integrand f₁ g hf₁ hg ξ)
    (intIntegrable_circConv_integrand f₂ g hf₂ hg ξ)
  intro η hη
  exact mul_le_mul_of_nonneg_right (hle η hη) (hg_nn (ξ - η))

/-- **Full monotonicity of `circConvR`.** For non-negative continuous functions
with `f₁ ≤ f₂` *on `[-π, π]`* and `g₁ (ξ - ·) ≤ g₂ (ξ - ·)` *on `[-π, π]`*,
`circConvR f₁ g₁ ξ ≤ circConvR f₂ g₂ ξ`.

Both pointwise dominations are required only at the points the defining integral
`(1/2π)∫_{-π}^{π} f(η)·g(ξ-η)` actually samples: the left factor at `η ∈ [-π, π]`,
the right factor at `ξ - η` for `η ∈ [-π, π]`. -/
theorem circConvR_mono (f₁ f₂ g₁ g₂ : ℝ → ℝ)
    (hf₁_nn : ∀ x, 0 ≤ f₁ x) (hf₂_nn : ∀ x, 0 ≤ f₂ x)
    (hg₁_nn : ∀ x, 0 ≤ g₁ x) (hg₂_nn : ∀ x, 0 ≤ g₂ x)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (ξ : ℝ)
    (hfle : ∀ η ∈ Set.Icc (-Real.pi) Real.pi, f₁ η ≤ f₂ η)
    (hgle : ∀ η ∈ Set.Icc (-Real.pi) Real.pi, g₁ (ξ - η) ≤ g₂ (ξ - η)) :
    circConvR f₁ g₁ ξ ≤ circConvR f₂ g₂ ξ := by
  calc circConvR f₁ g₁ ξ
      ≤ circConvR f₁ g₂ ξ :=
        circConvR_mono_right f₁ g₁ g₂ hf₁_nn hf₁ hg₁ hg₂ ξ hgle
    _ ≤ circConvR f₂ g₂ ξ :=
        circConvR_mono_left f₁ f₂ g₂ hf₁ hf₂ hg₂_nn hg₂ hfle ξ

end CircConvMono
