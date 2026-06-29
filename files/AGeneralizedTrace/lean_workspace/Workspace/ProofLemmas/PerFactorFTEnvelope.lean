import Mathlib
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.PerFactorFourierModulus
import Workspace.ProofLemmas.PerFactorFTModulus
import Workspace.ProofLemmas.KwayFactorSummable

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Per-factor Fourier-transform envelope facts (paper Lemma 7, step G3)

This file lands the *structural* G3 building blocks needed to apply the
circular-convolution modulus-triangle inequality
(`ModulusOfCircularConvolutionTriangle`) to the per-factor Fourier transforms of
the k-way product in `SublemmaFourierKway`.

The two facts the modulus-triangle axiom requires of each Fourier transform are:

* **2π-periodicity** — true of *every* discrete Fourier transform on `ℤ`, since
  `e^{-i(η+2π)r} = e^{-iηr}` for integer `r`.  Proved here for an arbitrary
  `f : ℤ → ℂ` (`FT_periodic`), hence in particular for `FT (binAtom …)` and for
  the per-factor / partial-product Fourier transforms.

* **Integrability on `[-π, π]`** — true of `FT (g)` whenever `g` has *finite
  support* on `ℤ`, because then `FT (g)` is a finite sum of continuous functions,
  hence continuous, hence integrable on the compact interval.  Proved here for
  any finitely-supported `g` (`FT_integrableOn_of_finite_support`), and
  specialised to the binomial atom (`FT_binAtom_integrableOn`) and to the
  per-factor function (`FT_factor_integrableOn`), both of which have finite
  support.

Combining the two, we obtain the concrete one-step modulus-triangle bound for the
circular convolution of two per-factor Fourier transforms
(`circConv_modulus_triangle`), which is the exact shape consumed by the k-fold
induction of the G3 step.

Everything in this file is proved sorry-free.
-/

namespace PerFactorFTEnvelope

open KFoldConvolutionTheorem
open PerFactorFourierModulus
open PerFactorFTModulus
open KwayFactorSummable

/-! ### 2π-periodicity of any discrete Fourier transform on `ℤ`. -/

/-- The single Fourier mode `r ↦ e^{-iηr}` is `2π`-periodic in `η` for every fixed
integer `r`, because `e^{-2πir} = 1`. -/
theorem exp_mode_periodic (η : ℝ) (r : ℤ) :
    Complex.exp (-(Complex.I * ((η + 2 * Real.pi : ℝ) : ℂ) * (r : ℂ)))
      = Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))) := by
  have h2pi : Complex.exp (-(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))) = 1 := by
    rw [show -(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))
          = (((-r : ℤ) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
  rw [show -(Complex.I * ((η + 2 * Real.pi : ℝ) : ℂ) * (r : ℂ))
        = -(Complex.I * (η : ℂ) * (r : ℂ)) + (-(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))) by
        push_cast; ring]
  rw [Complex.exp_add, h2pi, mul_one]

/-- **Every discrete Fourier transform on `ℤ` is `2π`-periodic.** This is one of
the two hypotheses `ModulusOfCircularConvolutionTriangle` needs of each factor. -/
theorem FT_periodic (f : ℤ → ℂ) (η : ℝ) :
    FT f (η + 2 * Real.pi) = FT f η := by
  unfold FT
  apply tsum_congr
  intro r
  rw [exp_mode_periodic η r]

/-! ### Integrability on `[-π, π]` of the FT of a finitely-supported function. -/

/-- The discrete Fourier transform of a finitely-supported `g : ℤ → ℂ` is a
**finite sum** of Fourier modes: `FT g η = ∑_{r ∈ s} g r · e^{-iηr}` whenever the
support of `g` is contained in the finite set `s`. -/
theorem FT_eq_finsum_of_support (g : ℤ → ℂ) (s : Finset ℤ)
    (hsupp : ∀ r : ℤ, g r ≠ 0 → r ∈ s) (η : ℝ) :
    FT g η = ∑ r ∈ s, g r * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))) := by
  unfold FT
  apply tsum_eq_sum
  intro r hr
  have hg0 : g r = 0 := by
    by_contra h
    exact hr (hsupp r h)
  rw [hg0, zero_mul]

/-- The FT of a finitely-supported function is a **continuous** function of `η`
(a finite sum of continuous modes). -/
theorem FT_continuous_of_finite_support (g : ℤ → ℂ) (s : Finset ℤ)
    (hsupp : ∀ r : ℤ, g r ≠ 0 → r ∈ s) :
    Continuous (fun η : ℝ => FT g η) := by
  have heq : (fun η : ℝ => FT g η)
      = (fun η : ℝ => ∑ r ∈ s, g r * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))) := by
    funext η
    exact FT_eq_finsum_of_support g s hsupp η
  rw [heq]
  apply continuous_finset_sum
  intro r _
  apply continuous_const.mul
  apply Complex.continuous_exp.comp
  apply Continuous.neg
  apply Continuous.mul
  · exact (continuous_const.mul Complex.continuous_ofReal)
  · exact continuous_const

/-- **Integrability on `[-π, π]` of the FT of a finitely-supported function.**
The other hypothesis `ModulusOfCircularConvolutionTriangle` needs. -/
theorem FT_integrableOn_of_finite_support (g : ℤ → ℂ) (s : Finset ℤ)
    (hsupp : ∀ r : ℤ, g r ≠ 0 → r ∈ s) :
    MeasureTheory.IntegrableOn (fun η : ℝ => FT g η) (Set.Icc (-Real.pi) Real.pi) :=
  (FT_continuous_of_finite_support g s hsupp).continuousOn.integrableOn_compact isCompact_Icc

/-! ### Specialisation to the binomial atom and to the per-factor function. -/

/-- The complex-cast binomial atom `r ↦ (binAtom n ℓj r : ℂ)` has finite support:
it vanishes off `Finset.Icc (-c) (n - c)` with `c = (n-1)/4 + ℓj`. -/
theorem binAtomC_support (n : ℕ) (ℓj : ℕ) (r : ℤ)
    (hr : ((binAtom n ℓj r : ℝ) : ℂ) ≠ 0) :
    r ∈ Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                   ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) := by
  by_contra hmem
  apply hr
  -- off the support interval, binAtom = 0.
  have hz : binAtom n ℓj r = 0 := by
    show (if 0 ≤ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
              ∧ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ) ≤ (n : ℤ)
           then ((Nat.choose n (r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)).toNat : ℝ)
                   * (2 ^ n : ℝ)⁻¹)
           else 0) = 0
    rw [if_neg]
    rw [Finset.mem_Icc, not_and_or] at hmem
    rintro ⟨h1, h2⟩
    rcases hmem with hlo | hhi
    · omega
    · omega
  rw [hz, Complex.ofReal_zero]

/-- `FT (binAtom n ℓj ·)` is `2π`-periodic. -/
theorem FT_binAtom_periodic (n : ℕ) (ℓj : ℕ) (η : ℝ) :
    FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) (η + 2 * Real.pi)
      = FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η :=
  FT_periodic _ η

/-- `FT (binAtom n ℓj ·)` is integrable on `[-π, π]` (finite support). -/
theorem FT_binAtom_integrableOn (n : ℕ) (ℓj : ℕ) :
    MeasureTheory.IntegrableOn
      (fun η : ℝ => FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η)
      (Set.Icc (-Real.pi) Real.pi) :=
  FT_integrableOn_of_finite_support _ _ (binAtomC_support n ℓj)

/-- The complex per-factor function `r ↦ (factor n ℓj r : ℂ)` has finite support
(off the support interval `factor = 0`). -/
theorem factorC_support (n : ℕ) (ℓj : ℕ) (r : ℤ)
    (hr : ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ) ≠ 0) :
    r ∈ Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                   ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) := by
  by_contra hmem
  apply hr
  rw [KwayFactorSummable.factor_off_Icc_zero n ℓj r hmem, Complex.ofReal_zero]

/-- `FT (factor n ℓj ·)` is `2π`-periodic. -/
theorem FT_factor_periodic (n : ℕ) (ℓj : ℕ) (η : ℝ) :
    FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) (η + 2 * Real.pi)
      = FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) η :=
  FT_periodic _ η

/-- `FT (factor n ℓj ·)` is integrable on `[-π, π]` (finite support). -/
theorem FT_factor_integrableOn (n : ℕ) (ℓj : ℕ) :
    MeasureTheory.IntegrableOn
      (fun η : ℝ => FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) η)
      (Set.Icc (-Real.pi) Real.pi) :=
  FT_integrableOn_of_finite_support _ _ (factorC_support n ℓj)

/-! ### The one-step circular-convolution modulus-triangle bound (G3 step). -/

/-- **One step of the G3 modulus-triangle bound.** For any two finitely-supported
functions `g₁ g₂ : ℤ → ℂ`, the modulus of the circular convolution of their
Fourier transforms is bounded by the circular convolution of the moduli:

  `‖circConv (FT g₁) (FT g₂) ξ‖ ≤ (1/2π) ∫_{-π}^{π} ‖FT g₁ η‖ · ‖FT g₂ (ξ-η)‖`.

This is exactly `ModulusOfCircularConvolutionTriangle` with its two hypotheses
(`2π`-periodicity, `[-π,π]`-integrability) discharged via `FT_periodic` and
`FT_integrableOn_of_finite_support`.  It is the building block the k-fold
induction of the G3 step iterates over the `kConv` recurrence. -/
theorem circConv_modulus_triangle (g₁ g₂ : ℤ → ℂ) (s₁ s₂ : Finset ℤ)
    (hs₁ : ∀ r : ℤ, g₁ r ≠ 0 → r ∈ s₁) (hs₂ : ∀ r : ℤ, g₂ r ≠ 0 → r ∈ s₂)
    (ξ : ℝ) :
    ‖circConv (FT g₁) (FT g₂) ξ‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi, ‖FT g₁ η‖ * ‖FT g₂ (ξ - η)‖ := by
  have hper₁ : ∀ x, FT g₁ (x + 2 * Real.pi) = FT g₁ x := fun x => FT_periodic g₁ x
  have hper₂ : ∀ x, FT g₂ (x + 2 * Real.pi) = FT g₂ x := fun x => FT_periodic g₂ x
  have hint₁ := FT_integrableOn_of_finite_support g₁ s₁ hs₁
  have hint₂ := FT_integrableOn_of_finite_support g₂ s₂ hs₂
  have hax := ModulusOfCircularConvolutionTriangle (FT g₁) (FT g₂) hper₁ hper₂
    hint₁ hint₂ ξ
  -- `circConv` is `(1/(2π)) * ∫ …`; the axiom uses the ℂ-cast `(1/(2π) : ℂ)`.
  unfold circConv
  -- Bridge the real `1/(2π)` and the complex `(1/(2π) : ℂ)` coefficient.
  have hcoef : ((1 : ℂ) / (2 * (Real.pi : ℂ)))
      = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast; ring
  calc
    ‖(1 / (2 * Real.pi) : ℂ) * ∫ η in (-Real.pi)..Real.pi, FT g₁ η * FT g₂ (ξ - η)‖
        = ‖(1 / (2 * (Real.pi : ℂ))) *
            ∫ η in (-Real.pi)..Real.pi, FT g₁ η * FT g₂ (ξ - η)‖ := by
          norm_num
      _ ≤ (1 / (2 * Real.pi)) *
            ∫ η in (-Real.pi)..Real.pi, ‖FT g₁ η‖ * ‖FT g₂ (ξ - η)‖ := hax

end PerFactorFTEnvelope
