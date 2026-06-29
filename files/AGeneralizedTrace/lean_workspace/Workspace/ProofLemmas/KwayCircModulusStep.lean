import Mathlib
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle
import Workspace.ProofLemmas.KFoldConvolutionTheorem

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# One generalized step of the circular-convolution modulus bound (Lemma 7, step G3)

The k-fold induction of the G3 step needs to bound, at each stage,
`‖circConv F (FT g) ξ‖` where `F = kConv f (m+1)` is itself an *iterated* circular
convolution (NOT literally `FT g₁` of a single function).  The existing
`PerFactorFTEnvelope.circConv_modulus_triangle` only handles the base shape
`circConv (FT g₁) (FT g₂)`; it does not chain through the induction because the
left argument of the convolution is no longer a single Fourier transform.

This file lands the *parametrized* one-step bound that DOES chain: given any
`2π`-periodic, `[-π,π]`-integrable complex function `F`, a **continuous**
`2π`-periodic `G` (the per-factor Fourier transform — continuous because each
factor has finite support), and a **real envelope** `E : ℝ → ℝ`, integrable on
`[-π,π]`, that dominates `‖F‖` pointwise, the modulus of the circular convolution
is bounded by the circular convolution of the envelopes:

  `‖circConv F G ξ‖ ≤ (1/2π) ∫_{-π}^{π} E η · ‖G (ξ-η)‖ dη`.

This is exactly `ModulusOfCircularConvolutionTriangle` followed by a monotone
replacement of `‖F‖` by its dominating envelope `E` under the integral.  It is the
shape the G3 induction iterates: at stage `m+1` the inductive hypothesis supplies
the envelope `E := kModEnv f (m+1) ≥ ‖kConv f (m+1)‖`, and `G := FT (f (m+1))`,
which is continuous by `PerFactorFTEnvelope.FT_continuous_of_finite_support`.

Everything here is sorry-free.  The remaining G3/G4 assembly (defining the
iterated real envelope `kModEnv`, running the induction, and the final
periodisation comparison via `CircularConvolutionAsPeriodisation`) is the part
still left open in `SublemmaFourierKway`.
-/

namespace KwayCircModulusStep

open KFoldConvolutionTheorem

/-- Helper: a continuous `G : ℝ → ℂ` is bounded on the compact interval `[-π, π]`,
so the shifted modulus `η ↦ ‖G (ξ - η)‖` is bounded there. -/
theorem shifted_norm_bdd (G : ℝ → ℂ) (hGcont : Continuous G) (ξ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Set.Icc (-Real.pi) Real.pi, ‖G (ξ - η)‖ ≤ C := by
  -- η ↦ ‖G (ξ - η)‖ is continuous, [-π,π] is compact, so it attains a max.
  have hcont : Continuous (fun η => ‖G (ξ - η)‖) :=
    (hGcont.comp (continuous_const.sub continuous_id)).norm
  obtain ⟨η₀, _, hη₀⟩ :=
    (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_isMaxOn
      (Set.nonempty_Icc.mpr (by linarith [Real.pi_pos])) hcont.continuousOn
  refine ⟨‖G (ξ - η₀)‖, norm_nonneg _, ?_⟩
  intro η hη
  exact hη₀ hη

/-- **Parametrized one-step circular-convolution modulus bound (G3 chaining step).**

For a `2π`-periodic, `[-π,π]`-integrable `F : ℝ → ℂ`, a continuous `2π`-periodic
`G : ℝ → ℂ`, and a real envelope `E`, integrable on `[-π,π]`, with `‖F η‖ ≤ E η`
for all `η`, the modulus of the circular convolution `circConv F G` at `ξ` is
bounded by the circular convolution of `E` and `‖G‖`:

  `‖circConv F G ξ‖ ≤ (1/2π) ∫_{-π}^{π} E η · ‖G (ξ-η)‖ dη`.

Unlike `circConv_modulus_triangle`, the left factor `F` is arbitrary (it need not
be a single `FT g`), so this lemma chains through the k-fold `kConv` recurrence. -/
theorem circConv_modulus_envelope
    (F G : ℝ → ℂ) (E : ℝ → ℝ)
    (hFper : ∀ x, F (x + 2 * Real.pi) = F x)
    (hGper : ∀ x, G (x + 2 * Real.pi) = G x)
    (hFint : MeasureTheory.IntegrableOn F (Set.Icc (-Real.pi) Real.pi))
    (hGcont : Continuous G)
    (hEint : MeasureTheory.IntegrableOn E (Set.Icc (-Real.pi) Real.pi))
    (hEdom : ∀ η, ‖F η‖ ≤ E η)
    (ξ : ℝ) :
    ‖circConv F G ξ‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi, E η * ‖G (ξ - η)‖ := by
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  -- G integrable on [-π, π] (continuous on a compact set).
  have hGint : MeasureTheory.IntegrableOn G (Set.Icc (-Real.pi) Real.pi) :=
    hGcont.continuousOn.integrableOn_compact isCompact_Icc
  -- Step 1: the raw modulus-triangle from the axiom.
  have hax := ModulusOfCircularConvolutionTriangle F G hFper hGper hFint hGint ξ
  -- `circConv F G ξ = (1/(2π) : ℂ) * ∫ …`; bridge the real / complex coefficient.
  have hcirc_eq : circConv F G ξ
      = (1 / (2 * (Real.pi : ℂ))) * ∫ η in (-Real.pi)..Real.pi, F η * G (ξ - η) := by
    unfold circConv
    norm_num
  -- Boundedness of η ↦ ‖G (ξ - η)‖ on [-π, π].
  obtain ⟨C, hC0, hCbd⟩ := shifted_norm_bdd G hGcont ξ
  -- Continuity of η ↦ ‖G (ξ - η)‖.
  have hGshift_cont : Continuous (fun η => ‖G (ξ - η)‖) :=
    (hGcont.comp (continuous_const.sub continuous_id)).norm
  -- IntegrableOn (fun η => ‖F η‖ * ‖G(ξ-η)‖) on [-π,π]:
  -- ‖F‖ is integrable, ‖G(ξ-·)‖ is continuous & bounded by C, so the product is
  -- integrable (bounded measurable factor times integrable).
  have hnormF_int : MeasureTheory.IntegrableOn (fun η => ‖F η‖) (Set.Icc (-Real.pi) Real.pi) :=
    hFint.norm
  have hprodF_int : MeasureTheory.IntegrableOn
      (fun η => ‖F η‖ * ‖G (ξ - η)‖) (Set.Icc (-Real.pi) Real.pi) := by
    apply MeasureTheory.Integrable.mul_bdd (c := C) hnormF_int
    · exact hGshift_cont.aestronglyMeasurable.restrict
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall (fun η hη => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hCbd η hη
  -- IntegrableOn (fun η => E η * ‖G(ξ-η)‖) on [-π,π]: same argument with E in place of ‖F‖.
  have hprodE_int : MeasureTheory.IntegrableOn
      (fun η => E η * ‖G (ξ - η)‖) (Set.Icc (-Real.pi) Real.pi) := by
    apply MeasureTheory.Integrable.mul_bdd (c := C) hEint
    · exact hGshift_cont.aestronglyMeasurable.restrict
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall (fun η hη => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hCbd η hη
  -- Convert IntegrableOn (Icc) to IntervalIntegrable for `integral_mono_on`.
  have hII_F : IntervalIntegrable (fun η => ‖F η‖ * ‖G (ξ - η)‖)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hprodF_int
  have hII_E : IntervalIntegrable (fun η => E η * ‖G (ξ - η)‖)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hprodE_int
  -- Step 2: replace ‖F η‖ by E η under the integral (monotonicity).
  have hmono :
      (∫ η in (-Real.pi)..Real.pi, ‖F η‖ * ‖G (ξ - η)‖)
        ≤ ∫ η in (-Real.pi)..Real.pi, E η * ‖G (ξ - η)‖ := by
    apply intervalIntegral.integral_mono_on (by linarith) hII_F hII_E
    intro η _
    exact mul_le_mul_of_nonneg_right (hEdom η) (norm_nonneg _)
  calc
    ‖circConv F G ξ‖
        ≤ (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, ‖F η‖ * ‖G (ξ - η)‖ := by
          rw [hcirc_eq]
          calc ‖(1 / (2 * (Real.pi : ℂ))) * ∫ η in (-Real.pi)..Real.pi, F η * G (ξ - η)‖
              = ‖(1 / (2 * Real.pi : ℂ)) * ∫ η in (-Real.pi)..Real.pi, F η * G (ξ - η)‖ := by
                norm_num
            _ ≤ _ := hax
      _ ≤ (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, E η * ‖G (ξ - η)‖ := by
          apply mul_le_mul_of_nonneg_left hmono
          positivity

end KwayCircModulusStep
