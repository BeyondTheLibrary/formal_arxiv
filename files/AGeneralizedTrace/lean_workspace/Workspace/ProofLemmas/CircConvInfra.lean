import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem

open scoped Real Complex

set_option maxHeartbeats 4000000

namespace CircConvInfra

open KFoldConvolutionTheorem

/-- **L1: `circConv` is continuous.** -/
theorem circConv_continuous (F G : ℝ → ℂ)
    (hFcont : Continuous F) (hGcont : Continuous G) :
    Continuous (fun ξ : ℝ => circConv F G ξ) := by
  simp only [circConv]
  apply Continuous.mul continuous_const
  set f : ℝ → ℝ → ℂ := fun ξ η => F η * G (ξ - η) with hf
  have huncurry : Continuous (Function.uncurry f) := by
    rw [hf]
    unfold Function.uncurry
    apply Continuous.mul
    · exact hFcont.comp continuous_snd
    · exact hGcont.comp (continuous_fst.sub continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    huncurry (-Real.pi) Real.pi

/-- **L2: `circConv` is integrable on `[-π, π]`.** -/
theorem circConv_integrableOn (F G : ℝ → ℂ)
    (hFcont : Continuous F) (hGcont : Continuous G) :
    MeasureTheory.IntegrableOn (fun ξ : ℝ => circConv F G ξ) (Set.Icc (-Real.pi) Real.pi) :=
  (circConv_continuous F G hFcont hGcont).continuousOn.integrableOn_compact isCompact_Icc

/-- **L3: `circConv` is `2π`-periodic if `G` is.** -/
theorem circConv_periodic (F G : ℝ → ℂ)
    (hGper : ∀ x, G (x + 2 * Real.pi) = G x) (ξ : ℝ) :
    circConv F G (ξ + 2 * Real.pi) = circConv F G ξ := by
  unfold circConv
  congr 1
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [show (ξ + 2 * Real.pi - η) = (ξ - η) + 2 * Real.pi by ring, hGper]

/-- Real-valued circular convolution on `ℝ/(2πℤ)` of two functions `f g : ℝ → ℝ`. -/
noncomputable def circConvR (f g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, f η * g (ξ - η)

/-- **L4a: `circConvR` is continuous.** -/
theorem circConvR_continuous (f g : ℝ → ℝ)
    (hfcont : Continuous f) (hgcont : Continuous g) :
    Continuous (fun ξ : ℝ => circConvR f g ξ) := by
  simp only [circConvR]
  apply Continuous.mul continuous_const
  set F : ℝ → ℝ → ℝ := fun ξ η => f η * g (ξ - η) with hF
  have huncurry : Continuous (Function.uncurry F) := by
    rw [hF]
    unfold Function.uncurry
    apply Continuous.mul
    · exact hfcont.comp continuous_snd
    · exact hgcont.comp (continuous_fst.sub continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    huncurry (-Real.pi) Real.pi

/-- **L4b: `circConvR` is integrable on `[-π, π]`.** -/
theorem circConvR_integrableOn (f g : ℝ → ℝ)
    (hfcont : Continuous f) (hgcont : Continuous g) :
    MeasureTheory.IntegrableOn (fun ξ : ℝ => circConvR f g ξ) (Set.Icc (-Real.pi) Real.pi) :=
  (circConvR_continuous f g hfcont hgcont).continuousOn.integrableOn_compact isCompact_Icc

/-- **L4c: `circConvR` is `2π`-periodic if `g` is.** -/
theorem circConvR_periodic (f g : ℝ → ℝ)
    (hgper : ∀ x, g (x + 2 * Real.pi) = g x) (ξ : ℝ) :
    circConvR f g (ξ + 2 * Real.pi) = circConvR f g ξ := by
  unfold circConvR
  congr 1
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [show (ξ + 2 * Real.pi - η) = (ξ - η) + 2 * Real.pi by ring, hgper]

/-- **L4d: `circConvR` of nonnegative functions is nonnegative.** -/
theorem circConvR_nonneg (f g : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (ξ : ℝ) :
    0 ≤ circConvR f g ξ := by
  unfold circConvR
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro η _
  exact mul_nonneg (hf η) (hg _)

end CircConvInfra
