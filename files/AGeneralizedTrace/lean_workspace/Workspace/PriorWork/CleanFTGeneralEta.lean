-- General-η version of the k=0 / empty-ℓ outer bound (Lemma 8 region |ζ| < 2,
-- arXiv:2412.00674v1, §3, F24 `hpt` with ζ = π - η). SORRY-FREE.
--
-- Generalizes `AltRSumEmptyOuterBound.cleanFT_pi_abs_le_Couter` from ξ = π to all
-- η in the band [π-2, π+2], using the SAME constant `Couter`. The outer triangle
-- bound and convolution identity are ξ-general; only the pointwise interval
-- arithmetic in the inner/corner decay widens.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.DelAtomPairFTContinuity
import Workspace.PriorWork.CleanFTOuterModulusBound
import Workspace.PriorWork.AltRSumEmptyInnerModulusBound
import Workspace.PriorWork.AltRSumEmptyInnerPointwise
import Workspace.PriorWork.AltRSumEmptyRegionDecay
import Workspace.PriorWork.AltRSumEmptyAtomBounds
import Workspace.PriorWork.AltRSumEmptyOuterBound
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle

set_option maxHeartbeats 1600000

namespace Workspace.PriorWork.CleanFTGeneralEta

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.DelAtomPairFTContinuity
open Workspace.PriorWork.AltRSumEmptyInnerModulusBound
open Workspace.PriorWork.AltRSumEmptyInnerPointwise
open Workspace.PriorWork.AltRSumEmptyRegionDecay
open Workspace.PriorWork.AltRSumEmptyAtomBounds
open Workspace.PriorWork.AltRSumEmptyOuterBound

/-! ### Step A — general-η OUTER triangle modulus bound -/

/-- **OUTER triangle modulus bound on `cleanFT(η)` for any `η`.** Generalizes
`CleanFTOuterModulusBound.cleanFT_pi_abs_le_outer_modulus_integral` from π to all η. -/
theorem cleanFT_abs_le_outer_modulus_integral
    (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zMinus zPlus : ℕ) (η : ℝ) :
    ‖cleanFT n δ zMinus zPlus η‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ t in (-Real.pi)..Real.pi,
            ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ := by
  set f : ℝ → ℂ := fun t : ℝ =>
    ∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))) with hf
  set g : ℝ → ℂ := fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ with hg
  have hconv : cleanFT n δ zMinus zPlus η
      = (1 / (2 * Real.pi : ℂ)) *
          ∫ t in (-Real.pi)..Real.pi, f t * g (η - t) := by
    rw [cleanThreeFactor_FT_eq_conv n δ zMinus zPlus η]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hf, hg]
    unfold delAtomPairFT
    congr 1
    apply tsum_congr
    intro r
    congr 2
    push_cast
    ring
  rw [hconv]
  have hfper : ∀ x, f (x + 2 * Real.pi) = f x := by
    intro x
    simp only [hf]
    exact discreteFT_periodic (fun r : ℤ => ((binAtom n r : ℝ) : ℂ)) x
  have hgper : ∀ x, g (x + 2 * Real.pi) = g x := by
    intro x
    simp only [hg]
    exact delAtomPairFT_periodic n δ zMinus zPlus x
  have hfint : MeasureTheory.IntegrableOn f (Set.Icc (-Real.pi) Real.pi) := by
    simp only [hf]
    exact binAtom_FT_integrableOn n hn
  have hgint : MeasureTheory.IntegrableOn g (Set.Icc (-Real.pi) Real.pi) := by
    simp only [hg]
    exact delAtomPairFT_integrableOn n δ hδ0 hδ1 zMinus zPlus
  exact ModulusOfCircularConvolutionTriangle f g hfper hgper hfint hgint η

/-! ### Step B — WIDER corner decay for delAtom3FT -/

/-- **Wide corner decay for `delAtom3FT`.** If `ζ ∈ [π - 8/3, π + 8/3]`, then
`‖delAtom3FT(ζ)‖ ≤ e^{-δz₊/20}/(1-δ)`. -/
theorem delAtom3FT_corner_decay_wide (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zPlus : ℕ) (ζ : ℝ) (hlo : Real.pi - 8 / 3 ≤ ζ) (hhi : ζ ≤ Real.pi + 8 / 3) :
    ‖delAtom3FT n δ zPlus ζ‖ ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by
  have hδ1 : δ < 1 := by linarith
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  by_cases hc : ζ ≤ Real.pi
  · -- ζ ∈ [π - 8/3, π]; |ζ| = ζ ∈ [π - 8/3, π] ⊆ [1/3, π]
    have hζnonneg : 0 ≤ ζ := by linarith
    have habs : |ζ| = ζ := abs_of_nonneg hζnonneg
    apply delAtom3FT_decay n δ hδ0 hδ zPlus ζ
    · rw [habs]; exact hc
    · rw [habs]; linarith
  · -- ζ ∈ (π, π + 8/3]; shift by -2π: ζ' := ζ - 2π ∈ (-π, 8/3 - π]
    push Not at hc
    have hshift : delAtom3FT n δ zPlus ζ = delAtom3FT n δ zPlus (ζ - 2 * Real.pi) := by
      have := delAtom3FT_periodic n δ zPlus (ζ - 2 * Real.pi)
      rw [show ζ - 2 * Real.pi + 2 * Real.pi = ζ by ring] at this
      exact this
    rw [hshift]
    set ζ' := ζ - 2 * Real.pi with hζ'
    have hζ'neg : ζ' < 0 := by rw [hζ']; linarith
    have habs : |ζ'| = -ζ' := abs_of_neg hζ'neg
    apply delAtom3FT_decay n δ hδ0 hδ zPlus ζ'
    · rw [habs, hζ']; linarith
    · rw [habs, hζ']; linarith

/-! ### Step C — general-η INNER pointwise bound -/

/-- **General-η inner-integrand bound.** For `ζ ∈ [π - 7/3, π + 7/3]` and `|η'| ≤ π`,
`‖delAtom2FT(η')‖ · ‖delAtom3FT(ζ-η')‖ ≤ Cinner`. -/
theorem inner_integrand_le_general (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (ζ : ℝ) (hζlo : Real.pi - 7 / 3 ≤ ζ) (hζhi : ζ ≤ Real.pi + 7 / 3)
    (η' : ℝ) (hη'π : |η'| ≤ Real.pi) :
    ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
      ≤ Cinner δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hM2nn : (0:ℝ) ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) := by positivity
  have hM3nn : (0:ℝ) ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by positivity
  have hDnn : (0:ℝ) ≤ 1 / (1 - δ) := by positivity
  have hn2 : 0 ≤ ‖delAtom2FT n δ zMinus η'‖ := norm_nonneg _
  have hn3 : 0 ≤ ‖delAtom3FT n δ zPlus (ζ - η')‖ := norm_nonneg _
  unfold Cinner
  by_cases hcase : 1 / 3 ≤ |η'|
  · -- |η'| ≥ 1/3 : delAtom2 decays, delAtom3 global
    have hb2 : ‖delAtom2FT n δ zMinus η'‖ ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) :=
      delAtom2FT_decay n δ hδ0 hδ zMinus η' hη'π hcase
    have hb3 : ‖delAtom3FT n δ zPlus (ζ - η')‖ ≤ 1 / (1 - δ) :=
      delAtom3FT_global n δ hδ0.le hδ1 zPlus _
    calc ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
        ≤ (Real.exp (- δ * zMinus / 20) / (1 - δ)) * (1 / (1 - δ)) :=
          mul_le_mul hb2 hb3 hn3 hM2nn
      _ = (1 / (1 - δ)) * (Real.exp (- δ * zMinus / 20) / (1 - δ)) := by ring
      _ ≤ (1 / (1 - δ)) *
            max (Real.exp (- δ * zMinus / 20) / (1 - δ))
                (Real.exp (- δ * zPlus / 20) / (1 - δ)) := by
          apply mul_le_mul_of_nonneg_left (le_max_left _ _) hDnn
  · -- |η'| < 1/3 : delAtom2 global, delAtom3 WIDE corner decay
    push Not at hcase
    have hb2 : ‖delAtom2FT n δ zMinus η'‖ ≤ 1 / (1 - δ) :=
      delAtom2FT_global n δ hδ0.le hδ1 zMinus η'
    -- ζ - η' ∈ [π - 8/3, π + 8/3]
    have hη'b : -(1/3) ≤ η' ∧ η' ≤ 1/3 := abs_le.mp (le_of_lt hcase)
    have hlo : Real.pi - 8 / 3 ≤ ζ - η' := by linarith [hη'b.2]
    have hhi : ζ - η' ≤ Real.pi + 8 / 3 := by linarith [hη'b.1]
    have hb3 : ‖delAtom3FT n δ zPlus (ζ - η')‖
        ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) :=
      delAtom3FT_corner_decay_wide n δ hδ0 hδ zPlus _ hlo hhi
    calc ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
        ≤ (1 / (1 - δ)) * (Real.exp (- δ * zPlus / 20) / (1 - δ)) :=
          mul_le_mul hb2 hb3 hn3 hDnn
      _ ≤ (1 / (1 - δ)) *
            max (Real.exp (- δ * zMinus / 20) / (1 - δ))
                (Real.exp (- δ * zPlus / 20) / (1 - δ)) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _) hDnn

/-! ### Step D — general-η INNER integral bound -/

/-- **General-η inner integral bound.** For `ζ ∈ [π - 7/3, π + 7/3]`,
`∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT(ζ-η')‖ dη' ≤ (2π)·Cinner`. -/
theorem inner_integral_le_general (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (ζ : ℝ) (hζlo : Real.pi - 7 / 3 ≤ ζ) (hζhi : ζ ≤ Real.pi + 7 / 3) :
    (∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖)
      ≤ (2 * Real.pi) * Cinner δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hcont : Continuous (fun η' : ℝ =>
      ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖) := by
    apply Continuous.mul
    · exact (delAtom2FT_continuous n δ hδ0.le hδ1 zMinus).norm
    · apply Continuous.norm
      exact (delAtom3FT_continuous n δ hδ0.le hδ1 zPlus).comp
        (continuous_const.sub continuous_id)
  have hint : IntervalIntegrable
      (fun η' : ℝ => ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hbound : ∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
      ≤ ∫ _ in (-Real.pi)..Real.pi, Cinner δ zMinus zPlus := by
    apply intervalIntegral.integral_mono_on hπ hint (intervalIntegrable_const)
    intro η' hη'
    rw [Set.mem_Icc] at hη'
    have hη'π : |η'| ≤ Real.pi := abs_le.mpr ⟨hη'.1, hη'.2⟩
    exact inner_integrand_le_general n δ hδ0 hδ zMinus zPlus ζ hζlo hζhi η' hη'π
  refine le_trans hbound ?_
  rw [intervalIntegral.integral_const, smul_eq_mul,
      show Real.pi - (-Real.pi) = 2 * Real.pi by ring]

/-! ### Step E — general-η OUTER pointwise bound -/

/-- **General-η pointwise outer-integrand bound.** For `n ≥ 1`, `0 < δ ≤ 1/2`,
`η ∈ [π-2, π+2]`, `|t| ≤ π`,
`‖binAtomFT(t)‖ · ‖delAtomPairFT(η-t)‖ ≤ Couter`. -/
theorem outer_integrand_le_general (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hηlo : Real.pi - 2 ≤ η) (hηhi : η ≤ Real.pi + 2)
    (t : ℝ) (htπ : |t| ≤ Real.pi) :
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ *
        ‖delAtomPairFT n δ zMinus zPlus (η - t)‖
      ≤ Couter n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hbin_nn : 0 ≤ ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ := norm_nonneg _
  have hpair_nn : 0 ≤ ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ := norm_nonneg _
  unfold Couter
  by_cases hcase : 1 / 3 ≤ |t|
  · -- |t| ≥ 1/3 : binAtom decays, delAtomPairFT global
    have hbd : ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) :=
      binAtom_FT_decay n hn t hcase htπ
    have hpg : ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ ≤ (1 / (1 - δ)) ^ 2 :=
      delAtomPairFT_global_le n δ hδ0.le hδ1 zMinus zPlus _
    have hexpnn : (0:ℝ) ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) := (Real.exp_pos _).le
    calc ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus (η - t)‖
        ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) * (1 / (1 - δ)) ^ 2 :=
          mul_le_mul hbd hpg hpair_nn hexpnn
      _ = Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2 := by
          rw [div_pow, one_pow]; ring
      _ ≤ max (Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2) (Cinner δ zMinus zPlus) :=
          le_max_left _ _
  · -- |t| < 1/3 : binAtom ≤ 1, delAtomPairFT decays via inner integral
    push Not at hcase
    have hbd : ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ ≤ 1 :=
      binAtom_FT_modulus_le_one n hn t htπ
    -- ζ := η - t ∈ [π - 7/3, π + 7/3]
    set ζ := η - t with hζdef
    have htb : -(1/3) ≤ t ∧ t ≤ 1/3 := abs_le.mp (le_of_lt hcase)
    have hζlo : Real.pi - 7 / 3 ≤ ζ := by rw [hζdef]; linarith [htb.2]
    have hζhi : ζ ≤ Real.pi + 7 / 3 := by rw [hζdef]; linarith [htb.1]
    have h1 := delAtomPairFT_abs_le_inner_modulus_integral n δ hδ0.le hδ1 zMinus zPlus ζ
    have h2 := inner_integral_le_general n δ hδ0 hδ zMinus zPlus ζ hζlo hζhi
    have hCinner_nn : 0 ≤ Cinner δ zMinus zPlus := Cinner_nonneg δ hδ1 zMinus zPlus
    have hpdecay : ‖delAtomPairFT n δ zMinus zPlus ζ‖ ≤ Cinner δ zMinus zPlus := by
      calc ‖delAtomPairFT n δ zMinus zPlus ζ‖
          ≤ (1 / (2 * Real.pi)) *
              ∫ η' in (-Real.pi)..Real.pi,
                ‖delAtom2FT n δ zMinus η'‖ *
                  ‖delAtom3FT n δ zPlus (ζ - η')‖ := h1
        _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * Cinner δ zMinus zPlus) := by
            apply mul_le_mul_of_nonneg_left h2
            positivity
        _ = Cinner δ zMinus zPlus := by field_simp
    calc ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus ζ‖
        ≤ 1 * Cinner δ zMinus zPlus := mul_le_mul hbd hpdecay hpair_nn (by norm_num)
      _ = Cinner δ zMinus zPlus := by ring
      _ ≤ max (Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2) (Cinner δ zMinus zPlus) :=
          le_max_right _ _

/-! ### Step F — assemble -/

/-- **General-η outer integral bound.** For `η ∈ [π-2, π+2]`,
`‖cleanFT(η)‖ ≤ Couter`. Same constant `Couter` as the π-proof, valid in the band. -/
theorem cleanFT_abs_le_Couter_general
    (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hηlo : Real.pi - 2 ≤ η) (hηhi : η ≤ Real.pi + 2) :
    ‖cleanFT n δ zMinus zPlus η‖
      ≤ Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- OUTER triangle bound (general η)
  have houter := cleanFT_abs_le_outer_modulus_integral n hn δ hδ0.le hδ1 zMinus zPlus η
  -- integrability of the outer integrand
  have hbin_int := binAtom_FT_integrableOn n hn
  have hpair_cont := delAtomPairFT_continuous n δ hδ0.le hδ1 zMinus zPlus
  set F : ℝ → ℝ := fun t =>
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖ *
      ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ with hF
  have hbinnorm_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))))‖)
      (Set.Icc (-Real.pi) Real.pi) := hbin_int.norm
  have hpairnorm_cont : Continuous
      (fun t => ‖delAtomPairFT n δ zMinus zPlus (η - t)‖) := by
    apply Continuous.norm
    exact hpair_cont.comp (continuous_const.sub continuous_id)
  have hFint : MeasureTheory.IntegrableOn F (Set.Icc (-Real.pi) Real.pi) := by
    rw [hF]
    exact MeasureTheory.IntegrableOn.mul_continuousOn hbinnorm_int
      hpairnorm_cont.continuousOn isCompact_Icc
  have hFiint : IntervalIntegrable F MeasureTheory.volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
    exact hFint
  -- pointwise bound F t ≤ Couter on [-π,π]
  have hpt : ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
      F t ≤ Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htπ : |t| ≤ Real.pi := abs_le.mpr ⟨ht.1, ht.2⟩
    rw [hF]
    exact outer_integrand_le_general n hn δ hδ0 hδ zMinus zPlus η hηlo hηhi t htπ
  -- integrate
  have hintbound : (∫ t in (-Real.pi)..Real.pi, F t)
      ≤ ∫ _ in (-Real.pi)..Real.pi,
          Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus :=
    intervalIntegral.integral_mono_on hπ hFiint intervalIntegrable_const hpt
  have hconst : (∫ _ in (-Real.pi)..Real.pi,
        Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus)
      = (2 * Real.pi) * Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus := by
    rw [intervalIntegral.integral_const, smul_eq_mul,
        show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
  calc ‖cleanFT n δ zMinus zPlus η‖
      ≤ (1 / (2 * Real.pi)) * ∫ t in (-Real.pi)..Real.pi, F t := houter
    _ ≤ (1 / (2 * Real.pi)) *
          ((2 * Real.pi) * Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hconst]; exact hintbound
    _ = Workspace.PriorWork.AltRSumEmptyOuterBound.Couter n δ zMinus zPlus := by field_simp

end Workspace.PriorWork.CleanFTGeneralEta
