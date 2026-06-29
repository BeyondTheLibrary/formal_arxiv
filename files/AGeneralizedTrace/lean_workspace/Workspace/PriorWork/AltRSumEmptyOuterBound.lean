-- Outer region split + final numeric reduction for `AltRSumFourierBoundEmpty`
-- (k = 0 / empty-ℓ case of Lemma 8, arXiv:2412.00674v1, §3, lines 369-381).
-- SORRY-FREE.
--
-- Combines:
--   * the OUTER triangle bound `cleanFT_pi_abs_le_outer_modulus_integral`;
--   * the global bound ‖delAtomPairFT(ζ)‖ ≤ 1/(1-δ)² (from the inner integral);
--   * the inner integral bound (decay) ‖delAtomPairFT(π-η)‖ ≤ Cinner for |η| ≤ 1/3;
--   * the binAtom decay e^{-n/73} on |η| ≥ 1/3 / trivial bound 1 on |η| < 1/3,
-- into a POINTWISE outer-integrand bound by the constant
--   Couter := max(e^{-n/73}/(1-δ)², Cinner),
-- whence ‖cleanFT(π)‖ ≤ Couter, and finally a numeric weakening to the axiom RHS.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.DelAtomPairFTContinuity
import Workspace.PriorWork.CleanFTOuterModulusBound
import Workspace.PriorWork.AltRSumEmptyInnerModulusBound
import Workspace.PriorWork.AltRSumEmptyInnerPointwise
import Workspace.PriorWork.AltRSumEmptyAtomBounds

set_option maxHeartbeats 1600000

namespace Workspace.PriorWork.AltRSumEmptyOuterBound

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.DelAtomPairFTContinuity
open Workspace.PriorWork.AltRSumEmptyInnerModulusBound
open Workspace.PriorWork.AltRSumEmptyInnerPointwise
open Workspace.PriorWork.AltRSumEmptyAtomBounds

/-- **Global bound on `delAtomPairFT`.** For every `ζ`,
`‖delAtomPairFT(ζ)‖ ≤ 1/(1-δ)²`. -/
theorem delAtomPairFT_global_le (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (ζ : ℝ) :
    ‖delAtomPairFT n δ zMinus zPlus ζ‖ ≤ (1 / (1 - δ)) ^ 2 := by
  have hD : (0:ℝ) < 1 - δ := by linarith
  have h1 := delAtomPairFT_abs_le_inner_modulus_integral n δ hδ0 hδ1 zMinus zPlus ζ
  have h2 := inner_integral_global_le n δ hδ0 hδ1 zMinus zPlus ζ
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  calc ‖delAtomPairFT n δ zMinus zPlus ζ‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η' in (-Real.pi)..Real.pi,
            ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖ := h1
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * (1 / (1 - δ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = (1 / (1 - δ)) ^ 2 := by field_simp

/-- The outer pointwise bound constant. -/
noncomputable def Couter (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) : ℝ :=
  max (Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2) (Cinner δ zMinus zPlus)

theorem Couter_nonneg (n : ℕ) (δ : ℝ) (hδ1 : δ < 1) (zMinus zPlus : ℕ) :
    0 ≤ Couter n δ zMinus zPlus := by
  unfold Couter
  apply le_max_of_le_right
  exact Cinner_nonneg δ hδ1 zMinus zPlus

/-- **Pointwise outer-integrand bound.** For `n ≥ 1`, `0 < δ ≤ 1/2`, `|η| ≤ π`,
`‖binAtomFT(η)‖ · ‖delAtomPairFT(π-η)‖ ≤ Couter`. -/
theorem outer_integrand_le (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hηπ : |η| ≤ Real.pi) :
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ *
        ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖
      ≤ Couter n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hbin_nn : 0 ≤ ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ := norm_nonneg _
  have hpair_nn : 0 ≤ ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖ := norm_nonneg _
  unfold Couter
  by_cases hcase : 1 / 3 ≤ |η|
  · -- |η| ≥ 1/3 : binAtom decays, delAtomPairFT global
    have hbd : ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) :=
      binAtom_FT_decay n hn η hcase hηπ
    have hpg : ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖ ≤ (1 / (1 - δ)) ^ 2 :=
      delAtomPairFT_global_le n δ hδ0.le hδ1 zMinus zPlus _
    have hexpnn : (0:ℝ) ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) := (Real.exp_pos _).le
    calc ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖
        ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) * (1 / (1 - δ)) ^ 2 :=
          mul_le_mul hbd hpg hpair_nn hexpnn
      _ = Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2 := by
          rw [div_pow, one_pow]; ring
      _ ≤ max (Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2) (Cinner δ zMinus zPlus) :=
          le_max_left _ _
  · -- |η| < 1/3 : binAtom ≤ 1, delAtomPairFT decays via inner integral
    push_neg at hcase
    have hbd : ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ ≤ 1 :=
      binAtom_FT_modulus_le_one n hn η hηπ
    -- ‖delAtomPairFT(π-η)‖ ≤ (1/2π)·(2π·Cinner) = Cinner
    have hηle : |η| ≤ 1 / 3 := le_of_lt hcase
    have h1 := delAtomPairFT_abs_le_inner_modulus_integral n δ hδ0.le hδ1 zMinus zPlus (Real.pi - η)
    have h2 := inner_integral_le n δ hδ0 hδ zMinus zPlus η hηle
    have hCinner_nn : 0 ≤ Cinner δ zMinus zPlus := Cinner_nonneg δ hδ1 zMinus zPlus
    have hpdecay : ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖ ≤ Cinner δ zMinus zPlus := by
      calc ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖
          ≤ (1 / (2 * Real.pi)) *
              ∫ η' in (-Real.pi)..Real.pi,
                ‖delAtom2FT n δ zMinus η'‖ *
                  ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖ := h1
        _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * Cinner δ zMinus zPlus) := by
            apply mul_le_mul_of_nonneg_left h2
            positivity
        _ = Cinner δ zMinus zPlus := by field_simp
    calc ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖
        ≤ 1 * Cinner δ zMinus zPlus := mul_le_mul hbd hpdecay hpair_nn (by norm_num)
      _ = Cinner δ zMinus zPlus := by ring
      _ ≤ max (Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2) (Cinner δ zMinus zPlus) :=
          le_max_right _ _

/-! ### Outer integral bound -/

/-- **Outer integral bound.** `‖cleanFT(π)‖ ≤ Couter`. -/
theorem cleanFT_pi_abs_le_Couter (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) (zMinus zPlus : ℕ) :
    ‖cleanFT n δ zMinus zPlus Real.pi‖ ≤ Couter n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- OUTER triangle bound
  have houter := Workspace.PriorWork.CleanFTOuterModulusBound.cleanFT_pi_abs_le_outer_modulus_integral
    n hn δ hδ0.le hδ1 zMinus zPlus
  -- integrability of the outer integrand
  have hbin_int := binAtom_FT_integrableOn n hn
  have hpair_cont := delAtomPairFT_continuous n δ hδ0.le hδ1 zMinus zPlus
  -- integrand η ↦ ‖binAtomFT η‖ * ‖delAtomPairFT (π - η)‖
  set F : ℝ → ℝ := fun η =>
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ *
      ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖ with hF
  -- F is integrable on [-π,π]: |binAtomFT| integrable, |delAtomPairFT(π-·)| continuous bounded
  have hbinnorm_int : MeasureTheory.IntegrableOn
      (fun η : ℝ => ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖)
      (Set.Icc (-Real.pi) Real.pi) := hbin_int.norm
  have hpairnorm_cont : Continuous
      (fun η => ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖) := by
    apply Continuous.norm
    exact hpair_cont.comp (continuous_const.sub continuous_id)
  have hFint : MeasureTheory.IntegrableOn F (Set.Icc (-Real.pi) Real.pi) := by
    rw [hF]
    exact MeasureTheory.IntegrableOn.mul_continuousOn hbinnorm_int
      hpairnorm_cont.continuousOn isCompact_Icc
  have hFiint : IntervalIntegrable F MeasureTheory.volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ]
    exact hFint
  -- pointwise bound F η ≤ Couter on [-π,π]
  have hpt : ∀ η ∈ Set.Icc (-Real.pi) Real.pi, F η ≤ Couter n δ zMinus zPlus := by
    intro η hη
    rw [Set.mem_Icc] at hη
    have hηπ : |η| ≤ Real.pi := abs_le.mpr ⟨hη.1, hη.2⟩
    rw [hF]
    exact outer_integrand_le n hn δ hδ0 hδ zMinus zPlus η hηπ
  -- integrate
  have hintbound : (∫ η in (-Real.pi)..Real.pi, F η)
      ≤ ∫ _ in (-Real.pi)..Real.pi, Couter n δ zMinus zPlus :=
    intervalIntegral.integral_mono_on hπ hFiint intervalIntegrable_const hpt
  have hconst : (∫ _ in (-Real.pi)..Real.pi, Couter n δ zMinus zPlus)
      = (2 * Real.pi) * Couter n δ zMinus zPlus := by
    rw [intervalIntegral.integral_const, smul_eq_mul,
        show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
  calc ‖cleanFT n δ zMinus zPlus Real.pi‖
      ≤ (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, F η := houter
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * Couter n δ zMinus zPlus) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hconst]; exact hintbound
    _ = Couter n δ zMinus zPlus := by field_simp

/-! ### Final numeric reduction to the axiom RHS -/

/-- The axiom's `M` factor. -/
noncomputable def Maxiom (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) : ℝ :=
  max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
           (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
      (Real.exp (-((n / 2 : ℕ) : ℝ) / 73))

/-- `e^{-δ z/20}` written as `Real.exp (-(δ*z/20))` matches `Real.exp (-δ*z/20)`. -/
theorem exp_neg_form (δ : ℝ) (z : ℕ) :
    Real.exp (- δ * (z : ℝ) / 20) = Real.exp (-(δ * (z : ℝ) / 20)) := by
  congr 1; ring

/-- **Prefactor lower bound.** `1/(1-δ)² ≤ (n+1)(2π-2)(2π)²/(1-δ)²`. -/
theorem prefactor_ge (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ1 : δ < 1) :
    1 / (1 - δ) ^ 2
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 := by
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hD2 : (0:ℝ) < (1 - δ) ^ 2 := by positivity
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  rw [div_le_div_iff_of_pos_right hD2]
  have hn1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hfac1 : (4:ℝ) ≤ 2 * Real.pi - 2 := by linarith
  have hfac2 : (36:ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [hpi]
  have hpos1 : (0:ℝ) ≤ 2 * Real.pi - 2 := by linarith
  have hstep1 : (4:ℝ) ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) := by
    calc (4:ℝ) = 1 * 4 := by ring
      _ ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) := by
          apply mul_le_mul hn1 hfac1 (by norm_num) (by linarith)
  have hstep2 : (4:ℝ) * 36 ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 := by
    apply mul_le_mul hstep1 hfac2 (by norm_num) (by linarith)
  linarith [hstep2]

/-- **`Couter` is bounded by the axiom's main term.** -/
theorem Couter_le_axiom_main (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) :
    Couter n δ zMinus zPlus
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
          Maxiom n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hD1 : 1 - δ ≤ 1 := by linarith
  have hMnn : 0 ≤ Maxiom n δ zMinus zPlus := by
    unfold Maxiom
    apply le_max_of_le_right; positivity
  set P := ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 with hP
  have hPge : 1 / (1 - δ) ^ 2 ≤ P := prefactor_ge n hn δ hδ1
  have hPnn : 0 ≤ P := le_trans (by positivity) hPge
  -- key: 1/(1-δ)² · M ≤ P · M
  have hkey : (1 / (1 - δ) ^ 2) * Maxiom n δ zMinus zPlus ≤ P * Maxiom n δ zMinus zPlus :=
    mul_le_mul_of_nonneg_right hPge hMnn
  unfold Couter
  apply max_le
  · -- A = e^{-(n/2)/73}/(1-δ)² ≤ (1/(1-δ)²)·M ≤ P·M
    have hexp : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) ≤ Maxiom n δ zMinus zPlus := by
      unfold Maxiom
      apply le_max_of_le_right
      exact le_refl _
    have hAstep : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2
        ≤ (1 / (1 - δ) ^ 2) * Maxiom n δ zMinus zPlus := by
      rw [one_div, ← div_eq_inv_mul]
      apply div_le_div_of_nonneg_right hexp (by positivity)
    exact le_trans hAstep hkey
  · -- B = Cinner ≤ (1/(1-δ))·M ≤ (1/(1-δ)²)·M ≤ P·M
    have hCinner_le : Cinner δ zMinus zPlus
        ≤ (1 / (1 - δ)) * Maxiom n δ zMinus zPlus := by
      unfold Cinner
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply max_le
      · unfold Maxiom
        apply le_max_of_le_left
        rw [exp_neg_form] at *
        apply le_max_left
      · unfold Maxiom
        apply le_max_of_le_left
        rw [exp_neg_form] at *
        apply le_max_right
    have hstep2 : (1 / (1 - δ)) * Maxiom n δ zMinus zPlus
        ≤ (1 / (1 - δ) ^ 2) * Maxiom n δ zMinus zPlus := by
      apply mul_le_mul_of_nonneg_right _ hMnn
      rw [div_le_div_iff_of_pos_left (by norm_num) hD (by positivity)]
      nlinarith [hD, hD1]
    exact le_trans hCinner_le (le_trans hstep2 hkey)

/-- **|altRSum(∅)| ≤ Couter.** -/
theorem altRSum_empty_abs_le_Couter (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) (α : ℝ) (zMinus zPlus : ℕ) :
    |altRSum n δ α zMinus zPlus ∅| ≤ Couter n δ zMinus zPlus :=
  le_trans (altRSum_empty_abs_le_FT_modulus n δ α zMinus zPlus)
    (cleanFT_pi_abs_le_Couter n hn δ hδ0 hδ zMinus zPlus)

/-- **MAIN k=0 bound (axiom RHS form).** -/
theorem altRSum_empty_abs_le_axiomRHS (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) (α : ℝ) (zMinus zPlus : ℕ) :
    |altRSum n δ α zMinus zPlus ∅|
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n / 2 : ℕ) : ℝ) / 73)))
          +
          4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt n) := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have h1 := altRSum_empty_abs_le_Couter n hn δ hδ0 hδ α zMinus zPlus
  have h2 := Couter_le_axiom_main n hn δ hδ0 hδ zMinus zPlus
  have hBFou : (0:ℝ) ≤ 4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt n) := by
    positivity
  have hcombined : Couter n δ zMinus zPlus
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            Maxiom n δ zMinus zPlus
          + 4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt n) := by
    linarith [h2, hBFou]
  -- unfold Maxiom into the explicit max form
  have hMeq : Maxiom n δ zMinus zPlus
      = max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                 (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
            (Real.exp (-((n / 2 : ℕ) : ℝ) / 73)) := rfl
  rw [hMeq] at hcombined
  exact le_trans h1 hcombined

end Workspace.PriorWork.AltRSumEmptyOuterBound
