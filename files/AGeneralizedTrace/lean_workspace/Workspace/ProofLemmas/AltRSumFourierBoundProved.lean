-- DE-AXIOMATIZATION of `AltRSumFourierBound` (k ≥ 1 case), Lemma 8 of
-- Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, lines 362-382.
--
-- This file discharges the region-split integrand hypothesis `hpt` of
-- `AltRSumKwayRegionSplit.altRSum_fourier_bound_of_region_split` using
--   * the now-proved Lemma 7 (`SublemmaFourierKway`), wrapped by
--     `AltRSumKwayFourierBridge.kwayFactor_fourier_tail_bound` (the k-way factor
--     FT modulus ≤ 2 e^{-√n} on `2 ≤ |ζ| ≤ π`),
--   * the general-η outer (3-binom) modulus bound `CleanFTGeneralEta`
--     (`‖cleanFT η‖ ≤ Couter` on the band `[π-2, π+2]`),
--   * a GLOBAL `‖cleanFT η‖ ≤ 1/(1-δ)²` bound (proved here, mirroring
--     `delAtomPairFT_global_le`),
--   * the trivial k-way ℓ¹ bound `‖kwayFT ζ‖ ≤ n+1` (proved here from
--     `T4L1NormBound`'s `kwayProd ∈ [0,1]` + `∑ kwayProd ≤ n+1`),
--   * a tighter `Couter ≤ (2π-2)(2π)²/(1-δ)²·M` bound (proved here),
-- producing the EXACT RHS of the axiom `AltRSumFourierBound`, sorry-free.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumKwayRegionSplit
import Workspace.PriorWork.AltRSumKwayFourierBridge
import Workspace.PriorWork.CleanFTGeneralEta
import Workspace.PriorWork.AltRSumEmptyOuterBound
import Workspace.ProofLemmas.T4L1NormBound

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.AltRSumFourierBoundProved

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.AltRSumEmptyFourierBridge
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumFourierBoundKway
open Workspace.PriorWork.AltRSumKwayRegionSplit
open Workspace.PriorWork.AltRSumEmptyOuterBound
open Workspace.PriorWork.DelAtomPairFTContinuity
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.AltRSumEmptyInnerPointwise
open Workspace.PriorWork.AltRSumKwayFourierBridge

/-! ### (A) Global modulus bound on `cleanFT` (mirrors `delAtomPairFT_global_le`). -/

/-- **Global bound on `cleanFT`.** For every `η`, `‖cleanFT η‖ ≤ (1/(1-δ))^2`.
Via `cleanThreeFactor_FT_eq_conv` + `binAtom_FT_modulus_le_one` (on `[-π,π]`) +
`delAtomPairFT_global_le`. -/
theorem cleanFT_global_le (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (η : ℝ) :
    ‖cleanFT n δ zMinus zPlus η‖ ≤ (1 / (1 - δ)) ^ 2 := by
  have hD : (0:ℝ) < 1 - δ := by linarith
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  set f : ℝ → ℂ := fun t : ℝ =>
    ∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (r : ℂ))) with hf
  -- cleanFT η = (1/2π) ∫ f t · delAtomPairFT (η - t)
  have hconv : cleanFT n δ zMinus zPlus η
      = (1 / (2 * Real.pi : ℂ)) *
          ∫ t in (-Real.pi)..Real.pi,
            f t * delAtomPairFT n δ zMinus zPlus (η - t) := by
    rw [cleanThreeFactor_FT_eq_conv n δ zMinus zPlus η]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hf]
    unfold delAtomPairFT
    congr 1
    apply tsum_congr
    intro r
    congr 2
    push_cast
    ring
  -- integrand modulus bound: ‖f t‖·‖delAtomPairFT (η-t)‖ ≤ (1/(1-δ))^2
  have hpt : ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
      ‖f t‖ * ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ ≤ (1 / (1 - δ)) ^ 2 := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htπ : |t| ≤ Real.pi := abs_le.mpr ⟨ht.1, ht.2⟩
    have hb1 : ‖f t‖ ≤ 1 := by
      simp only [hf]
      exact binAtom_FT_modulus_le_one n hn t htπ
    have hb2 : ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ ≤ (1 / (1 - δ)) ^ 2 :=
      delAtomPairFT_global_le n δ hδ0 hδ1 zMinus zPlus _
    calc ‖f t‖ * ‖delAtomPairFT n δ zMinus zPlus (η - t)‖
        ≤ 1 * (1 / (1 - δ)) ^ 2 :=
          mul_le_mul hb1 hb2 (norm_nonneg _) (by norm_num)
      _ = (1 / (1 - δ)) ^ 2 := by ring
  -- Triangle bound on the convolution integral.
  have hfper : ∀ x, f (x + 2 * Real.pi) = f x := by
    intro x
    simp only [hf]
    exact discreteFT_periodic (fun r : ℤ => ((binAtom n r : ℝ) : ℂ)) x
  have hgper : ∀ x, delAtomPairFT n δ zMinus zPlus (x + 2 * Real.pi)
      = delAtomPairFT n δ zMinus zPlus x := fun x =>
    delAtomPairFT_periodic n δ zMinus zPlus x
  have hfint : MeasureTheory.IntegrableOn f (Set.Icc (-Real.pi) Real.pi) := by
    simp only [hf]
    exact binAtom_FT_integrableOn n hn
  have hgint : MeasureTheory.IntegrableOn
      (fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ)
      (Set.Icc (-Real.pi) Real.pi) :=
    delAtomPairFT_integrableOn n δ hδ0 hδ1 zMinus zPlus
  have htri :
      ‖cleanFT n δ zMinus zPlus η‖
        ≤ (1 / (2 * Real.pi)) *
            ∫ t in (-Real.pi)..Real.pi,
              ‖f t‖ * ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ := by
    rw [hconv]
    exact ModulusOfCircularConvolutionTriangle
      f (fun ζ => delAtomPairFT n δ zMinus zPlus ζ) hfper hgper hfint hgint η
  -- integrate the constant bound
  set F : ℝ → ℝ := fun t => ‖f t‖ * ‖delAtomPairFT n δ zMinus zPlus (η - t)‖ with hF
  have hFcont : Continuous F := by
    rw [hF]
    apply Continuous.mul
    · apply Continuous.norm
      simp only [hf]
      exact finiteSupport_FT_continuous (binAtom n)
        (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4))
        (fun r hr => binAtom_off_zero n r hr)
    · apply Continuous.norm
      exact (delAtomPairFT_continuous n δ hδ0 hδ1 zMinus zPlus).comp
        (continuous_const.sub continuous_id)
  have hFiint : IntervalIntegrable F MeasureTheory.volume (-Real.pi) Real.pi :=
    hFcont.intervalIntegrable _ _
  have hintbound : (∫ t in (-Real.pi)..Real.pi, F t)
      ≤ ∫ _ in (-Real.pi)..Real.pi, (1 / (1 - δ)) ^ 2 :=
    intervalIntegral.integral_mono_on hπ hFiint intervalIntegrable_const
      (fun t ht => hpt t ht)
  have hconst : (∫ _ in (-Real.pi)..Real.pi, (1 / (1 - δ)) ^ 2)
      = (2 * Real.pi) * (1 / (1 - δ)) ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul,
        show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
  calc ‖cleanFT n δ zMinus zPlus η‖
      ≤ (1 / (2 * Real.pi)) * ∫ t in (-Real.pi)..Real.pi, F t := htri
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * (1 / (1 - δ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hconst]; exact hintbound
    _ = (1 / (1 - δ)) ^ 2 := by field_simp

/-! ### (B) Tighter `Couter` bound (without the `(n+1)` factor). -/

/-- **Prefactor lower bound, no `(n+1)`.** `1/(1-δ)² ≤ (2π-2)(2π)²/(1-δ)²`. -/
theorem prefactor_ge_no_n (δ : ℝ) (hδ1 : δ < 1) :
    1 / (1 - δ) ^ 2
      ≤ (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 := by
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hD2 : (0:ℝ) < (1 - δ) ^ 2 := by positivity
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  rw [div_le_div_iff_of_pos_right hD2]
  have hfac1 : (4:ℝ) ≤ 2 * Real.pi - 2 := by linarith
  have hfac2 : (36:ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [hpi]
  nlinarith [hfac1, hfac2]

/-- **Tighter `Couter` bound.** `Couter ≤ (2π-2)(2π)²/(1-δ)²·Maxiom` (no `(n+1)`). -/
theorem Couter_le_main_no_n (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) :
    Couter n δ zMinus zPlus
      ≤ (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
          Maxiom n δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hD1 : 1 - δ ≤ 1 := by linarith
  have hMnn : 0 ≤ Maxiom n δ zMinus zPlus := by
    unfold Maxiom
    apply le_max_of_le_right; positivity
  set P := (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 with hP
  have hPge : 1 / (1 - δ) ^ 2 ≤ P := prefactor_ge_no_n δ hδ1
  have hkey : (1 / (1 - δ) ^ 2) * Maxiom n δ zMinus zPlus ≤ P * Maxiom n δ zMinus zPlus :=
    mul_le_mul_of_nonneg_right hPge hMnn
  unfold Couter
  apply max_le
  · have hncast : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hexp : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) ≤ Maxiom n δ zMinus zPlus := by
      unfold Maxiom
      apply le_max_of_le_right
      apply le_refl
    have hAstep : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) / (1 - δ) ^ 2
        ≤ (1 / (1 - δ) ^ 2) * Maxiom n δ zMinus zPlus := by
      rw [one_div, ← div_eq_inv_mul]
      apply div_le_div_of_nonneg_right hexp (by positivity)
    exact le_trans hAstep hkey
  · have hCinner_le : Cinner δ zMinus zPlus
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

/-! ### (C) Trivial ℓ¹ bound on `kwayFT`: `‖kwayFT ζ‖ ≤ n+1`. -/

/-- **kwayProd vanishes off `Icc (-n) n`.** -/
theorem kwayProd_off_bigwindow_zero (n : ℕ) (α : ℝ) (ℓ : Finset ℕ)
    (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ) (hj₀le : j₀ ≤ n / 2) (r : ℤ)
    (hr : r ∉ Finset.Icc (-(n : ℤ)) (n : ℤ)) :
    kwayProd n α ℓ r = 0 := by
  apply kwayProd_off_window_zero n α ℓ j₀ hj₀
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr ⊢
  rcases hr with hlo | hhi
  · left; omega
  · right; omega

/-- **Trivial k-way ℓ¹ bound.** For nonempty `ℓ ⊆ Icc 1 (n/2)` (with `n ≡ 1 mod 8`)
and `α := c'·√n`, `‖kwayFT n α ℓ ζ‖ ≤ n + 1`. -/
theorem kwayFT_L1_le (n : ℕ) (hn : (10:ℕ)^12 ≤ n) (hn8 : n % 8 = 1)
    (ℓ : Finset ℕ) (hℓsub : ℓ ⊆ Finset.Icc 1 (n / 2)) (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ)
    (ζ : ℝ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    ‖kwayFT n α ℓ ζ‖ ≤ (n : ℝ) + 1 := by
  intro α
  have hn1 : 1 ≤ n := by
    have : (1:ℕ) ≤ (10:ℕ)^12 := by norm_num
    omega
  have hj₀range : j₀ ∈ Finset.Icc 1 (n / 2) := hℓsub hj₀
  have hj₀le : j₀ ≤ n / 2 := (Finset.mem_Icc.mp hj₀range).2
  -- kwayProd = T4L1NormBound's T4 (same α); pull its [0,1] + ∑ ≤ n+1.
  have hcard : 1 ≤ ℓ.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
  have hT4 := T4L1NormBound n hn hn8 ℓ hℓsub hcard
  simp only at hT4
  obtain ⟨hkw01, hkwsum, _⟩ := hT4
  -- kwayProd r equals T4L1NormBound's T4 at the SHIFTED index (r-1):
  -- `ellFactor n α r (j-1) = ellFactor n α (r-1) j` for `j ≥ 1` (witness index
  -- `r + n/4 + (j-1) = (r-1) + n/4 + j`), so `kwayProd r = ∏ ellFactor (r-1) j`.
  have hkw_eq : ∀ r : ℤ, kwayProd n α ℓ r = ∏ j ∈ ℓ, ellFactor n α (r - 1) j := by
    intro r
    unfold kwayProd
    apply Finset.prod_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (hℓsub hj)).1
    unfold ellFactor
    simp only
    congr 2 <;> push_cast [Nat.cast_sub hj1] <;> ring
  -- step 1: ‖kwayFT‖ ≤ ∑' ‖kwayProd r‖
  have hsumm : Summable (fun r : ℤ =>
      ‖((kwayProd n α ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))‖) := by
    have heq : (fun r : ℤ => ‖((kwayProd n α ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))‖)
        = (fun r : ℤ => ‖kwayProd n α ℓ r‖) := by
      funext r
      rw [norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : (-(Complex.I * (ζ : ℂ) * (r : ℂ))).re = 0 := by
        simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hre, Real.exp_zero, mul_one]
    rw [heq]
    exact kwayProd_summable n α ℓ j₀ hj₀
  have htri : ‖kwayFT n α ℓ ζ‖ ≤ ∑' r : ℤ, ‖kwayProd n α ℓ r‖ := by
    unfold kwayFT
    calc ‖∑' r : ℤ, ((kwayProd n α ℓ r : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))‖
        ≤ ∑' r : ℤ, ‖((kwayProd n α ℓ r : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))‖ := norm_tsum_le_tsum_norm hsumm
      _ = ∑' r : ℤ, ‖kwayProd n α ℓ r‖ := by
          apply tsum_congr
          intro r
          rw [norm_mul, Complex.norm_real, Complex.norm_exp]
          have hre : (-(Complex.I * (ζ : ℂ) * (r : ℂ))).re = 0 := by
            simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
          rw [hre, Real.exp_zero, mul_one]
  -- step 2: ∑' ‖kwayProd r‖ = ∑' kwayProd r (nonneg) = ∑ over Icc(-n)(n) ≤ n+1
  have hnorm_eq : (fun r : ℤ => ‖kwayProd n α ℓ r‖) = (fun r : ℤ => kwayProd n α ℓ r) := by
    funext r
    rw [Real.norm_eq_abs, abs_of_nonneg]
    rw [hkw_eq r]; exact (hkw01 (r - 1)).1
  rw [hnorm_eq] at htri
  -- ∑' kwayProd r = ∑ over Icc(-n)(n)
  have htsum_fin : ∑' r : ℤ, kwayProd n α ℓ r
      = ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), kwayProd n α ℓ r := by
    rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) (n : ℤ))]
    intro b hb
    exact kwayProd_off_bigwindow_zero n α ℓ j₀ hj₀ hj₀le b hb
  -- the finite sum is ≤ n+1.  Via the (r-1)-shift it equals the tsum of
  -- T4 r := ∏ j∈ℓ, ellFactor n α r j, which equals T4L1NormBound's finite sum.
  set T4 : ℤ → ℝ := fun r => ∏ j ∈ ℓ, ellFactor n α r j with hT4def
  -- T4 vanishes off the big window Icc(-n)(n) (uses j₀ ∈ ℓ as the witness factor).
  have hT4_off : ∀ r : ℤ, r ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) → T4 r = 0 := by
    intro r hr
    rw [hT4def]
    apply Finset.prod_eq_zero hj₀
    apply T4L1NormBoundAux.ellFactor_zero_of_out_support n α r j₀
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
    have hj₀1 : 1 ≤ j₀ := (Finset.mem_Icc.mp hj₀range).1
    rintro ⟨h1, h2⟩
    rcases hr with hlo | hhi <;> omega
  -- the tsum of T4 collapses to the finite window sum, hence ≤ n+1.
  have hT4_summ : Summable (fun r : ℤ => ‖T4 r‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(n : ℤ)) (n : ℤ))
    intro b hb; rw [hT4_off b hb, norm_zero]
  have hT4_summ' : Summable T4 :=
    (summable_norm_iff).mp hT4_summ
  have hT4_tsum : ∑' r : ℤ, T4 r ≤ (n : ℝ) + 1 := by
    rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun b hb => hT4_off b hb)]
    exact hkwsum
  have hfinsum_le : ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), kwayProd n α ℓ r ≤ (n : ℝ) + 1 := by
    rw [← htsum_fin]
    -- ∑' kwayProd r = ∑' T4 (r-1) = ∑' T4 s ≤ n+1
    have hreindex : ∑' r : ℤ, kwayProd n α ℓ r = ∑' s : ℤ, T4 s := by
      have h1 : (fun r : ℤ => kwayProd n α ℓ r) = (fun r : ℤ => T4 (r - 1)) := by
        funext r; rw [hkw_eq r, hT4def]
      rw [h1]
      exact (Equiv.subRight (1 : ℤ)).tsum_eq T4
    rw [hreindex]; exact hT4_tsum
  calc ‖kwayFT n α ℓ ζ‖
      ≤ ∑' r : ℤ, kwayProd n α ℓ r := htri
    _ = ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), kwayProd n α ℓ r := htsum_fin
    _ ≤ (n : ℝ) + 1 := hfinsum_le

/-! ### (D) k-way Fourier tail bound: `‖kwayFT ζ‖ ≤ 2 e^{-√n}` on `2 ≤ |ζ| ≤ π`.
This reindexes `kwayProd` (Finset product) to the tuple product the bridge consumes,
then invokes `kwayFactor_fourier_tail_bound` (which invokes Lemma 7). -/

theorem kwayFT_tail_le (n : ℕ) (hn : (10:ℕ)^12 ≤ n) (hn8 : n % 8 = 1)
    (ℓ : Finset ℕ) (hℓsub : ℓ ⊆ Finset.Icc 1 (n / 2))
    (hℓpar : Workspace.Types.AlternatingSumExpression.sameParity ℓ)
    (ζ : ℝ) (hζπ : |ζ| ≤ Real.pi) (hζ2 : (2 : ℝ) ≤ |ζ|) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    ‖kwayFT n α ℓ ζ‖ ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) := by
  intro α
  have hn1 : 1 ≤ n := by
    have : (1:ℕ) ≤ (10:ℕ)^12 := by norm_num
    omega
  set k := ℓ.card with hk
  set g : Fin k → ℕ := ⇑(ℓ.orderEmbOfFin hk.symm) with hg
  -- `g i ∈ ℓ`, hence `g i ≥ 1` (used for the per-factor index shift below).
  have hmem : ∀ i : Fin k, g i ∈ ℓ := by
    intro i; rw [hg]; exact orderEmbOfFin_mem ℓ k hk.symm i
  have hg1 : ∀ i : Fin k, 1 ≤ g i := fun i =>
    (Finset.mem_Icc.mp (hℓsub (hmem i))).1
  -- The k-way tuple product has the SHIFTED index `g i - 1` (matching `kwayProd`'s
  -- new `(j-1)` body).  Per factor `ellFactor n α r (g i - 1) = ellFactor n α (r-1) (g i)`
  -- since the witness index `r + n/4 + (g i - 1) = (r-1) + n/4 + g i` (using `g i ≥ 1`).
  have hfac_shift : ∀ (r : ℤ) (i : Fin k),
      ellFactor n α r (g i - 1) = ellFactor n α (r - 1) (g i) := by
    intro r i
    unfold ellFactor
    simp only
    congr 2 <;> push_cast [Nat.cast_sub (hg1 i)] <;> ring
  -- Rewrite kwayFT so the bound separates out a unit-modulus phase `e^{-iζ}`.
  -- kwayFT ζ = ∑' r, (∏ i, ellFactor n α r (g i - 1)) e^{-iζr}
  --          = ∑' r, (∏ i, ellFactor n α (r-1) (g i)) e^{-iζr}
  --          = e^{-iζ} · ∑' r, (∏ i, ellFactor n α r (g i)) e^{-iζr}   (reindex r↦r+1)
  have hrewrite : kwayFT n α ℓ ζ
      = Complex.exp (-(Complex.I * (ζ : ℂ))) *
          ∑' r : ℤ, ((∏ i : Fin k, ellFactor n α r (g i) : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))) := by
    unfold kwayFT
    -- Step 1: replace kwayProd r by the shifted tuple product ∏ ellFactor (r-1) (g i).
    have hstep1 : (fun r : ℤ => ((kwayProd n α ℓ r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))))
        = (fun r : ℤ => ((∏ i : Fin k, ellFactor n α (r - 1) (g i) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))) := by
      funext r
      have htp := kwayProd_eq_tupleProd n α ℓ r k hk.symm
      rw [hg, ← htp]
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      exact hfac_shift r i
    rw [hstep1]
    -- Step 2: reindex r ↦ r + 1 on the LHS, then factor out the phase e^{-iζ}.
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
      (fun r : ℤ => ((∏ i : Fin k, ellFactor n α (r - 1) (g i) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))))]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have hexp : Complex.exp (-(Complex.I * (ζ : ℂ) * ((r : ℂ) + 1)))
        = Complex.exp (-(Complex.I * (ζ : ℂ)))
            * Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    rw [hexp]; ring
  rw [hrewrite, norm_mul]
  have hphase : ‖Complex.exp (-(Complex.I * (ζ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (-(Complex.I * (ζ : ℂ))).re = 0 := by
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [this, Real.exp_zero]
  rw [hphase, one_mul]
  -- discharge the bridge hypotheses on the tuple g
  have hstrict : ∀ i j : Fin k, i.val < j.val → g i < g j := by
    intro i j hij
    rw [hg]; exact orderEmbOfFin_strict ℓ k hk.symm i j hij
  have hpar : ∀ i j : Fin k, g i % 2 = g j % 2 := by
    intro i j; exact hℓpar (g i) (hmem i) (g j) (hmem j)
  have hrange : ∀ i : Fin k, 1 ≤ g i ∧ g i ≤ (n - 1) / 2 := by
    intro i
    have hmemIcc : g i ∈ Finset.Icc 1 (n / 2) := hℓsub (hmem i)
    rw [Finset.mem_Icc] at hmemIcc
    refine ⟨hmemIcc.1, ?_⟩
    -- n odd ⇒ n/2 = (n-1)/2
    have : n / 2 = (n - 1) / 2 := by omega
    rw [← this]; exact hmemIcc.2
  exact kwayFactor_fourier_tail_bound n hn1 hn8 k g hstrict hpar hrange ζ hζπ hζ2

/-! ### (E) The region-split pointwise integrand bound `hpt`. -/

/-- **kwayFT tail bound, periodised to all `ζ` with `|ζ| ≥ 2`'s representative.**
For `η ∈ [-π, π]`, if the [-π,π]-representative of `π - η` has modulus `≥ 2`, then
`‖kwayFT n α ℓ (π - η)‖ ≤ 2 e^{-√n}`. -/
theorem kwayFT_tail_le_periodised (n : ℕ) (hn : (10:ℕ)^12 ≤ n) (hn8 : n % 8 = 1)
    (ℓ : Finset ℕ) (hℓsub : ℓ ⊆ Finset.Icc 1 (n / 2))
    (hℓpar : Workspace.Types.AlternatingSumExpression.sameParity ℓ)
    (η : ℝ) (hηlo : -Real.pi ≤ η) (hηhi : η ≤ Real.pi)
    (α : ℝ) (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) :
    -- representative-modulus ≥ 2 hypothesis, expressed concretely:
    (2 ≤ |Real.pi - η| ∧ |Real.pi - η| ≤ Real.pi) ∨
      (2 ≤ |Real.pi - η - 2 * Real.pi| ∧ |Real.pi - η - 2 * Real.pi| ≤ Real.pi) →
    ‖kwayFT n α ℓ (Real.pi - η)‖ ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) := by
  intro hrep
  subst hα
  rcases hrep with ⟨h2, hπ⟩ | ⟨h2, hπ⟩
  · exact kwayFT_tail_le n hn hn8 ℓ hℓsub hℓpar (Real.pi - η) hπ h2
  · -- shift by 2π
    have hshift : kwayFT n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) ℓ
          (Real.pi - η)
        = kwayFT n
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) ℓ
            (Real.pi - η - 2 * Real.pi) := by
      have := kwayFT_periodic n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) ℓ
        (Real.pi - η - 2 * Real.pi)
      rw [show Real.pi - η - 2 * Real.pi + 2 * Real.pi = Real.pi - η by ring] at this
      rw [this]
    rw [hshift]
    exact kwayFT_tail_le n hn hn8 ℓ hℓsub hℓpar (Real.pi - η - 2 * Real.pi) hπ h2

/-- **Periodised general-η Couter bound on cleanFT.** For `η ∈ [-π, π]` with
`π - η < 2` (i.e. `η > π - 2`) OR `η < 2 - π` (the two `|ζ'| < 2` sub-bands),
`‖cleanFT n δ z₋ z₊ η‖ ≤ Couter n δ z₋ z₊`. -/
theorem cleanFT_Couter_periodised (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hηlo : -Real.pi ≤ η) (hηhi : η ≤ Real.pi)
    (hsmall : η > Real.pi - 2 ∨ η < 2 - Real.pi) :
    ‖cleanFT n δ zMinus zPlus η‖ ≤ Couter n δ zMinus zPlus := by
  rcases hsmall with hbig | hsm
  · -- η ∈ (π-2, π] ⊆ band [π-2, π+2]
    exact Workspace.PriorWork.CleanFTGeneralEta.cleanFT_abs_le_Couter_general
      n hn δ hδ0 hδ zMinus zPlus η
      (le_of_lt hbig) (by linarith)
  · -- η ∈ [-π, 2-π); shift +2π into band
    have hshift : cleanFT n δ zMinus zPlus η = cleanFT n δ zMinus zPlus (η + 2 * Real.pi) :=
      (cleanFT_periodic n δ zMinus zPlus η).symm
    rw [hshift]
    exact Workspace.PriorWork.CleanFTGeneralEta.cleanFT_abs_le_Couter_general
      n hn δ hδ0 hδ zMinus zPlus
      (η + 2 * Real.pi) (by linarith) (by linarith)

/-! ### (E-main) The pointwise integrand bound matching `hpt`. -/

theorem region_integrand_bound
    (n : ℕ) (hn : (10:ℕ)^12 ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (ℓ : Finset ℕ) (hℓsub : ℓ ⊆ Finset.Icc 1 (n / 2))
    (hℓpar : Workspace.Types.AlternatingSumExpression.sameParity ℓ)
    (zMinus zPlus : ℕ)
    (α : ℝ) (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ))
    (hjne : ℓ.Nonempty)
    (η : ℝ) (hη : η ∈ Set.Icc (-Real.pi) Real.pi) :
    ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
      ≤ (((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n : ℝ) / 150)))))
        + (4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ))) := by
  rw [Set.mem_Icc] at hη
  obtain ⟨hηlo, hηhi⟩ := hη
  have hn1 : 1 ≤ n := by
    have : (1:ℕ) ≤ (10:ℕ)^12 := by norm_num
    omega
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  obtain ⟨j₀, hj₀⟩ := hjne
  have hpi : (3:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  -- nonneg pieces
  set Bexp := ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
      (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
           (Real.exp (-((n : ℝ) / 150)))) with hBexp
  set BFou := 4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)) with hBFou
  have hBexp_nn : 0 ≤ Bexp := by
    rw [hBexp]
    apply mul_nonneg
    · apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    · apply le_max_of_le_right; positivity
  have hBFou_nn : 0 ≤ BFou := by rw [hBFou]; positivity
  have hclean_nn : 0 ≤ ‖cleanFT n δ zMinus zPlus η‖ := norm_nonneg _
  have hkway_nn : 0 ≤ ‖kwayFT n α ℓ (Real.pi - η)‖ := norm_nonneg _
  -- Case split on the representative modulus of ζ = π - η.
  by_cases hsmall : η > Real.pi - 2 ∨ η < 2 - Real.pi
  · -- |ζ'| < 2 : cleanFT ≤ Couter ≤ Bexp/(n+1-free), kwayFT ≤ n+1.  Product ≤ Bexp.
    have hcleanB : ‖cleanFT n δ zMinus zPlus η‖ ≤ Couter n δ zMinus zPlus :=
      cleanFT_Couter_periodised n hn1 δ hδ0 hδ zMinus zPlus η hηlo hηhi hsmall
    have hCouter_main : Couter n δ zMinus zPlus
        ≤ (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Maxiom n δ zMinus zPlus :=
      Couter_le_main_no_n n hn1 δ hδ0 hδ zMinus zPlus
    have hkwayB : ‖kwayFT n α ℓ (Real.pi - η)‖ ≤ (n : ℝ) + 1 := by
      have := kwayFT_L1_le n hn hn8 ℓ hℓsub j₀ hj₀ (Real.pi - η)
      simp only at this
      rw [hα]; exact this
    have hCouter_nn : 0 ≤ Couter n δ zMinus zPlus := Couter_nonneg n δ hδ1 zMinus zPlus
    -- product ≤ Couter · (n+1) ≤ [(2π-2)(2π)²/(1-δ)²·M] · (n+1) = Bexp
    have hprod : ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
        ≤ Couter n δ zMinus zPlus * ((n : ℝ) + 1) :=
      mul_le_mul hcleanB hkwayB hkway_nn hCouter_nn
    have hn1nn : (0:ℝ) ≤ (n:ℝ) + 1 := by positivity
    have hstep : Couter n δ zMinus zPlus * ((n : ℝ) + 1)
        ≤ ((2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Maxiom n δ zMinus zPlus)
            * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hCouter_main hn1nn
    -- monotonicity: exp(-(n/2)/73) ≤ exp(-(n/150)) (since 73·n ≤ 150·(n/2) for n ≥ 41
    -- and n ≡ 1 mod 8 ⟹ 2·(n/2)+1 = n)
    have hexpmono : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) ≤ Real.exp (-((n : ℝ) / 150)) := by
      apply Real.exp_le_exp.mpr
      have hhalf : 2 * (n / 2) + 1 = n := by omega
      have hbig : (41 : ℕ) ≤ n := by omega
      have hcast : (73 : ℝ) * (n : ℝ) ≤ 150 * ((n / 2 : ℕ) : ℝ) := by
        have h1 : (73 : ℕ) * n ≤ 150 * (n / 2) := by omega
        have := (Nat.cast_le (α := ℝ)).mpr h1
        push_cast at this ⊢
        linarith
      rw [neg_div, neg_le_neg_iff]
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hcast]
    -- Maxiom ≤ (the max in Bexp, with exp(-(n/150)) third term)
    have hMaxmono : Maxiom n δ zMinus zPlus
        ≤ max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                   (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
              (Real.exp (-((n : ℝ) / 150))) := by
      unfold Maxiom
      apply max_le_max (le_refl _) hexpmono
    have hMaxle : ((2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Maxiom n δ zMinus zPlus)
        * ((n : ℝ) + 1) ≤ Bexp := by
      rw [hBexp]
      have hPnn : (0:ℝ) ≤ (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 := by
        apply div_nonneg _ (by positivity)
        apply mul_nonneg (by linarith) (by positivity)
      calc ((2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Maxiom n δ zMinus zPlus)
            * ((n : ℝ) + 1)
          ≤ ((2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
              (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                        (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                   (Real.exp (-((n : ℝ) / 150)))))
              * ((n : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_right _ hn1nn
            exact mul_le_mul_of_nonneg_left hMaxmono hPnn
        _ = ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
              (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                        (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                   (Real.exp (-((n : ℝ) / 150)))) := by ring
    have hstep' : Couter n δ zMinus zPlus * ((n : ℝ) + 1) ≤ Bexp :=
      le_trans hstep hMaxle
    calc ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
        ≤ Couter n δ zMinus zPlus * ((n : ℝ) + 1) := hprod
      _ ≤ Bexp := hstep'
      _ ≤ Bexp + BFou := by linarith
  · -- |ζ'| ≥ 2 : kwayFT tail ≤ 2 e^{-√n}, cleanFT global ≤ 1/(1-δ)².  Product ≤ BFou.
    push_neg at hsmall
    obtain ⟨hle1, hle2⟩ := hsmall  -- η ≤ π-2  and  η ≥ 2-π
    -- representative modulus ≥ 2:
    have hrep : (2 ≤ |Real.pi - η| ∧ |Real.pi - η| ≤ Real.pi) ∨
        (2 ≤ |Real.pi - η - 2 * Real.pi| ∧ |Real.pi - η - 2 * Real.pi| ≤ Real.pi) := by
      by_cases hge0 : 0 ≤ η
      · -- π - η ∈ [0, π], and π - η ≥ 2 since η ≤ π - 2
        left
        have hζnn : 0 ≤ Real.pi - η := by linarith
        rw [abs_of_nonneg hζnn]
        exact ⟨by linarith, by linarith⟩
      · -- η < 0 : ζ' = π - η - 2π = -π - η ∈ (-π, 0], |ζ'| = π + η ≥ 2 since η ≥ 2-π
        right
        push_neg at hge0
        have hζ' : Real.pi - η - 2 * Real.pi = -(Real.pi + η) := by ring
        rw [hζ']
        have hpe_nn : 0 ≤ Real.pi + η := by linarith
        rw [abs_neg, abs_of_nonneg hpe_nn]
        exact ⟨by linarith, by linarith⟩
    have hkwayB : ‖kwayFT n α ℓ (Real.pi - η)‖ ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) :=
      kwayFT_tail_le_periodised n hn hn8 ℓ hℓsub hℓpar η hηlo hηhi α hα hrep
    have hcleanB : ‖cleanFT n δ zMinus zPlus η‖ ≤ (1 / (1 - δ)) ^ 2 :=
      cleanFT_global_le n hn1 δ hδ0.le hδ1 zMinus zPlus η
    have hexp_nn : (0:ℝ) ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) := by positivity
    have hcleanB_nn : (0:ℝ) ≤ (1 / (1 - δ)) ^ 2 := by positivity
    have hprod : ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
        ≤ (1 / (1 - δ)) ^ 2 * (2 * Real.exp (- Real.sqrt (n : ℝ))) :=
      mul_le_mul hcleanB hkwayB hkway_nn hcleanB_nn
    -- (1/(1-δ))²·2e^{-√n} ≤ 4(2π)²/(1-δ)²·e^{-√n} = BFou
    have hcoef : (1 / (1 - δ)) ^ 2 * 2 ≤ 4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 := by
      rw [div_pow, one_pow]
      rw [show (1:ℝ) / (1 - δ) ^ 2 * 2 = 2 / (1 - δ) ^ 2 by ring]
      gcongr
      nlinarith [hpi, sq_nonneg Real.pi]
    have hBFou_eq : (1 / (1 - δ)) ^ 2 * (2 * Real.exp (- Real.sqrt (n : ℝ)))
        ≤ BFou := by
      rw [hBFou]
      have : (1 / (1 - δ)) ^ 2 * (2 * Real.exp (- Real.sqrt (n : ℝ)))
          = ((1 / (1 - δ)) ^ 2 * 2) * Real.exp (- Real.sqrt (n : ℝ)) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    calc ‖cleanFT n δ zMinus zPlus η‖ * ‖kwayFT n α ℓ (Real.pi - η)‖
        ≤ (1 / (1 - δ)) ^ 2 * (2 * Real.exp (- Real.sqrt (n : ℝ))) := hprod
      _ ≤ BFou := hBFou_eq
      _ ≤ Bexp + BFou := by linarith

/-! ### (F) The de-axiomatized Lemma 8 (k ≥ 1), EXACT axiom statement. -/

/-- **De-axiomatization of `AltRSumFourierBound` (k ≥ 1 case).** This is the exact
statement of the prior-work axiom `Workspace.PriorWork.AltRSumFourierBound`, now
proved sorry-free by discharging the region-split integrand bound from the proved
Lemma 7 (`SublemmaFourierKway`) plus the k = 0 outer machinery. -/
theorem AltRSumFourierBoundProved :
    ∀ (n : ℕ), (10 : ℕ) ^ 12 ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
    ∀ (zMinus zPlus : ℕ),
      zMinus < n / 2 + 1 → zPlus < n / 2 + 1 →
    ∀ (ℓ : Finset ℕ),
      ℓ ⊆ Finset.Icc 1 (n / 2) →
      Workspace.Types.AlternatingSumExpression.sameParity ℓ →
      ℓ.Nonempty →
      let _cPrime : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
        ≤
        ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n : ℝ) / 150))))
          +
          4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)) := by
  intro n hn hn8 δ hδ0 hδ zMinus zPlus _hzm _hzp ℓ hℓsub hℓpar hne
  intro _cPrime α
  have hn1 : 1 ≤ n := by
    have : (1:ℕ) ≤ (10:ℕ)^12 := by norm_num
    omega
  obtain ⟨j₀, hj₀⟩ := hne
  have hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ) := rfl
  -- Discharge `hpt` for `altRSum_fourier_bound_of_region_split`.
  apply altRSum_fourier_bound_of_region_split n δ α zMinus zPlus ℓ j₀ hj₀ hδ0.le (by linarith)
  intro η hη
  exact region_integrand_bound n hn hn8 δ hδ0 hδ ℓ hℓsub hℓpar zMinus zPlus α hα ⟨j₀, hj₀⟩ η hη

end Workspace.ProofLemmas.AltRSumFourierBoundProved
