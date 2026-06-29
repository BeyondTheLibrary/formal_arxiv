-- Assembly (SORRY-FREE) lemmas for the k = 0 / empty-ℓ case of Lemma 8
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, lines 369-381, k = 0).
--
-- This file pushes the empty-ℓ Fourier-convolution argument from the bridge
-- lemmas (`AltRSumEmptyFourierBridge`) toward de-axiomatizing
-- `AltRSumFourierBoundEmpty`. The bridge already established:
--   * `altRSum_empty_cos`   : altRSum(∅) = ∑_{r∈window} cos(πr)·(clamped 3-product).
--   * `clamped_eq_clean_on_window` / `cleanThreeFactor_off_window_zero`:
--       the clamped 3-product equals the honest `cleanThreeFactor` on the window
--       and `cleanThreeFactor` vanishes off it.
--
-- Steps landed here (all sorry-free):
--   (1) `cleanThreeFactor` has finite support ⇒ is summable (the ℓ¹ hypothesis
--       the discrete convolution theorem consumes), in ℝ and in its ℂ-cast.
--   (2) The finite alternating r-sum over the window equals the FULL ℤ-Fourier
--       transform of `cleanThreeFactor` at ξ = π (real form), via the off-window
--       vanishing — `altRSum_empty_eq_ztsum_cos`.
--   (3) `altRSum(∅)` is the REAL PART of the complex ℤ-Fourier transform of
--       `cleanThreeFactor` at ξ = π, hence
--          |altRSum(∅)| ≤ ‖FT(cleanThreeFactor)(π)‖.                (`altRSum_empty_abs_le_FT_modulus`)
--       This converts the whole problem into bounding the modulus of ONE complex
--       ℤ-Fourier transform at ξ = π — exactly the object the convolution
--       argument bounds.
--   (4) Two-fold convolution decomposition: writing `cleanThreeFactor = T₁ · (T₂·T₃)`
--       and applying `ConvolutionTheoremDiscrete`, the FT of `cleanThreeFactor`
--       at any ξ equals the circular convolution of FT(T₁) and FT(T₂·T₃).
--       (`cleanThreeFactor_FT_eq_conv`)
--
-- REMAINING GAP (the genuine analytic step): bound the modulus of the resulting
-- (double) circular-convolution integral at ξ = π by `B_exp + B_Fou`. This needs
--   * a second application of `ConvolutionTheoremDiscrete` to split FT(T₂·T₃) into
--     the convolution of FT(T₂) and FT(T₃) (same shape as (4));
--   * `ModulusOfCircularConvolutionTriangle` to pass to the modulus integrand;
--   * the [-π,π]² region split: in any decomposition π = η₁+η₂+η₃ (mod 2π) at
--     least one |ηᵢ| ≥ 1/3, so that atom's decay bound applies, the other two are
--     bounded by their on-axis maxima 1/(1-δ) (T₂,T₃) or 1 (T₁); integrating the
--     2π·2π box gives the (2π)²/(1-δ)² · max{...} shape, which weakens to the
--     axiom RHS.
-- This is the same hard triple-integral estimate the k ≥ 1 axiom
-- `AltRSumFourierBound` also leaves open.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyEllReduction
import Workspace.PriorWork.AltRSumEmptyFourierBridge
import Workspace.PriorWork.ConvolutionTheoremDiscrete

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyFourierAssembly

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyEllReduction
open Workspace.PriorWork.AltRSumEmptyFourierBridge

/-! ### (1) Summability of `cleanThreeFactor` -/

/-- `cleanThreeFactor` is summable in absolute value over `ℤ` (finite support on
the window `Icc (-(n/4)) (n/4)`). This is the ℓ¹ hypothesis the discrete
convolution theorem consumes. -/
theorem cleanThreeFactor_summable (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (fun r : ℤ => ‖cleanThreeFactor n δ zMinus zPlus r‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
  intro b hb
  rw [cleanThreeFactor_off_window_zero n δ zMinus zPlus b hb, norm_zero]

/-- Plain summability of `cleanThreeFactor` over `ℤ`. -/
theorem cleanThreeFactor_summable' (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (cleanThreeFactor n δ zMinus zPlus) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
  intro b hb
  exact cleanThreeFactor_off_window_zero n δ zMinus zPlus b hb

/-! ### (2) Finite window sum = full ℤ-Fourier transform at ξ = π (real form) -/

/-- The finite alternating r-sum over the window equals the full ℤ-sum of
`cos(πr)·cleanThreeFactor(r)` (the summand vanishes off the window). -/
theorem altRSum_empty_eq_ztsum_cos (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) :
    altRSum n δ α zMinus zPlus ∅
      = ∑' r : ℤ, Real.cos ((r : ℝ) * Real.pi) * cleanThreeFactor n δ zMinus zPlus r := by
  rw [altRSum_empty_cos]
  -- Rewrite the finite summand using clamped = clean on the window.
  have hfin : ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Real.cos ((r : ℝ) * Real.pi) *
          (binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          Real.cos ((r : ℝ) * Real.pi) * cleanThreeFactor n δ zMinus zPlus r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [clamped_eq_clean_on_window n δ zMinus zPlus r hr]
  rw [hfin]
  -- Now extend the finite sum to the ℤ-tsum (summand vanishes off the window).
  rw [tsum_eq_sum (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))]
  intro b hb
  rw [cleanThreeFactor_off_window_zero n δ zMinus zPlus b hb, mul_zero]

/-! ### (3) `altRSum(∅)` is the real part of the complex FT at ξ = π -/

/-- The complex ℤ-Fourier transform of `cleanThreeFactor` at frequency `ξ`:
`∑'_{r:ℤ} (cleanThreeFactor r : ℂ) · exp(-(I·ξ·r))`. -/
noncomputable def cleanFT (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (ξ : ℝ) : ℂ :=
  ∑' r : ℤ, ((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))

/-- At `ξ = π`, the summand `(clean r : ℂ)·exp(-(I·π·r))` has real part
`cos(πr)·clean r` (since `exp(-(I·π·r)) = cos(πr) - i·sin(πr)` and the coefficient
is real). -/
theorem cleanFT_pi_summand_re (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) :
    (((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))).re
      = Real.cos ((r : ℝ) * Real.pi) * cleanThreeFactor n δ zMinus zPlus r := by
  -- exp(-(I·π·r)) = exp((-(π r))·I) = cos(-(π r)) + i sin(-(π r)).
  have hphase : Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))
      = Complex.exp (((-(Real.pi * r) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hphase, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring_nf

/-- **`altRSum(∅)` is the real part of the complex ℤ-Fourier transform of
`cleanThreeFactor` at ξ = π.** -/
theorem altRSum_empty_eq_cleanFT_re (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) :
    altRSum n δ α zMinus zPlus ∅ = (cleanFT n δ zMinus zPlus Real.pi).re := by
  rw [altRSum_empty_eq_ztsum_cos]
  unfold cleanFT
  -- summability of the complex FT summand at ξ = π
  have hsum : Summable (fun r : ℤ => ((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))) := by
    apply Summable.of_norm
    have h : (fun r : ℤ => ‖((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))‖)
        = (fun r : ℤ => ‖cleanThreeFactor n δ zMinus zPlus r‖) := by
      funext r
      rw [norm_mul, Complex.norm_real]
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * (Real.pi : ℂ) * (r : ℂ))).re = 0 := by
        simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hre, Real.exp_zero, mul_one]
    rw [h]
    exact cleanThreeFactor_summable n δ zMinus zPlus
  -- Re of a convergent ℂ-tsum is the ℝ-tsum of the real parts.
  rw [Complex.re_tsum hsum]
  apply tsum_congr
  intro r
  rw [cleanFT_pi_summand_re]

/-- **Modulus bound: `|altRSum(∅)| ≤ ‖FT(cleanThreeFactor)(π)‖`.** The empty-ℓ
alternating r-sum is dominated in absolute value by the modulus of the complex
ℤ-Fourier transform of `cleanThreeFactor` at ξ = π. This converts the whole
problem into bounding ONE complex Fourier-transform modulus, the object the
3-fold convolution argument bounds. -/
theorem altRSum_empty_abs_le_FT_modulus (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) :
    |altRSum n δ α zMinus zPlus ∅| ≤ ‖cleanFT n δ zMinus zPlus Real.pi‖ := by
  rw [altRSum_empty_eq_cleanFT_re]
  exact (Complex.abs_re_le_norm _)

/-! ### (4) Two-fold convolution decomposition of `cleanFT`

We split `cleanThreeFactor = T₁ · (T₂·T₃)` where
  `T₁(r) := binPMFInt (n/2) (1/2) (r + n/4)`        (first binomial atom)
  `T₂(r) := delFac (n/4) δ z₋ r`                     (deletion atom at +r)
  `T₃(r) := delFac (n/4) δ z₊ (-r)`                  (deletion atom at -r, reflected)
and apply `ConvolutionTheoremDiscrete` to the pair `(T₁ : ℂ)`, `(T₂·T₃ : ℂ)`. -/

/-- First binomial atom `T₁(r) = binPMFInt (n/2) (1/2) (r + n/4)`, as a function of `r`. -/
noncomputable def binAtom (n : ℕ) (r : ℤ) : ℝ :=
  binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ))

/-- Product of the two deletion atoms `T₂(r)·T₃(r)`, as a function of `r`. -/
noncomputable def delAtomPair (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) : ℝ :=
  delFac (n / 4 : ℤ) δ zMinus r * delFac (n / 4 : ℤ) δ zPlus (-r)

/-- Pointwise factorization `cleanThreeFactor r = binAtom r · delAtomPair r`. -/
theorem cleanThreeFactor_factor (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) :
    cleanThreeFactor n δ zMinus zPlus r
      = binAtom n r * delAtomPair n δ zMinus zPlus r := by
  unfold cleanThreeFactor binAtom delAtomPair
  ring

/-- `binAtom` vanishes off `Icc (-(n/4)) (n/2 - n/4)` (its first binomial factor's
support), hence is summable. -/
theorem binAtom_off_zero (n : ℕ) (r : ℤ)
    (hr : r ∉ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4)) :
    binAtom n r = 0 := by
  rw [Finset.mem_Icc, not_and_or] at hr
  unfold binAtom
  apply binPMFInt_off_support
  rintro ⟨h1, h2⟩
  rcases hr with hlo | hhi
  · omega
  · omega

/-- `‖(binAtom · : ℂ)‖` is summable over `ℤ` (finite support). -/
theorem binAtom_summable_complex (n : ℕ) :
    Summable (fun r : ℤ => ‖((binAtom n r : ℝ) : ℂ)‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4))
  intro b hb
  rw [binAtom_off_zero n b hb]
  simp

/-- `delAtomPair` vanishes off `Icc (-(n/4)) (n/4)` (the deletion atoms' supports
in `r`), hence is summable. -/
theorem delAtomPair_off_zero (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ)
    (hr : r ∉ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))) :
    delAtomPair n δ zMinus zPlus r = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  unfold delAtomPair delFac
  rcases hr with hlo | hhi
  · rw [if_neg (by omega : ¬ (zMinus : ℤ) ≤ (n / 4 : ℤ) + r)]
    ring
  · rw [if_neg (by omega : ¬ (zPlus : ℤ) ≤ (n / 4 : ℤ) + (-r))]
    ring

/-- `‖(delAtomPair · : ℂ)‖` is summable over `ℤ` (finite support). -/
theorem delAtomPair_summable_complex (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (fun r : ℤ => ‖((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ)‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
  intro b hb
  rw [delAtomPair_off_zero n δ zMinus zPlus b hb]
  simp

/-- **Two-fold convolution decomposition of `cleanFT`.** For any `ξ`, the complex
ℤ-Fourier transform of `cleanThreeFactor` factors as the circular convolution of
the Fourier transform of `binAtom` (= FT of `T₁`) and the Fourier transform of
`delAtomPair` (= FT of `T₂·T₃`):

  cleanFT(ξ) = (1/2π) ∫_{-π}^{π} FT(binAtom)(η) · FT(delAtomPair)(ξ-η) dη.

This is one application of `ConvolutionTheoremDiscrete` to the pair
`(binAtom : ℂ)`, `(delAtomPair : ℂ)`, whose pointwise product is `cleanThreeFactor`. -/
theorem cleanThreeFactor_FT_eq_conv (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (ξ : ℝ) :
    cleanFT n δ zMinus zPlus ξ
      = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            (∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))) *
            (∑' r : ℤ, ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((ξ - η) : ℂ) * (r : ℂ)))) := by
  unfold cleanFT
  -- rewrite the summand product so it matches `(f r * g r) * exp`
  have hcongr : ∀ r : ℤ,
      ((cleanThreeFactor n δ zMinus zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))
      = (((binAtom n r : ℝ) : ℂ) * ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))) := by
    intro r
    rw [cleanThreeFactor_factor n δ zMinus zPlus r]
    push_cast
    ring
  rw [tsum_congr hcongr]
  exact ConvolutionTheoremDiscrete
    (fun r => ((binAtom n r : ℝ) : ℂ))
    (fun r => ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ))
    (binAtom_summable_complex n)
    (delAtomPair_summable_complex n δ zMinus zPlus)
    ξ

/-! ### (5) Second convolution: `FT(delAtomPair) = conv(FT T₂, FT T₃)` -/

/-- Deletion atom `T₂(r) = delFac (n/4) δ z₋ r`. -/
noncomputable def delAtom2 (n : ℕ) (δ : ℝ) (zMinus : ℕ) (r : ℤ) : ℝ :=
  delFac (n / 4 : ℤ) δ zMinus r

/-- Reflected deletion atom `T₃(r) = delFac (n/4) δ z₊ (-r)`. -/
noncomputable def delAtom3 (n : ℕ) (δ : ℝ) (zPlus : ℕ) (r : ℤ) : ℝ :=
  delFac (n / 4 : ℤ) δ zPlus (-r)

/-- The reindexing map `m ↦ z + m - n/4` from excess-deletions `m : ℕ` to the
integer index `r : ℤ` (mirrors `DeletionFactorFourierInR.reidx`). -/
private def reidx2 (n : ℕ) (z : ℕ) : ℕ → ℤ := fun m => (z : ℤ) + (m : ℤ) - (n / 4 : ℤ)

private theorem reidx2_injective (n z : ℕ) : Function.Injective (reidx2 n z) := by
  intro a b h
  unfold reidx2 at h
  omega

/-- On the reindex map, `delFac (n/4) δ z (reidx2 m) = C(z+m,z)(1-δ)^z δ^m`. -/
private theorem delFac_reidx2 (n : ℕ) (δ : ℝ) (z : ℕ) (m : ℕ) :
    delFac (n / 4 : ℤ) δ z (reidx2 n z m)
      = (Nat.choose (z + m) z : ℝ) * (1 - δ) ^ z * δ ^ m := by
  unfold delFac reidx2
  rw [if_pos (by omega)]
  have htn : ((n / 4 : ℤ) + ((z : ℤ) + (m : ℤ) - (n / 4 : ℤ))).toNat = z + m := by omega
  rw [htn]
  congr 2
  omega

/-- The `delFac` atom (in `r`) has support contained in the range of `reidx2`. -/
private theorem delFac_support_reidx2 (n : ℕ) (δ : ℝ) (z : ℕ) :
    ∀ r : ℤ, delFac (n / 4 : ℤ) δ z r ≠ 0 → r ∈ Set.range (reidx2 n z) := by
  intro r hr
  have hz : z ≤ (n / 4 : ℤ) + r := by
    by_contra hzc
    apply hr
    unfold delFac
    rw [if_neg hzc]
  refine ⟨((n / 4 : ℤ) + r).toNat - z, ?_⟩
  unfold reidx2
  omega

/-- **`delFac (n/4) δ z ·` is summable over `ℤ`** (negative-binomial tail: the
binomial coefficient grows polynomially while `δ^m` decays geometrically). -/
theorem delFac_summable (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (z : ℕ) :
    Summable (fun r : ℤ => delFac (n / 4 : ℤ) δ z r) := by
  rw [← Function.Injective.summable_iff (reidx2_injective n z)
        (fun x hx => by
          by_contra hne
          exact hx (delFac_support_reidx2 n δ z x hne))]
  have hcongr : (fun r : ℤ => delFac (n / 4 : ℤ) δ z r) ∘ (reidx2 n z)
      = fun m : ℕ => (1 - δ) ^ z * ((Nat.choose (m + z) z : ℝ) * δ ^ m) := by
    funext m
    simp only [Function.comp_apply]
    rw [delFac_reidx2 n δ z m, Nat.add_comm z m]
    ring
  rw [hcongr]
  apply Summable.mul_left
  have hsum := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) z
    (r := δ) (by rwa [Real.norm_eq_abs, abs_of_nonneg hδ0])
  simpa using hsum

/-- `delAtom2` is summable over `ℤ`. -/
theorem delAtom2_summable (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zMinus : ℕ) :
    Summable (fun r : ℤ => delAtom2 n δ zMinus r) := by
  unfold delAtom2
  exact delFac_summable n δ hδ0 hδ1 zMinus

/-- `delAtom3` (the reflection `r ↦ delFac (n/4) δ z₊ (-r)`) is summable over `ℤ`. -/
theorem delAtom3_summable (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zPlus : ℕ) :
    Summable (fun r : ℤ => delAtom3 n δ zPlus r) := by
  unfold delAtom3
  have h := delFac_summable n δ hδ0 hδ1 zPlus
  exact (Equiv.neg ℤ).summable_iff.mpr h

/-- `‖(delAtom2 · : ℂ)‖` is summable over `ℤ`. -/
theorem delAtom2_summable_complex (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) :
    Summable (fun r : ℤ => ‖((delAtom2 n δ zMinus r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((delAtom2 n δ zMinus r : ℝ) : ℂ)‖)
      = (fun r : ℤ => |delAtom2 n δ zMinus r|) := by
    funext r; rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h]
  exact (delAtom2_summable n δ hδ0 hδ1 zMinus).abs

/-- `‖(delAtom3 · : ℂ)‖` is summable over `ℤ`. -/
theorem delAtom3_summable_complex (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) :
    Summable (fun r : ℤ => ‖((delAtom3 n δ zPlus r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((delAtom3 n δ zPlus r : ℝ) : ℂ)‖)
      = (fun r : ℤ => |delAtom3 n δ zPlus r|) := by
    funext r; rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h]
  exact (delAtom3_summable n δ hδ0 hδ1 zPlus).abs

theorem delAtomPair_eq_atom2_mul_atom3 (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) :
    delAtomPair n δ zMinus zPlus r
      = delAtom2 n δ zMinus r * delAtom3 n δ zPlus r := by
  unfold delAtomPair delAtom2 delAtom3
  rfl

/-- **Second convolution: `FT(delAtomPair)(ζ) = conv(FT delAtom2, FT delAtom3)(ζ)`.**
For any `ζ`, the Fourier transform of `delAtomPair` equals the circular
convolution of the Fourier transforms of the two deletion atoms `T₂`, `T₃`. One
application of `ConvolutionTheoremDiscrete` to `(delAtom2 : ℂ)`, `(delAtom3 : ℂ)`. -/
theorem delAtomPair_FT_eq_conv (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (ζ : ℝ) :
    (∑' r : ℤ, ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))))
      = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            (∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))) *
            (∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((ζ - η) : ℂ) * (r : ℂ)))) := by
  have hcongr : ∀ r : ℤ,
      ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))
      = (((delAtom2 n δ zMinus r : ℝ) : ℂ) * ((delAtom3 n δ zPlus r : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ))) := by
    intro r
    rw [delAtomPair_eq_atom2_mul_atom3 n δ zMinus zPlus r]
    push_cast
    ring
  rw [tsum_congr hcongr]
  exact ConvolutionTheoremDiscrete
    (fun r => ((delAtom2 n δ zMinus r : ℝ) : ℂ))
    (fun r => ((delAtom3 n δ zPlus r : ℝ) : ℂ))
    (delAtom2_summable_complex n δ hδ0 hδ1 zMinus)
    (delAtom3_summable_complex n δ hδ0 hδ1 zPlus)
    ζ

/-- **Full double-convolution identity for `cleanFT`.** Combining
`cleanThreeFactor_FT_eq_conv` (outer split `T₁ ⋆ (T₂T₃)`) with
`delAtomPair_FT_eq_conv` (inner split `T₂ ⋆ T₃`), the complex ℤ-Fourier transform
of `cleanThreeFactor` at any `ξ` is the iterated circular convolution

  cleanFT(ξ)
    = (1/2π) ∫_{-π}^{π} FT(T₁)(η) ·
        [ (1/2π) ∫_{-π}^{π} FT(T₂)(η') · FT(T₃)(ξ-η-η') dη' ] dη.

This is the exact starting point of the region-split modulus estimate (the
genuine remaining analytic gap toward `AltRSumFourierBoundEmpty`). -/
theorem cleanFT_eq_double_conv (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (ξ : ℝ) :
    cleanFT n δ zMinus zPlus ξ
      = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            (∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))) *
            ((1 / (2 * Real.pi)) *
              ∫ η' in (-Real.pi)..Real.pi,
                (∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
                    Complex.exp (-(Complex.I * (η' : ℂ) * (r : ℂ)))) *
                (∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
                    Complex.exp (-(Complex.I * (((ξ - η) - η') : ℂ) * (r : ℂ))))) := by
  rw [cleanThreeFactor_FT_eq_conv n δ zMinus zPlus ξ]
  congr 1
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  congr 1
  have hconv := delAtomPair_FT_eq_conv n δ hδ0 hδ1 zMinus zPlus (ξ - η)
  push_cast at hconv
  rw [hconv]

/-! ### (6) Periodicity of the atom Fourier transforms (2π-periodic in ξ)

These are the hypotheses `ModulusOfCircularConvolutionTriangle` consumes. Each
atom Fourier transform `ξ ↦ ∑'_r f(r)·exp(-iξr)` is `2π`-periodic because
`exp(-i·2π·r) = 1` for every integer `r`. -/

/-- For integer `r`, the phase at frequency `2π` is trivial: `exp(-(I·2π·r)) = 1`. -/
private theorem exp_two_pi_int (r : ℤ) :
    Complex.exp (-(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))) = 1 := by
  rw [show -(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))
        = ((-r : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-r)

/-- **Generic 2π-periodicity of a discrete Fourier transform.** For any
`f : ℤ → ℂ`, the function `ξ ↦ ∑'_r f(r)·exp(-(I·ξ·r))` is `2π`-periodic. -/
theorem discreteFT_periodic (f : ℤ → ℂ) (ξ : ℝ) :
    (∑' r : ℤ, f r * Complex.exp (-(Complex.I * ((ξ + 2 * Real.pi : ℝ) : ℂ) * (r : ℂ))))
      = ∑' r : ℤ, f r * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))) := by
  apply tsum_congr
  intro r
  congr 1
  rw [show -(Complex.I * ((ξ + 2 * Real.pi : ℝ) : ℂ) * (r : ℂ))
        = -(Complex.I * (ξ : ℂ) * (r : ℂ)) + -(Complex.I * ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ))
      by push_cast; ring]
  rw [Complex.exp_add, exp_two_pi_int r, mul_one]

end Workspace.PriorWork.AltRSumEmptyFourierAssembly
