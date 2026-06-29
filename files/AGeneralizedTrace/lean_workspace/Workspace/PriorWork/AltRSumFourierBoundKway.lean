-- CONDITIONAL k ≥ 1 region-split assembly for Lemma 8 (`AltRSumFourierBound`),
-- Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, lines 362-382.
-- SORRY-FREE (the Lemma-7 / k-way Fourier tail input is an EXPLICIT HYPOTHESIS,
-- not a `sorry`).
--
-- This file mirrors the (now-proved) k = 0 assembly
-- (`AltRSumFourierBoundEmpty` via `AltRSumEmptyOuterBound` and friends) for the
-- NONEMPTY-ℓ case. For nonempty `ℓ` the inner summand of `altRSum` is the
-- empty-ℓ three-binomial product TIMES the k-way product factor
-- `∏ j ∈ ℓ, ellFactor n α r j`:
--
--   Fterm n δ α r z₋ z₊ ℓ
--     = [binPMFInt n (1/2) (r+n/2)
--          · binPMFInt (n/4+r) (1-δ) z₋
--          · binPMFInt (n/4-r) (1-δ) z₊]              -- the 3-binom product
--       · (∏ j ∈ ℓ, ellFactor n α r j)                 -- the k-way factor
--
-- Define `kwayProd r := ∏ j ∈ ℓ, ellFactor n α r j` and
-- `fullClean r := cleanThreeFactor n δ z₋ z₊ r · kwayProd r`. Since
-- `cleanThreeFactor` already has finite support on the window `Icc (-(n/4)) (n/4)`
-- (proved in `AltRSumEmptyFourierBridge`), `fullClean` inherits finite support
-- (hence ℓ¹-summability) WITHOUT any control on `kwayProd` itself.
--
-- We land, sorry-free:
--   (1) `fullClean` has finite support / is summable (ℝ and ℂ-cast).
--   (2) `altRSum n δ α z₋ z₊ ℓ = ∑'_{r:ℤ} cos(πr) · fullClean r`  (window → ℤ).
--   (3) `altRSum n δ α z₋ z₊ ℓ = (fullCleanFT π).re`, hence
--       `|altRSum n δ α z₋ z₊ ℓ| ≤ ‖fullCleanFT π‖`.
--   (4) The CONDITIONAL bound `altRSum_fourier_bound_of_kway`: GIVEN a region-split
--       modulus bound on `fullCleanFT π` (the exact statement produced by
--       Lemma 7 = `SublemmaFourierKway` / `kwayFactor_fourier_tail_bound`
--       convolved with the 3-binom atom FTs and split at ξ = π), conclude
--       `|altRSum| ≤ B_exp + B_Fou`, the RHS of the axiom `AltRSumFourierBound`.
--
-- Once Lemma 7 (`SublemmaFourierKway`) is proved sorry-free, the region-split
-- modulus hypothesis `hFT` discharges from `kwayFactor_fourier_tail_bound`
-- (imported here via `AltRSumKwayFourierBridge`, which already wraps Lemma 7)
-- plus the k=0 region-split machinery, and
--   `AltRSumFourierBound = altRSum_fourier_bound_of_kway hFT`
-- de-axiomatizes Lemma 8. We do NOT turn the axiom into a theorem this round
-- (that would pull in the still-open bridge `sorry`); we land the sorry-free
-- conditional assembly only.
--
-- NOTE: we import `AltRSumKwayFourierBridge` (which wraps the Lemma-7 result) and
-- the k=0 assembly files; we do NOT import `SublemmaFourierKway` directly (it is
-- being edited concurrently) — the bridge already mediates it.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumEmptyEllReduction
import Workspace.PriorWork.AltRSumEmptyFourierBridge
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumKwayFourierBridge

set_option maxHeartbeats 1600000

namespace Workspace.PriorWork.AltRSumFourierBoundKway

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.AltRSumEmptyEllReduction
open Workspace.PriorWork.AltRSumEmptyFourierBridge
open Workspace.PriorWork.AltRSumEmptyFourierAssembly

/-! ### The k-way product factor and the full (3-binom × k-way) clean function -/

/-- The k-way product factor `kwayProd r := ∏ j ∈ ℓ, ellFactor n α r (j - 1)`.
The `(j - 1)` index matches `Fterm`'s k-way factor (witness index `r + n/4 + (j-1)`,
aligning the closed-form 1-based location set `ℓ ⊆ {1,…,n/2}` with the
partial-deletion process's 0-based middle-window indexing). -/
noncomputable def kwayProd (n : ℕ) (α : ℝ) (ℓ : Finset ℕ) (r : ℤ) : ℝ :=
  ∏ j ∈ ℓ, ellFactor n α r (j - 1)

/-- The full clean summand for nonempty ℓ: the clean three-binom product TIMES the
k-way product factor. -/
noncomputable def fullClean (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ)
    (r : ℤ) : ℝ :=
  cleanThreeFactor n δ zMinus zPlus r * kwayProd n α ℓ r

/-- **`fullClean` vanishes off the window `Icc (-(n/4)) (n/4)`** (inherited from
`cleanThreeFactor`, which already vanishes there). -/
theorem fullClean_off_window_zero (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ)
    (ℓ : Finset ℕ) (r : ℤ)
    (hr : r ∉ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))) :
    fullClean n δ α zMinus zPlus ℓ r = 0 := by
  unfold fullClean
  rw [cleanThreeFactor_off_window_zero n δ zMinus zPlus r hr, zero_mul]

/-- **`fullClean` is summable in absolute value over `ℤ`** (finite support). -/
theorem fullClean_summable (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) :
    Summable (fun r : ℤ => ‖fullClean n δ α zMinus zPlus ℓ r‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
  intro b hb
  rw [fullClean_off_window_zero n δ α zMinus zPlus ℓ b hb, norm_zero]

/-- Plain summability of `fullClean` over `ℤ`. -/
theorem fullClean_summable' (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) :
    Summable (fullClean n δ α zMinus zPlus ℓ) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))
  intro b hb
  exact fullClean_off_window_zero n δ α zMinus zPlus ℓ b hb

/-- ℂ-cast summability of `fullClean` (the ℓ¹ hypothesis the FT consumes). -/
theorem fullClean_summable_complex (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ)
    (ℓ : Finset ℕ) :
    Summable (fun r : ℤ => ‖((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ)‖)
      = (fun r : ℤ => ‖fullClean n δ α zMinus zPlus ℓ r‖) := by
    funext r; rw [Complex.norm_real]
  rw [h]
  exact fullClean_summable n δ α zMinus zPlus ℓ

/-! ### (2) Window reduction: `altRSum(ℓ) = ∑'_{r:ℤ} cos(πr) · fullClean r` -/

/-- **Nonempty-ℓ reduction of `altRSum` to a cosine sum over the window.**
`altRSum n δ α z₋ z₊ ℓ = ∑_{r∈window} cos(πr) · (3-binom product)(r) · kwayProd r`. -/
theorem altRSum_cos_window (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) :
    altRSum n δ α zMinus zPlus ℓ
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          Real.cos ((r : ℝ) * Real.pi) *
            ((binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
              * kwayProd n α ℓ r) := by
  unfold altRSum
  apply Finset.sum_congr rfl
  intro r _
  rw [neg_one_natAbs_eq_cos_pi_mul]
  unfold Fterm kwayProd
  ring

/-- **`altRSum(ℓ)` as a full ℤ-sum of `cos(πr) · fullClean r`.** The window sum
extends to all of `ℤ` because `fullClean` vanishes off the window; inside the
window the clamped 3-binom product equals `cleanThreeFactor`. -/
theorem altRSum_eq_ztsum_cos (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) :
    altRSum n δ α zMinus zPlus ℓ
      = ∑' r : ℤ, Real.cos ((r : ℝ) * Real.pi) * fullClean n δ α zMinus zPlus ℓ r := by
  rw [altRSum_cos_window]
  -- inside the window: clamped 3-binom = cleanThreeFactor, so summand = cos·fullClean
  have hfin : ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Real.cos ((r : ℝ) * Real.pi) *
          ((binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
            * kwayProd n α ℓ r)
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          Real.cos ((r : ℝ) * Real.pi) * fullClean n δ α zMinus zPlus ℓ r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [clamped_eq_clean_on_window n δ zMinus zPlus r hr]
    unfold fullClean
    ring
  rw [hfin]
  -- extend to ℤ-tsum (fullClean vanishes off the window)
  rw [tsum_eq_sum (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))]
  intro b hb
  rw [fullClean_off_window_zero n δ α zMinus zPlus ℓ b hb, mul_zero]

/-! ### (3) `altRSum(ℓ)` is the real part of the full Fourier transform at ξ = π -/

/-- The complex ℤ-Fourier transform of `fullClean` at frequency `ξ`. -/
noncomputable def fullCleanFT (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ)
    (ξ : ℝ) : ℂ :=
  ∑' r : ℤ, ((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))

/-- At `ξ = π` the summand's real part is `cos(πr) · fullClean r`. -/
theorem fullCleanFT_pi_summand_re (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ)
    (ℓ : Finset ℕ) (r : ℤ) :
    (((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))).re
      = Real.cos ((r : ℝ) * Real.pi) * fullClean n δ α zMinus zPlus ℓ r := by
  have hphase : Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))
      = Complex.exp (((-(Real.pi * r) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hphase, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring_nf

/-- **`altRSum(ℓ)` is the real part of `fullCleanFT(π)`.** -/
theorem altRSum_eq_fullCleanFT_re (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ)
    (ℓ : Finset ℕ) :
    altRSum n δ α zMinus zPlus ℓ = (fullCleanFT n δ α zMinus zPlus ℓ Real.pi).re := by
  rw [altRSum_eq_ztsum_cos]
  unfold fullCleanFT
  have hsum : Summable (fun r : ℤ =>
      ((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))) := by
    apply Summable.of_norm
    have h : (fun r : ℤ => ‖((fullClean n δ α zMinus zPlus ℓ r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.pi : ℂ) * (r : ℂ)))‖)
        = (fun r : ℤ => ‖fullClean n δ α zMinus zPlus ℓ r‖) := by
      funext r
      rw [norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : (-(Complex.I * (Real.pi : ℂ) * (r : ℂ))).re = 0 := by
        simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hre, Real.exp_zero, mul_one]
    rw [h]
    exact fullClean_summable n δ α zMinus zPlus ℓ
  rw [Complex.re_tsum hsum]
  apply tsum_congr
  intro r
  rw [fullCleanFT_pi_summand_re]

/-- **Modulus bound: `|altRSum(ℓ)| ≤ ‖fullCleanFT(π)‖`.** -/
theorem altRSum_abs_le_fullCleanFT_modulus (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ)
    (ℓ : Finset ℕ) :
    |altRSum n δ α zMinus zPlus ℓ| ≤ ‖fullCleanFT n δ α zMinus zPlus ℓ Real.pi‖ := by
  rw [altRSum_eq_fullCleanFT_re]
  exact Complex.abs_re_le_norm _

/-! ### (4) The CONDITIONAL region-split bound -/

/-- **CONDITIONAL k ≥ 1 Fourier convolution bound on `altRSum` (Lemma 8, k ≥ 1).**

GIVEN the region-split modulus bound on the full (3-binom × k-way) Fourier
transform at `ξ = π`,

  `‖fullCleanFT n δ α z₋ z₊ ℓ π‖ ≤ B_exp + B_Fou`,

which is EXACTLY the conclusion of (i) writing `fullClean = cleanThreeFactor ·
kwayProd`, (ii) the discrete convolution theorem expressing `fullCleanFT(π)` as
the circular convolution of `cleanFT` (the 3-binom atom FTs, bounded by the k=0
machinery in `AltRSumEmptyOuterBound`) with the k-way factor FT, and (iii) the
`ξ = π` region split using **Lemma 7** (`SublemmaFourierKway`, wrapped by
`AltRSumKwayFourierBridge.kwayFactor_fourier_tail_bound`: the k-way factor FT is
`≤ 2 e^{-√n}` on `2 ≤ |ζ| ≤ π`, and trivially `≤ n+1` everywhere) — we conclude
the axiom-RHS modulus bound

  `|altRSum n δ α z₋ z₊ ℓ| ≤ B_exp + B_Fou`.

This lemma is SORRY-FREE: the analytic Lemma-7 input is the hypothesis `hFT`, not
an admitted `sorry`. Once `SublemmaFourierKway` is proved sorry-free, `hFT`
discharges from `kwayFactor_fourier_tail_bound` + the k=0 region split, and this
lemma de-axiomatizes `AltRSumFourierBound`. -/
theorem altRSum_fourier_bound_of_kway
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ)
    (hFT : ‖fullCleanFT n δ α zMinus zPlus ℓ Real.pi‖
        ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
              (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                        (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                   (Real.exp (-((n : ℝ) / 150))))
            +
            4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ))) :
    |altRSum n δ α zMinus zPlus ℓ|
      ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n : ℝ) / 150))))
          +
          4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt (n : ℝ)) :=
  le_trans (altRSum_abs_le_fullCleanFT_modulus n δ α zMinus zPlus ℓ) hFT

end Workspace.PriorWork.AltRSumFourierBoundKway
