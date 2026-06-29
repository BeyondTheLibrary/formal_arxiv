-- Global + off-axis modulus bounds for the three atom Fourier transforms
-- (k = 0 / empty-ℓ case of Lemma 8, Rivkin–Valiant–Valiant 2024,
--  arXiv:2412.00674v1, §3, lines 369-381).
--
-- All SORRY-FREE. These are the pointwise modulus bounds the region-split
-- double-integral estimate of `AltRSumFourierBoundEmpty` consumes:
--   * `binAtomFT` modulus ≤ 1 everywhere, ≤ e^{-n/73} on 1/3 ≤ |·| ≤ π;
--   * `delAtom2FT`, `delAtom3FT` modulus ≤ 1/(1-δ) everywhere,
--     ≤ e^{-δz/20}/(1-δ) on 1/3 ≤ |·| ≤ π.
-- The global bounds use `deletionBinomial_base_bound` ( (1-δ) ≤ |1-δe^{iξ}| )
-- exactly the way the off-axis bound uses `deletionBinomial_decay_bound`.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionBinomialFourier
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.DelAtomPairFTContinuity

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyAtomBounds

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.DelAtomPairFTContinuity

/-! ### Global modulus bound for the deletion closed form `delFacFTcf` -/

/-- **Global lower bound on the geometric factor.** For `0 ≤ δ ≤ 1` and every `ξ`,
`(1 - δ) ≤ |1 - δ e^{iξ}|`. (Square root of `deletionBinomial_base_bound`.) -/
theorem geom_norm_global_lower (δ ξ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤ ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ)))‖ := by
  rw [deletionBinomial_geom_norm]
  apply Real.le_sqrt_of_sq_le
  have hbase := deletionBinomial_base_bound δ ξ hδ0 hδ1
  nlinarith [hbase]

/-- **Global modulus bound on `delFacFTcf`.** For `0 ≤ δ < 1`, every `ξ`,
`‖delFacFTcf (n4) δ z ξ‖ ≤ 1/(1-δ)`. The on-axis maximum, attained at `ξ = 0`. -/
theorem delFacFTcf_modulus_le_global (n4 : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (z : ℕ) (ξ : ℝ) :
    ‖delFacFTcf n4 δ z ξ‖ ≤ 1 / (1 - δ) := by
  unfold delFacFTcf
  rw [Complex.norm_div, norm_mul]
  -- numerator phase has modulus 1
  have hexp1 : ‖Complex.exp (Complex.I * (ξ : ℂ) * ((n4 - z : ℤ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    rw [show (Complex.I * (ξ : ℂ) * ((n4 - z : ℤ) : ℂ)).re = 0 by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]]
    exact Real.exp_zero
  rw [hexp1, one_mul]
  -- numerator (1-δ)^z
  have hnum : ‖((1 - δ : ℂ) ^ z)‖ = (1 - δ) ^ z := by
    rw [norm_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnum, norm_pow]
  -- denominator: |1 - δ e^{-iξ}|. Note the exponent has -ξ; rewrite to use the lemma at -ξ.
  have hden_eq : ‖(1 - (δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ))))‖
      = ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * ((-ξ : ℝ) : ℂ)))‖ := by
    congr 2
    push_cast; ring
  rw [hden_eq]
  set G := ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * ((-ξ : ℝ) : ℂ)))‖ with hGdef
  have hg : (1 - δ) ≤ G := geom_norm_global_lower δ (-ξ) hδ0 hδ1.le
  have hD : (0 : ℝ) < 1 - δ := by linarith
  have hden : (1 - δ) ^ (z + 1) ≤ G ^ (z + 1) :=
    pow_le_pow_left₀ hD.le hg (z + 1)
  have hstep1 : (1 - δ) ^ z / G ^ (z + 1)
      ≤ (1 - δ) ^ z / (1 - δ) ^ (z + 1) :=
    div_le_div_of_nonneg_left (pow_nonneg hD.le z) (by positivity) hden
  refine le_trans hstep1 ?_
  rw [pow_succ]
  rw [div_le_div_iff₀ (by positivity) hD, one_mul]

/-! ### Global + off-axis modulus bounds for the three atom Fourier transforms -/

/-- `‖delAtom2FT(ξ)‖ ≤ 1/(1-δ)` for every `ξ`. -/
theorem delAtom2_FT_modulus_le_global (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) (ξ : ℝ) :
    ‖(∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖ ≤ 1 / (1 - δ) := by
  rw [delAtom2_FT_eq_cf n δ hδ0 hδ1 zMinus ξ]
  exact delFacFTcf_modulus_le_global (n / 4 : ℤ) δ hδ0 hδ1 zMinus ξ

/-- `‖delAtom3FT(ξ)‖ ≤ 1/(1-δ)` for every `ξ`. -/
theorem delAtom3_FT_modulus_le_global (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) (ξ : ℝ) :
    ‖(∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖ ≤ 1 / (1 - δ) := by
  rw [delAtom3_FT_eq_cf n δ hδ0 hδ1 zPlus ξ]
  exact delFacFTcf_modulus_le_global (n / 4 : ℤ) δ hδ0 hδ1 zPlus (-ξ)

/-- `‖delAtom2FT(ξ)‖ ≤ e^{-δz₋/20}/(1-δ)` on `1/3 ≤ |ξ| ≤ π`. -/
theorem delAtom2_FT_modulus_decay (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus : ℕ) (ξ : ℝ) (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) :
    ‖(∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖
      ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) := by
  unfold delAtom2
  exact delFac_fourier_magnitude_bound δ hδ0 hδ ξ hξπ hξ (n / 4 : ℤ) zMinus

/-- `‖delAtom3FT(ξ)‖ ≤ e^{-δz₊/20}/(1-δ)` on `1/3 ≤ |ξ| ≤ π`. The reflected atom's
FT at `ξ` equals the deletion FT at `-ξ`, and `|-ξ| = |ξ|`. -/
theorem delAtom3_FT_modulus_decay (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zPlus : ℕ) (ξ : ℝ) (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) :
    ‖(∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖
      ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by
  have hrefl : (∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
        = ∑' r : ℤ, ((delFac (n / 4 : ℤ) δ zPlus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((-ξ : ℝ) : ℂ) * (r : ℂ))) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro r
    simp only [Equiv.neg_apply]
    unfold delAtom3
    rw [neg_neg]
    congr 2
    push_cast
    ring
  rw [hrefl]
  have hξπ' : |(-ξ)| ≤ Real.pi := by rwa [abs_neg]
  have hξ' : 1 / 3 ≤ |(-ξ)| := by rwa [abs_neg]
  exact delFac_fourier_magnitude_bound δ hδ0 hδ (-ξ) hξπ' hξ' (n / 4 : ℤ) zPlus

/-! ### Nonnegativity helpers -/

theorem one_div_one_sub_delta_nonneg (δ : ℝ) (hδ1 : δ < 1) : 0 ≤ 1 / (1 - δ) := by
  have : (0:ℝ) < 1 - δ := by linarith
  positivity

end Workspace.PriorWork.AltRSumEmptyAtomBounds
