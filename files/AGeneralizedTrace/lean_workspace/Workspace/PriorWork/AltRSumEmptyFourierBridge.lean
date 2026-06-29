-- Bridge lemmas (SORRY-FREE) for the k = 0 / empty-ℓ case of Lemma 8
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, line 369-381, k = 0).
--
-- These connect the empty-ℓ reduction `altRSum_empty_cos` (a finite alternating
-- r-sum of three binomial factors) to the THREE Fourier atoms whose closed forms
-- and modulus bounds are now proved:
--   * first binomial  T₁(r) = binPMFInt (n/2) (1/2) (r + n/4)   (FT: BinomialFourierClosedForm)
--   * deletion z₋     T₂(r) = binPMFInt (n/4+r) (1-δ) z₋    (FT: DeletionFactorFourierInR)
--   * deletion z₊     T₃(r) = binPMFInt (n/4-r) (1-δ) z₊    (FT: DeletionFactorFourierInR, reflected)
--
-- Step achieved here: identify T₂, T₃ with the clean `delFac` atoms (so their
-- Fourier transforms in r are exactly `delFac_fourier_closedForm` /
-- `delFac_fourier_magnitude_bound`), and confirm the product of the three factors
-- is supported on `Icc (-(n/4)) (n/4)` (so the finite alternating r-sum equals the
-- full ℤ Fourier transform at ξ = π via (-1)^|r| = cos(π r) = Re e^{iπr}).
--
-- REMAINING (the genuine analytic gap, see report): assemble the 3-fold circular
-- convolution at ξ = π via `ConvolutionTheoremDiscrete` (applied pairwise twice),
-- then perform the [-π,π]² region split + integral estimates to recover the exact
-- `B_exp + B_Fou` constants. That triple-integral estimate is the same hard step
-- the k ≥ 1 axiom `AltRSumFourierBound` also leaves open.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyEllReduction

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyFourierBridge

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR

/-- **Second factor = deletion atom `delFac` at `+r`.** On the support region
`n/4 + r ≥ 0`, the `Fterm` deletion factor `binPMFInt (n/4+r) (1-δ) z₋` equals the
clean Fourier atom `delFac (n/4) δ z₋ r`. -/
theorem secondFactor_eq_delFac (n : ℕ) (δ : ℝ) (z : ℕ) (r : ℤ)
    (hr : 0 ≤ (n / 4 : ℤ) + r) :
    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) (z : ℤ)
      = delFac (n / 4 : ℤ) δ z r := by
  rw [delFac_eq_binPMFInt (n / 4 : ℤ) δ z r hr]

/-- **Third factor = deletion atom `delFac` at `-r` (reflection).** On the support
region `n/4 - r ≥ 0`, the `Fterm` deletion factor `binPMFInt (n/4-r) (1-δ) z₊`
equals the reflected Fourier atom `delFac (n/4) δ z₊ (-r)`. -/
theorem thirdFactor_eq_delFac (n : ℕ) (δ : ℝ) (z : ℕ) (r : ℤ)
    (hr : 0 ≤ (n / 4 : ℤ) - r) :
    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) (z : ℤ)
      = delFac (n / 4 : ℤ) δ z (-r) := by
  rw [delFac_eq_binPMFInt (n / 4 : ℤ) δ z (-r) (by omega)]
  rw [show ((n : ℤ) / 4 + -r) = (n : ℤ) / 4 - r from by ring]

/-- **The clean three-factor product** `T₁(r)·delFac(z₋,r)·delFac(z₊,-r)`, using the
honest (unclamped) deletion atoms, as a function of `r : ℤ`. This is the function
whose ℤ-Fourier transform at `ξ = π` the convolution argument bounds; its three
atoms have closed-form Fourier transforms (`BinomialFourierClosedForm`,
`delFac_fourier_closedForm` ×2). -/
noncomputable def cleanThreeFactor (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) : ℝ :=
  binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
    delFac (n / 4 : ℤ) δ zMinus r *
    delFac (n / 4 : ℤ) δ zPlus (-r)

/-- **On the window `Icc (-(n/4)) (n/4)`, the clamped `Fterm` product equals the
clean `delFac` product.** Inside the window both deletion indices are `≥ 0`, so the
`.toNat`-clamp is inert and the honest atoms agree with the `binPMFInt` factors.
This is the identity that lets `altRSum_empty_cos` (a finite sum of clamped factors)
be rewritten as a finite sum of the clean atoms — which then extend to all of `ℤ`. -/
theorem clamped_eq_clean_on_window (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))) :
    binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus
      = cleanThreeFactor n δ zMinus zPlus r := by
  rw [Finset.mem_Icc] at hr
  unfold cleanThreeFactor
  rw [secondFactor_eq_delFac n δ zMinus r (by omega)]
  rw [thirdFactor_eq_delFac n δ zPlus r (by omega)]

/-- **The clean three-factor product vanishes off the window `Icc (-(n/4)) (n/4)`.**
For `r < -(n/4)` the `delFac (n/4) δ z₋ r` atom is `0` (support `z₋ ≤ n/4 + r` fails
since `n/4 + r < 0 ≤ z₋`); for `r > n/4` the reflected atom `delFac (n/4) δ z₊ (-r)`
is `0`. Hence the finite alternating r-sum over the window equals the FULL Fourier
transform over `ℤ` of `cleanThreeFactor` at `ξ = π` (real part). -/
theorem cleanThreeFactor_off_window_zero (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ)
    (hr : r ∉ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ))) :
    cleanThreeFactor n δ zMinus zPlus r = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  unfold cleanThreeFactor delFac
  rcases hr with hlo | hhi
  · -- r < -(n/4): second atom support `zMinus ≤ n/4 + r` fails (n/4 + r < 0).
    rw [if_neg (by omega : ¬ (zMinus : ℤ) ≤ (n / 4 : ℤ) + r)]
    ring
  · -- r > n/4: third atom support `zPlus ≤ n/4 + (-r)` fails (n/4 - r < 0).
    rw [if_neg (by omega : ¬ (zPlus : ℤ) ≤ (n / 4 : ℤ) + (-r))]
    ring

end Workspace.PriorWork.AltRSumEmptyFourierBridge
