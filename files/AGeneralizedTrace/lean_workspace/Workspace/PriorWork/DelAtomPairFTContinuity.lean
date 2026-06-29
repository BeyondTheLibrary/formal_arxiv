import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit

set_option maxHeartbeats 1000000

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit

namespace Workspace.PriorWork.DelAtomPairFTContinuity

/-- **FT of `delAtom2` equals its closed form.** -/
theorem delAtom2_FT_eq_cf (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zMinus : ℕ)
    (ξ : ℝ) :
    (∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = delFacFTcf (n / 4 : ℤ) δ zMinus ξ := by
  unfold delAtom2
  exact delFac_FT_eq_cf (n / 4 : ℤ) δ hδ0 hδ1 zMinus ξ

/-- **FT of `delAtom3` equals the closed form at `-ξ`.** Reflecting the summation
index `r ↦ -r` turns the FT of the reflected deletion atom into the deletion FT
evaluated at `-ξ`, whose closed form is `delFacFTcf (-ξ)`. -/
theorem delAtom3_FT_eq_cf (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zPlus : ℕ)
    (ξ : ℝ) :
    (∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = delFacFTcf (n / 4 : ℤ) δ zPlus (-ξ) := by
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
  rw [hrefl, delFac_FT_eq_cf (n / 4 : ℤ) δ hδ0 hδ1 zPlus (-ξ)]

/-- **The Fourier transform of `delAtomPair`** (the outer deletion-pair atom). -/
noncomputable def delAtomPairFT (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (ζ : ℝ) : ℂ :=
  ∑' r : ℤ, ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ζ : ℂ) * (r : ℂ)))

/-- **`delAtomPairFT` equals the circular convolution of the two closed forms.** -/
theorem delAtomPairFT_eq_cfConv (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (ζ : ℝ) :
    delAtomPairFT n δ zMinus zPlus ζ
      = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            delFacFTcf (n / 4 : ℤ) δ zMinus η *
              delFacFTcf (n / 4 : ℤ) δ zPlus (-(ζ - η)) := by
  unfold delAtomPairFT
  rw [delAtomPair_FT_eq_conv n δ hδ0 hδ1 zMinus zPlus ζ]
  congr 1
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [delAtom2_FT_eq_cf n δ hδ0 hδ1 zMinus η]
  rw [show ((ζ : ℂ) - (η : ℂ)) = (((ζ - η : ℝ)) : ℂ) by push_cast; ring]
  rw [delAtom3_FT_eq_cf n δ hδ0 hδ1 zPlus (ζ - η)]

/-- **MAIN: `delAtomPairFT` is continuous in `ζ`.** -/
theorem delAtomPairFT_continuous (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) :
    Continuous (fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ) := by
  have hfun : (fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ)
      = fun ζ : ℝ => (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            delFacFTcf (n / 4 : ℤ) δ zMinus η *
              delFacFTcf (n / 4 : ℤ) δ zPlus (-(ζ - η)) := by
    funext ζ
    exact delAtomPairFT_eq_cfConv n δ hδ0 hδ1 zMinus zPlus ζ
  rw [hfun]
  apply Continuous.mul continuous_const
  -- integrand as a two-argument function
  set f : ℝ → ℝ → ℂ := fun ζ η =>
    delFacFTcf (n / 4 : ℤ) δ zMinus η *
      delFacFTcf (n / 4 : ℤ) δ zPlus (-(ζ - η)) with hf
  have huncurry : Continuous (Function.uncurry f) := by
    rw [hf]
    unfold Function.uncurry
    apply Continuous.mul
    · exact (delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zMinus).comp continuous_snd
    · apply (delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zPlus).comp
      exact (continuous_fst.sub continuous_snd).neg
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    huncurry (-Real.pi) Real.pi

/-- **IntegrableOn `[-π, π]` of `delAtomPairFT`.** -/
theorem delAtomPairFT_integrableOn (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) :
    MeasureTheory.IntegrableOn (fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ)
      (Set.Icc (-Real.pi) Real.pi) :=
  (delAtomPairFT_continuous n δ hδ0 hδ1 zMinus zPlus).continuousOn.integrableOn_compact
    isCompact_Icc

/-- **`delAtomPairFT` is `2π`-periodic.** -/
theorem delAtomPairFT_periodic (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (ζ : ℝ) :
    delAtomPairFT n δ zMinus zPlus (ζ + 2 * Real.pi)
      = delAtomPairFT n δ zMinus zPlus ζ := by
  unfold delAtomPairFT
  exact discreteFT_periodic
    (fun r : ℤ => ((delAtomPair n δ zMinus zPlus r : ℝ) : ℂ)) ζ

end Workspace.PriorWork.DelAtomPairFTContinuity
