-- Cited from: Folland, G. B. (1999). Real Analysis (2nd ed.). §8.2 (Fourier series and convolutions on the torus).
-- Paper label: Outer circular-convolution triangle bound on cleanFT(π).
-- NL statement: At ξ = π, the modulus of the clean Fourier transform is bounded by the
--   circular convolution of the moduli of the binom-atom FT and the deletion-pair FT.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.DelAtomPairFTContinuity
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle

set_option maxHeartbeats 1000000

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.DelAtomPairFTContinuity

namespace Workspace.PriorWork.CleanFTOuterModulusBound

/-- **OUTER triangle modulus bound on `cleanFT(π)`.**

The modulus of the clean Fourier transform at `ξ = π` is bounded by the circular
convolution (over `[-π, π]`) of the moduli of the binom-atom Fourier sum and the
deletion-pair Fourier transform. -/
theorem cleanFT_pi_abs_le_outer_modulus_integral
    (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zMinus zPlus : ℕ) :
    ‖cleanFT n δ zMinus zPlus Real.pi‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))‖ *
            ‖delAtomPairFT n δ zMinus zPlus (Real.pi - η)‖ := by
  -- The two convolution factors.
  set f : ℝ → ℂ := fun η : ℝ =>
    ∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))) with hf
  set g : ℝ → ℂ := fun ζ : ℝ => delAtomPairFT n δ zMinus zPlus ζ with hg
  -- STEP 1: rewrite cleanFT(π) as the circular convolution (1/(2π:ℂ)) ∫ f η · g(π - η).
  have hconv : cleanFT n δ zMinus zPlus Real.pi
      = (1 / (2 * Real.pi : ℂ)) *
          ∫ η in (-Real.pi)..Real.pi, f η * g (Real.pi - η) := by
    rw [cleanThreeFactor_FT_eq_conv n δ zMinus zPlus Real.pi]
    congr 1
    apply intervalIntegral.integral_congr
    intro η _
    simp only [hf, hg]
    -- second factor is delAtomPairFT at (π - η); reconcile the cast in the exponent
    unfold delAtomPairFT
    congr 1
    apply tsum_congr
    intro r
    congr 2
    push_cast
    ring
  rw [hconv]
  -- STEP 2: periodicity & integrability hypotheses.
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
  -- STEP 3: apply the circular-convolution triangle axiom at ξ = π.
  exact ModulusOfCircularConvolutionTriangle f g hfper hgper hfint hgint Real.pi

end Workspace.PriorWork.CleanFTOuterModulusBound
