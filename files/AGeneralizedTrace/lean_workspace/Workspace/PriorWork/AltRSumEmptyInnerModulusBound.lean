-- Inner circular-convolution modulus bound on `delAtomPairFT` (k = 0 / empty-ℓ
-- case of Lemma 8, arXiv:2412.00674v1, §3, lines 369-381).
--
-- SORRY-FREE. Pointwise bound, for every ζ:
--   ‖delAtomPairFT(ζ)‖ ≤ (1/2π) ∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT(ζ-η')‖ dη'.
-- Obtained by applying `ModulusOfCircularConvolutionTriangle` to the inner
-- convolution `delAtomPair_FT_eq_conv`, with the periodicity + integrability of
-- the two deletion-atom Fourier transforms.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.DelAtomPairFTContinuity
import Workspace.PriorWork.ModulusOfCircularConvolutionTriangle

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyInnerModulusBound

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.DelAtomPairFTContinuity

/-- The Fourier transform of `delAtom2`, as a function of `ξ`. -/
noncomputable def delAtom2FT (n : ℕ) (δ : ℝ) (zMinus : ℕ) (ξ : ℝ) : ℂ :=
  ∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))

/-- The Fourier transform of `delAtom3`, as a function of `ξ`. -/
noncomputable def delAtom3FT (n : ℕ) (δ : ℝ) (zPlus : ℕ) (ξ : ℝ) : ℂ :=
  ∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))

theorem delAtom2FT_periodic (n : ℕ) (δ : ℝ) (zMinus : ℕ) (x : ℝ) :
    delAtom2FT n δ zMinus (x + 2 * Real.pi) = delAtom2FT n δ zMinus x := by
  unfold delAtom2FT
  exact discreteFT_periodic (fun r : ℤ => ((delAtom2 n δ zMinus r : ℝ) : ℂ)) x

theorem delAtom3FT_periodic (n : ℕ) (δ : ℝ) (zPlus : ℕ) (x : ℝ) :
    delAtom3FT n δ zPlus (x + 2 * Real.pi) = delAtom3FT n δ zPlus x := by
  unfold delAtom3FT
  exact discreteFT_periodic (fun r : ℤ => ((delAtom3 n δ zPlus r : ℝ) : ℂ)) x

theorem delAtom2FT_integrableOn (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) :
    MeasureTheory.IntegrableOn (fun ξ : ℝ => delAtom2FT n δ zMinus ξ)
      (Set.Icc (-Real.pi) Real.pi) :=
  delAtom2_FT_integrableOn n δ hδ0 hδ1 zMinus

theorem delAtom3FT_integrableOn (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) :
    MeasureTheory.IntegrableOn (fun ξ : ℝ => delAtom3FT n δ zPlus ξ)
      (Set.Icc (-Real.pi) Real.pi) :=
  delAtom3_FT_integrableOn n δ hδ0 hδ1 zPlus

/-- **Inner triangle modulus bound on `delAtomPairFT(ζ)`.** For every `ζ`,
`‖delAtomPairFT(ζ)‖ ≤ (1/2π) ∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT(ζ-η')‖ dη'`. -/
theorem delAtomPairFT_abs_le_inner_modulus_integral
    (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (zMinus zPlus : ℕ) (ζ : ℝ) :
    ‖delAtomPairFT n δ zMinus zPlus ζ‖
      ≤ (1 / (2 * Real.pi)) *
          ∫ η' in (-Real.pi)..Real.pi,
            ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖ := by
  set f : ℝ → ℂ := fun η : ℝ => delAtom2FT n δ zMinus η with hf
  set g : ℝ → ℂ := fun ξ : ℝ => delAtom3FT n δ zPlus ξ with hg
  -- rewrite delAtomPairFT(ζ) as the convolution (1/(2π:ℂ)) ∫ f η · g(ζ - η)
  have hconv : delAtomPairFT n δ zMinus zPlus ζ
      = (1 / (2 * Real.pi : ℂ)) *
          ∫ η in (-Real.pi)..Real.pi, f η * g (ζ - η) := by
    unfold delAtomPairFT
    rw [delAtomPair_FT_eq_conv n δ hδ0 hδ1 zMinus zPlus ζ]
    congr 1
    apply intervalIntegral.integral_congr
    intro η _
    simp only [hf, hg, delAtom2FT, delAtom3FT]
    congr 1
    apply tsum_congr
    intro r
    congr 2
    push_cast
    ring
  rw [hconv]
  have hfper : ∀ x, f (x + 2 * Real.pi) = f x := fun x => delAtom2FT_periodic n δ zMinus x
  have hgper : ∀ x, g (x + 2 * Real.pi) = g x := fun x => delAtom3FT_periodic n δ zPlus x
  have hfint : MeasureTheory.IntegrableOn f (Set.Icc (-Real.pi) Real.pi) :=
    delAtom2FT_integrableOn n δ hδ0 hδ1 zMinus
  have hgint : MeasureTheory.IntegrableOn g (Set.Icc (-Real.pi) Real.pi) :=
    delAtom3FT_integrableOn n δ hδ0 hδ1 zPlus
  exact ModulusOfCircularConvolutionTriangle f g hfper hgper hfint hgint ζ

end Workspace.PriorWork.AltRSumEmptyInnerModulusBound
