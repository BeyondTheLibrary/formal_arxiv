import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.SignedGaussianCombination

set_option maxHeartbeats 400000

namespace Workspace.Types.L1AndTVDistance

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.SignedGaussianCombination

/--
The `L¹`-norm of a real-valued function on `ℝ` with respect to Lebesgue measure:

  `L1Norm f = ∫ x, |f x| dx`.

This is the elementary `L¹`-norm used throughout Section 2 of Moitra–Valiant
(the variation distance `D(F, G) = (1/2) · ‖F − G‖₁`). We define it directly as
a Bochner integral of `|f|` against `MeasureTheory.volume`; no integrability
hypothesis is baked in (if `|f|` is not Lebesgue-integrable, the Bochner
integral is `0` by Mathlib convention, but downstream lemmas can supply
integrability when they need it).

`noncomputable` because the Bochner integral is `noncomputable`.
-/
noncomputable def L1Norm : (ℝ → ℝ) → ℝ :=
  fun f => ∫ x, |f x| ∂MeasureTheory.volume

/--
The `L¹`-norm of a signed Gaussian combination, evaluated on its density:

  `L1NormSigned S = L1Norm S.density = ∫ x, |S.density x| dx`.

`noncomputable` because `L1Norm` and `SignedGaussianCombination.density` both are.
-/
noncomputable def L1NormSigned :
    Workspace.Types.SignedGaussianCombination.SignedGaussianCombination → ℝ :=
  fun S => L1Norm S.density

/--
The `L¹`-norm of the difference of two `GaussianMixture2` densities:

  `L1NormMixtureDiff F G = ∫ x, |F.density x − G.density x| dx`.

This is the quantity `‖F − G‖₁` from Section 2 of Moitra–Valiant.
-/
noncomputable def L1NormMixtureDiff :
    Workspace.Types.GaussianMixture2.GaussianMixture2 →
    Workspace.Types.GaussianMixture2.GaussianMixture2 → ℝ :=
  fun F G => L1Norm (fun x => F.density x - G.density x)

/--
The total-variation distance between two `GaussianMixture2` distributions, as
used in Theorem 4 / Section 2 of Moitra–Valiant:

  `TVDistance F G = (1 / 2) · ‖F − G‖₁ = (1 / 2) · ∫ x, |F.density x − G.density x| dx`.

We expose the explicit `(1/2) · ‖·‖₁` formula (rather than Mathlib's general
TV-distance between measures) because the proof of Theorem 4 manipulates the
integral directly.
-/
noncomputable def TVDistance :
    Workspace.Types.GaussianMixture2.GaussianMixture2 →
    Workspace.Types.GaussianMixture2.GaussianMixture2 → ℝ :=
  fun F G => (1 / 2) * L1NormMixtureDiff F G

/-- Definitional unfolding of `L1Norm`. -/
theorem L1Norm_def (f : ℝ → ℝ) :
    L1Norm f = ∫ x, |f x| ∂MeasureTheory.volume := rfl

/-- Definitional unfolding of `L1NormSigned`. -/
theorem L1NormSigned_def
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) :
    L1NormSigned S = L1Norm S.density := rfl

/-- Definitional unfolding of `L1NormMixtureDiff`. -/
theorem L1NormMixtureDiff_def
    (F G : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    L1NormMixtureDiff F G = L1Norm (fun x => F.density x - G.density x) := rfl

/-- Definitional unfolding of `TVDistance`. -/
theorem TVDistance_def
    (F G : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    TVDistance F G = (1 / 2) * L1NormMixtureDiff F G := rfl

end Workspace.Types.L1AndTVDistance
