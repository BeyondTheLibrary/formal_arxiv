import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.Types.GaussianConvolution

open MeasureTheory
open Workspace.Types.GaussianPDF

/--
The centered Gaussian density `N(0, σ², ·)` packaged as a `GaussianPDF` value, given
a strictly positive variance `σSq`. This is the kernel used in `convolveWithGaussian`.
-/
noncomputable def centeredGaussian (σSq : ℝ) (σSq_pos : 0 < σSq) :
    Workspace.Types.GaussianPDF.GaussianPDF :=
  { mean := 0, varSq := σSq, varSq_pos := σSq_pos }

/--
Convolution of an arbitrary `f : ℝ → ℝ` with the centered Gaussian density
`N(0, σ², ·)` of variance `σSq > 0`.

Explicitly,
  `(f * N(0, σ²))(x) = ∫_ℝ f(y) · N(0, σ², x − y) dy`
where the Gaussian density `N(0, σ², ·)` is `(centeredGaussian σSq σSq_pos).density`.

The integral is taken with respect to Lebesgue measure on `ℝ`
(`MeasureTheory.volume`). By Mathlib's convention, `MeasureTheory.integral`
returns `0` for functions that are not integrable, so this definition
makes sense for any `f : ℝ → ℝ` — no integrability hypothesis is needed
in the signature.
-/
noncomputable def convolveWithGaussian :
    (ℝ → ℝ) → (σSq : ℝ) → (σSq_pos : 0 < σSq) → (ℝ → ℝ) :=
  fun f σSq σSq_pos x =>
    ∫ y, f y *
      (Workspace.Types.GaussianPDF.GaussianPDF.density
        ⟨0, σSq, σSq_pos⟩ (x - y)) ∂(MeasureTheory.volume)

/--
Explicit unfolding lemma for `convolveWithGaussian`. Exposes the underlying
integral so that downstream lemmas can reason directly with the Gaussian
density.
-/
theorem convolveWithGaussian_def
    (f : ℝ → ℝ) (σSq : ℝ) (σSq_pos : 0 < σSq) (x : ℝ) :
    convolveWithGaussian f σSq σSq_pos x =
      ∫ y, f y *
        (Workspace.Types.GaussianPDF.GaussianPDF.density
          ⟨0, σSq, σSq_pos⟩ (x - y)) ∂(MeasureTheory.volume) := rfl

end Workspace.Types.GaussianConvolution
