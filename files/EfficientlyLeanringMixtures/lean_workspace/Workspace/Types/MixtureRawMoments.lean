import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.SignedGaussianCombination

set_option maxHeartbeats 400000

namespace Workspace.Types.MixtureRawMoments

/--
The `i`-th raw moment of a single Gaussian probability density function,

  `M_i(G) := ∫_ℝ x^i · G.density(x) dx`,

defined as a Lebesgue integral against `MeasureTheory.volume` on `ℝ`. The integral
exists and is finite for every `i : ℕ` because Gaussian densities have all moments;
the existence claim is not enforced here in the definition itself but appears as
separate (downstream) theorems. The definition is given by the explicit integral
formula in all cases — there is no closed-form polynomial in `(μ, σ²)` baked in
at the definitional level.

`noncomputable` because `GaussianPDF.density` is itself `noncomputable` and
`MeasureTheory.integral` requires classical choice.
-/
noncomputable def rawMoment_ofGaussian :
    Workspace.Types.GaussianPDF.GaussianPDF → ℕ → ℝ :=
  fun G i => ∫ x, x ^ i * G.density x ∂MeasureTheory.volume

/--
The `i`-th raw moment of a two-component Gaussian probability mixture,

  `M_i(F) := ∫_ℝ x^i · F.density(x) dx`,

defined as a Lebesgue integral against `MeasureTheory.volume` on `ℝ`. By linearity
of the integral one expects `M_i(F) = w₁ · M_i(N(μ₁,σ₁²)) + w₂ · M_i(N(μ₂,σ₂²))`;
that decomposition is a separately-stated lemma downstream.

`noncomputable` for the same reasons as `rawMoment_ofGaussian`.
-/
noncomputable def rawMoment_ofMixture2 :
    Workspace.Types.GaussianMixture2.GaussianMixture2 → ℕ → ℝ :=
  fun F i => ∫ x, x ^ i * F.density x ∂MeasureTheory.volume

/--
The `i`-th raw moment of a signed (real-coefficient) linear combination of Gaussian
densities,

  `M_i(S) := ∫_ℝ x^i · S.density(x) dx`,

defined as a Lebesgue integral against `MeasureTheory.volume` on `ℝ`. Coefficients
in `S` may be negative or zero, so this is a genuinely signed integral; the result
can be any real number.

`noncomputable` for the same reasons as `rawMoment_ofGaussian`.
-/
noncomputable def rawMoment_ofSigned :
    Workspace.Types.SignedGaussianCombination.SignedGaussianCombination → ℕ → ℝ :=
  fun S i => ∫ x, x ^ i * S.density x ∂MeasureTheory.volume

/-- Explicit unfolding lemma for `rawMoment_ofGaussian`: matches the spec formula
verbatim. Holds by definition. -/
theorem rawMoment_ofGaussian_def
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) :
    rawMoment_ofGaussian G i = ∫ x, x ^ i * G.density x ∂MeasureTheory.volume := rfl

/-- Explicit unfolding lemma for `rawMoment_ofMixture2`: matches the spec formula
verbatim. Holds by definition. -/
theorem rawMoment_ofMixture2_def
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2) (i : ℕ) :
    rawMoment_ofMixture2 F i = ∫ x, x ^ i * F.density x ∂MeasureTheory.volume := rfl

/-- Explicit unfolding lemma for `rawMoment_ofSigned`: matches the spec formula
verbatim. Holds by definition. -/
theorem rawMoment_ofSigned_def
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) (i : ℕ) :
    rawMoment_ofSigned S i = ∫ x, x ^ i * S.density x ∂MeasureTheory.volume := rfl

end Workspace.Types.MixtureRawMoments
