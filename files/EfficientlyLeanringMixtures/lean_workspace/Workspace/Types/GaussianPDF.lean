import Mathlib

set_option maxHeartbeats 400000

namespace Workspace.Types.GaussianPDF

/--
A single one-dimensional Gaussian probability density function, parameterised by a
real mean `μ` and a strictly positive *variance* `σ²` (NOT the standard deviation).

The density function is

  `N(μ, σ², x) = (1 / √(2π σ²)) · exp(-(x - μ)² / (2 σ²))`

and is exposed via `GaussianPDF.density` below.
-/
structure GaussianPDF where
  /-- The mean `μ ∈ ℝ`. -/
  mean : ℝ
  /-- The *variance* `σ² ∈ ℝ`, NOT the standard deviation `σ`.
      Field name `varSq` is chosen to make this unambiguous. -/
  varSq : ℝ
  /-- Strict positivity of the variance. A Gaussian PDF is only defined for `σ² > 0`. -/
  varSq_pos : 0 < varSq

namespace GaussianPDF

/--
The Gaussian probability density function as a real-valued function of `x`, given
explicitly by the formula

  `density G x = (1 / √(2π · G.varSq)) · exp(-(x - G.mean)² / (2 · G.varSq))`.

`noncomputable` because it uses `Real.sqrt` and `Real.exp`.
-/
noncomputable def density (G : GaussianPDF) : ℝ → ℝ := fun x =>
  (1 / Real.sqrt (2 * Real.pi * G.varSq))
    * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))

/-- Explicit unfolding lemma for `GaussianPDF.density`. Matches the formula in the spec
verbatim and can be applied via `simp only [GaussianPDF.density_eq]` or by direct
rewriting. -/
theorem density_eq (G : GaussianPDF) (x : ℝ) :
    G.density x =
      (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)) := rfl

/-- Convenient unfolding lemma that exposes `density` as a function (point-free form). -/
theorem density_def (G : GaussianPDF) :
    G.density = fun x =>
      (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)) := rfl

/--
Relating our density to Mathlib's `ProbabilityTheory.gaussianPDFReal`. Mathlib uses
`NNReal` for the variance argument; once we coerce `G.varSq` (with its positivity
hypothesis) to `NNReal`, the two definitions agree.
-/
theorem density_eq_gaussianPDFReal (G : GaussianPDF) (x : ℝ) :
    G.density x =
      ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩ x := by
  rw [density_eq, ProbabilityTheory.gaussianPDFReal_def]
  show (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))
      = (Real.sqrt (2 * Real.pi * G.varSq))⁻¹
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))
  rw [one_div]

end GaussianPDF

end Workspace.Types.GaussianPDF
