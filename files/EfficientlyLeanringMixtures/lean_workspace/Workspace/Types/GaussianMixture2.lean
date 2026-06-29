import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.Types.GaussianMixture2

/--
A two-component univariate Gaussian probability mixture

  `F(x) = w₁ · N(μ₁, σ₁², x) + w₂ · N(μ₂, σ₂², x)`

with non-negative mixing weights summing to one. The components are individual
`GaussianPDF` records (each carrying its mean and *variance* together with the
positivity proof for the variance).

The strict-positivity condition `w_i ≥ ε > 0` that appears in the paper's
`ε`-standard predicate is intentionally *not* enforced here: this type allows
`weight_i = 0`, i.e. the degenerate single-Gaussian case. Strict positivity is
the job of a separate (downstream) predicate.
-/
structure GaussianMixture2 where
  /-- The first mixing weight `w₁`. -/
  weight1 : ℝ
  /-- The second mixing weight `w₂`. -/
  weight2 : ℝ
  /-- The first Gaussian component `N(μ₁, σ₁²)`. -/
  comp1 : Workspace.Types.GaussianPDF.GaussianPDF
  /-- The second Gaussian component `N(μ₂, σ₂²)`. -/
  comp2 : Workspace.Types.GaussianPDF.GaussianPDF
  /-- The first mixing weight is non-negative. -/
  weight1_nonneg : weight1 ≥ 0
  /-- The second mixing weight is non-negative. -/
  weight2_nonneg : weight2 ≥ 0
  /-- The mixing weights sum to one. -/
  weights_sum_one : weight1 + weight2 = 1

namespace GaussianMixture2

/--
The probability density function of the mixture, as a real-valued function of `x`:

  `density F x = F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x`.

`noncomputable` because the component densities use `Real.sqrt` and `Real.exp`.
-/
noncomputable def density (F : GaussianMixture2) : ℝ → ℝ := fun x =>
  F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x

/-- Explicit unfolding lemma for `GaussianMixture2.density`. Matches the formula in
the spec verbatim; can be applied via `simp only [GaussianMixture2.density_eq]` or
by direct rewriting. -/
theorem density_eq (F : GaussianMixture2) (x : ℝ) :
    F.density x = F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x := rfl

/-- Point-free unfolding lemma for `GaussianMixture2.density`. -/
theorem density_def (F : GaussianMixture2) :
    F.density = fun x => F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x := rfl

end GaussianMixture2

end Workspace.Types.GaussianMixture2
