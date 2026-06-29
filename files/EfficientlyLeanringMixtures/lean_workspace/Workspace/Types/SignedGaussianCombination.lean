import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.Types.SignedGaussianCombination

open Workspace.Types.GaussianPDF

/--
A signed (real-coefficient) linear combination of one-dimensional Gaussian densities.

Mathematically this represents a function

  `f(x) = Σ_{i = 1..n} a_i · N(μ_i, σ_i², x)`

where each `a_i ∈ ℝ` may be positive, negative, or zero, and each `N(μ_i, σ_i², ·)`
is a Gaussian PDF (with strictly positive variance, packaged in `GaussianPDF`).

The combination is stored as a `List` of `(coefficient, Gaussian)` pairs. We do **not**
require:

* the coefficients to sum to one (so this is not a probabilistic mixture);
* the coefficients to be non-negative;
* the underlying Gaussians to have distinct means or variances.

Downstream lemmas/predicates (e.g. the "up to 6 components with distinct variances"
constraint used by Proposition 7 of Moitra–Valiant) live outside this structure.

The empty combination `⟨[]⟩` represents the zero function (see `density_empty`).
-/
structure SignedGaussianCombination where
  /-- The list of `(coefficient, Gaussian)` pairs comprising the combination. -/
  components : List (ℝ × GaussianPDF)

namespace SignedGaussianCombination

/--
The density of a signed Gaussian combination, defined as

  `S.density x = Σ_{(a, G) ∈ S.components} a · G.density x`.

`noncomputable` because each `GaussianPDF.density` is itself `noncomputable`
(it uses `Real.sqrt` and `Real.exp`). The empty combination yields the
constant zero function.
-/
noncomputable def density (S : SignedGaussianCombination) : ℝ → ℝ :=
  fun x => (S.components.map (fun p => p.1 * p.2.density x)).sum

/--
Explicit unfolding lemma: `density` is exactly the sum over `components` of
`coefficient * Gaussian.density x`. Holds by definition.
-/
theorem density_eq (S : SignedGaussianCombination) (x : ℝ) :
    S.density x = (S.components.map (fun p => p.1 * p.2.density x)).sum := rfl

/--
Point-free version of `density_eq`.
-/
theorem density_def (S : SignedGaussianCombination) :
    S.density = fun x => (S.components.map (fun p => p.1 * p.2.density x)).sum := rfl

/-- The empty signed combination has identically zero density. -/
theorem density_empty (x : ℝ) :
    (⟨[]⟩ : SignedGaussianCombination).density x = 0 := rfl

end SignedGaussianCombination

end Workspace.Types.SignedGaussianCombination
