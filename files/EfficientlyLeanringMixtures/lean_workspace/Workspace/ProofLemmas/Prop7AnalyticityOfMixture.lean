import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

/--
For every signed Gaussian combination `S` with components `{(a_i, G_i)}_{i=1..n}`,
where each `G_i` has variance `σ_i² > 0`, the density function `S.density : ℝ → ℝ`
defined by `x ↦ Σ_i a_i · N(μ_i, σ_i², x)` is real-analytic on all of `ℝ`.

Specifically, `AnalyticOnNhd ℝ S.density Set.univ` holds.

The proof goes: each Gaussian density `N(μ, σ², ·)` is real-analytic (composition
of `Real.exp`, a polynomial in `x`, and a constant multiplier); real-analyticity
is closed under finite linear combinations; and a finite `List.sum` of analytic
functions is analytic.
-/
theorem Prop7AnalyticityOfMixture :
    ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination),
      AnalyticOnNhd ℝ S.density Set.univ := by
  intro S
  rw [SignedGaussianCombination.density_def]
  induction S.components with
  | nil =>
    simp
    exact analyticOnNhd_const
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    refine AnalyticOnNhd.add ?_ ih
    refine analyticOnNhd_const.mul ?_
    rw [GaussianPDF.density_def]
    refine analyticOnNhd_const.mul ?_
    refine analyticOnNhd_rexp.comp ?_ (fun _ _ => Set.mem_univ _)
    apply AnalyticOnNhd.div_const
    apply AnalyticOnNhd.neg
    apply AnalyticOnNhd.pow
    exact analyticOnNhd_id.sub analyticOnNhd_const

end Workspace.ProofLemmas
