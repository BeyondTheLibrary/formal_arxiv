import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

/-!
# Variance-perturbation family for the Prop 7 general-case reduction

Given a base `SignedGaussianCombination` `S` with `k = S.components.length`
components and a parameter `δ ≥ 0`, this file defines the one-parameter family

  `S_δ` = same coefficients `aᵢ` and means `μᵢ` as `S`, but with the variance of
  the component at 0-based index `i` replaced by `σᵢ² + δ·(i+1)/k`.

So `S_0 = S`, and for small positive `δ` the variances become pairwise distinct.
This is the concrete family used by `DistinctVariancePerturbationExists` and
`SimpleZeroPersistsUnderVariancePerturbation`.

The shift `δ·(i+1)/k` is `≥ 0` whenever `δ ≥ 0`, so the perturbed variance stays
strictly positive; the def therefore takes a proof `0 ≤ δ` to supply
`GaussianPDF.varSq_pos`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

/-- The perturbed variance of the `i`-th (0-based) component of a length-`k`
combination at parameter `δ`: `σᵢ² + δ·(i+1)/k`. -/
noncomputable def perturbVarSq (σSq δ : ℝ) (i k : ℕ) : ℝ :=
  σSq + δ * (i + 1) / k

/-- `perturbVarSq` is strictly positive when the base variance is positive,
`δ ≥ 0`, and `k ≥ 1` (the shift `δ·(i+1)/k` is `≥ 0`). -/
theorem perturbVarSq_pos {σSq δ : ℝ} (hσ : 0 < σSq) (hδ : 0 ≤ δ)
    (i k : ℕ) (hk : 1 ≤ k) : 0 < perturbVarSq σSq δ i k := by
  unfold perturbVarSq
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  have : 0 ≤ δ * (i + 1) / k := by positivity
  linarith

/-- The variance-perturbation family `S_δ` as a `SignedGaussianCombination`.

Each base component `(aᵢ, Gᵢ)` at 0-based index `i` is mapped to
`(aᵢ, ⟨Gᵢ.mean, Gᵢ.varSq + δ·(i+1)/k, _⟩)` where `k = S.components.length`.
Requires `0 ≤ δ` so the perturbed variances are positive. -/
noncomputable def variancePerturb
    (S : SignedGaussianCombination) (δ : ℝ) (hδ : 0 ≤ δ) :
    SignedGaussianCombination :=
  let k := S.components.length
  ⟨(List.finRange k).map
      (fun i =>
        let p := S.components.get i
        (p.1,
         ({ mean := p.2.mean,
            varSq := perturbVarSq p.2.varSq δ i.val k,
            varSq_pos :=
              perturbVarSq_pos p.2.varSq_pos hδ i.val k
                (by
                  have : 0 < k := i.pos
                  omega) } : GaussianPDF)))⟩

/-- The perturbed combination has the same number of components as `S`. -/
theorem variancePerturb_length
    (S : SignedGaussianCombination) (δ : ℝ) (hδ : 0 ≤ δ) :
    (variancePerturb S δ hδ).components.length = S.components.length := by
  unfold variancePerturb
  simp

end Workspace.ProofLemmas
