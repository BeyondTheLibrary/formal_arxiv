import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

set_option maxHeartbeats 400000

namespace Workspace.ProofLemmas

open MeasureTheory

/-- Integrability of a single Gaussian PDF (`i = 0` specialisation of
`SublemmaIntegrabilityXPowGaussian`). -/
private lemma SDI_integrable_gaussian_density
    (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Integrable (fun x : ℝ => G.density x) volume := by
  have h : Integrable (fun x : ℝ => x ^ 0 * G.density x) volume :=
    SublemmaIntegrabilityXPowGaussian G 0
  simpa using h

theorem SublemmaSGCDensityIntegrable
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) :
    MeasureTheory.Integrable S.density MeasureTheory.volume := by
  -- Rewrite S.density as the list sum.
  have hrw : (fun x : ℝ => S.density x) =
      (fun x : ℝ =>
        (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            q.1 * q.2.density x)).sum) := by
    funext x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
  -- Rewrite `S.density` as itself-as-fun (eta).
  show Integrable S.density volume
  have hS : S.density = (fun x : ℝ =>
      (S.components.map
        (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
          q.1 * q.2.density x)).sum) := by
    funext x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
  rw [hS]
  -- Induct over the component list.
  induction S.components with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact integrable_zero _ _ _
  | cons q rest ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Integrable.add
    · exact (SDI_integrable_gaussian_density q.2).const_mul q.1
    · exact ih

end Workspace.ProofLemmas
