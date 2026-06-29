import Mathlib
import Workspace.Types.L1AndTVDistance

open MeasureTheory

theorem Lemma35L1NormGeSetIntegral :
    ∀ (f : ℝ → ℝ) (S : Set ℝ), MeasurableSet S →
      MeasureTheory.Integrable f MeasureTheory.volume →
      (∫ x in S, |f x| ∂MeasureTheory.volume) ≤ Workspace.Types.L1AndTVDistance.L1Norm f := by
  intro f S hS hf
  unfold Workspace.Types.L1AndTVDistance.L1Norm
  exact MeasureTheory.setIntegral_le_integral hf.abs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
