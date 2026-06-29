import Mathlib
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureRawMoments
import Workspace.Types.GaussianPDF

open MeasureTheory ProbabilityTheory

namespace Workspace.ProofLemmas.M0Helpers

/-- Helper: integral of a `GaussianPDF.density` over volume equals `1`. -/
private lemma integral_gaussianPDF_density_eq_one
    (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    ∫ x, G.density x ∂MeasureTheory.volume = 1 := by
  set v : NNReal := ⟨G.varSq, le_of_lt G.varSq_pos⟩ with hv_def
  have hv_ne : v ≠ 0 := by
    intro h
    have h1 : (v : ℝ) = 0 := by rw [h]; rfl
    have h2 : (v : ℝ) = G.varSq := rfl
    linarith [G.varSq_pos]
  have hdens : (fun x : ℝ => G.density x) =
      (fun x : ℝ => gaussianPDFReal G.mean v x) := by
    funext x
    exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal G x
  show ∫ x, G.density x ∂volume = 1
  rw [show (fun x => G.density x) = fun x => gaussianPDFReal G.mean v x from hdens]
  rw [integral_eq_lintegral_of_nonneg_ae]
  · rw [lintegral_gaussianPDFReal_eq_one G.mean hv_ne]
    rfl
  · filter_upwards with x using gaussianPDFReal_nonneg G.mean v x
  · exact (integrable_gaussianPDFReal G.mean v).aestronglyMeasurable

/-- Helper: `GaussianPDF.density` is volume-integrable. -/
private lemma integrable_gaussianPDF_density
    (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Integrable (fun x => G.density x) MeasureTheory.volume := by
  set v : NNReal := ⟨G.varSq, le_of_lt G.varSq_pos⟩ with hv_def
  have hdens : (fun x : ℝ => G.density x) =
      (fun x : ℝ => gaussianPDFReal G.mean v x) := by
    funext x
    exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal G x
  rw [show (fun x => G.density x) = fun x => gaussianPDFReal G.mean v x from hdens]
  exact integrable_gaussianPDFReal G.mean v

end Workspace.ProofLemmas.M0Helpers

theorem M0OfMixtureDifferenceIsZero
    (G G' : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 G 0 = 1
    ∧ Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 G' 0 = 1
    ∧ Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 G 0
        - Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 G' 0 = 0 := by
  have key : ∀ (F : Workspace.Types.GaussianMixture2.GaussianMixture2),
      Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F 0 = 1 := by
    intro F
    unfold Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
    simp only [pow_zero, one_mul]
    have hdensity : ∀ x, F.density x =
        F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x := by
      intro x
      exact Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq F x
    rw [show (fun x => F.density x) =
        fun x => F.weight1 * F.comp1.density x + F.weight2 * F.comp2.density x from by
      funext x; exact hdensity x]
    have h_int1 : MeasureTheory.Integrable
        (fun x => F.weight1 * F.comp1.density x) MeasureTheory.volume :=
      (Workspace.ProofLemmas.M0Helpers.integrable_gaussianPDF_density F.comp1).const_mul
        F.weight1
    have h_int2 : MeasureTheory.Integrable
        (fun x => F.weight2 * F.comp2.density x) MeasureTheory.volume :=
      (Workspace.ProofLemmas.M0Helpers.integrable_gaussianPDF_density F.comp2).const_mul
        F.weight2
    rw [MeasureTheory.integral_add h_int1 h_int2]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [Workspace.ProofLemmas.M0Helpers.integral_gaussianPDF_density_eq_one F.comp1]
    rw [Workspace.ProofLemmas.M0Helpers.integral_gaussianPDF_density_eq_one F.comp2]
    rw [mul_one, mul_one]
    exact F.weights_sum_one
  refine ⟨key G, key G', ?_⟩
  rw [key G, key G']
  ring
