import Mathlib
import Workspace.Types.GaussianConvolution

open MeasureTheory

namespace Workspace.ProofLemmas

theorem ConvolveWithGaussianBounded
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C)
    (σSq : ℝ) (h_pos : 0 < σSq) :
    ∃ C' : ℝ, ∀ x : ℝ,
      |Workspace.Types.GaussianConvolution.convolveWithGaussian f σSq h_pos x| ≤ C' := by
  obtain ⟨C, hC⟩ := hf_bdd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hC 0)
  refine ⟨C, fun x => ?_⟩
  -- the centered gaussian PDF as a NNReal-variance gaussianPDFReal
  set v : NNReal := ⟨σSq, le_of_lt h_pos⟩ with hv
  have hv_ne : v ≠ 0 := by
    have : (0 : ℝ) < (v : ℝ) := by rw [hv]; exact h_pos
    intro hcontra
    rw [hcontra] at this
    simp at this
  -- rewrite density as gaussianPDFReal
  have hdens : ∀ z : ℝ,
      Workspace.Types.GaussianPDF.GaussianPDF.density ⟨0, σSq, h_pos⟩ z
        = ProbabilityTheory.gaussianPDFReal 0 v z := by
    intro z
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal ⟨0, σSq, h_pos⟩ z]
  -- abbreviation for the gaussian density centered at 0
  set g : ℝ → ℝ := fun z => ProbabilityTheory.gaussianPDFReal 0 v z with hg
  -- g is nonneg
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z =>
    ProbabilityTheory.gaussianPDFReal_nonneg 0 v z
  -- g integrable
  have hg_int : Integrable g volume :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 v
  -- ∫ g = 1
  have hg_one : ∫ z, g z ∂volume = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv_ne
  -- unfold convolution
  rw [Workspace.Types.GaussianConvolution.convolveWithGaussian_def]
  -- rewrite the integrand using hdens
  have hrw : (fun y => f y *
      (Workspace.Types.GaussianPDF.GaussianPDF.density ⟨0, σSq, h_pos⟩ (x - y)))
      = (fun y => f y * g (x - y)) := by
    funext y
    rw [hdens (x - y)]
  rw [hrw]
  -- translation invariance: ∫ y, g (x - y) = ∫ y, g y = 1
  have htrans : (∫ y, g (x - y) ∂volume) = 1 := by
    rw [MeasureTheory.integral_sub_left_eq_self g volume x, hg_one]
  -- integrability of y ↦ f y * g (x - y)
  have hgx_int : Integrable (fun y => g (x - y)) volume := by
    have := (MeasureTheory.integral_sub_left_eq_self g volume x)
    exact (hg_int.comp_sub_left x)
  have hprod_int : Integrable (fun y => f y * g (x - y)) volume := by
    apply MeasureTheory.Integrable.mono' (g := fun y => C * g (x - y))
    · exact hgx_int.const_mul C
    · exact (hf_cont.aestronglyMeasurable.mul hgx_int.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nonneg (x - y))]
      exact mul_le_mul_of_nonneg_right (hC y) (hg_nonneg (x - y))
  -- now bound
  calc |∫ y, f y * g (x - y) ∂volume|
      ≤ ∫ y, |f y * g (x - y)| ∂volume := by
        exact MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ y, |f y| * g (x - y) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun y => ?_)
        simp only [abs_mul, abs_of_nonneg (hg_nonneg (x - y))]
    _ ≤ ∫ y, C * g (x - y) ∂volume := by
        apply MeasureTheory.integral_mono_of_nonneg
        · refine Filter.Eventually.of_forall (fun y => ?_)
          exact mul_nonneg (abs_nonneg _) (hg_nonneg (x - y))
        · exact hgx_int.const_mul C
        · refine Filter.Eventually.of_forall (fun y => ?_)
          exact mul_le_mul_of_nonneg_right (hC y) (hg_nonneg (x - y))
    _ = C * ∫ y, g (x - y) ∂volume := by
        rw [MeasureTheory.integral_const_mul]
    _ = C := by rw [htrans, mul_one]

end Workspace.ProofLemmas
