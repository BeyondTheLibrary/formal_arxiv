import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Lemma5LocalizedWeightGapTV

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory

/-- Each `GaussianPDF` density is integrable on ℝ. -/
private lemma case2a_density_integrable (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    MeasureTheory.Integrable G.density MeasureTheory.volume := by
  have h : G.density = fun x => ProbabilityTheory.gaussianPDFReal G.mean
      ⟨G.varSq, le_of_lt G.varSq_pos⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h]; exact ProbabilityTheory.integrable_gaussianPDFReal _ _

/-- A `GaussianMixture2` density is integrable on ℝ. -/
private lemma case2a_mixture_integrable
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    MeasureTheory.Integrable F.density MeasureTheory.volume := by
  unfold Workspace.Types.GaussianMixture2.GaussianMixture2.density
  exact ((case2a_density_integrable F.comp1).const_mul F.weight1).add
        ((case2a_density_integrable F.comp2).const_mul F.weight2)

theorem Lemma5Case2aAssembly :
    ∃ K_5_2a ε_max : ℝ, 0 < K_5_2a ∧ 0 < ε_max ∧
      ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
        0 < ε → ε ≤ 1 → ε ≤ ε_max →
        Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
        F.comp1.varSq ≤ F.comp2.varSq →
        F.comp1.varSq ≤ F'.comp1.varSq →
        F.comp1.varSq ≤ F'.comp2.varSq →
        F'.comp1.varSq - F.comp1.varSq < 16 * ε ^ 10 →
        |F'.comp1.mean - F.comp1.mean| < 6 * ε ^ 5 →
        ε ^ 2 ≤ |F.weight1 - F'.weight1| →
        ∃ α : ℝ,
          ∃ h₁ : α < min F.comp1.varSq F.comp2.varSq,
            ∃ h₂ : α < min F'.comp1.varSq F'.comp2.varSq,
              (-1 : ℝ) ≤ α
              ∧ ε ^ 12 ≤
                  min
                    (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp1.varSq
                         (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp2.varSq)
                    (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp1.varSq
                         (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp2.varSq)
              ∧ K_5_2a * ε ^ 4 ≤
                  Workspace.Types.L1AndTVDistance.TVDistance
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) := by
  refine ⟨1/4, 1/100000, by norm_num, by norm_num, ?_⟩
  intro F F' ε hε_pos hε_le_one hε_small h_std h12 h1'1 h1'2 hCase2_var hCase2_mean hCase2a_w
  set α : ℝ := F.comp1.varSq - ε^8 with hα_def
  have hF1_pos : 0 < F.comp1.varSq := F.comp1.varSq_pos
  have hε8_pos : 0 < ε^8 := by positivity
  have hε_nn : 0 ≤ ε := le_of_lt hε_pos
  have hε8_le_one : ε^8 ≤ 1 := by
    have := pow_le_pow_left₀ hε_nn hε_le_one 8; simpa using this
  have hε12_pos : 0 < ε^12 := by positivity
  have hε12_le_ε8 : ε^12 ≤ ε^8 := by
    have hrw : ε^12 = ε^8 * ε^4 := by ring
    rw [hrw]
    have h_ε4_le1 : ε^4 ≤ 1 := by
      have := pow_le_pow_left₀ hε_nn hε_le_one 4; simpa using this
    have hh := mul_le_mul_of_nonneg_left h_ε4_le1 (le_of_lt hε8_pos)
    simpa using hh
  have hα_lt_F1 : α < F.comp1.varSq := by rw [hα_def]; linarith
  have hα_lt_F2 : α < F.comp2.varSq := by rw [hα_def]; linarith
  have h₁ : α < min F.comp1.varSq F.comp2.varSq := lt_min hα_lt_F1 hα_lt_F2
  have hα_lt_F'1 : α < F'.comp1.varSq := by rw [hα_def]; linarith
  have hα_lt_F'2 : α < F'.comp2.varSq := by rw [hα_def]; linarith
  have h₂ : α < min F'.comp1.varSq F'.comp2.varSq := lt_min hα_lt_F'1 hα_lt_F'2
  refine ⟨α, h₁, h₂, ?_, ?_, ?_⟩
  · rw [hα_def]; linarith [hF1_pos]
  · have h_F1_var : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp1.varSq
                    = F.comp1.varSq - α := rfl
    have h_F2_var : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp2.varSq
                    = F.comp2.varSq - α := rfl
    have h_F'1_var : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp1.varSq
                     = F'.comp1.varSq - α := rfl
    have h_F'2_var : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp2.varSq
                     = F'.comp2.varSq - α := rfl
    rw [h_F1_var, h_F2_var, h_F'1_var, h_F'2_var]
    have h_F1 : F.comp1.varSq - α = ε^8 := by rw [hα_def]; ring
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · rw [h_F1]; exact hε12_le_ε8
    · rw [hα_def]; linarith [hε12_le_ε8]
    · rw [hα_def]; linarith [hε12_le_ε8]
    · rw [hα_def]; linarith [hε12_le_ε8]
  · -- TV bound via the localized weight-gap lemma (compactness-free, both weight directions).
    have hsub : ε ^ 2 / 4 ≤
        Workspace.Types.L1AndTVDistance.TVDistance
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) :=
      Lemma5LocalizedWeightGapTV F F' ε hε_pos hε_le_one h_std h12 h1'1 h1'2
        hCase2_var hCase2_mean hCase2a_w hε_small h₁ h₂
    have hε4_le_ε2 : ε^4 ≤ ε^2 := by
      have : ε^2 * ε^2 ≤ ε^2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hε_le_one, hε_pos.le]
      nlinarith [this]
    nlinarith [hsub, hε4_le_ε2]

end Workspace.ProofLemmas
