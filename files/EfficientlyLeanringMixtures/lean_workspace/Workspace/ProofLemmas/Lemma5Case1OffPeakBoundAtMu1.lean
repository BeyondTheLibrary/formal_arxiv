import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureDeconvolution
import Workspace.ProofLemmas.Corollary24

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureDeconvolution

/-- Helper: For a Gaussian PDF, the density at any point equals the density of a centred
    Gaussian (mean=0, same variance) at the translated argument. -/
private lemma gaussian_density_eq_centred
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    G.density x =
      ({ mean := 0, varSq := G.varSq, varSq_pos := G.varSq_pos } :
        Workspace.Types.GaussianPDF.GaussianPDF).density (x - G.mean) := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq,
      Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  show (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))
      = (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean - 0) ^ 2 / (2 * G.varSq))
  congr 1
  congr 1
  ring

/-- Helper: Per-component off-peak bound.
    Given the disjunctive Case 1 hypothesis (variance-gap OR mean-gap) for the i-th
    component of F', the density of the i-th deconvolved component at μ_1 is at most
    `1 / (4 · √(2π) · ε^5)`. -/
private lemma off_peak_component_bound
    (G : Workspace.Types.GaussianPDF.GaussianPDF)  -- shifted component
    (Gmean_orig : ℝ)                                -- F'.compi.mean (the original mean)
    (μ1 : ℝ) (varOrig : ℝ) (varBase : ℝ) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le1 : ε ≤ 1)
    (hG_mean : G.mean = Gmean_orig)
    (hG_var : G.varSq = varOrig - (varBase - ε^12))
    (h_disj : 16 * ε^10 ≤ varOrig - varBase ∨ 6 * ε^5 ≤ |Gmean_orig - μ1|) :
    G.density μ1 ≤ 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hε5_pos : 0 < ε^5 := by positivity
  have hε5_nonneg : 0 ≤ ε^5 := le_of_lt hε5_pos
  have hε10_pos : 0 < ε^10 := by positivity
  have hε12_pos : 0 < ε^12 := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have h2pi_nonneg : 0 ≤ 2 * Real.pi := le_of_lt h2pi_pos
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr h2pi_pos
  have hsqrt_2pi_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := le_of_lt hsqrt_2pi_pos
  rcases h_disj with h_var | h_mean
  · -- Variance-gap case: G.varSq ≥ 16·ε^10
    have hG_var_lower : 16 * ε^10 ≤ G.varSq := by
      rw [hG_var]
      have : 16 * ε^10 + ε^12 ≤ varOrig - varBase + ε^12 := by linarith
      have h16 : 16 * ε^10 ≤ 16 * ε^10 + ε^12 := by linarith
      linarith
    have hG_var_pos : 0 < G.varSq := G.varSq_pos
    -- Density bound: density ≤ 1/√(2π·varSq).
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    have hsqrt_denom_pos : 0 < Real.sqrt (2 * Real.pi * G.varSq) := by
      apply Real.sqrt_pos.mpr
      exact mul_pos h2pi_pos hG_var_pos
    have hexp_le_one : Real.exp (-(μ1 - G.mean)^2 / (2 * G.varSq)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hsq_nonneg : 0 ≤ (μ1 - G.mean)^2 := sq_nonneg _
      have h2v_pos : 0 < 2 * G.varSq := by linarith
      have hquot_nn : 0 ≤ (μ1 - G.mean)^2 / (2 * G.varSq) :=
        div_nonneg hsq_nonneg (le_of_lt h2v_pos)
      have hneg_eq : -(μ1 - G.mean)^2 / (2 * G.varSq)
                      = -((μ1 - G.mean)^2 / (2 * G.varSq)) := by ring
      rw [hneg_eq]
      linarith
    -- LHS ≤ 1 / √(2π·G.varSq).
    have hone_div_sqrt_nonneg : 0 ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) := by
      apply div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hstep1 :
        1 / Real.sqrt (2 * Real.pi * G.varSq) *
            Real.exp (-(μ1 - G.mean)^2 / (2 * G.varSq))
          ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) := by
      calc 1 / Real.sqrt (2 * Real.pi * G.varSq) *
              Real.exp (-(μ1 - G.mean)^2 / (2 * G.varSq))
          ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le_one hone_div_sqrt_nonneg
        _ = 1 / Real.sqrt (2 * Real.pi * G.varSq) := by ring
    -- Now 1 / √(2π·G.varSq) ≤ 1 / √(2π·16·ε^10) = 1/(4√(2π)·ε^5).
    have h2pi16_pos : 0 < 2 * Real.pi * (16 * ε^10) := by positivity
    have hsqrt_mono :
        Real.sqrt (2 * Real.pi * (16 * ε^10)) ≤ Real.sqrt (2 * Real.pi * G.varSq) := by
      apply Real.sqrt_le_sqrt
      have : 16 * ε^10 ≤ G.varSq := hG_var_lower
      nlinarith [h2pi_pos]
    have hsqrt_pos_inner : 0 < Real.sqrt (2 * Real.pi * (16 * ε^10)) :=
      Real.sqrt_pos.mpr h2pi16_pos
    have hstep2 :
        1 / Real.sqrt (2 * Real.pi * G.varSq) ≤
        1 / Real.sqrt (2 * Real.pi * (16 * ε^10)) := by
      apply one_div_le_one_div_of_le hsqrt_pos_inner hsqrt_mono
    -- Simplify √(2π·16·ε^10) = 4 · √(2π) · ε^5.
    have hε10_eq : ε^10 = (ε^5)^2 := by ring
    have hsixteen_eq : (16 : ℝ) = (4 : ℝ)^2 := by norm_num
    have hsqrt_simp :
        Real.sqrt (2 * Real.pi * (16 * ε^10)) = 4 * Real.sqrt (2 * Real.pi) * ε^5 := by
      rw [hε10_eq]
      have h_inner_eq : 2 * Real.pi * (16 * (ε^5)^2) = (2 * Real.pi) * ((4 * ε^5)^2) := by
        ring
      rw [h_inner_eq]
      rw [Real.sqrt_mul h2pi_nonneg]
      have h4eps5_nonneg : 0 ≤ 4 * ε^5 := by positivity
      rw [Real.sqrt_sq h4eps5_nonneg]
      ring
    rw [hsqrt_simp] at hstep2
    linarith
  · -- Mean-gap case: |F'.compi.mean - μ1| ≥ 6·ε^5.
    -- Apply Corollary24 to the centred version.
    set G_centred : Workspace.Types.GaussianPDF.GaussianPDF :=
      { mean := 0, varSq := G.varSq, varSq_pos := G.varSq_pos }
    have h_density_eq : G.density μ1 = G_centred.density (μ1 - G.mean) :=
      gaussian_density_eq_centred G μ1
    rw [h_density_eq]
    have h_centred_mean : G_centred.mean = 0 := rfl
    have h_abs_ge : 6 * ε^5 ≤ |μ1 - G.mean| := by
      rw [hG_mean]
      have : |Gmean_orig - μ1| = |μ1 - Gmean_orig| := abs_sub_comm _ _
      rw [this] at h_mean
      exact h_mean
    have h6eps5_pos : 0 < 6 * ε^5 := by positivity
    have hcor := Corollary24 (6 * ε^5) h6eps5_pos G_centred h_centred_mean
                   (μ1 - G.mean) h_abs_ge
    -- hcor : G_centred.density (μ1 - G.mean) ≤ 1 / (6·ε^5 · √(2π))
    have h_target_bound :
        (1 : ℝ) / (6 * ε^5 * Real.sqrt (2 * Real.pi)) ≤
        1 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [hsqrt_2pi_pos, hε5_pos]
    linarith

theorem Lemma5Case1OffPeakBoundAtMu1 :
    ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
      0 < ε → ε ≤ 1 →
      (16 * ε ^ 10 ≤ F'.comp1.varSq - F.comp1.varSq ∨
        6 * ε ^ 5 ≤ |F'.comp1.mean - F.comp1.mean|) →
      (16 * ε ^ 10 ≤ F'.comp2.varSq - F.comp1.varSq ∨
        6 * ε ^ 5 ≤ |F'.comp2.mean - F.comp1.mean|) →
      ∀ (h : F.comp1.varSq - ε ^ 12 < min F'.comp1.varSq F'.comp2.varSq),
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F'
            (F.comp1.varSq - ε ^ 12) h).density F.comp1.mean
        ≤ (F'.weight1 + F'.weight2) / (4 * Real.sqrt (2 * Real.pi) * ε ^ 5) := by
  intro F F' ε hε_pos hε_le1 h_disj1 h_disj2 h
  -- Setup.
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hε5_pos : 0 < ε^5 := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr h2pi_pos
  have hsqrt_2pi_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := le_of_lt hsqrt_2pi_pos
  have hw1_nonneg : 0 ≤ F'.weight1 := F'.weight1_nonneg
  have hw2_nonneg : 0 ≤ F'.weight2 := F'.weight2_nonneg
  -- Unfold the mixture density.
  rw [Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
  set Gd := Workspace.Types.MixtureDeconvolution.deconvMixture2 F'
              (F.comp1.varSq - ε^12) h
  -- Identify the deconvolved components and weights.
  have hGdw1 : Gd.weight1 = F'.weight1 := rfl
  have hGdw2 : Gd.weight2 = F'.weight2 := rfl
  have hGd_c1_mean : Gd.comp1.mean = F'.comp1.mean := rfl
  have hGd_c2_mean : Gd.comp2.mean = F'.comp2.mean := rfl
  have hGd_c1_var : Gd.comp1.varSq = F'.comp1.varSq - (F.comp1.varSq - ε^12) := rfl
  have hGd_c2_var : Gd.comp2.varSq = F'.comp2.varSq - (F.comp1.varSq - ε^12) := rfl
  -- Bound each component.
  have hbound1 : Gd.comp1.density F.comp1.mean ≤ 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
    apply off_peak_component_bound Gd.comp1 F'.comp1.mean F.comp1.mean
            F'.comp1.varSq F.comp1.varSq ε hε_pos hε_le1
    · exact hGd_c1_mean
    · exact hGd_c1_var
    · exact h_disj1
  have hbound2 : Gd.comp2.density F.comp1.mean ≤ 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
    apply off_peak_component_bound Gd.comp2 F'.comp2.mean F.comp1.mean
            F'.comp2.varSq F.comp1.varSq ε hε_pos hε_le1
    · exact hGd_c2_mean
    · exact hGd_c2_var
    · exact h_disj2
  -- Combine.
  rw [hGdw1, hGdw2]
  have hdenom_pos : 0 < 4 * Real.sqrt (2 * Real.pi) * ε^5 := by positivity
  -- F'.weight1 * d1 + F'.weight2 * d2 ≤ F'.weight1 * (1/D) + F'.weight2 * (1/D) = (w1+w2)/D
  have h_combined :
      F'.weight1 * Gd.comp1.density F.comp1.mean +
      F'.weight2 * Gd.comp2.density F.comp1.mean
        ≤ F'.weight1 * (1 / (4 * Real.sqrt (2 * Real.pi) * ε^5)) +
          F'.weight2 * (1 / (4 * Real.sqrt (2 * Real.pi) * ε^5)) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hbound1 hw1_nonneg
    · exact mul_le_mul_of_nonneg_left hbound2 hw2_nonneg
  have h_simp :
      F'.weight1 * (1 / (4 * Real.sqrt (2 * Real.pi) * ε^5)) +
      F'.weight2 * (1 / (4 * Real.sqrt (2 * Real.pi) * ε^5))
        = (F'.weight1 + F'.weight2) / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
    field_simp
  linarith

end Workspace.ProofLemmas
