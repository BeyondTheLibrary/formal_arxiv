import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureDeconvolution

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureDeconvolution

set_option maxHeartbeats 400000

namespace Workspace.ProofLemmas

theorem Lemma5Case1PeakBoundAtMu1 :
    ∀ (F : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
      0 < ε → ε ≤ 1 → ε ≤ F.weight1 →
      ∀ (h : F.comp1.varSq - ε^12 < min F.comp1.varSq F.comp2.varSq),
        F.weight1 / (Real.sqrt (2 * Real.pi) * ε^6) ≤
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
              (F.comp1.varSq - ε^12) h).density F.comp1.mean := by
  intro F ε hε_pos hε_le1 hε_le_w1 h
  -- Set up basic non-negativity facts.
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hε6_nonneg : 0 ≤ ε^6 := by positivity
  have hε6_pos : 0 < ε^6 := by positivity
  have hε12_nonneg : 0 ≤ ε^12 := by positivity
  have hε12_pos : 0 < ε^12 := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have h2pi_nonneg : 0 ≤ 2 * Real.pi := le_of_lt h2pi_pos
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr h2pi_pos
  have hw1_nonneg : 0 ≤ F.weight1 := F.weight1_nonneg
  have hw2_nonneg : 0 ≤ F.weight2 := F.weight2_nonneg
  -- Unfold the mixture density.
  rw [Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
  -- Now: F.weight1 / (√(2π) · ε^6) ≤
  --   (deconvMixture2 F (..) h).weight1 * (..).comp1.density (..).comp1.mean
  --   + (..).weight2 * (..).comp2.density (..).comp1.mean
  -- Compute the second component contribution is ≥ 0.
  have hw1_eq : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
                  (F.comp1.varSq - ε^12) h).weight1 = F.weight1 := rfl
  have hw2_eq : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
                  (F.comp1.varSq - ε^12) h).weight2 = F.weight2 := rfl
  have hμ1_eq : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
                  (F.comp1.varSq - ε^12) h).comp1.mean = F.comp1.mean := rfl
  have hvar1_eq : (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
                  (F.comp1.varSq - ε^12) h).comp1.varSq
                  = F.comp1.varSq - (F.comp1.varSq - ε^12) := rfl
  -- Simplify the comp1 density at F.comp1.mean.
  set Gd := (Workspace.Types.MixtureDeconvolution.deconvMixture2 F
              (F.comp1.varSq - ε^12) h)
  -- Reduce variance: F.comp1.varSq - (F.comp1.varSq - ε^12) = ε^12.
  have hvar1_simp : Gd.comp1.varSq = ε^12 := by
    show F.comp1.varSq - (F.comp1.varSq - ε^12) = ε^12
    ring
  -- Density at the mean: distance is zero, so exp(0) = 1.
  have hd1 : Gd.comp1.density F.comp1.mean = 1 / Real.sqrt (2 * Real.pi * ε^12) := by
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    have hmean : Gd.comp1.mean = F.comp1.mean := rfl
    rw [hmean, hvar1_simp]
    have hzero : (-(F.comp1.mean - F.comp1.mean) ^ 2 / (2 * ε^12)) = 0 := by
      have : F.comp1.mean - F.comp1.mean = 0 := sub_self _
      rw [this]
      ring
    rw [hzero, Real.exp_zero, mul_one]
  -- The comp2 density is non-negative.
  have hd2_nonneg : 0 ≤ Gd.comp2.density F.comp1.mean := by
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    have hpos : 0 < 2 * Real.pi * Gd.comp2.varSq := by
      have := Gd.comp2.varSq_pos
      positivity
    apply mul_nonneg
    · apply div_nonneg
      · norm_num
      · exact Real.sqrt_nonneg _
    · exact (Real.exp_pos _).le
  -- √(2 * π * ε^12) = √(2 * π) * ε^6.
  have hsqrt_split : Real.sqrt (2 * Real.pi * ε^12)
                      = Real.sqrt (2 * Real.pi) * ε^6 := by
    have hε12_eq : ε^12 = (ε^6)^2 := by ring
    rw [hε12_eq, Real.sqrt_mul h2pi_nonneg, Real.sqrt_sq hε6_nonneg]
  -- Now write the RHS in a usable form.
  -- RHS = F.weight1 * Gd.comp1.density F.comp1.mean + F.weight2 * Gd.comp2.density F.comp1.mean
  show F.weight1 / (Real.sqrt (2 * Real.pi) * ε^6) ≤
        Gd.weight1 * Gd.comp1.density F.comp1.mean
        + Gd.weight2 * Gd.comp2.density F.comp1.mean
  have hGdw1 : Gd.weight1 = F.weight1 := rfl
  have hGdw2 : Gd.weight2 = F.weight2 := rfl
  rw [hGdw1, hGdw2, hd1]
  -- Goal: F.weight1 / (√(2π) · ε^6) ≤
  --       F.weight1 * (1 / √(2π · ε^12)) + F.weight2 * Gd.comp2.density F.comp1.mean
  rw [hsqrt_split]
  -- Goal: F.weight1 / (√(2π) · ε^6) ≤
  --       F.weight1 * (1 / (√(2π) · ε^6)) + F.weight2 * Gd.comp2.density F.comp1.mean
  -- Use F.weight1 / x = F.weight1 * (1 / x).
  have hdenom_pos : 0 < Real.sqrt (2 * Real.pi) * ε^6 := mul_pos hsqrt_2pi_pos hε6_pos
  have hdenom_ne : Real.sqrt (2 * Real.pi) * ε^6 ≠ 0 := ne_of_gt hdenom_pos
  have hrewrite : F.weight1 / (Real.sqrt (2 * Real.pi) * ε^6)
                = F.weight1 * (1 / (Real.sqrt (2 * Real.pi) * ε^6)) := by
    rw [mul_one_div]
  rw [hrewrite]
  have hweight2_density_nonneg : 0 ≤ F.weight2 * Gd.comp2.density F.comp1.mean :=
    mul_nonneg hw2_nonneg hd2_nonneg
  linarith
