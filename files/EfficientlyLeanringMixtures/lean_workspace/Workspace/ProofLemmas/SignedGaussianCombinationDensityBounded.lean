import Mathlib
import Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianPDF

/-- Each Gaussian density is nonnegative. -/
private lemma gaussian_density_nonneg (G : GaussianPDF) (x : ℝ) :
    0 ≤ G.density x := by
  rw [GaussianPDF.density_eq]
  apply mul_nonneg
  · apply div_nonneg
    · norm_num
    · exact Real.sqrt_nonneg _
  · exact Real.exp_nonneg _

/-- Each Gaussian density is bounded above by its peak `1 / √(2π σ²)`. -/
private lemma gaussian_density_le_peak (G : GaussianPDF) (x : ℝ) :
    G.density x ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) := by
  rw [GaussianPDF.density_eq]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * G.varSq) := by
    apply Real.sqrt_pos.mpr
    have : (0:ℝ) < 2 * Real.pi := by positivity
    have := G.varSq_pos
    positivity
  have hcoef_nonneg : 0 ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) := by
    positivity
  have hexp_le : Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · have : 0 ≤ (x - G.mean) ^ 2 := sq_nonneg _
      linarith
    · have := G.varSq_pos
      linarith
  calc (1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))
      ≤ (1 / Real.sqrt (2 * Real.pi * G.varSq)) * 1 := by
        apply mul_le_mul_of_nonneg_left hexp_le hcoef_nonneg
    _ = 1 / Real.sqrt (2 * Real.pi * G.varSq) := by ring

/-- Existence of a uniform bound for the signed-combination density, by induction
on the list of components. -/
private lemma list_density_bounded (l : List (ℝ × GaussianPDF)) :
    ∃ C : ℝ, ∀ x : ℝ, |(l.map (fun p => p.1 * p.2.density x)).sum| ≤ C := by
  induction l with
  | nil =>
    refine ⟨0, ?_⟩
    intro x
    simp
  | cons hd tl ih =>
    obtain ⟨Ctl, hCtl⟩ := ih
    refine ⟨|hd.1| * (1 / Real.sqrt (2 * Real.pi * hd.2.varSq)) + Ctl, ?_⟩
    intro x
    have hmap : ((hd :: tl).map (fun p => p.1 * p.2.density x)).sum
        = hd.1 * hd.2.density x + (tl.map (fun p => p.1 * p.2.density x)).sum := by
      simp [List.map_cons, List.sum_cons]
    rw [hmap]
    calc |hd.1 * hd.2.density x + (tl.map (fun p => p.1 * p.2.density x)).sum|
        ≤ |hd.1 * hd.2.density x| + |(tl.map (fun p => p.1 * p.2.density x)).sum| :=
          abs_add_le _ _
      _ ≤ |hd.1| * (1 / Real.sqrt (2 * Real.pi * hd.2.varSq)) + Ctl := by
          apply add_le_add
          · rw [abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [abs_of_nonneg (gaussian_density_nonneg hd.2 x)]
            exact gaussian_density_le_peak hd.2 x
          · exact hCtl x

theorem SignedGaussianCombinationDensityBounded
    (S : SignedGaussianCombination) :
    ∃ C : ℝ, ∀ x : ℝ, |S.density x| ≤ C := by
  obtain ⟨C, hC⟩ := list_density_bounded S.components
  refine ⟨C, ?_⟩
  intro x
  rw [SignedGaussianCombination.density_eq]
  exact hC x

end Workspace.ProofLemmas
