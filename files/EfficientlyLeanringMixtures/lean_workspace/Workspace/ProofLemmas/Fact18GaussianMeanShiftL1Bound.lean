import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Fact18GaussianL1FromKL
import Workspace.ProofLemmas.Fact18KLBoundMeanPerturbation

open Workspace.Types.GaussianPDF
open Workspace.Types.L1AndTVDistance

namespace Workspace.ProofLemmas

/--
Fact 18 (mean-shift form, Appendix 9.2 of Moitra–Valiant).

For every real `μ`, every real `δ`, and every `σ² ∈ [1/2, 3/2]`, the `L¹` distance
between two Gaussians of the same variance whose means differ by `δ` is bounded
above by `10 · |δ|`:

  `‖N(μ, σ²) − N(μ + δ, σ²)‖₁ ≤ 10 · |δ|`.
-/
theorem Fact18GaussianMeanShiftL1Bound :
    ∀ (μ δ σSq : ℝ) (hσ : 0 < σSq),
      (1 / 2 : ℝ) ≤ σSq → σSq ≤ (3 / 2 : ℝ) →
      L1Norm (fun x =>
          (⟨μ, σSq, hσ⟩ : GaussianPDF).density x
            - (⟨μ + δ, σSq, hσ⟩ : GaussianPDF).density x)
        ≤ 10 * |δ| := by
  intro μ δ σSq hσ hσ_lb hσ_ub
  -- Set s = √σ² and δ' = δ / s.
  set s : ℝ := Real.sqrt σSq with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hσ
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s * s = σSq := by
    rw [hs_def]; exact Real.mul_self_sqrt (le_of_lt hσ)
  -- s ≥ √(1/2)
  have hs_lb : Real.sqrt (1/2) ≤ s := by
    rw [hs_def]; exact Real.sqrt_le_sqrt hσ_lb
  have h_half_pos : (0 : ℝ) < 1/2 := by norm_num
  have h_sqrt_half_pos : 0 < Real.sqrt (1/2) := Real.sqrt_pos.mpr h_half_pos
  set δ' : ℝ := δ / s with hδ'_def
  -- μ + s * δ' = μ + δ
  have h_mean : μ + s * δ' = μ + δ := by
    rw [hδ'_def]
    field_simp
  -- Apply Fact18GaussianL1FromKL with the two means μ and (μ + δ) = (μ + s*δ').
  have hL1 := Fact18GaussianL1FromKL μ σSq (μ + δ) σSq hσ hσ
  -- Apply Fact18KLBoundMeanPerturbation with μ, σSq, δ'.
  have hKL := Fact18KLBoundMeanPerturbation μ σSq δ' hσ
  -- Rewrite the second mean in hL1's integrand using h_mean.symm.
  have h_eq_means : μ + δ = μ + s * δ' := h_mean.symm
  rw [h_eq_means] at hL1
  rw [hKL] at hL1
  -- Now hL1 : L1Norm ≤ √(2 * (δ'² / 2)) = √(δ'²) = |δ'|.
  have h2 : (2 : ℝ) * (δ' ^ 2 / 2) = δ' ^ 2 := by ring
  rw [h2] at hL1
  rw [Real.sqrt_sq_eq_abs] at hL1
  -- Now hL1 : L1Norm ≤ |δ'| = |δ / s| = |δ| / s.
  have h_abs_δ' : |δ'| = |δ| / s := by
    rw [hδ'_def, abs_div, abs_of_pos hs_pos]
  rw [h_abs_δ'] at hL1
  -- Now hL1 : L1Norm ≤ |δ| / s.
  -- We need: |δ| / s ≤ 10 * |δ|, i.e., the rest of the chain.
  -- Suffices to show |δ| / s ≤ 10 * |δ|.
  have h_chain : |δ| / s ≤ 10 * |δ| := by
    -- Equivalent (since s > 0) to: |δ| ≤ 10 * |δ| * s, i.e., |δ| * (10*s - 1) ≥ 0.
    -- Since s ≥ √(1/2) ≈ 0.707 and 10*s ≥ 10*√(1/2) > 1.
    have h_sqrt_half_ge : (1/10 : ℝ) ≤ Real.sqrt (1/2) := by
      have h1 : Real.sqrt ((1/10:ℝ)^2) ≤ Real.sqrt (1/2) := by
        apply Real.sqrt_le_sqrt
        norm_num
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/10)] at h1
      exact h1
    have hs_ge : (1/10 : ℝ) ≤ s := le_trans h_sqrt_half_ge hs_lb
    -- Now |δ| / s ≤ |δ| / (1/10) = 10 * |δ| when 1/10 ≤ s and |δ| ≥ 0.
    have habs : 0 ≤ |δ| := abs_nonneg δ
    rw [div_le_iff₀ hs_pos]
    -- Goal: |δ| ≤ 10 * |δ| * s
    have : |δ| * 1 ≤ |δ| * (10 * s) := by
      apply mul_le_mul_of_nonneg_left _ habs
      linarith
    linarith [this]
  -- Rewrite hL1 back so its L1Norm matches the goal's L1Norm (μ + δ form).
  rw [h_mean] at hL1
  linarith [hL1, h_chain]

end Workspace.ProofLemmas
