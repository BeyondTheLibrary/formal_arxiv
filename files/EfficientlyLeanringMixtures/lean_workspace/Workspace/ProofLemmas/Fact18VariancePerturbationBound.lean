import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Fact18GaussianL1FromKL
import Workspace.ProofLemmas.Fact18KLBoundVariancePerturbation

theorem Fact18VariancePerturbationBound :
    ∀ (μ σSq δ : ℝ) (hσ : 0 < σSq) (hδ_pos : 0 ≤ δ) (hδ_half : δ ≤ 1/2),
      Workspace.Types.L1AndTVDistance.L1Norm
        (fun x => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x -
                  (⟨μ, σSq * (1 + δ), by nlinarith⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) ≤
        10 * δ := by
  intro μ σSq δ hσ hδ_pos hδ_half
  have hσ' : 0 < σSq * (1 + δ) := by nlinarith
  -- Step 1: Pinsker bound (L1 ≤ √(2·KL))
  have h_pinsker := Workspace.ProofLemmas.Fact18GaussianL1FromKL μ σSq μ (σSq * (1 + δ)) hσ hσ'
  -- Step 2: KL bound (KL ≤ 50·δ²)
  have h_kl := Workspace.ProofLemmas.Fact18KLBoundVariancePerturbation μ σSq δ hσ hδ_pos hδ_half
  -- The KL term in h_pinsker should match h_kl
  -- Now we have: L1 ≤ √(2·KL) and KL ≤ 50·δ²
  -- So L1 ≤ √(2·KL) ≤ √(2·50·δ²) = √(100·δ²) = 10·|δ| = 10·δ
  set KL := ∫ x, (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
            Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
                      (⟨μ, σSq * (1 + δ), by nlinarith⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) with hKL_def
  -- h_pinsker: L1Norm ≤ √(2 * KL)
  -- h_kl: KL ≤ 50 * δ^2
  have h_two_kl : 2 * KL ≤ 100 * δ^2 := by linarith
  have h_nonneg : (0 : ℝ) ≤ 100 * δ^2 := by positivity
  have h_sqrt_mono : Real.sqrt (2 * KL) ≤ Real.sqrt (100 * δ^2) :=
    Real.sqrt_le_sqrt h_two_kl
  have h_sqrt_eq : Real.sqrt (100 * δ^2) = 10 * δ := by
    have h100 : (100 : ℝ) = 10^2 := by norm_num
    rw [h100]
    rw [show (10^2 : ℝ) * δ^2 = (10 * δ)^2 by ring]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 10 * δ)]
  linarith [h_pinsker, h_sqrt_mono, h_sqrt_eq.le, h_sqrt_eq.ge]
