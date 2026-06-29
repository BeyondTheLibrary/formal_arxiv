import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Fact18VariancePerturbationBound

open Workspace.Types.GaussianPDF
open Workspace.Types.L1AndTVDistance

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

/-- Auxiliary: density is non-negative. -/
private lemma vshift_density_nonneg_aux (G : GaussianPDF) (x : ℝ) : 0 ≤ G.density x := by
  rw [GaussianPDF.density_eq_gaussianPDFReal]
  exact ProbabilityTheory.gaussianPDFReal_nonneg _ _ _

/-- Auxiliary: density is integrable. -/
private lemma vshift_density_integrable_aux (G : GaussianPDF) :
    MeasureTheory.Integrable G.density MeasureTheory.volume := by
  have hrew : G.density =
      fun x => ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩ x := by
    funext x
    exact GaussianPDF.density_eq_gaussianPDFReal G x
  rw [hrew]
  exact ProbabilityTheory.integrable_gaussianPDFReal _ _

/-- Auxiliary: each Gaussian density has integral 1 over ℝ. -/
private lemma vshift_integral_density_eq_one_aux (G : GaussianPDF) :
    ∫ x, G.density x ∂MeasureTheory.volume = 1 := by
  have h_v_ne : (⟨G.varSq, le_of_lt G.varSq_pos⟩ : NNReal) ≠ 0 := by
    intro h
    have hcoe : ((⟨G.varSq, le_of_lt G.varSq_pos⟩ : NNReal) : ℝ) = 0 := by
      rw [h]; rfl
    have : G.varSq = 0 := by simpa using hcoe
    linarith [G.varSq_pos]
  have hrew : G.density =
      fun x => ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩ x := by
    funext x
    exact GaussianPDF.density_eq_gaussianPDFReal G x
  rw [hrew]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one G.mean h_v_ne

/-- Auxiliary: L¹ distance between two densities is at most 2. -/
private lemma vshift_L1Norm_diff_le_two_aux (G₁ G₂ : GaussianPDF) :
    L1Norm (fun x => G₁.density x - G₂.density x) ≤ 2 := by
  unfold L1Norm
  have h_pt : ∀ x, |G₁.density x - G₂.density x| ≤ G₁.density x + G₂.density x := by
    intro x
    have h1 := vshift_density_nonneg_aux G₁ x
    have h2 := vshift_density_nonneg_aux G₂ x
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩ <;> linarith
  have h_int_abs : MeasureTheory.Integrable (fun x => |G₁.density x - G₂.density x|)
      MeasureTheory.volume := by
    exact ((vshift_density_integrable_aux G₁).sub (vshift_density_integrable_aux G₂)).abs
  have h_int_sum : MeasureTheory.Integrable (fun x => G₁.density x + G₂.density x)
      MeasureTheory.volume := (vshift_density_integrable_aux G₁).add (vshift_density_integrable_aux G₂)
  have h_le :
      ∫ x, |G₁.density x - G₂.density x| ∂MeasureTheory.volume ≤
      ∫ x, (G₁.density x + G₂.density x) ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_mono_ae h_int_abs h_int_sum
    exact Filter.Eventually.of_forall h_pt
  have h_sum_eq :
      ∫ x, (G₁.density x + G₂.density x) ∂MeasureTheory.volume = 2 := by
    rw [MeasureTheory.integral_add (vshift_density_integrable_aux G₁)
        (vshift_density_integrable_aux G₂)]
    rw [vshift_integral_density_eq_one_aux G₁, vshift_integral_density_eq_one_aux G₂]
    norm_num
  linarith

/-- Symmetry of L1Norm under swap of two densities. -/
private lemma vshift_L1Norm_swap (f g : ℝ → ℝ) :
    L1Norm (fun x => f x - g x) = L1Norm (fun x => g x - f x) := by
  unfold L1Norm
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [abs_sub_comm]

/-- One-sided form: assuming σSq ≤ σTildeSq. -/
private lemma vshift_oriented (μ σSq σTildeSq : ℝ) (hσ : 0 < σSq) (hσTilde : 0 < σTildeSq)
    (hLo : (1 / 2 : ℝ) ≤ σSq) (hHi : σSq ≤ (3 / 2 : ℝ))
    (hLoT : (1 / 2 : ℝ) ≤ σTildeSq) (hHiT : σTildeSq ≤ (3 / 2 : ℝ))
    (hOrder : σSq ≤ σTildeSq) :
    L1Norm (fun x =>
        (⟨μ, σSq, hσ⟩ : GaussianPDF).density x
          - (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF).density x)
      ≤ 20 * |σTildeSq - σSq| := by
  -- Set δ := σTildeSq / σSq - 1; then σTildeSq = σSq * (1 + δ) and δ ≥ 0.
  set δ : ℝ := σTildeSq / σSq - 1 with hδ_def
  have hδ_pos : 0 ≤ δ := by
    have : 1 ≤ σTildeSq / σSq := by
      rw [le_div_iff₀ hσ]; linarith
    linarith
  have hσTilde_eq : σTildeSq = σSq * (1 + δ) := by
    show σTildeSq = σSq * (1 + (σTildeSq / σSq - 1))
    field_simp
    ring
  have habs : |σTildeSq - σSq| = σTildeSq - σSq := abs_of_nonneg (by linarith)
  by_cases hδ_small : δ ≤ 1/2
  · -- Small δ branch: use Fact18VariancePerturbationBound at (μ, σSq, δ).
    have hbound :=
      Fact18VariancePerturbationBound μ σSq δ hσ hδ_pos hδ_small
    -- hbound : L1Norm (fun x => density (μ,σSq) − density (μ, σSq*(1+δ))) ≤ 10*δ
    -- Rewrite second density: σTildeSq = σSq*(1+δ) so the densities match.
    have hpos' : 0 < σSq * (1 + δ) := by nlinarith
    -- We need to massage hbound into the goal's form.
    have h_eq : (⟨μ, σSq * (1 + δ), hpos'⟩ : GaussianPDF).density =
        (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF).density := by
      funext y
      simp only [GaussianPDF.density_eq]
      rw [← hσTilde_eq]
    rw [h_eq] at hbound
    -- Now: hbound : L1Norm (fun x => density (μ,σSq) x − density (μ,σTildeSq) x) ≤ 10*δ
    -- Goal: L1Norm ... ≤ 20 * |σTildeSq - σSq|
    -- 10*δ = 10*(σTildeSq - σSq)/σSq ≤ 10*(σTildeSq - σSq)*2 = 20*(σTildeSq - σSq)
    have hδ_val : δ = (σTildeSq - σSq) / σSq := by
      rw [hδ_def]; field_simp
    rw [habs]
    have hδ_bound : δ ≤ 2 * (σTildeSq - σSq) := by
      rw [hδ_val]
      rw [div_le_iff₀ hσ]
      nlinarith
    linarith
  · -- Large δ branch: trivial L1 ≤ 2, and 20*(σTildeSq - σSq) = 20*σSq*δ ≥ 20*(1/2)*(1/2) = 5
    push_neg at hδ_small
    have htriv := vshift_L1Norm_diff_le_two_aux
      (⟨μ, σSq, hσ⟩ : GaussianPDF)
      (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF)
    rw [habs]
    -- 20*(σTildeSq - σSq) ≥ 5
    have hdiff_eq : σTildeSq - σSq = σSq * δ := by
      rw [hσTilde_eq]; ring
    have hge : (5 : ℝ) ≤ 20 * (σTildeSq - σSq) := by
      rw [hdiff_eq]
      nlinarith
    linarith

theorem Fact18GaussianVarianceShiftL1Bound :
    ∀ (μ σSq σTildeSq : ℝ) (hσ : 0 < σSq) (hσTilde : 0 < σTildeSq),
      (1 / 2 : ℝ) ≤ σSq → σSq ≤ (3 / 2 : ℝ) →
      (1 / 2 : ℝ) ≤ σTildeSq → σTildeSq ≤ (3 / 2 : ℝ) →
      L1Norm (fun x =>
          (⟨μ, σSq, hσ⟩ : GaussianPDF).density x
            - (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF).density x)
        ≤ 20 * |σTildeSq - σSq| := by
  intro μ σSq σTildeSq hσ hσTilde hLo hHi hLoT hHiT
  by_cases hOrder : σSq ≤ σTildeSq
  · exact vshift_oriented μ σSq σTildeSq hσ hσTilde hLo hHi hLoT hHiT hOrder
  · push_neg at hOrder
    -- Swap roles. L1Norm is symmetric in the difference.
    have hRev := vshift_oriented μ σTildeSq σSq hσTilde hσ hLoT hHiT hLo hHi (le_of_lt hOrder)
    have hsym :
        L1Norm (fun x => (⟨μ, σSq, hσ⟩ : GaussianPDF).density x -
                          (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF).density x)
        = L1Norm (fun x => (⟨μ, σTildeSq, hσTilde⟩ : GaussianPDF).density x -
                            (⟨μ, σSq, hσ⟩ : GaussianPDF).density x) :=
      vshift_L1Norm_swap _ _
    rw [hsym]
    have habs_swap : |σTildeSq - σSq| = |σSq - σTildeSq| := abs_sub_comm _ _
    rw [habs_swap]
    exact hRev

end Workspace.ProofLemmas
