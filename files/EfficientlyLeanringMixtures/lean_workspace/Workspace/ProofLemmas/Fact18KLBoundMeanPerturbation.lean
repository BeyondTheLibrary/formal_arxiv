import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory Real

/-- Helper: NNReal coercion ≠ 0 from positivity. -/
private lemma nnreal_mk_ne_zero_kl (τSq : ℝ) (hτ : 0 < τSq) :
    (⟨τSq, le_of_lt hτ⟩ : NNReal) ≠ 0 := by
  intro h
  have h2 : ((⟨τSq, le_of_lt hτ⟩ : NNReal) : ℝ) = ((0 : NNReal) : ℝ) := by
    exact_mod_cast congrArg (Subtype.val : NNReal → ℝ) h
  simp at h2
  linarith

/-- Density of `(⟨μ, σSq, hσ⟩ : GaussianPDF)` equals `gaussianPDFReal μ ⟨σSq, hσ.le⟩`. -/
private lemma dens_eq_pdf (μ σSq : ℝ) (hσ : 0 < σSq) :
    (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
    fun x => gaussianPDFReal μ ⟨σSq, le_of_lt hσ⟩ x := by
  funext x
  exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal _ x

/-- Integrability of the Gaussian density (in our wrapper form). -/
private lemma integrable_density (μ σSq : ℝ) (hσ : 0 < σSq) :
    Integrable (fun x : ℝ =>
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume := by
  rw [dens_eq_pdf μ σSq hσ]
  exact integrable_gaussianPDFReal _ _

/-- ∫ density = 1. -/
private lemma int_density_eq_one (μ σSq : ℝ) (hσ : 0 < σSq) :
    ∫ x, (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x ∂volume = 1 := by
  rw [dens_eq_pdf μ σSq hσ]
  exact integral_gaussianPDFReal_eq_one μ (nnreal_mk_ne_zero_kl σSq hσ)

/-- For Gaussians with same variance: log(density(μ,σ²,x) / density(μ',σ²,x))
    = ((x - μ')² - (x - μ)²) / (2σ²). -/
private lemma log_density_ratio (μ μ' σSq x : ℝ) (hσ : 0 < σSq) :
    Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
              (⟨μ', σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x)
    = ((x - μ')^2 - (x - μ)^2) / (2 * σSq) := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq,
      Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  show Real.log ((1 / Real.sqrt (2 * Real.pi * σSq)) *
    Real.exp (-(x - μ) ^ 2 / (2 * σSq)) /
    ((1 / Real.sqrt (2 * Real.pi * σSq)) * Real.exp (-(x - μ') ^ 2 / (2 * σSq)))) = _
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * σSq) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsqrt_ne : Real.sqrt (2 * Real.pi * σSq) ≠ 0 := ne_of_gt hsqrt_pos
  have h_inv_pos : 0 < (1 : ℝ) / Real.sqrt (2 * Real.pi * σSq) := by positivity
  have h_inv_ne : (1 : ℝ) / Real.sqrt (2 * Real.pi * σSq) ≠ 0 := ne_of_gt h_inv_pos
  have h_ratio_eq : (1 / Real.sqrt (2 * Real.pi * σSq)) *
        Real.exp (-(x - μ) ^ 2 / (2 * σSq)) /
        ((1 / Real.sqrt (2 * Real.pi * σSq)) * Real.exp (-(x - μ') ^ 2 / (2 * σSq)))
      = Real.exp (((x - μ')^2 - (x - μ)^2) / (2 * σSq)) := by
    rw [mul_div_mul_left _ _ h_inv_ne, ← Real.exp_sub]
    congr 1
    have hne : (2 * σSq : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [h_ratio_eq, Real.log_exp]

/-- Algebraic identity: ((x - μ')² - (x - μ)²)/(2σ²) where μ' = μ + √σ²·δ
    simplifies to -(x-μ)·δ/√σ² + δ²/2. -/
private lemma log_ratio_simplify (μ σSq δ x : ℝ) (hσ : 0 < σSq) :
    ((x - (μ + Real.sqrt σSq * δ))^2 - (x - μ)^2) / (2 * σSq)
    = -(x - μ) * δ / Real.sqrt σSq + δ^2 / 2 := by
  set s := Real.sqrt σSq with hs_def
  have h_sq : s^2 = σSq := Real.sq_sqrt (le_of_lt hσ)
  have hσ_ne : σSq ≠ 0 := ne_of_gt hσ
  have h_sqrt_pos : 0 < s := Real.sqrt_pos.mpr hσ
  have h_sqrt_ne : s ≠ 0 := ne_of_gt h_sqrt_pos
  have hsigma_eq : σSq = s * s := by rw [← sq]; exact h_sq.symm
  rw [hsigma_eq]
  field_simp
  ring

/-- The first central moment ∫ (x - μ) · density(μ,σ²,x) dx = 0. -/
private lemma int_central_first_moment (μ σSq : ℝ) (hσ : 0 < σSq) :
    ∫ x, (x - μ) *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x ∂volume = 0 := by
  set v : NNReal := ⟨σSq, le_of_lt hσ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero_kl σSq hσ
  have h_smul_eq :
      (fun x : ℝ => (x - μ) *
        (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
    show (x - μ) * gaussianPDFReal μ v x = gaussianPDFReal μ v x • (x - μ)
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_eq, ← integral_gaussianReal_eq_integral_smul hv_ne]
  -- ∫ (x - μ) ∂(gaussianReal μ v) = μ - μ = 0
  have h_integrable_id : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal' 1 (by simp)).integrable (le_refl _)
  rw [show (fun x : ℝ => x - μ) = (fun x : ℝ => x + (-μ)) by funext; ring]
  rw [integral_add h_integrable_id (integrable_const _)]
  rw [integral_id_gaussianReal, integral_const]
  have hp : IsProbabilityMeasure (gaussianReal μ v) := instIsProbabilityMeasureGaussianReal μ v
  rw [measureReal_univ_eq_one]
  ring

/-- Integrability of `(x - μ) · density(μ, σSq, x)` over volume. -/
private lemma integrable_centered_density (μ σSq : ℝ) (hσ : 0 < σSq) :
    Integrable (fun x : ℝ => (x - μ) *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume := by
  set v : NNReal := ⟨σSq, le_of_lt hσ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero_kl σSq hσ
  have h_smul_eq :
      (fun x : ℝ => (x - μ) *
        (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
    show (x - μ) * gaussianPDFReal μ v x = gaussianPDFReal μ v x • (x - μ)
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_eq]
  -- Want Integrable (fun x => gaussianPDFReal μ v x • (x - μ)) volume
  have h_integrable_at_meas : Integrable (fun x : ℝ => x - μ) (gaussianReal μ v) := by
    have h1 : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
      (memLp_id_gaussianReal' 1 (by simp)).integrable (le_refl _)
    exact h1.sub (integrable_const μ)
  rw [gaussianReal_of_var_ne_zero μ hv_ne] at h_integrable_at_meas
  -- Use integrable_withDensity_iff_integrable_smul'
  have hmeas : Measurable (gaussianPDF μ v) := measurable_gaussianPDF μ v
  have h_lt_top : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF μ v x < ⊤ :=
    ae_of_all _ (fun _ ↦ gaussianPDF_lt_top)
  have heq : Integrable (fun x : ℝ => x - μ) (volume.withDensity (gaussianPDF μ v)) ↔
      Integrable (fun x : ℝ => (gaussianPDF μ v x).toReal • (x - μ)) volume :=
    integrable_withDensity_iff_integrable_smul' (g := fun x => x - μ) hmeas h_lt_top
  have h_smul_match :
      (fun x : ℝ => (gaussianPDF μ v x).toReal • (x - μ)) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)) := by
    funext x
    rw [toReal_gaussianPDF]
  rw [h_smul_match] at heq
  exact heq.mp h_integrable_at_meas

theorem Fact18KLBoundMeanPerturbation :
    ∀ (μ σSq δ : ℝ) (hσ : 0 < σSq),
      (∫ x, (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
            Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
                      (⟨μ + Real.sqrt σSq * δ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x))
        = δ^2 / 2 := by
  intro μ σSq δ hσ
  -- Rewrite integrand pointwise
  have h_integrand :
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
          (⟨μ + Real.sqrt σSq * δ, σSq, hσ⟩ :
            Workspace.Types.GaussianPDF.GaussianPDF).density x)) =
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        (-(x - μ) * δ / Real.sqrt σSq + δ^2 / 2)) := by
    funext x
    rw [log_density_ratio μ (μ + Real.sqrt σSq * δ) σSq x hσ]
    rw [log_ratio_simplify μ σSq δ x hσ]
  rw [h_integrand]
  -- Split via linearity
  have h_factor :
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        (-(x - μ) * δ / Real.sqrt σSq + δ^2 / 2)) =
      (fun x : ℝ => (-δ / Real.sqrt σSq) *
          ((x - μ) * (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x)
        + (δ^2 / 2) *
          (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) := by
    funext x
    ring
  rw [h_factor]
  have h_int1 : Integrable (fun x : ℝ => (-δ / Real.sqrt σSq) *
      ((x - μ) * (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x))
      volume := (integrable_centered_density μ σSq hσ).const_mul _
  have h_int2 : Integrable (fun x : ℝ => (δ^2 / 2) *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume :=
    (integrable_density μ σSq hσ).const_mul _
  rw [integral_add h_int1 h_int2]
  rw [integral_const_mul, integral_const_mul]
  rw [int_density_eq_one μ σSq hσ]
  rw [int_central_first_moment μ σSq hσ]
  ring

end Workspace.ProofLemmas
