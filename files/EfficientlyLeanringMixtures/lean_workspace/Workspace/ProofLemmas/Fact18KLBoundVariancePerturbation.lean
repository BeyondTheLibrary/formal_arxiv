import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory Real

/-- Helper: NNReal coercion ≠ 0 from positivity. -/
private lemma nnreal_mk_ne_zero_var (τSq : ℝ) (hτ : 0 < τSq) :
    (⟨τSq, le_of_lt hτ⟩ : NNReal) ≠ 0 := by
  intro h
  have h2 : ((⟨τSq, le_of_lt hτ⟩ : NNReal) : ℝ) = ((0 : NNReal) : ℝ) := by
    exact_mod_cast congrArg (Subtype.val : NNReal → ℝ) h
  simp at h2
  linarith

/-- Density of `(⟨μ, σSq, hσ⟩ : GaussianPDF)` equals `gaussianPDFReal μ ⟨σSq, hσ.le⟩`. -/
private lemma dens_eq_pdf_var (μ σSq : ℝ) (hσ : 0 < σSq) :
    (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
    fun x => gaussianPDFReal μ ⟨σSq, le_of_lt hσ⟩ x := by
  funext x
  exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal _ x

/-- Integrability of the Gaussian density. -/
private lemma integrable_density_var (μ σSq : ℝ) (hσ : 0 < σSq) :
    Integrable (fun x : ℝ =>
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume := by
  rw [dens_eq_pdf_var μ σSq hσ]
  exact integrable_gaussianPDFReal _ _

/-- ∫ density = 1. -/
private lemma int_density_eq_one_var (μ σSq : ℝ) (hσ : 0 < σSq) :
    ∫ x, (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x ∂volume = 1 := by
  rw [dens_eq_pdf_var μ σSq hσ]
  exact integral_gaussianPDFReal_eq_one μ (nnreal_mk_ne_zero_var σSq hσ)

/-- Log of ratio of densities with same mean μ but variances σSq and σSq·(1+δ).
    `log(N(μ,σ²,x) / N(μ, σ²(1+δ), x)) = (1/2)·log(1+δ) - δ·(x-μ)²/(2σ²(1+δ))`. -/
private lemma log_density_ratio_var (μ σSq δ x : ℝ) (hσ : 0 < σSq) (hδ : 0 ≤ δ) :
    Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
              (⟨μ, σSq * (1 + δ), by nlinarith⟩ :
                Workspace.Types.GaussianPDF.GaussianPDF).density x)
    = (1/2) * Real.log (1 + δ) - δ * (x - μ)^2 / (2 * σSq * (1 + δ)) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hσ1δ : 0 < σSq * (1 + δ) := by positivity
  have h_sqrt_σ_pos : 0 < Real.sqrt (2 * Real.pi * σSq) :=
    Real.sqrt_pos.mpr (by positivity)
  have h_sqrt_σ_ne : Real.sqrt (2 * Real.pi * σSq) ≠ 0 := ne_of_gt h_sqrt_σ_pos
  have h_sqrt_σ1δ_pos : 0 < Real.sqrt (2 * Real.pi * (σSq * (1 + δ))) :=
    Real.sqrt_pos.mpr (by positivity)
  have h_sqrt_σ1δ_ne : Real.sqrt (2 * Real.pi * (σSq * (1 + δ))) ≠ 0 := ne_of_gt h_sqrt_σ1δ_pos
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq,
      Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  set N := Real.sqrt (2 * Real.pi * σSq) with hN_def
  set D := Real.sqrt (2 * Real.pi * (σSq * (1 + δ))) with hD_def
  have hN_pos : 0 < N := h_sqrt_σ_pos
  have hD_pos : 0 < D := h_sqrt_σ1δ_pos
  have hN_ne : N ≠ 0 := h_sqrt_σ_ne
  have hD_ne : D ≠ 0 := h_sqrt_σ1δ_ne
  have h_ratio :
      (1 / N) * Real.exp (-(x - μ) ^ 2 / (2 * σSq)) /
        ((1 / D) * Real.exp (-(x - μ) ^ 2 / (2 * (σSq * (1 + δ)))))
      = (D / N) * Real.exp (-(x - μ) ^ 2 / (2 * σSq) -
            (-(x - μ) ^ 2 / (2 * (σSq * (1 + δ))))) := by
    rw [Real.exp_sub]
    field_simp
  rw [h_ratio]
  have h_DN_pos : 0 < D / N := div_pos hD_pos hN_pos
  have h_exp_pos : 0 < Real.exp (-(x - μ) ^ 2 / (2 * σSq) -
                      (-(x - μ) ^ 2 / (2 * (σSq * (1 + δ))))) := Real.exp_pos _
  rw [Real.log_mul (ne_of_gt h_DN_pos) (ne_of_gt h_exp_pos)]
  rw [Real.log_exp]
  have hD_sq : D^2 = 2 * Real.pi * (σSq * (1 + δ)) := by
    rw [hD_def, Real.sq_sqrt (by positivity)]
  have hN_sq : N^2 = 2 * Real.pi * σSq := by
    rw [hN_def, Real.sq_sqrt (by positivity)]
  have h_DN_ratio_sq : (D/N)^2 = 1 + δ := by
    rw [div_pow, hD_sq, hN_sq]
    have hN2_ne : N^2 ≠ 0 := by rw [hN_sq]; positivity
    field_simp
  -- 2 · log(D/N) = log((D/N)²) = log(1+δ)
  have h_log_pow : Real.log ((D/N)^2) = 2 * Real.log (D/N) := by
    rw [sq, Real.log_mul (ne_of_gt h_DN_pos) (ne_of_gt h_DN_pos)]
    ring
  have h_log_DN : Real.log (D / N) = (1/2) * Real.log (1 + δ) := by
    have h_eq : 2 * Real.log (D / N) = Real.log (1 + δ) := by
      rw [← h_log_pow, h_DN_ratio_sq]
    linarith
  rw [h_log_DN]
  field_simp
  ring

/-- The second central moment: ∫ (x - μ)² · density(μ, σSq, x) dx = σSq. -/
private lemma int_second_central_moment_var (μ σSq : ℝ) (hσ : 0 < σSq) :
    ∫ x, (x - μ)^2 *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x ∂volume = σSq := by
  set v : NNReal := ⟨σSq, le_of_lt hσ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero_var σSq hσ
  have h_smul_eq :
      (fun x : ℝ => (x - μ)^2 *
        (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)^2) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
    show (x - μ)^2 * gaussianPDFReal μ v x = gaussianPDFReal μ v x • (x - μ)^2
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_eq, ← integral_gaussianReal_eq_integral_smul hv_ne]
  have h_var : variance (fun x : ℝ => x) (gaussianReal μ v) = (v : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral measurable_id'.aemeasurable] at h_var
  simp only [integral_id_gaussianReal] at h_var
  show ∫ x, (x - μ)^2 ∂gaussianReal μ v = σSq
  exact h_var

/-- Integrability of `(x - μ)² · density(μ, σSq, x)` over volume. -/
private lemma integrable_second_moment_var (μ σSq : ℝ) (hσ : 0 < σSq) :
    Integrable (fun x : ℝ => (x - μ)^2 *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume := by
  set v : NNReal := ⟨σSq, le_of_lt hσ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero_var σSq hσ
  have h_smul_eq :
      (fun x : ℝ => (x - μ)^2 *
        (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)^2) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
    show (x - μ)^2 * gaussianPDFReal μ v x = gaussianPDFReal μ v x • (x - μ)^2
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_eq]
  have h_integrable_at_meas : Integrable (fun x : ℝ => (x - μ)^2) (gaussianReal μ v) := by
    have h1 : MemLp (fun x : ℝ => x) 2 (gaussianReal μ v) := memLp_id_gaussianReal' 2 (by simp)
    have h2 : MemLp (fun x : ℝ => x - μ) 2 (gaussianReal μ v) := h1.sub (memLp_const μ)
    have h3 := h2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simp only [Real.norm_eq_abs, sq_abs] at h3
    convert h3 using 1
  rw [gaussianReal_of_var_ne_zero μ hv_ne] at h_integrable_at_meas
  have hmeas : Measurable (gaussianPDF μ v) := measurable_gaussianPDF μ v
  have h_lt_top : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF μ v x < ⊤ :=
    ae_of_all _ (fun _ ↦ gaussianPDF_lt_top)
  have heq : Integrable (fun x : ℝ => (x - μ)^2)
      (volume.withDensity (gaussianPDF μ v)) ↔
      Integrable (fun x : ℝ => (gaussianPDF μ v x).toReal • (x - μ)^2) volume :=
    integrable_withDensity_iff_integrable_smul' (g := fun x => (x - μ)^2) hmeas h_lt_top
  have h_smul_match :
      (fun x : ℝ => (gaussianPDF μ v x).toReal • (x - μ)^2) =
      (fun x : ℝ => gaussianPDFReal μ v x • (x - μ)^2) := by
    funext x
    rw [toReal_gaussianPDF]
  rw [h_smul_match] at heq
  exact heq.mp h_integrable_at_meas

theorem Fact18KLBoundVariancePerturbation :
    ∀ (μ σSq δ : ℝ) (hσ : 0 < σSq) (hδ : 0 ≤ δ) (_hδhalf : δ ≤ 1/2),
      (∫ x, (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
            Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
                      (⟨μ, σSq * (1 + δ), by nlinarith⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x))
        ≤ 50 * δ^2 := by
  intro μ σSq δ hσ hδ hδhalf
  have h1δ : 0 < 1 + δ := by linarith
  have hσne : σSq ≠ 0 := ne_of_gt hσ
  have h1δne : (1 + δ) ≠ 0 := ne_of_gt h1δ
  have h_integrand_eq :
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        Real.log ((⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
          (⟨μ, σSq * (1 + δ), by nlinarith⟩ :
            Workspace.Types.GaussianPDF.GaussianPDF).density x)) =
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        ((1/2) * Real.log (1 + δ) - δ * (x - μ)^2 / (2 * σSq * (1 + δ)))) := by
    funext x
    rw [log_density_ratio_var μ σSq δ x hσ hδ]
  rw [h_integrand_eq]
  have h_factor :
      (fun x : ℝ => (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
        ((1/2) * Real.log (1 + δ) - δ * (x - μ)^2 / (2 * σSq * (1 + δ)))) =
      (fun x : ℝ => ((1/2) * Real.log (1 + δ)) *
          (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x
        + (-(δ / (2 * σSq * (1 + δ)))) *
          ((x - μ)^2 *
            (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x)) := by
    funext x
    have hne : (2 * σSq * (1 + δ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [h_factor]
  have h_int1 : Integrable (fun x : ℝ => ((1/2) * Real.log (1 + δ)) *
      (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) volume :=
    (integrable_density_var μ σSq hσ).const_mul _
  have h_int2 : Integrable (fun x : ℝ => (-(δ / (2 * σSq * (1 + δ)))) *
      ((x - μ)^2 *
        (⟨μ, σSq, hσ⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x)) volume :=
    (integrable_second_moment_var μ σSq hσ).const_mul _
  rw [integral_add h_int1 h_int2]
  rw [integral_const_mul, integral_const_mul]
  rw [int_density_eq_one_var μ σSq hσ]
  rw [int_second_central_moment_var μ σSq hσ]
  -- Now goal: (1/2)·log(1+δ) · 1 + (-(δ/(2σ²(1+δ)))) · σSq ≤ 50·δ²
  have h_log_le : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos h1δ
    linarith
  have h_lhs_eq :
      (1/2) * Real.log (1 + δ) * 1 + (-(δ / (2 * σSq * (1 + δ)))) * σSq
      = (1/2) * Real.log (1 + δ) - δ / (2 * (1 + δ)) := by
    field_simp
    ring
  rw [h_lhs_eq]
  -- Goal: (1/2)·log(1+δ) - δ/(2(1+δ)) ≤ 50·δ²
  -- log(1+δ) ≤ δ. So (1/2)log(1+δ) ≤ δ/2
  -- (1/2)log(1+δ) - δ/(2(1+δ)) ≤ δ/2 - δ/(2(1+δ)) = δ²/(2(1+δ)) ≤ δ²/2 ≤ 50δ²
  have h_key : (1/2) * δ - δ / (2 * (1 + δ)) = δ^2 / (2 * (1 + δ)) := by
    field_simp
    ring
  have h_half_pos : (0 : ℝ) < 2 * (1 + δ) := by positivity
  have h_main : δ^2 / (2 * (1 + δ)) ≤ 50 * δ^2 := by
    rw [div_le_iff₀ h_half_pos]
    nlinarith [sq_nonneg δ]
  have h_step1 : (1/2) * Real.log (1 + δ) ≤ (1/2) * δ := by linarith
  have h_step2 : (1/2) * Real.log (1 + δ) - δ / (2 * (1 + δ))
                ≤ (1/2) * δ - δ / (2 * (1 + δ)) := by linarith
  linarith [h_key ▸ h_step2, h_main]

end Workspace.ProofLemmas
