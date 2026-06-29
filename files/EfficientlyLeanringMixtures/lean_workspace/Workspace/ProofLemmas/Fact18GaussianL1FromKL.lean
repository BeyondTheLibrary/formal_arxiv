import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.PinskerL1FromTwoPoint

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas

/-- Helper: density is continuous, hence measurable. -/
private lemma density_measurable (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Measurable G.density := by
  unfold Workspace.Types.GaussianPDF.GaussianPDF.density
  exact (((measurable_id.sub_const _).pow_const _).neg.div_const _).exp.const_mul _

/-- Helper: density is positive everywhere. -/
private lemma density_pos (G : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    0 < G.density x := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  apply mul_pos
  · apply one_div_pos.mpr
    apply Real.sqrt_pos.mpr
    have : 0 < 2 * Real.pi := by positivity
    exact mul_pos this G.varSq_pos
  · exact Real.exp_pos _

/-- Helper: density is nonneg. -/
private lemma density_nonneg (G : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    0 ≤ G.density x := le_of_lt (density_pos G x)

/-- Helper: nnreal coercion of varSq is nonzero. -/
private lemma varSq_nnreal_ne_zero (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    (⟨G.varSq, le_of_lt G.varSq_pos⟩ : NNReal) ≠ 0 := by
  intro h
  have h' : G.varSq = 0 := congr_arg Subtype.val h
  linarith [G.varSq_pos]

/-- Helper: density integrates to 1. -/
private lemma density_integral_eq_one (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    ∫ x, G.density x ∂volume = 1 := by
  have hv := varSq_nnreal_ne_zero G
  have hbridge : G.density = ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩ := by
    funext x
    exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal G x
  rw [hbridge]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one G.mean hv

/-- Helper: density is integrable. -/
private lemma density_integrable (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Integrable G.density volume := by
  have hbridge : G.density = ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩ := by
    funext x
    exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal G x
  rw [hbridge]
  exact ProbabilityTheory.integrable_gaussianPDFReal G.mean _

/-- Helper: `(x - μ)^2 * density` is integrable. -/
private lemma sq_density_integrable (G : Workspace.Types.GaussianPDF.GaussianPDF) (a : ℝ) :
    Integrable (fun x => (x - a) ^ 2 * G.density x) volume := by
  set σ := G.varSq with hσdef
  set μ := G.mean with hμdef
  have hσ : 0 < σ := G.varSq_pos
  have hα : 0 < 1 / (2 * σ) := by positivity
  -- Factor out the constant
  have step : ∀ x, (x - a) ^ 2 * G.density x =
      (1 / Real.sqrt (2 * Real.pi * σ)) * ((x - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ))) := by
    intro x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    ring
  rw [show (fun x => (x - a) ^ 2 * G.density x) =
        (fun x => (1 / Real.sqrt (2 * Real.pi * σ)) * ((x - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ)))) from
        funext step]
  apply Integrable.const_mul
  have hint_main : Integrable (fun y => y^2 * Real.exp (-y^2 / (2 * σ))) volume := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1/(2*σ)) hα (s := 2) (by norm_num)
    convert h using 1
    funext y
    rw [show -(1/(2*σ)) * y^2 = -y^2 / (2*σ) by ring]
    congr 1
    rw [show y^(2:ℝ) = y^(2:ℕ) by norm_cast]
  have hint_lin : Integrable (fun y => y * Real.exp (-y^2 / (2 * σ))) volume := by
    have h := integrable_mul_exp_neg_mul_sq (b := 1/(2*σ)) hα
    convert h using 1
    funext y
    rw [show -(1/(2*σ)) * y^2 = -y^2 / (2*σ) by ring]
  have hint_exp : Integrable (fun y => Real.exp (-y^2 / (2 * σ))) volume := by
    have h := integrable_exp_neg_mul_sq (b := 1/(2*σ)) hα
    convert h using 1
    funext y
    rw [show -(1/(2*σ)) * y^2 = -y^2 / (2*σ) by ring]
  have hint_shifted_main :
      Integrable (fun x => (x - μ)^2 * Real.exp (-(x - μ)^2 / (2 * σ))) volume :=
    hint_main.comp_sub_right μ
  have hint_shifted_lin :
      Integrable (fun x => (x - μ) * Real.exp (-(x - μ)^2 / (2 * σ))) volume :=
    hint_lin.comp_sub_right μ
  have hint_shifted_exp :
      Integrable (fun x => Real.exp (-(x - μ)^2 / (2 * σ))) volume :=
    hint_exp.comp_sub_right μ
  have heq : ∀ x, (x - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ)) =
      (x - μ)^2 * Real.exp (-(x - μ)^2 / (2 * σ)) +
      2 * (μ - a) * ((x - μ) * Real.exp (-(x - μ)^2 / (2 * σ))) +
      (μ - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ)) := by
    intro x; ring
  rw [show (fun x => (x - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ))) =
        (fun x => (x - μ)^2 * Real.exp (-(x - μ)^2 / (2 * σ)) +
                  2 * (μ - a) * ((x - μ) * Real.exp (-(x - μ)^2 / (2 * σ))) +
                  (μ - a)^2 * Real.exp (-(x - μ)^2 / (2 * σ))) from funext heq]
  exact (hint_shifted_main.add (hint_shifted_lin.const_mul (2 * (μ - a)))).add
        (hint_shifted_exp.const_mul ((μ - a)^2))

/-- Helper: log of (G₁.density / G₂.density) = const + quadratic. -/
private lemma log_density_ratio (G₁ G₂ : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    Real.log (G₁.density x / G₂.density x) =
      Real.log (Real.sqrt (2 * Real.pi * G₂.varSq)) - Real.log (Real.sqrt (2 * Real.pi * G₁.varSq)) +
      ((x - G₂.mean)^2 / (2 * G₂.varSq) - (x - G₁.mean)^2 / (2 * G₁.varSq)) := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq, Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  have hs₁ : 0 < Real.sqrt (2 * Real.pi * G₁.varSq) := by
    apply Real.sqrt_pos.mpr
    have := G₁.varSq_pos; positivity
  have hs₂ : 0 < Real.sqrt (2 * Real.pi * G₂.varSq) := by
    apply Real.sqrt_pos.mpr
    have := G₂.varSq_pos; positivity
  have he₁ : (0 : ℝ) < Real.exp (-(x - G₁.mean)^2 / (2 * G₁.varSq)) := Real.exp_pos _
  have he₂ : (0 : ℝ) < Real.exp (-(x - G₂.mean)^2 / (2 * G₂.varSq)) := Real.exp_pos _
  have hinv1 : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi * G₁.varSq) := one_div_pos.mpr hs₁
  have hinv2 : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi * G₂.varSq) := one_div_pos.mpr hs₂
  have hd₁ : (1 : ℝ) / Real.sqrt (2 * Real.pi * G₁.varSq) * Real.exp (-(x - G₁.mean)^2 / (2 * G₁.varSq)) > 0 :=
    mul_pos hinv1 he₁
  have hd₂ : (1 : ℝ) / Real.sqrt (2 * Real.pi * G₂.varSq) * Real.exp (-(x - G₂.mean)^2 / (2 * G₂.varSq)) > 0 :=
    mul_pos hinv2 he₂
  rw [Real.log_div hd₁.ne' hd₂.ne']
  rw [Real.log_mul hinv1.ne' he₁.ne']
  rw [Real.log_mul hinv2.ne' he₂.ne']
  rw [Real.log_exp, Real.log_exp]
  have hlog1 : Real.log (1 / Real.sqrt (2 * Real.pi * G₁.varSq)) = -Real.log (Real.sqrt (2 * Real.pi * G₁.varSq)) := by
    rw [one_div, Real.log_inv]
  have hlog2 : Real.log (1 / Real.sqrt (2 * Real.pi * G₂.varSq)) = -Real.log (Real.sqrt (2 * Real.pi * G₂.varSq)) := by
    rw [one_div, Real.log_inv]
  rw [hlog1, hlog2]
  ring

/-- The integrand `G₁.density * log(G₁.density / G₂.density)` is integrable. -/
private lemma kl_integrand_integrable (G₁ G₂ : Workspace.Types.GaussianPDF.GaussianPDF) :
    Integrable (fun x => G₁.density x * Real.log (G₁.density x / G₂.density x)) volume := by
  have heq : ∀ x, G₁.density x * Real.log (G₁.density x / G₂.density x) =
      G₁.density x * (Real.log (Real.sqrt (2 * Real.pi * G₂.varSq)) - Real.log (Real.sqrt (2 * Real.pi * G₁.varSq)))
      + G₁.density x * ((x - G₂.mean)^2 / (2 * G₂.varSq))
      - G₁.density x * ((x - G₁.mean)^2 / (2 * G₁.varSq)) := by
    intro x
    rw [log_density_ratio G₁ G₂ x]
    ring
  rw [show (fun x => G₁.density x * Real.log (G₁.density x / G₂.density x)) =
        (fun x => G₁.density x * (Real.log (Real.sqrt (2 * Real.pi * G₂.varSq)) - Real.log (Real.sqrt (2 * Real.pi * G₁.varSq)))
          + G₁.density x * ((x - G₂.mean)^2 / (2 * G₂.varSq))
          - G₁.density x * ((x - G₁.mean)^2 / (2 * G₁.varSq))) from funext heq]
  have h₁ : Integrable (fun x => G₁.density x * (Real.log (Real.sqrt (2 * Real.pi * G₂.varSq)) - Real.log (Real.sqrt (2 * Real.pi * G₁.varSq)))) volume :=
    (density_integrable G₁).mul_const _
  have h₂ : Integrable (fun x => G₁.density x * ((x - G₂.mean)^2 / (2 * G₂.varSq))) volume := by
    have hsq := sq_density_integrable G₁ G₂.mean
    have heq2 : (fun x => G₁.density x * ((x - G₂.mean)^2 / (2 * G₂.varSq))) =
           (fun x => (1 / (2 * G₂.varSq)) * ((x - G₂.mean)^2 * G₁.density x)) := by
      funext x; ring
    rw [heq2]
    exact hsq.const_mul _
  have h₃ : Integrable (fun x => G₁.density x * ((x - G₁.mean)^2 / (2 * G₁.varSq))) volume := by
    have hsq := sq_density_integrable G₁ G₁.mean
    have heq3 : (fun x => G₁.density x * ((x - G₁.mean)^2 / (2 * G₁.varSq))) =
           (fun x => (1 / (2 * G₁.varSq)) * ((x - G₁.mean)^2 * G₁.density x)) := by
      funext x; ring
    rw [heq3]
    exact hsq.const_mul _
  exact (h₁.add h₂).sub h₃

/-- KL nonnegativity: for f, g probability densities, `∫ f log(f/g) ≥ 0`. -/
private lemma kl_nonneg (G₁ G₂ : Workspace.Types.GaussianPDF.GaussianPDF) :
    0 ≤ ∫ x, G₁.density x * Real.log (G₁.density x / G₂.density x) ∂volume := by
  have hf_pos : ∀ x, 0 < G₁.density x := density_pos G₁
  have hg_pos : ∀ x, 0 < G₂.density x := density_pos G₂
  have hf_int : Integrable G₁.density volume := density_integrable G₁
  have hg_int : Integrable G₂.density volume := density_integrable G₂
  have hf_one : ∫ x, G₁.density x ∂volume = 1 := density_integral_eq_one G₁
  have hg_one : ∫ x, G₂.density x ∂volume = 1 := density_integral_eq_one G₂
  have hkl_int := kl_integrand_integrable G₁ G₂
  have h_pointwise : ∀ x, G₁.density x - G₂.density x ≤
      G₁.density x * Real.log (G₁.density x / G₂.density x) := by
    intro x
    have hf := hf_pos x
    have hg := hg_pos x
    have hratio : 0 < G₁.density x / G₂.density x := div_pos hf hg
    have hlog_ineq := Real.one_sub_inv_le_log_of_pos hratio
    have hmul : G₁.density x * (1 - (G₁.density x / G₂.density x)⁻¹) ≤
                G₁.density x * Real.log (G₁.density x / G₂.density x) :=
      mul_le_mul_of_nonneg_left hlog_ineq (le_of_lt hf)
    have hsimp : G₁.density x * (1 - (G₁.density x / G₂.density x)⁻¹) = G₁.density x - G₂.density x := by
      rw [inv_div]
      field_simp
    linarith
  have hdiff_int : Integrable (fun x => G₁.density x - G₂.density x) volume := hf_int.sub hg_int
  have hbnd := MeasureTheory.integral_mono_ae hdiff_int hkl_int
    (Filter.Eventually.of_forall h_pointwise)
  have hdiff_eq : ∫ x, (G₁.density x - G₂.density x) ∂volume = 0 := by
    rw [integral_sub hf_int hg_int, hf_one, hg_one]; ring
  linarith

theorem Fact18GaussianL1FromKL :
    ∀ (μ₁ σ₁Sq μ₂ σ₂Sq : ℝ) (hσ₁ : 0 < σ₁Sq) (hσ₂ : 0 < σ₂Sq),
      Workspace.Types.L1AndTVDistance.L1Norm
        (fun x => (⟨μ₁, σ₁Sq, hσ₁⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x -
                  (⟨μ₂, σ₂Sq, hσ₂⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x) ≤
        Real.sqrt (2 * (∫ x, (⟨μ₁, σ₁Sq, hσ₁⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x *
                              Real.log ((⟨μ₁, σ₁Sq, hσ₁⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x /
                                        (⟨μ₂, σ₂Sq, hσ₂⟩ : Workspace.Types.GaussianPDF.GaussianPDF).density x))) := by
  intro μ₁ σ₁Sq μ₂ σ₂Sq hσ₁ hσ₂
  set G₁ : Workspace.Types.GaussianPDF.GaussianPDF := ⟨μ₁, σ₁Sq, hσ₁⟩ with hG₁
  set G₂ : Workspace.Types.GaussianPDF.GaussianPDF := ⟨μ₂, σ₂Sq, hσ₂⟩ with hG₂
  apply PinskerL1FromTwoPoint G₁.density G₂.density
  · exact density_measurable G₁
  · exact density_measurable G₂
  · exact density_nonneg G₁
  · exact density_nonneg G₂
  · exact density_integrable G₁
  · exact density_integrable G₂
  · exact density_integral_eq_one G₁
  · exact density_integral_eq_one G₂
  · exact Filter.Eventually.of_forall (density_pos G₂)
  · exact kl_integrand_integrable G₁ G₂
  · exact kl_nonneg G₁ G₂

end Workspace.ProofLemmas
