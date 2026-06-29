import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Lemma5LocalizedWeightGapTVNarrow
import Workspace.ProofLemmas.GaussianL1LowerBoundCombinedGap
import Workspace.ProofLemmas.WeightedMixtureL1TriangleSplit
import Workspace.ProofLemmas.Fact18GaussianMeanShiftL1Bound
import Workspace.ProofLemmas.Fact18GaussianVarianceShiftL1Bound

set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureDeconvolution
open Workspace.Types.L1AndTVDistance
open Workspace.Types.EpsilonStandardPair

/-! ## Helpers for the assembly. -/

/-- L1Norm depends only on a Gaussian's mean and variance: any `GaussianPDF`
equals the canonical `⟨mean, varSq, _⟩` in density, so their L1Norm differences
agree. -/
private lemma cb_density_eq (G : GaussianPDF) (hσ : 0 < G.varSq) :
    G.density = (⟨G.mean, G.varSq, hσ⟩ : GaussianPDF).density := by
  funext x; rw [GaussianPDF.density_eq]

/-- Integrability of any `GaussianPDF` density. -/
private lemma cb_int (G : GaussianPDF) : MeasureTheory.Integrable G.density MeasureTheory.volume := by
  have h : G.density = fun x => ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h]; exact ProbabilityTheory.integrable_gaussianPDFReal _ _

/-- `L1Norm` of a single normalized density equals 1. -/
private lemma cb_L1Norm_density_eq_one (G : GaussianPDF) :
    L1Norm G.density = 1 := by
  rw [L1Norm_def]
  have h : G.density = fun x => ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  have hv : (⟨G.varSq, G.varSq_pos.le⟩ : NNReal) ≠ 0 := by
    have h0 : (0:NNReal) < ⟨G.varSq, G.varSq_pos.le⟩ := by
      rw [← NNReal.coe_lt_coe]; simpa using G.varSq_pos
    exact ne_of_gt h0
  calc ∫ x, |G.density x| ∂MeasureTheory.volume
      = ∫ x, G.density x ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        simp only
        rw [abs_of_nonneg]
        rw [G.density_eq_gaussianPDFReal x]
        exact ProbabilityTheory.gaussianPDFReal_nonneg _ _ _
    _ = ∫ x, ProbabilityTheory.gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x ∂MeasureTheory.volume := by
        rw [h]
    _ = 1 := by
        rw [ProbabilityTheory.integral_gaussianPDFReal_eq_one G.mean hv]

/-- Helper: triangle for L1Norm. -/
private lemma cb_L1Norm_add_le (f g : ℝ → ℝ)
    (hf : MeasureTheory.Integrable f MeasureTheory.volume)
    (hg : MeasureTheory.Integrable g MeasureTheory.volume) :
    L1Norm (fun x => f x + g x) ≤ L1Norm f + L1Norm g := by
  unfold L1Norm
  have h1 : MeasureTheory.Integrable (fun x => |f x|) MeasureTheory.volume := hf.abs
  have h2 : MeasureTheory.Integrable (fun x => |g x|) MeasureTheory.volume := hg.abs
  rw [← MeasureTheory.integral_add h1 h2]
  apply MeasureTheory.integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun x => abs_nonneg _)
  · exact h1.add h2
  · exact Filter.Eventually.of_forall (fun x => abs_add_le (f x) (g x))

private lemma cb_L1Norm_const_mul (c : ℝ) (f : ℝ → ℝ) :
    L1Norm (fun x => c * f x) = |c| * L1Norm f := by
  unfold L1Norm
  simp only [abs_mul]
  rw [← MeasureTheory.integral_const_mul]

private lemma cb_L1Norm_nonneg (f : ℝ → ℝ) : 0 ≤ L1Norm f := by
  unfold L1Norm; exact MeasureTheory.integral_nonneg (fun x => abs_nonneg _)

/-- Weighted single-pair reverse triangle:
`L1Norm (w₂G₂ − w₂'G₂') ≥ w₂·L1Norm(G₂−G₂') − |w₂−w₂'|·L1Norm G₂'`. -/
private lemma cb_weighted_rev_tri (w₂ w₂' : ℝ) (G₂ G₂' : ℝ → ℝ)
    (hG₂ : MeasureTheory.Integrable G₂ MeasureTheory.volume)
    (hG₂' : MeasureTheory.Integrable G₂' MeasureTheory.volume)
    (hw₂ : 0 ≤ w₂) :
    w₂ * L1Norm (fun x => G₂ x - G₂' x) - |w₂ - w₂'| * L1Norm G₂'
      ≤ L1Norm (fun x => w₂ * G₂ x - w₂' * G₂' x) := by
  have htri := cb_L1Norm_add_le (fun x => w₂ * G₂ x - w₂' * G₂' x) (fun x => (w₂' - w₂) * G₂' x)
    ((hG₂.const_mul w₂).sub (hG₂'.const_mul w₂')) (hG₂'.const_mul (w₂' - w₂))
  -- htri : L1Norm (fun x => (w₂G₂−w₂'G₂') + (w₂'−w₂)G₂') ≤ L1Norm(w₂G₂−w₂'G₂') + L1Norm((w₂'−w₂)G₂')
  have hlhs_eq : L1Norm (fun x => (w₂ * G₂ x - w₂' * G₂' x) + (w₂' - w₂) * G₂' x)
      = w₂ * L1Norm (fun x => G₂ x - G₂' x) := by
    have : (fun x => (w₂ * G₂ x - w₂' * G₂' x) + (w₂' - w₂) * G₂' x)
        = (fun x => w₂ * (G₂ x - G₂' x)) := by funext x; ring
    rw [this, cb_L1Norm_const_mul w₂ (fun x => G₂ x - G₂' x), abs_of_nonneg hw₂]
  have hrhs_eq : L1Norm (fun x => (w₂' - w₂) * G₂' x) = |w₂ - w₂'| * L1Norm G₂' := by
    rw [cb_L1Norm_const_mul (w₂' - w₂) G₂', abs_sub_comm w₂' w₂]
  rw [hlhs_eq, hrhs_eq] at htri
  linarith [htri]

/-- comp1 L¹ difference upper bound via Fact 18 (mean shift + variance shift, triangle).
For two Gaussians with variances in `[1/2, 3/2]`, mean gap `< 6ε⁵`, variance gap `< 16ε¹⁰`:
`‖G₁ − G₁'‖₁ ≤ 60ε⁵ + 320ε¹⁰`. Extracted as its own declaration so its (substantial)
elaboration gets a fresh heartbeat budget. -/
private lemma cb_comp1_diff_ub (G1 G1' : GaussianPDF) (ε : ℝ)
    (hG1lo : (1/2:ℝ) ≤ G1.varSq) (hG1hi : G1.varSq ≤ (3/2:ℝ))
    (hG1'lo : (1/2:ℝ) ≤ G1'.varSq) (hG1'hi : G1'.varSq ≤ (3/2:ℝ))
    (hμgap : |G1.mean - G1'.mean| < 6 * ε^5)
    (hvgap : |G1'.varSq - G1.varSq| < 16 * ε^10) :
    L1Norm (fun x => G1.density x - G1'.density x) ≤ 60*ε^5 + 320*ε^10 := by
  set v₁ := G1.varSq with hv1
  set v₁' := G1'.varSq with hv1'
  set μa := G1.mean with hμa
  set μb := G1'.mean with hμb
  have hG1pos : 0 < v₁ := G1.varSq_pos
  have hG'1pos : 0 < v₁' := G1'.varSq_pos
  -- Fact18 mean shift: ‖N(μa,v₁) − N(μa+(μb-μa),v₁)‖ ≤ 10|μb−μa|
  have hmean := Fact18GaussianMeanShiftL1Bound μa (μb - μa) v₁ hG1pos hG1lo hG1hi
  -- Fact18 variance shift: ‖N(μb,v₁) − N(μb,v₁')‖ ≤ 20|v₁'−v₁|
  have hvar := Fact18GaussianVarianceShiftL1Bound μb v₁ v₁' hG1pos hG'1pos hG1lo hG1hi hG1'lo hG1'hi
  have hGa : (⟨μa, v₁, hG1pos⟩ : GaussianPDF).density = G1.density :=
    (cb_density_eq G1 hG1pos).symm
  have hGb' : (⟨μb, v₁', hG'1pos⟩ : GaussianPDF).density = G1'.density :=
    (cb_density_eq G1' hG'1pos).symm
  have hμb_eq : μa + (μb - μa) = μb := by ring
  have htri := cb_L1Norm_add_le
    (fun x => (⟨μa, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μa + (μb-μa), v₁, hG1pos⟩ : GaussianPDF).density x)
    (fun x => (⟨μb, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μb, v₁', hG'1pos⟩ : GaussianPDF).density x)
    ((cb_int _).sub (cb_int _)) ((cb_int _).sub (cb_int _))
  have hsum_eq : (fun x => ((⟨μa, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μa + (μb-μa), v₁, hG1pos⟩ : GaussianPDF).density x)
        + ((⟨μb, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μb, v₁', hG'1pos⟩ : GaussianPDF).density x))
      = (fun x => G1.density x - G1'.density x) := by
    funext x
    have e1 : (⟨μa + (μb-μa), v₁, hG1pos⟩ : GaussianPDF).density x = (⟨μb, v₁, hG1pos⟩ : GaussianPDF).density x := by
      rw [GaussianPDF.density_eq, GaussianPDF.density_eq, hμb_eq]
    rw [e1, ← hGa, ← hGb']; ring
  rw [hsum_eq] at htri
  have hpiece1 : L1Norm (fun x => (⟨μa, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μa + (μb-μa), v₁, hG1pos⟩ : GaussianPDF).density x) ≤ 10 * |μb - μa| := hmean
  have hpiece2 : L1Norm (fun x => (⟨μb, v₁, hG1pos⟩ : GaussianPDF).density x - (⟨μb, v₁', hG'1pos⟩ : GaussianPDF).density x) ≤ 20 * |v₁' - v₁| := hvar
  have hμsym : |μb - μa| = |μa - μb| := abs_sub_comm μb μa
  rw [hμsym] at hpiece1
  linarith [htri, hpiece1, hpiece2, hμgap, hvgap]

/-- Branch L of Case 2b: small weight gap (`|Δw₁| < 48ε³`), deconvolution
`β = σ₁² − 1/2` (post-deconv variances in `[1/2, 3/2]`). The comp2 combined-gap
(`GaussianL1LowerBoundCombinedGap`) supplies an `Ω(ε²)` L¹ signal that beats both
the weight-gap noise `O(ε³)` and the comp1 Fact-18 shift noise `O(ε⁵)`. Concludes
`ε²/(24C₀) ≤ TVDistance`. Extracted into its own declaration for a fresh heartbeat
budget. -/
private lemma cb_branchL_TV
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε β C₀ : ℝ)
    (h₁ : β < min F.comp1.varSq F.comp2.varSq)
    (h₂ : β < min F'.comp1.varSq F'.comp2.varSq)
    (hC₀_pos : 0 < C₀)
    (hCG : ∀ (μ μ' σSq σ'Sq : ℝ) (hσ : 0 < σSq) (hσ' : 0 < σ'Sq),
        (1 / 2 : ℝ) ≤ σSq → σSq ≤ (3 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ σ'Sq → σ'Sq ≤ (3 / 2 : ℝ) →
        max (min |μ - μ'| 1) |σSq - σ'Sq| / C₀ ≤
          L1Norm (fun x =>
            (⟨μ, σSq, hσ⟩ : GaussianPDF).density x - (⟨μ', σ'Sq, hσ'⟩ : GaussianPDF).density x))
    (hβ : β = F.comp1.varSq - 1/2)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) (hε_le_1e5 : ε ≤ 1/100000)
    (hε_le_C : ε ≤ 1 / (96 * 96 * C₀))
    (h_std : Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε)
    (h12 : F.comp1.varSq ≤ F.comp2.varSq)
    (h1'1 : F.comp1.varSq ≤ F'.comp1.varSq)
    (h1'2 : F.comp1.varSq ≤ F'.comp2.varSq)
    (hVF1 : 0 < F.comp1.varSq)
    (hVF1_le1 : F.comp1.varSq ≤ 1) (hVF2_le1 : F.comp2.varSq ≤ 1)
    (hVF'1_le1 : F'.comp1.varSq ≤ 1) (hVF'2_le1 : F'.comp2.varSq ≤ 1)
    (hCase2_var : F'.comp1.varSq - F.comp1.varSq < 16 * ε ^ 10)
    (hCase2_mean : |F'.comp1.mean - F.comp1.mean| < 6 * ε ^ 5)
    (hbranch : |F.weight1 - F'.weight1| < 48 * ε^3) :
    ε^2/(24*C₀) ≤ Workspace.Types.L1AndTVDistance.TVDistance
      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F β h₁)
      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' β h₂) := by
  set G := Workspace.Types.MixtureDeconvolution.deconvMixture2 F β h₁ with hG
  set G' := Workspace.Types.MixtureDeconvolution.deconvMixture2 F' β h₂ with hG'
  have hG1m : G.comp1.mean = F.comp1.mean := rfl
  have hG1v : G.comp1.varSq = F.comp1.varSq - β := rfl
  have hG2m : G.comp2.mean = F.comp2.mean := rfl
  have hG2v : G.comp2.varSq = F.comp2.varSq - β := rfl
  have hG'1m : G'.comp1.mean = F'.comp1.mean := rfl
  have hG'1v : G'.comp1.varSq = F'.comp1.varSq - β := rfl
  have hG'2m : G'.comp2.mean = F'.comp2.mean := rfl
  have hG'2v : G'.comp2.varSq = F'.comp2.varSq - β := rfl
  have hGw1 : G.weight1 = F.weight1 := rfl
  have hGw2 : G.weight2 = F.weight2 := rfl
  have hG'w1 : G'.weight1 = F'.weight1 := rfl
  have hG'w2 : G'.weight2 = F'.weight2 := rfl
  have hG2v_lo : (1/2:ℝ) ≤ G.comp2.varSq := by rw [hG2v, hβ]; linarith [h12]
  have hG2v_hi : G.comp2.varSq ≤ (3/2:ℝ) := by rw [hG2v, hβ]; linarith [hVF2_le1, hVF1]
  have hG'2v_lo : (1/2:ℝ) ≤ G'.comp2.varSq := by rw [hG'2v, hβ]; linarith [h1'2]
  have hG'2v_hi : G'.comp2.varSq ≤ (3/2:ℝ) := by rw [hG'2v, hβ]; linarith [hVF'2_le1, hVF1]
  have hG1v_lo : (1/2:ℝ) ≤ G.comp1.varSq := by rw [hG1v, hβ]; linarith
  have hG1v_hi : G.comp1.varSq ≤ (3/2:ℝ) := by rw [hG1v, hβ]; linarith [hVF1_le1]
  have hG'1v_lo : (1/2:ℝ) ≤ G'.comp1.varSq := by rw [hG'1v, hβ]; linarith [h1'1]
  have hG'1v_hi : G'.comp1.varSq ≤ (3/2:ℝ) := by rw [hG'1v, hβ]; linarith [hVF'1_le1, hVF1]
  have hG2pos : 0 < G.comp2.varSq := G.comp2.varSq_pos
  have hG'2pos : 0 < G'.comp2.varSq := G'.comp2.varSq_pos
  have hw2_lb : ε ≤ F.weight2 := h_std.eps_le_weight2_F
  have hw1_nn : 0 ≤ F.weight1 := F.weight1_nonneg
  have hw2_nn : 0 ≤ F.weight2 := F.weight2_nonneg
  have hw1_le : F.weight1 ≤ 1 := by linarith [F.weight2_nonneg, F.weights_sum_one]
  have hΔw2_eq : |F.weight2 - F'.weight2| = |F.weight1 - F'.weight1| := by
    have e1 : F.weight2 = 1 - F.weight1 := by linarith [F.weights_sum_one]
    have e2 : F'.weight2 = 1 - F'.weight1 := by linarith [F'.weights_sum_one]
    rw [e1, e2, show (1 - F.weight1) - (1 - F'.weight1) = -(F.weight1 - F'.weight1) from by ring, abs_neg]
  have hΔμ1 : |F.comp1.mean - F'.comp1.mean| < 6 * ε^5 := by rw [abs_sub_comm]; exact hCase2_mean
  have hΔv1 : |F.comp1.varSq - F'.comp1.varSq| < 16 * ε^10 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [h1'1])]; exact hCase2_var
  have hinter := h_std.inter_sep_id
  have hε3_le_ε2' : ε^3 ≤ ε^2 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
  have hε5_le_ε2 : ε^5 ≤ ε^2 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
  have hε10_le_ε2 : ε^10 ≤ ε^2 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
  have hε2_le_small : ε^2 ≤ ε * (1/100000) := by
    have : ε^2 = ε * ε := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hε_le_1e5 hε_pos.le
  have hcomp2_gap : ε/2 ≤ |F.comp2.mean - F'.comp2.mean| + |F.comp2.varSq - F'.comp2.varSq| := by
    have hw2gap : |F.weight2 - F'.weight2| < 48*ε^3 := by rw [hΔw2_eq]; exact hbranch
    have hb1 : 48*ε^3 ≤ 48*ε^2 := by linarith [hε3_le_ε2']
    have hb2 : 6*ε^5 ≤ 6*ε^2 := by linarith [hε5_le_ε2]
    have hb3 : 16*ε^10 ≤ 16*ε^2 := by linarith [hε10_le_ε2]
    have hsmall : 118*ε^2 ≤ ε/2 := by
      have : 118*ε^2 ≤ 118*(ε*(1/100000)) := by linarith [hε2_le_small]
      nlinarith [this, hε_pos.le]
    linarith [hinter, hΔμ1, hΔv1, hbranch, hw2gap, hb1, hb2, hb3, hsmall]
  have hmaxgap : ε/6 ≤ max (min |F.comp2.mean - F'.comp2.mean| 1) |F.comp2.varSq - F'.comp2.varSq| := by
    rcases le_or_gt (ε/4) (|F.comp2.varSq - F'.comp2.varSq|) with hv | hv
    · exact le_trans (by linarith) (le_max_right _ _)
    · have hμ : ε/4 ≤ |F.comp2.mean - F'.comp2.mean| := by linarith [hcomp2_gap]
      have hε4_le1 : ε/4 ≤ 1 := by linarith [hε_le_one]
      have hmin : ε/4 ≤ min |F.comp2.mean - F'.comp2.mean| 1 := le_min hμ hε4_le1
      exact le_trans (by linarith) (le_trans hmin (le_max_left _ _))
  have hCG2 := hCG G.comp2.mean G'.comp2.mean G.comp2.varSq G'.comp2.varSq hG2pos hG'2pos
    hG2v_lo hG2v_hi hG'2v_lo hG'2v_hi
  have hd2 : (⟨G.comp2.mean, G.comp2.varSq, hG2pos⟩ : GaussianPDF).density = G.comp2.density :=
    (cb_density_eq G.comp2 hG2pos).symm
  have hd2' : (⟨G'.comp2.mean, G'.comp2.varSq, hG'2pos⟩ : GaussianPDF).density = G'.comp2.density :=
    (cb_density_eq G'.comp2 hG'2pos).symm
  rw [hd2, hd2'] at hCG2
  have hgapeq : max (min |G.comp2.mean - G'.comp2.mean| 1) |G.comp2.varSq - G'.comp2.varSq|
      = max (min |F.comp2.mean - F'.comp2.mean| 1) |F.comp2.varSq - F'.comp2.varSq| := by
    rw [hG2m, hG'2m, hG2v, hG'2v, hβ]
    congr 2
    · ring_nf
  rw [hgapeq] at hCG2
  have hG2diff_lb : (ε/6)/C₀ ≤ L1Norm (fun x => G.comp2.density x - G'.comp2.density x) := by
    refine le_trans ?_ hCG2
    gcongr
  have hG2'_L1 : L1Norm G'.comp2.density = 1 := cb_L1Norm_density_eq_one G'.comp2
  have hwrt := cb_weighted_rev_tri F.weight2 F'.weight2 G.comp2.density G'.comp2.density
    (cb_int G.comp2) (cb_int G'.comp2) hw2_nn
  rw [hG2'_L1, mul_one] at hwrt
  have hw2diff_lb : ε * ((ε/6)/C₀) - 48*ε^3
      ≤ L1Norm (fun x => F.weight2 * G.comp2.density x - F'.weight2 * G'.comp2.density x) := by
    have h1 : ε * ((ε/6)/C₀) ≤ F.weight2 * L1Norm (fun x => G.comp2.density x - G'.comp2.density x) := by
      apply mul_le_mul hw2_lb hG2diff_lb (by positivity) hw2_nn
    have h2 : |F.weight2 - F'.weight2| ≤ 48*ε^3 := by rw [hΔw2_eq]; linarith [hbranch]
    linarith [hwrt, h1, h2, cb_L1Norm_nonneg (fun x => G.comp2.density x - G'.comp2.density x)]
  have hμgap1 : |G.comp1.mean - G'.comp1.mean| < 6*ε^5 := by
    have heq : G.comp1.mean - G'.comp1.mean = F.comp1.mean - F'.comp1.mean := rfl
    rw [heq, abs_sub_comm]; exact hCase2_mean
  have hvgap1 : |G'.comp1.varSq - G.comp1.varSq| < 16*ε^10 := by
    have heq : G'.comp1.varSq - G.comp1.varSq = F'.comp1.varSq - F.comp1.varSq := by
      show (F'.comp1.varSq - β) - (F.comp1.varSq - β) = F'.comp1.varSq - F.comp1.varSq; ring
    rw [heq, abs_of_nonneg (by linarith [h1'1])]; exact hCase2_var
  have hG1diff_ub : L1Norm (fun x => G.comp1.density x - G'.comp1.density x) ≤ 60*ε^5 + 320*ε^10 :=
    cb_comp1_diff_ub G.comp1 G'.comp1 ε hG1v_lo hG1v_hi hG'1v_lo hG'1v_hi hμgap1 hvgap1
  have hsplit := WeightedMixtureL1TriangleSplit F.weight1 F.weight2 F'.weight1 F'.weight2
    G.comp1.density G.comp2.density G'.comp1.density G'.comp2.density
    (cb_int G.comp1) (cb_int G.comp2) (cb_int G'.comp1) (cb_int G'.comp2) hw1_nn
  have hG'1_L1 : L1Norm G'.comp1.density = 1 := cb_L1Norm_density_eq_one G'.comp1
  have hG'2_L1' : L1Norm G'.comp2.density = 1 := cb_L1Norm_density_eq_one G'.comp2
  rw [hG'1_L1, hG'2_L1'] at hsplit
  have hrhs_fun : (fun x => (F.weight1 * G.comp1.density x + F.weight2 * G.comp2.density x)
        - (F'.weight1 * G'.comp1.density x + F'.weight2 * G'.comp2.density x))
      = (fun x => G.density x - G'.density x) := by
    funext x
    rw [GaussianMixture2.density_eq, GaussianMixture2.density_eq, hGw1, hGw2, hG'w1, hG'w2]
  rw [hrhs_fun] at hsplit
  have h2TV : 2 * Workspace.Types.L1AndTVDistance.TVDistance G G'
      = L1Norm (fun x => G.density x - G'.density x) := by
    rw [Workspace.Types.L1AndTVDistance.TVDistance_def,
        Workspace.Types.L1AndTVDistance.L1NormMixtureDiff_def]
    ring
  have hΔw1_le : |F.weight1 - F'.weight1| ≤ 48*ε^3 := le_of_lt hbranch
  have hw1_bound : F.weight1 * L1Norm (fun x => G.comp1.density x - G'.comp1.density x)
      ≤ 60*ε^5 + 320*ε^10 := by
    have hh := mul_le_mul_of_nonneg_left hG1diff_ub hw1_nn
    calc F.weight1 * L1Norm (fun x => G.comp1.density x - G'.comp1.density x)
        ≤ F.weight1 * (60*ε^5 + 320*ε^10) := hh
      _ ≤ 1 * (60*ε^5 + 320*ε^10) := by
          apply mul_le_mul_of_nonneg_right hw1_le (by positivity)
      _ = 60*ε^5 + 320*ε^10 := by ring
  have hwgapnoise : |F.weight1 - F'.weight1| * (1 + 1) ≤ 96*ε^3 := by
    rw [show (1:ℝ)+1 = 2 from by ring]; linarith [hΔw1_le, abs_nonneg (F.weight1 - F'.weight1)]
  have hTVchain : ε * ((ε/6)/C₀) - 48*ε^3 - (60*ε^5 + 320*ε^10) - 96*ε^3
      ≤ 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' := by
    rw [h2TV]
    linarith [hsplit, hw2diff_lb, hw1_bound, hwgapnoise]
  have hεC : 96*96*C₀*ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hε_le_C
    nlinarith [hε_le_C, hε_pos.le, hC₀_pos]
  have hval_eq : ε * ((ε/6)/C₀) = ε^2/(6*C₀) := by field_simp
  rw [hval_eq] at hTVchain
  have hε5_le3 : ε^5 ≤ ε^3 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
  have hε10_le3 : ε^10 ≤ ε^3 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
  have hnoise_le : 48*ε^3 + (60*ε^5 + 320*ε^10) + 96*ε^3 ≤ ε^2/(12*C₀) := by
    have hLHS : 48*ε^3 + (60*ε^5 + 320*ε^10) + 96*ε^3 ≤ 524*ε^3 := by
      linarith [hε5_le3, hε10_le3]
    have h524 : 524*ε^3 ≤ ε^2/(12*C₀) := by
      rw [le_div_iff₀ (by positivity)]
      have hε2pos : 0 < ε^2 := by positivity
      have hkey : 6288*C₀*ε ≤ 1 := by nlinarith [hεC, hC₀_pos, hε_pos.le]
      have hrw : 524*ε^3*(12*C₀) = (6288*C₀*ε) * ε^2 := by ring
      rw [hrw]
      calc (6288*C₀*ε) * ε^2 ≤ 1 * ε^2 := by
            apply mul_le_mul_of_nonneg_right hkey hε2pos.le
        _ = ε^2 := by ring
    linarith [hLHS, h524]
  have h2TV_lb : ε^2/(12*C₀) ≤ 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' := by
    have hsplit_half : ε^2/(6*C₀) - ε^2/(12*C₀) = ε^2/(12*C₀) := by field_simp; ring
    linarith [hTVchain, hnoise_le, hsplit_half]
  have hh : ε^2/(12*C₀) = 2 * (ε^2/(24*C₀)) := by field_simp; ring
  linarith [h2TV_lb, hh ▸ h2TV_lb]

/-! ## Main theorem. -/

theorem Lemma5Case2bAssembly :
    ∃ K_5_2b ε_max : ℝ, 0 < K_5_2b ∧ 0 < ε_max ∧
      ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
        0 < ε → ε ≤ 1 → ε ≤ ε_max →
        Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
        F.comp1.varSq ≤ F.comp2.varSq →
        F.comp1.varSq ≤ F'.comp1.varSq →
        F.comp1.varSq ≤ F'.comp2.varSq →
        F'.comp1.varSq - F.comp1.varSq < 16 * ε ^ 10 →
        |F'.comp1.mean - F.comp1.mean| < 6 * ε ^ 5 →
        |F.weight1 - F'.weight1| < ε ^ 2 →
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
              ∧ K_5_2b * ε ^ 4 ≤
                  Workspace.Types.L1AndTVDistance.TVDistance
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) := by
  obtain ⟨C₀, hC₀_pos, hCG⟩ := GaussianL1LowerBoundCombinedGap
  -- Branch constants: U gives 16; L gives 1/(96 C₀).
  refine ⟨min 16 (1 / (96 * C₀)), min (1/100000) (1 / (96 * 96 * C₀)),
    lt_min (by norm_num) (by positivity),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro F F' ε hε_pos hε_le_one hε_small h_std h12 h1'1 h1'2 hCase2_var hCase2_mean hCase2b_w
  set K := min 16 (1 / (96 * C₀)) with hK
  have hε_le_1e5 : ε ≤ 1/100000 := le_trans hε_small (min_le_left _ _)
  have hε_le_C : ε ≤ 1 / (96 * 96 * C₀) := le_trans hε_small (min_le_right _ _)
  have hε4_nn : 0 ≤ ε^4 := by positivity
  have hΔw_abs : |F.weight1 - F'.weight1| < ε^2 := hCase2b_w
  have hK_le_16 : K ≤ 16 := min_le_left _ _
  have hK_le_L : K ≤ 1 / (96 * C₀) := min_le_right _ _
  -- common variance positivity facts
  have hVF1 : 0 < F.comp1.varSq := F.comp1.varSq_pos
  have hε10_pos : 0 < ε^10 := by positivity
  have hε3_le_ε2 : ε^3 ≤ ε^2 := by nlinarith [hε_pos.le, hε_le_one, pow_pos hε_pos 2, mul_pos hε_pos hε_pos]
  by_cases hbranch : 48 * ε^3 ≤ |F.weight1 - F'.weight1|
  · -- ===== Branch U: localized narrow-window weight gap, α = σ₁² − ε¹⁰ =====
    set α : ℝ := F.comp1.varSq - ε^10 with hα
    have h₁ : α < min F.comp1.varSq F.comp2.varSq := by
      rw [hα, lt_min_iff]; constructor
      · linarith [hε10_pos]
      · linarith [h12, hε10_pos]
    have h₂ : α < min F'.comp1.varSq F'.comp2.varSq := by
      rw [hα, lt_min_iff]; constructor
      · linarith [h1'1, hε10_pos]
      · linarith [h1'2, hε10_pos]
    refine ⟨α, h₁, h₂, ?_, ?_, ?_⟩
    · rw [hα]; linarith [hVF1, hε10_pos, pow_le_one₀ hε_pos.le hε_le_one (n := 10)]
    · -- variance floor: every post-deconv variance ≥ ε¹⁰ ≥ ε¹²
      have hε12_le_ε10 : ε^12 ≤ ε^10 := by nlinarith [pow_pos hε_pos 10, hε_le_one, hε_pos.le, sq_nonneg ε, pow_le_one₀ hε_pos.le hε_le_one (n := 2)]
      rw [le_min_iff, le_min_iff, le_min_iff]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · show ε^12 ≤ F.comp1.varSq - α; rw [hα]; linarith [hε12_le_ε10]
      · show ε^12 ≤ F.comp2.varSq - α; rw [hα]; linarith [h12, hε12_le_ε10]
      · show ε^12 ≤ F'.comp1.varSq - α; rw [hα]; linarith [h1'1, hε12_le_ε10]
      · show ε^12 ≤ F'.comp2.varSq - α; rw [hα]; linarith [h1'2, hε12_le_ε10]
    · -- TV bound from narrow-window lemma
      have hnar := Lemma5LocalizedWeightGapTVNarrow F F' ε hε_pos hε_le_one h_std h12 h1'1 h1'2
        hCase2_var hCase2_mean hε_le_1e5 h₁ h₂
      -- hnar : |Δw| - 16 ε³ ≤ 2 TV.  With 48ε³ ≤ |Δw|: 2TV ≥ 32ε³ ⟹ TV ≥ 16ε³ ≥ 16ε⁴ ≥ K ε⁴.
      have hε4_le_ε3 : ε^4 ≤ ε^3 := by nlinarith [pow_pos hε_pos 3, hε_le_one, hε_pos.le]
      have hTV_lb : 16 * ε^3 ≤ Workspace.Types.L1AndTVDistance.TVDistance
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
          (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) := by
        linarith [hnar, hbranch]
      have hKε4_le : K * ε^4 ≤ 16 * ε^4 := by nlinarith [hK_le_16, hε4_nn]
      calc K * ε^4 ≤ 16 * ε^4 := hKε4_le
        _ ≤ 16 * ε^3 := by nlinarith [hε4_le_ε3]
        _ ≤ _ := hTV_lb
  · -- ===== Branch L: comp2 combined-gap, β = σ₁² − 1/2 =====
    push_neg at hbranch
    set β : ℝ := F.comp1.varSq - 1/2 with hβ
    -- post-deconv comp2 vars ∈ [1/2, 3/2]; comp1 vars too.
    have hVF2_le1 : F.comp2.varSq ≤ 1 := h_std.varSq_le_one_F_comp2
    have hVF'1_le1 : F'.comp1.varSq ≤ 1 := h_std.varSq_le_one_F'_comp1
    have hVF'2_le1 : F'.comp2.varSq ≤ 1 := h_std.varSq_le_one_F'_comp2
    have hVF1_le1 : F.comp1.varSq ≤ 1 := h_std.varSq_le_one_F_comp1
    have h₁ : β < min F.comp1.varSq F.comp2.varSq := by
      rw [hβ, lt_min_iff]; constructor
      · linarith
      · linarith [h12]
    have h₂ : β < min F'.comp1.varSq F'.comp2.varSq := by
      rw [hβ, lt_min_iff]; constructor
      · linarith [h1'1]
      · linarith [h1'2]
    refine ⟨β, h₁, h₂, ?_, ?_, ?_⟩
    · rw [hβ]; linarith [hVF1_le1]
    · -- variance floor: all post-deconv vars ≥ 1/2 ≥ ε¹²
      have hε12_le_half : ε^12 ≤ 1/2 := by
        have h12 : ε^12 ≤ ε^1 := pow_le_pow_of_le_one hε_pos.le hε_le_one (by norm_num)
        simp only [pow_one] at h12
        linarith [hε_le_1e5]
      rw [le_min_iff, le_min_iff, le_min_iff]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · show ε^12 ≤ F.comp1.varSq - β; rw [hβ]; linarith [hε12_le_half]
      · show ε^12 ≤ F.comp2.varSq - β; rw [hβ]; linarith [h12, hε12_le_half]
      · show ε^12 ≤ F'.comp1.varSq - β; rw [hβ]; linarith [h1'1, hε12_le_half]
      · show ε^12 ≤ F'.comp2.varSq - β; rw [hβ]; linarith [h1'2, hε12_le_half]
    · -- TV bound via combined-gap on comp2 + weighted triangle split (extracted lemma)
      have hTV := cb_branchL_TV F F' ε β C₀ h₁ h₂ hC₀_pos hCG hβ hε_pos hε_le_one hε_le_1e5
        hε_le_C h_std h12 h1'1 h1'2 hVF1 hVF1_le1 hVF2_le1 hVF'1_le1 hVF'2_le1
        hCase2_var hCase2_mean hbranch
      -- K·ε⁴ ≤ (1/(96C₀))·ε⁴ ≤ ε²/(24C₀) ≤ TV
      have hε2_le1 : ε^2 ≤ 1 := pow_le_one₀ hε_pos.le hε_le_one
      have hε4_le2 : ε^4 ≤ ε^2 := by
        have he : ε^4 = ε^2 * ε^2 := by ring
        rw [he]; nlinarith [hε2_le1, pow_pos hε_pos 2]
      calc K * ε^4 ≤ (1/(96*C₀)) * ε^4 := by
            apply mul_le_mul_of_nonneg_right hK_le_L hε4_nn
        _ ≤ (1/(24*C₀)) * ε^2 := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul,
                div_le_div_iff₀ (by positivity) (by positivity)]
            have h1 : ε^4 * (24*C₀) ≤ ε^2 * (24*C₀) :=
              mul_le_mul_of_nonneg_right hε4_le2 (by positivity)
            have h2 : ε^2 * (24*C₀) ≤ ε^2 * (96*C₀) :=
              mul_le_mul_of_nonneg_left (by linarith [hC₀_pos]) (by positivity)
            linarith [h1, h2]
        _ = ε^2/(24*C₀) := by ring
        _ ≤ _ := hTV

end Workspace.ProofLemmas
