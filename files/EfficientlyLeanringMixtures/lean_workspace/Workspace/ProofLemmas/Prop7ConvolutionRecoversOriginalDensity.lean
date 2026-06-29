import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.MixtureDeconvolution

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.MixtureDeconvolution

/-! ## Auxiliary: density-level convolution of two Gaussians. -/

private noncomputable def gPdf (m s : ℝ) (hs : 0 < s) : GaussianPDF :=
  { mean := m, varSq := s, varSq_pos := hs }

private lemma gPdf_density (m s : ℝ) (hs : 0 < s) (x : ℝ) :
    (gPdf m s hs).density x =
      (1 / Real.sqrt (2 * Real.pi * s)) *
        Real.exp (-(x - m) ^ 2 / (2 * s)) := rfl

/-- Completing the square in `y`. -/
private lemma cts_identity (μ s b x y : ℝ) (hs : 0 < s) (hb : 0 < b) :
    -(y - μ) ^ 2 / (2 * s) + -(x - y) ^ 2 / (2 * b)
      = -(x - μ) ^ 2 / (2 * (s + b))
        + -((s + b) * (y - ((b * μ + s * x) / (s + b))) ^ 2) / (2 * (s * b)) := by
  have hsb : 0 < s + b := by linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hsb_ne : s + b ≠ 0 := ne_of_gt hsb
  field_simp
  ring

/-- Sqrt arithmetic identity. -/
private lemma sqrt_norm_collapse (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    (1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b)) *
        Real.sqrt (2 * Real.pi * (s * b) / (s + b))
      = 1 / Real.sqrt (2 * Real.pi * (s + b)) := by
  have hsb : 0 < s + b := by linarith
  have h2pis : (0 : ℝ) < 2 * Real.pi * s := by positivity
  have h2pib : (0 : ℝ) < 2 * Real.pi * b := by positivity
  have h2pisb : (0 : ℝ) < 2 * Real.pi * (s + b) := by positivity
  have h_sb_quot : (0 : ℝ) < 2 * Real.pi * (s * b) / (s + b) := by positivity
  have hD_pos : 0 < Real.sqrt (2 * Real.pi * (s + b)) := Real.sqrt_pos.mpr h2pisb
  rw [eq_div_iff (ne_of_gt hD_pos)]
  have h_sqrt_combine :
      Real.sqrt (2 * Real.pi * (s * b) / (s + b)) * Real.sqrt (2 * Real.pi * (s + b))
        = Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * b) := by
    rw [← Real.sqrt_mul (le_of_lt h_sb_quot)]
    rw [← Real.sqrt_mul (le_of_lt h2pis)]
    congr 1
    field_simp
  have rearr : 1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * b)) *
      Real.sqrt (2 * Real.pi * (s * b) / (s + b)) * Real.sqrt (2 * Real.pi * (s + b))
    = (1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b)) *
      (Real.sqrt (2 * Real.pi * (s * b) / (s + b)) * Real.sqrt (2 * Real.pi * (s + b))) := by
    ring
  rw [rearr, h_sqrt_combine]
  field_simp

/-- Integrability of the centered Gaussian density shifted by `c`. -/
private lemma integrable_shifted_gaussian (τ c : ℝ) (hτ : 0 < τ) :
    Integrable (fun y : ℝ => Real.exp (-τ * (y - c) ^ 2)) volume := by
  have hint : Integrable (fun y : ℝ => Real.exp (-τ * y ^ 2)) volume :=
    integrable_exp_neg_mul_sq hτ
  have := hint.comp_add_right (-c)
  simpa using this

/-! ## Integrability helpers for gPdf-density products. -/

private lemma gPdf_density_le_peak (m s : ℝ) (hs : 0 < s) (y : ℝ) :
    (gPdf m s hs).density y ≤ 1 / Real.sqrt (2 * Real.pi * s) := by
  rw [gPdf_density]
  have h2pis : (0 : ℝ) < 2 * Real.pi * s := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr h2pis
  have h_inv_pos : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi * s) := by positivity
  have hexp_le_one : Real.exp (-(y - m) ^ 2 / (2 * s)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnum : -(y - m) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (y - m)]
    have hden : 0 < 2 * s := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
  have : (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(y - m) ^ 2 / (2 * s))
       ≤ (1 / Real.sqrt (2 * Real.pi * s)) * 1 := by
    exact mul_le_mul_of_nonneg_left hexp_le_one (le_of_lt h_inv_pos)
  linarith

private lemma gPdf_density_nonneg (m s : ℝ) (hs : 0 < s) (y : ℝ) :
    0 ≤ (gPdf m s hs).density y := by
  rw [gPdf_density]
  have h2pis : (0 : ℝ) < 2 * Real.pi * s := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr h2pis
  have h_inv_pos : (0 : ℝ) < 1 / Real.sqrt (2 * Real.pi * s) := by positivity
  have hexp_pos : 0 < Real.exp (-(y - m) ^ 2 / (2 * s)) := Real.exp_pos _
  positivity

private lemma integrable_gPdf_density (m s : ℝ) (hs : 0 < s) :
    Integrable (fun y => (gPdf m s hs).density y) volume := by
  have hG : (gPdf m s hs).density =
      fun y => ProbabilityTheory.gaussianPDFReal m ⟨s, le_of_lt hs⟩ y := by
    funext y
    exact (gPdf m s hs).density_eq_gaussianPDFReal y
  rw [show (fun y => (gPdf m s hs).density y)
      = fun y => ProbabilityTheory.gaussianPDFReal m ⟨s, le_of_lt hs⟩ y from hG]
  exact ProbabilityTheory.integrable_gaussianPDFReal m ⟨s, le_of_lt hs⟩

/-- The pointwise density-level Gaussian convolution identity. -/
private lemma gaussian_conv_pointwise
    (μ s b : ℝ) (hs : 0 < s) (hb : 0 < b) (x : ℝ) :
    ∫ y, (gPdf μ s hs).density y *
          (gPdf 0 b hb).density (x - y) ∂volume
      = (gPdf μ (s + b) (by linarith)).density x := by
  have hsb : 0 < s + b := by linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hsb_ne : s + b ≠ 0 := ne_of_gt hsb
  have hsb_prod : 0 < s * b := mul_pos hs hb
  simp only [gPdf_density, sub_zero]
  have hreorg : ∀ y : ℝ,
      ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(y - μ) ^ 2 / (2 * s))) *
        ((1 / Real.sqrt (2 * Real.pi * b)) * Real.exp (-(x - y) ^ 2 / (2 * b)))
      = ((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
          Real.exp (-(y - μ) ^ 2 / (2 * s) + -(x - y) ^ 2 / (2 * b)) := by
    intro y
    rw [Real.exp_add]; ring
  rw [show (fun y : ℝ =>
      (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y - μ) ^ 2 / (2 * s))) *
        (1 / Real.sqrt (2 * Real.pi * b) * Real.exp (-(x - y) ^ 2 / (2 * b))))
    = (fun y : ℝ =>
      ((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
          Real.exp (-(y - μ) ^ 2 / (2 * s) + -(x - y) ^ 2 / (2 * b)))
    from funext hreorg]
  set c := (b * μ + s * x) / (s + b) with hc_def
  set τ := (s + b) / (2 * (s * b)) with hτ_def
  have hτ_pos : 0 < τ := by
    apply div_pos hsb
    positivity
  have hcts : ∀ y : ℝ,
      Real.exp (-(y - μ) ^ 2 / (2 * s) + -(x - y) ^ 2 / (2 * b))
      = Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) *
        Real.exp (-τ * (y - c) ^ 2) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    have hid := cts_identity μ s b x y hs hb
    rw [hid]
    have hτ_form : (-τ) * (y - c) ^ 2
        = -((s + b) * (y - c) ^ 2) / (2 * (s * b)) := by
      show (-((s + b) / (2 * (s * b)))) * (y - c) ^ 2
        = -((s + b) * (y - c) ^ 2) / (2 * (s * b))
      have hsb_prod_ne : (2 * (s * b)) ≠ 0 := by positivity
      field_simp
    linarith [hτ_form]
  rw [show (fun y : ℝ =>
      ((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
          Real.exp (-(y - μ) ^ 2 / (2 * s) + -(x - y) ^ 2 / (2 * b)))
    = (fun y : ℝ =>
      ((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
          (Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) *
            Real.exp (-τ * (y - c) ^ 2)))
    from funext (fun y => by rw [hcts y])]
  rw [show (fun y : ℝ =>
      ((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
          (Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) *
            Real.exp (-τ * (y - c) ^ 2)))
    = (fun y : ℝ =>
      (((1 / Real.sqrt (2 * Real.pi * s)) * (1 / Real.sqrt (2 * Real.pi * b))) *
        Real.exp (-(x - μ) ^ 2 / (2 * (s + b)))) *
        Real.exp (-τ * (y - c) ^ 2))
    from funext (fun y => by ring)]
  rw [MeasureTheory.integral_const_mul]
  have htrans :
      ∫ y : ℝ, Real.exp (-τ * (y - c) ^ 2) ∂volume
      = ∫ y : ℝ, Real.exp (-τ * y ^ 2) ∂volume := by
    have hr : (fun y : ℝ => Real.exp (-τ * (y - c) ^ 2))
        = (fun y : ℝ => (fun z => Real.exp (-τ * z ^ 2)) ((-c) + y)) := by
      funext y
      show Real.exp (-τ * (y - c) ^ 2) = Real.exp (-τ * ((-c) + y) ^ 2)
      congr 2
      ring
    rw [hr]
    exact MeasureTheory.integral_add_left_eq_self
      (μ := volume) (f := fun y : ℝ => Real.exp (-τ * y ^ 2)) (-c)
  rw [htrans, integral_gaussian τ]
  have hτval : Real.pi / τ = 2 * Real.pi * (s * b) / (s + b) := by
    show Real.pi / ((s + b) / (2 * (s * b))) = 2 * Real.pi * (s * b) / (s + b)
    have hsb_prod_ne : (2 * (s * b)) ≠ 0 := by positivity
    field_simp
  rw [hτval]
  -- Goal: (1/√(2πs)·1/√(2πb)) · exp(-(x-μ)²/(2(s+b))) · √(2π·sb/(s+b))
  --     = 1/√(2π(s+b)) · exp(-(x-μ)²/(2(s+b)))
  -- (RHS already in explicit form because simp only [gPdf_density] earlier reduced it.)
  have hcollapse := sqrt_norm_collapse s b hs hb
  have hassoc : 1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * b)) *
        Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) *
        Real.sqrt (2 * Real.pi * (s * b) / (s + b))
      = (1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * b)) *
          Real.sqrt (2 * Real.pi * (s * b) / (s + b))) *
        Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) := by ring
  rw [hassoc, hcollapse]

/-! ## Integrability of the head term in the convolution. -/

private lemma integrable_head_term
    (c : ℝ) (G : GaussianPDF) (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    Integrable (fun y : ℝ =>
      c * G.density y * (gPdf 0 β hβ).density (x - y)) volume := by
  have hGsame : G = gPdf G.mean G.varSq G.varSq_pos := by cases G; rfl
  have hrew : (fun y : ℝ => c * G.density y * (gPdf 0 β hβ).density (x - y))
      = (fun y : ℝ => c * ((gPdf G.mean G.varSq G.varSq_pos).density y *
          (gPdf 0 β hβ).density (x - y))) := by
    funext y; rw [← hGsame]; ring
  rw [hrew]
  apply Integrable.const_mul
  have h_int_G : Integrable (fun y => (gPdf G.mean G.varSq G.varSq_pos).density y) volume :=
    integrable_gPdf_density G.mean G.varSq G.varSq_pos
  have h_meas_gβ : AEStronglyMeasurable
      (fun y : ℝ => (gPdf 0 β hβ).density (x - y)) volume := by
    have h_cont : Continuous (fun y : ℝ => (gPdf 0 β hβ).density (x - y)) := by
      unfold gPdf
      simp only [GaussianPDF.density_def]
      fun_prop
    exact h_cont.aestronglyMeasurable
  have h_bdd : ∀ᵐ y ∂volume,
      ‖(gPdf 0 β hβ).density (x - y)‖ ≤ 1 / Real.sqrt (2 * Real.pi * β) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have h1 := gPdf_density_le_peak 0 β hβ (x - y)
    have h2 := gPdf_density_nonneg 0 β hβ (x - y)
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    exact h1
  exact h_int_G.mul_bdd h_meas_gβ h_bdd

/-! ## Linearity of convolveWithGaussian over list-sums. -/

/-- Helper: a list-sum times a constant `y` equals the term-wise list-sum. -/
private lemma sum_mul_eq_sum (l : List (ℝ × GaussianPDF)) (f : (ℝ × GaussianPDF) → ℝ) (c : ℝ) :
    (l.map f).sum * c = (l.map (fun p => f p * c)).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, ih]

/-- A list-sum can be split termwise across convolution. -/
private lemma convolve_list_sum (l : List (ℝ × GaussianPDF)) (β : ℝ)
    (hβ_pos : 0 < β) (x : ℝ) :
    ∫ y, (l.map (fun p => p.1 * p.2.density y)).sum *
        (gPdf 0 β hβ_pos).density (x - y) ∂volume
      = (l.map (fun p => p.1 *
            (gPdf p.2.mean (p.2.varSq + β) (by linarith [p.2.varSq_pos])).density x)).sum := by
  induction l with
  | nil =>
      simp
  | cons hp t ih =>
      simp only [List.map_cons, List.sum_cons]
      have hint_head : Integrable (fun y : ℝ =>
          hp.1 * hp.2.density y * (gPdf 0 β hβ_pos).density (x - y)) volume :=
        integrable_head_term hp.1 hp.2 β hβ_pos x
      -- htail_rew: distribute multiplication of the centered Gaussian into the sum.
      have htail_rew : (fun y : ℝ =>
            (t.map (fun p => p.1 * p.2.density y)).sum *
              (gPdf 0 β hβ_pos).density (x - y))
          = (fun y : ℝ =>
            (t.map (fun p => p.1 * p.2.density y *
              (gPdf 0 β hβ_pos).density (x - y))).sum) := by
        funext y
        exact sum_mul_eq_sum t (fun p => p.1 * p.2.density y)
          ((gPdf 0 β hβ_pos).density (x - y))
      -- Integrability of the tail
      have hint_tail : Integrable (fun y : ℝ =>
          (t.map (fun p => p.1 * p.2.density y)).sum *
            (gPdf 0 β hβ_pos).density (x - y)) volume := by
        rw [htail_rew]
        -- Sum of integrable functions
        clear ih htail_rew hint_head
        induction t with
        | nil =>
            simp only [List.map_nil, List.sum_nil]
            exact integrable_zero _ _ _
        | cons q s ih3 =>
            simp only [List.map_cons, List.sum_cons]
            apply Integrable.add
            · exact integrable_head_term q.1 q.2 β hβ_pos x
            · exact ih3
      have hsplit : (fun y : ℝ =>
          (hp.1 * hp.2.density y + (t.map (fun p => p.1 * p.2.density y)).sum) *
            (gPdf 0 β hβ_pos).density (x - y))
        = (fun y : ℝ =>
            hp.1 * hp.2.density y * (gPdf 0 β hβ_pos).density (x - y)
            + (t.map (fun p => p.1 * p.2.density y)).sum *
                (gPdf 0 β hβ_pos).density (x - y)) := by
        funext y; ring
      rw [hsplit, integral_add hint_head hint_tail, ih]
      have hhead_eq :
          ∫ y, hp.1 * hp.2.density y * (gPdf 0 β hβ_pos).density (x - y) ∂volume
          = hp.1 * (gPdf hp.2.mean (hp.2.varSq + β) (by linarith [hp.2.varSq_pos])).density x := by
        have hassoc : ∀ y : ℝ,
            hp.1 * hp.2.density y * (gPdf 0 β hβ_pos).density (x - y)
          = hp.1 * (hp.2.density y * (gPdf 0 β hβ_pos).density (x - y)) := by
          intro y; ring
        rw [show (fun y => hp.1 * hp.2.density y * (gPdf 0 β hβ_pos).density (x - y))
            = (fun y => hp.1 * (hp.2.density y * (gPdf 0 β hβ_pos).density (x - y)))
            from funext hassoc]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        have key := gaussian_conv_pointwise hp.2.mean hp.2.varSq β
          hp.2.varSq_pos hβ_pos x
        have hgp : hp.2 = gPdf hp.2.mean hp.2.varSq hp.2.varSq_pos := by
          cases hp.2
          rfl
        rw [hgp]
        exact key
      rw [hhead_eq]

/-! ## Main theorem proof. -/

/--
**Convolution recovers (shifted) signed-Gaussian densities.**
-/
theorem Prop7ConvolutionRecoversOriginalDensity :
    ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
      (α : ℝ)
      (h_α_lt : ∀ p ∈ S.components, α < p.snd.varSq)
      (β : ℝ) (hβ_pos : 0 < β) (hαβ_pos : 0 < α + β),
        let S_α := Workspace.Types.MixtureDeconvolution.deconvSigned S α h_α_lt
        let S' : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination :=
          ⟨S.components.attach.map
            (fun p =>
              (p.val.1,
                ({ mean := p.val.2.mean,
                   varSq := p.val.2.varSq + (β - α),
                   varSq_pos := by
                     have h1 : α < p.val.2.varSq := h_α_lt p.val p.property
                     linarith } :
                  Workspace.Types.GaussianPDF.GaussianPDF)))⟩
        ∀ x : ℝ,
          Workspace.Types.GaussianConvolution.convolveWithGaussian S_α.density β hβ_pos x
            = S'.density x := by
  intro S α h_α_lt β hβ_pos hαβ_pos S_α S' x
  -- Define the deconvolved-components list `l`.
  set l : List (ℝ × GaussianPDF) :=
    S.components.attach.map (fun p =>
      (p.val.1, Workspace.Types.MixtureDeconvolution.shiftGaussian p.val.2 α
        (h_α_lt p.val p.property)))
    with hl_def
  -- LHS: convolveWithGaussian S_α.density β x = ∫ y, S_α.density(y) * g₀,β(x-y) dy.
  -- S_α.density(y) = sum over l of (p.1 * p.2.density y).
  have hLHS :
      Workspace.Types.GaussianConvolution.convolveWithGaussian
          (Workspace.Types.MixtureDeconvolution.deconvSigned S α h_α_lt).density β hβ_pos x
      = ∫ y, (l.map (fun p => p.1 * p.2.density y)).sum *
              (gPdf 0 β hβ_pos).density (x - y) ∂volume := by
    show ∫ y,
        (Workspace.Types.MixtureDeconvolution.deconvSigned S α h_α_lt).density y *
          _ ∂volume = _
    congr 1
  -- Apply convolve_list_sum to convert the LHS into a list sum.
  rw [hLHS, convolve_list_sum l β hβ_pos x]
  -- Goal now: (List.map (fun p => p.1 * (gPdf p.2.mean (p.2.varSq + β) _).density x) l).sum = S'.density x
  -- Unfold S'.density: it's a list-map-sum over S.components.attach.
  show _ = (S'.components.map (fun p => p.1 * p.2.density x)).sum
  rw [hl_def]
  simp only [List.map_map]
  -- Both sides are List.map _ S.components.attach. Match pointwise.
  congr 1
  -- Unfold S'.components by `show`.
  show List.map _ S.components.attach = List.map _ (List.map _ S.components.attach)
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  show _ * _ = _ * _
  congr 1
  simp only [GaussianPDF.density_eq, shiftGaussian]
  -- Two GaussianPDFs: same mean, varSq differ by associativity.
  have h_var : p.val.2.varSq - α + β = p.val.2.varSq + (β - α) := by ring
  simp only [gPdf]
  rw [h_var]

end Workspace.ProofLemmas
