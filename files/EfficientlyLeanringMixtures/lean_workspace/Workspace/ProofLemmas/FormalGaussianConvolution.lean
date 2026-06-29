import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution

/-- A single Gaussian whose variance has been increased by `t > 0`. -/
noncomputable def shiftVarG (G : GaussianPDF) (t : ℝ) (ht : 0 < t) : GaussianPDF :=
  { mean := G.mean, varSq := G.varSq + t, varSq_pos := by have := G.varSq_pos; linarith }

/-- The heat-flow (variance shift) applied to a whole signed combination. -/
noncomputable def heatShift (S : SignedGaussianCombination) (t : ℝ) (ht : 0 < t) :
    SignedGaussianCombination :=
  ⟨S.components.map (fun p => (p.1, shiftVarG p.2 t ht))⟩

/-! ## Reusable pieces (mirroring Prop7ConvolutionRecoversOriginalDensity). -/

private noncomputable def gPdf (m s : ℝ) (hs : 0 < s) : GaussianPDF :=
  { mean := m, varSq := s, varSq_pos := hs }

private lemma gPdf_density (m s : ℝ) (hs : 0 < s) (x : ℝ) :
    (gPdf m s hs).density x =
      (1 / Real.sqrt (2 * Real.pi * s)) *
        Real.exp (-(x - m) ^ 2 / (2 * s)) := rfl

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
  have hcollapse := sqrt_norm_collapse s b hs hb
  have hassoc : 1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * b)) *
        Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) *
        Real.sqrt (2 * Real.pi * (s * b) / (s + b))
      = (1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * b)) *
          Real.sqrt (2 * Real.pi * (s * b) / (s + b))) *
        Real.exp (-(x - μ) ^ 2 / (2 * (s + b))) := by ring
  rw [hassoc, hcollapse]

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

private lemma sum_mul_eq_sum (l : List (ℝ × GaussianPDF)) (f : (ℝ × GaussianPDF) → ℝ) (c : ℝ) :
    (l.map f).sum * c = (l.map (fun p => f p * c)).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, ih]

/-- A list-sum can be split termwise across convolution. (Direct, β-shift form.) -/
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
      have htail_rew : (fun y : ℝ =>
            (t.map (fun p => p.1 * p.2.density y)).sum *
              (gPdf 0 β hβ_pos).density (x - y))
          = (fun y : ℝ =>
            (t.map (fun p => p.1 * p.2.density y *
              (gPdf 0 β hβ_pos).density (x - y))).sum) := by
        funext y
        exact sum_mul_eq_sum t (fun p => p.1 * p.2.density y)
          ((gPdf 0 β hβ_pos).density (x - y))
      have hint_tail : Integrable (fun y : ℝ =>
          (t.map (fun p => p.1 * p.2.density y)).sum *
            (gPdf 0 β hβ_pos).density (x - y)) volume := by
        rw [htail_rew]
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

/-! ## Main heat-semigroup variance-shift identity. -/

/--
**Heat semigroup shifts variance.** For a signed Gaussian combination `S` and a
heat-flow time `t > 0`, convolving `S.density` with the centered Gaussian `N(0,t)`
yields exactly the combination obtained by increasing every component's variance
by `t`. This is the well-defined heat-flow operator `H_t` on positive-variance
Gaussian combinations.
-/
theorem heatShift_density_eq_convolve
    (S : SignedGaussianCombination) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    convolveWithGaussian S.density t ht x = (heatShift S t ht).density x := by
  have hLHS :
      convolveWithGaussian S.density t ht x
      = ∫ y, (S.components.map (fun p => p.1 * p.2.density y)).sum *
              (gPdf 0 t ht).density (x - y) ∂volume := by
    show ∫ y, S.density y * _ ∂volume = _
    rfl
  rw [hLHS, convolve_list_sum S.components t ht x]
  show _ = ((heatShift S t ht).components.map (fun p => p.1 * p.2.density x)).sum
  unfold heatShift
  simp only [List.map_map]
  congr 1

/-- The heat-flow shift at time `t` then `s` equals the shift at time `t + s`
    (semigroup law on the variance-shift representation). -/
theorem heatShift_comp (S : SignedGaussianCombination) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    heatShift (heatShift S t ht) s hs
      = heatShift S (t + s) (by linarith) := by
  unfold heatShift
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  show (p.1, shiftVarG (shiftVarG p.2 t ht) s hs) = (p.1, shiftVarG p.2 (t + s) (by linarith))
  congr 1
  unfold shiftVarG
  congr 1
  ring

/-- The heat semigroup law at the level of densities: `H_s (H_t S) = H_{t+s} S`.
    Convolving with `N(0,t)` then `N(0,s)` equals convolving with `N(0,t+s)`,
    on positive-variance Gaussian combinations. This is exactly the heat-semigroup
    property `e^{sΔ} e^{tΔ} = e^{(t+s)Δ}` for the operator under which zero count
    is monotone. -/
theorem heat_semigroup_density
    (S : SignedGaussianCombination) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x : ℝ) :
    convolveWithGaussian (heatShift S t ht).density s hs x
      = convolveWithGaussian S.density (t + s) (by linarith) x := by
  rw [heatShift_density_eq_convolve]
  rw [heatShift_density_eq_convolve]
  rw [heatShift_comp S t s ht hs]

end Workspace.ProofLemmas
