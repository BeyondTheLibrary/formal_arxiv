import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Lemma35L1NormGeSetIntegral

set_option maxHeartbeats 8000000

open Workspace.Types.GaussianPDF
open Workspace.Types.L1AndTVDistance
open Real MeasureTheory

namespace Workspace.ProofLemmas

/-! ## Variance-as-parameter density function and its derivative. -/

/-- `Dfun u v = N(0, v, u)` viewed as a function of the variance `v` (point `u` fixed). -/
private noncomputable def Dfun (u : ℝ) : ℝ → ℝ :=
  fun v => (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt v)⁻¹ * Real.exp (-u^2/(2*v))

private lemma density_eq_Dfun (u v : ℝ) (hv : 0 < v) :
    (⟨0, v, hv⟩ : GaussianPDF).density u = Dfun u v := by
  rw [GaussianPDF.density_eq]
  simp only [Dfun]
  rw [show (2 * Real.pi * v) = (2*Real.pi) * v by ring, Real.sqrt_mul (by positivity)]
  rw [show (u - 0)^2 = u^2 by ring]
  field_simp

private lemma hasDerivAt_Dfun (u v : ℝ) (hv : 0 < v) :
    HasDerivAt (Dfun u) (Dfun u v * (u^2 - v)/(2*v^2)) v := by
  have hv' : v ≠ 0 := ne_of_gt hv
  have hsv : Real.sqrt v ≠ 0 := by positivity
  have h1 : HasDerivAt (fun v => (Real.sqrt v)⁻¹) (-(1/(2*v*Real.sqrt v))) v := by
    have hs : HasDerivAt Real.sqrt (1/(2*Real.sqrt v)) v := Real.hasDerivAt_sqrt hv'
    have := hs.inv hsv
    convert this using 1
    rw [Real.sq_sqrt hv.le]
    field_simp
  have h2 : HasDerivAt (fun v => Real.exp (-u^2/(2*v))) (Real.exp (-u^2/(2*v)) * (u^2/(2*v^2))) v := by
    have hinner : HasDerivAt (fun v => -u^2/(2*v)) (u^2/(2*v^2)) v := by
      have : HasDerivAt (fun v => (2*v)) 2 v := by simpa using (hasDerivAt_id v).const_mul 2
      have hd := (this.inv (by positivity : (2*v) ≠ 0))
      have hd2 := hd.const_mul (-u^2)
      convert hd2 using 1
      field_simp
    exact (Real.hasDerivAt_exp _).comp v hinner
  have hprod := (h1.mul h2).const_mul (1 / Real.sqrt (2 * Real.pi))
  convert hprod using 1 with x
  · funext y; simp only [Dfun, Pi.mul_apply]; ring
  · simp only [Dfun]
    have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
    rw [show (1 / Real.sqrt (2 * Real.pi) * (Real.sqrt v)⁻¹ * Real.exp (-u^2/(2*v))) * (u^2 - v)/(2*v^2)
          = Real.exp (-u^2/(2*v)) * (1 / Real.sqrt (2 * Real.pi) * (Real.sqrt v)⁻¹ * (u^2 - v)/(2*v^2)) by ring,
        show (1 / Real.sqrt (2 * Real.pi) *
              (-(1 / (2 * v * Real.sqrt v)) * Real.exp (-u^2/(2*v))
               + (Real.sqrt v)⁻¹ * (Real.exp (-u^2/(2*v)) * (u^2/(2*v^2)))))
          = Real.exp (-u^2/(2*v)) * (1 / Real.sqrt (2 * Real.pi) *
              (-(1 / (2 * v * Real.sqrt v)) + (Real.sqrt v)⁻¹ * (u^2/(2*v^2)))) by ring]
    congr 1
    field_simp
    nlinarith [hsq, Real.sqrt_nonneg v, hv]

private lemma differentiableAt_Dfun (u v : ℝ) (hv : 0 < v) : DifferentiableAt ℝ (Dfun u) v :=
  (hasDerivAt_Dfun u v hv).differentiableAt

private lemma continuous_Dfun (u : ℝ) : ContinuousOn (Dfun u) (Set.Icc (1/2 : ℝ) (3/2)) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn)
    intro x hx; simp only [Set.mem_Icc] at hx
    have : (0:ℝ) < x := by linarith [hx.1]
    positivity
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_const.mul continuous_id).continuousOn
    · intro x hx; simp only [Set.mem_Icc] at hx
      have : (0:ℝ) < x := by linarith [hx.1]
      positivity

private lemma deriv_Dfun_ge (u x : ℝ) (hx : x ∈ Set.Ioo (1/2 : ℝ) (3/2)) (hu : 4 ≤ u^2) (hu_hi : u^2 ≤ 16) :
    (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) * (5/9)
      ≤ deriv (Dfun u) x := by
  simp only [Set.mem_Ioo] at hx
  have hx_pos : (0:ℝ) < x := by linarith [hx.1]
  rw [(hasDerivAt_Dfun u x hx_pos).deriv]
  have hsqrt_mono : (Real.sqrt (3/2))⁻¹ ≤ (Real.sqrt x)⁻¹ := by
    apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt; linarith [hx.2]
  have hexp_ge : Real.exp (-16) ≤ Real.exp (-u^2/(2*x)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hu_hi, hx.1, hx.2]
  have hfrac_ge : (5/9 : ℝ) ≤ (u^2 - x)/(2*x^2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hu, hx.1, hx.2, sq_nonneg x]
  have hc0_pos : (0:ℝ) < 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_pos : (0:ℝ) < (Real.sqrt (3/2))⁻¹ := by positivity
  have hexp16_pos : (0:ℝ) < Real.exp (-16) := Real.exp_pos _
  have hDfun_ge : (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) ≤ Dfun u x := by
    simp only [Dfun]
    apply mul_le_mul
    apply mul_le_mul (le_refl _) hsqrt_mono (le_of_lt hsqrt_pos) (le_of_lt hc0_pos)
    · exact hexp_ge
    · exact le_of_lt hexp16_pos
    · positivity
  have hC_pos : (0:ℝ) ≤ (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) := by positivity
  calc (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) * (5/9)
      ≤ Dfun u x * ((u^2 - x)/(2*x^2)) := by
        apply mul_le_mul hDfun_ge hfrac_ge (by norm_num) (le_trans hC_pos hDfun_ge)
    _ = Dfun u x * (u^2 - x)/(2*x^2) := by ring

/-- The positive variance-piece constant. -/
private noncomputable def cV : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) * (5/9)

private lemma cV_pos : 0 < cV := by
  unfold cV; positivity

/-- The density `N(0,·,u)` is monotone in the variance when `u^2 ≥ 4 ≥ varSq`:
    `N(0,va,u) ≤ N(0,vb,u)` for `va ≤ vb`. (Derivative-in-variance nonneg.) -/
private lemma variance_piece_nonneg (u va vb : ℝ)
    (hva : 0 < va) (hvb : 0 < vb)
    (hva_lo : 1/2 ≤ va) (hvb_hi : vb ≤ 3/2) (hab : va ≤ vb)
    (hu : 4 ≤ u^2) :
    (⟨0, va, hva⟩ : GaussianPDF).density u ≤ (⟨0, vb, hvb⟩ : GaussianPDF).density u := by
  rw [density_eq_Dfun u vb hvb, density_eq_Dfun u va hva]
  have hva_mem : va ∈ Set.Icc (1/2 : ℝ) (3/2) := ⟨hva_lo, by linarith⟩
  have hvb_mem : vb ∈ Set.Icc (1/2 : ℝ) (3/2) := ⟨by linarith, hvb_hi⟩
  have hdiff : DifferentiableOn ℝ (Dfun u) (interior (Set.Icc (1/2 : ℝ) (3/2))) := by
    rw [interior_Icc]
    intro x hx; simp only [Set.mem_Ioo] at hx
    exact (differentiableAt_Dfun u x (by linarith [hx.1])).differentiableWithinAt
  have hderiv_nn : ∀ x ∈ interior (Set.Icc (1/2 : ℝ) (3/2)), (0:ℝ) ≤ deriv (Dfun u) x := by
    intro x hx; rw [interior_Icc] at hx; simp only [Set.mem_Ioo] at hx
    have hx_pos : (0:ℝ) < x := by linarith [hx.1]
    rw [(hasDerivAt_Dfun u x hx_pos).deriv]
    have hDfun_pos : 0 < Dfun u x := by simp only [Dfun]; positivity
    have hfrac_nn : (0:ℝ) ≤ (u^2 - x)/(2*x^2) := by
      apply div_nonneg (by nlinarith [hu, hx.2]) (by positivity)
    have : 0 ≤ Dfun u x * ((u^2 - x)/(2*x^2)) := mul_nonneg hDfun_pos.le hfrac_nn
    calc (0:ℝ) ≤ Dfun u x * ((u^2 - x)/(2*x^2)) := this
      _ = Dfun u x * (u^2 - x)/(2*x^2) := by ring
  have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (1/2 : ℝ) (3/2))
    (continuous_Dfun u) hdiff hderiv_nn va hva_mem vb hvb_mem hab
  linarith [this]

/-- Variance-piece pointwise lower bound for `u^2 ∈ [4,16]`, `1/2 ≤ va ≤ vb ≤ 3/2`. -/
private lemma variance_piece_lower (u va vb : ℝ)
    (hva : 0 < va) (hvb : 0 < vb)
    (hva_lo : 1/2 ≤ va) (hvb_hi : vb ≤ 3/2) (hab : va ≤ vb)
    (hu : 4 ≤ u^2) (hu_hi : u^2 ≤ 16) :
    cV * (vb - va)
      ≤ (⟨0, vb, hvb⟩ : GaussianPDF).density u - (⟨0, va, hva⟩ : GaussianPDF).density u := by
  rw [density_eq_Dfun u vb hvb, density_eq_Dfun u va hva]
  have hva_mem : va ∈ Set.Icc (1/2 : ℝ) (3/2) := ⟨hva_lo, by linarith⟩
  have hvb_mem : vb ∈ Set.Icc (1/2 : ℝ) (3/2) := ⟨by linarith, hvb_hi⟩
  have hdiff : DifferentiableOn ℝ (Dfun u) (interior (Set.Icc (1/2 : ℝ) (3/2))) := by
    rw [interior_Icc]
    intro x hx; simp only [Set.mem_Ioo] at hx
    exact (differentiableAt_Dfun u x (by linarith [hx.1])).differentiableWithinAt
  have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (1/2 : ℝ) (3/2))
    (continuous_Dfun u) hdiff
    (fun x hx => deriv_Dfun_ge u x (by rwa [interior_Icc] at hx) hu hu_hi)
    va hva_mem vb hvb_mem hab
  rw [show cV = (1 / Real.sqrt (2 * Real.pi)) * (Real.sqrt (3/2))⁻¹ * Real.exp (-16) * (5/9) from rfl]
  linarith [this]

/-! ## Mean-piece primitive. -/

private lemma one_sub_exp_ge (t : ℝ) (ht : 0 ≤ t) :
    (1 - Real.exp (-1)) * min t 1 ≤ 1 - Real.exp (-t) := by
  rcases le_or_gt t 1 with h | h
  · rw [min_eq_left h]
    have hconv : Real.exp (-t) ≤ 1 + t * (Real.exp (-1) - 1) := by
      have hcvx := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
        (by linarith : (0:ℝ) ≤ 1 - t) (by linarith : (0:ℝ) ≤ t) (by ring)
      simp only [smul_eq_mul, Real.exp_zero, mul_one, mul_neg, mul_zero, zero_add] at hcvx
      nlinarith [hcvx]
    nlinarith [hconv]
  · rw [min_eq_right (le_of_lt h)]
    have hmono : Real.exp (-t) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr; linarith
    linarith [hmono]

/-! ## Integrability. -/

private lemma density_integrable (m v : ℝ) (hv : 0 < v) :
    Integrable (⟨m, v, hv⟩ : GaussianPDF).density volume := by
  have heq : (⟨m, v, hv⟩ : GaussianPDF).density
      = ProbabilityTheory.gaussianPDFReal m ⟨v, hv.le⟩ := by
    ext x; exact GaussianPDF.density_eq_gaussianPDFReal _ x
  rw [heq]; exact ProbabilityTheory.integrable_gaussianPDFReal m ⟨v, hv.le⟩

/-! ## The WLOG-reduced core.

Compare `N(0, vb)` and `N(-δ, va)` with `δ ≥ 0`, `1/2 ≤ va ≤ vb ≤ 3/2`. -/

/-- On the band `[2,3]` both perturbations push the same way; the mean-piece is nonneg
and the variance-piece is nonneg, so `g(x) ≥ 0` and dominates each piece. -/
private lemma core_mean_bound (δ va vb : ℝ)
    (hva : 0 < va) (hvb : 0 < vb)
    (hva_lo : 1/2 ≤ va) (hvb_hi : vb ≤ 3/2) (hab : va ≤ vb) (hδ : 0 ≤ δ) :
    (1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9) * (1 - Real.exp (-1)) * min δ 1
      ≤ L1Norm (fun x =>
          (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) := by
  set g : ℝ → ℝ := fun x => (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x with hg
  set S : Set ℝ := Set.Icc (2:ℝ) 3 with hS
  have hS_meas : MeasurableSet S := measurableSet_Icc
  have hg_int : Integrable g volume := (density_integrable 0 vb hvb).sub (density_integrable (-δ) va hva)
  -- pointwise: on S, g x ≥ K_m·min δ 1, with the mean piece bounding it from below.
  set Km : ℝ := (1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9) * (1 - Real.exp (-1)) with hKm
  have h_pointwise : ∀ x ∈ S, Km * min δ 1 ≤ g x := by
    intro x hx
    rcases hx with ⟨hx2, hx3⟩
    -- decompose g = M + V with M (mean piece) and V (variance piece), both ≥ 0 on S.
    set pf : ℝ := 1 / Real.sqrt (2 * Real.pi * vb) with hpf
    have hpf_pos : 0 < pf := by rw [hpf]; positivity
    -- explicit densities
    have hN0vb : (⟨0, vb, hvb⟩ : GaussianPDF).density x = pf * Real.exp (-x^2/(2*vb)) := by
      rw [GaussianPDF.density_eq, hpf]; congr 1; ring_nf
    have hNδvb : (⟨-δ, vb, hvb⟩ : GaussianPDF).density x = pf * Real.exp (-(x+δ)^2/(2*vb)) := by
      rw [GaussianPDF.density_eq, hpf]; congr 1; ring_nf
    -- Variance piece V = N(-δ,vb,x) − N(-δ,va,x) ≥ 0 (larger variance, point far from center).
    have hV_nonneg : 0 ≤ (⟨-δ, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x := by
      -- translate to mean 0 at point u = x+δ; use variance_piece_lower ≥ 0.
      have htrans_vb : (⟨-δ, vb, hvb⟩ : GaussianPDF).density x = (⟨0, vb, hvb⟩ : GaussianPDF).density (x+δ) := by
        rw [GaussianPDF.density_eq, GaussianPDF.density_eq]; congr 2; ring
      have htrans_va : (⟨-δ, va, hva⟩ : GaussianPDF).density x = (⟨0, va, hva⟩ : GaussianPDF).density (x+δ) := by
        rw [GaussianPDF.density_eq, GaussianPDF.density_eq]; congr 2; ring
      rw [htrans_vb, htrans_va]
      have hu : 4 ≤ (x+δ)^2 := by nlinarith [hx2, hδ]
      linarith [variance_piece_nonneg (x+δ) va vb hva hvb hva_lo hvb_hi hab hu]
    -- Mean piece M = N(0,vb,x) − N(-δ,vb,x).
    have hM_lower : Km * min δ 1 ≤
        (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, vb, hvb⟩ : GaussianPDF).density x := by
      rw [hN0vb, hNδvb]
      -- pf·exp(-x²/(2vb)) − pf·exp(-(x+δ)²/(2vb)) = pf·exp(-x²/(2vb))·(1 − exp(-(2δx+δ²)/(2vb)))
      have hfac : pf * Real.exp (-x^2/(2*vb)) - pf * Real.exp (-(x+δ)^2/(2*vb))
          = pf * Real.exp (-x^2/(2*vb)) * (1 - Real.exp (-((2*δ*x+δ^2)/(2*vb)))) := by
        rw [show -(x+δ)^2/(2*vb) = (-x^2/(2*vb)) + (-((2*δ*x+δ^2)/(2*vb))) by ring, Real.exp_add]
        ring
      rw [hfac]
      set t : ℝ := (2*δ*x+δ^2)/(2*vb) with ht
      have ht_nn : 0 ≤ t := by rw [ht]; apply div_nonneg; nlinarith [hδ, hx2]; linarith
      have ht_ge : δ ≤ t := by
        rw [ht, le_div_iff₀ (by linarith : (0:ℝ) < 2*vb)]
        nlinarith [hδ, hx2, hvb_hi]
      have hmin_mono : min δ 1 ≤ min t 1 := min_le_min ht_ge (le_refl 1)
      have h1mexp : (1 - Real.exp (-1)) * min t 1 ≤ 1 - Real.exp (-t) := one_sub_exp_ge t ht_nn
      -- prefactor pf ≥ 1/√(2π·3/2), exp(-x²/(2vb)) ≥ exp(-9)
      have hpf_ge : 1 / Real.sqrt (2 * Real.pi * (3/2)) ≤ pf := by
        rw [hpf]; apply one_div_le_one_div_of_le (by positivity)
        apply Real.sqrt_le_sqrt
        have : (0:ℝ) < Real.pi := Real.pi_pos
        nlinarith [hvb_hi, this]
      have hexp_ge : Real.exp (-9) ≤ Real.exp (-x^2/(2*vb)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by linarith : (0:ℝ) < 2*vb)]
        nlinarith [hx2, hx3, hva_lo]
      -- combine
      have hbody_ge : (1 - Real.exp (-1)) * min δ 1 ≤ 1 - Real.exp (-t) := by
        calc (1 - Real.exp (-1)) * min δ 1
            ≤ (1 - Real.exp (-1)) * min t 1 := by
              apply mul_le_mul_of_nonneg_left hmin_mono
              have : Real.exp (-1) ≤ 1 := by
                have := Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0); linarith
              linarith
          _ ≤ 1 - Real.exp (-t) := h1mexp
      have hpe_pos : 0 < pf * Real.exp (-x^2/(2*vb)) := by positivity
      have hKm_eq : Km = (1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9) * (1 - Real.exp (-1)) := by
        rw [hKm]
      rw [hKm_eq]
      calc (1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9) * (1 - Real.exp (-1)) * min δ 1
          = ((1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9)) * ((1 - Real.exp (-1)) * min δ 1) := by ring
        _ ≤ (pf * Real.exp (-x^2/(2*vb))) * (1 - Real.exp (-t)) := by
              apply mul_le_mul
              · apply mul_le_mul hpf_ge hexp_ge (by positivity) (le_of_lt hpf_pos)
              · exact hbody_ge
              · apply mul_nonneg
                · have : Real.exp (-1) ≤ 1 := by
                    have := Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0); linarith
                  linarith
                · exact le_min hδ (by norm_num)
              · positivity
    -- g = M + V, V ≥ 0 ⟹ g ≥ M ≥ Km·min δ 1.
    have hg_eq : g x = ((⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, vb, hvb⟩ : GaussianPDF).density x)
        + ((⟨-δ, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) := by
      rw [hg]; ring
    rw [hg_eq]; linarith [hM_lower, hV_nonneg]
  have hL1_ge : (∫ x in S, |g x| ∂volume) ≤ L1Norm g :=
    Lemma35L1NormGeSetIntegral g S hS_meas hg_int
  have hKm_nn : 0 ≤ Km := by
    rw [hKm]
    apply mul_nonneg (by positivity)
    have : Real.exp (-1) ≤ 1 := by
      have := Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0); linarith
    linarith
  have hKm_min_nn : 0 ≤ Km * min δ 1 := mul_nonneg hKm_nn (le_min hδ (by norm_num))
  have h_abs_ge : ∀ x ∈ S, Km * min δ 1 ≤ |g x| := by
    intro x hx
    have := h_pointwise x hx
    rw [abs_of_nonneg (le_trans hKm_min_nn this)]; exact this
  have hg_abs_int_on : IntegrableOn (fun x => |g x|) S volume := (hg_int.abs).integrableOn
  have hS_vol_ne_top : volume S ≠ ⊤ := by rw [hS, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h_const_le : (∫ _ in S, Km * min δ 1 ∂volume) ≤ ∫ x in S, |g x| ∂volume := by
    apply MeasureTheory.setIntegral_mono_on (MeasureTheory.integrableOn_const hS_vol_ne_top)
      hg_abs_int_on hS_meas h_abs_ge
  have hS_vol_real : (volume.real S) = 1 := by
    rw [hS]; simp only [Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num
  have h_const_eq : (∫ _ in S, Km * min δ 1 ∂volume) = Km * min δ 1 := by
    rw [MeasureTheory.setIntegral_const, hS_vol_real]; ring
  rw [h_const_eq] at h_const_le
  rw [hKm] at h_const_le
  linarith [hL1_ge, h_const_le]

/-- Core variance bound: for `δ ∈ [0,1]`, `L1(g) ≥ cV·(vb−va)`.
    Uses band `[2,3]`, drops the nonneg mean-piece, keeps the variance-piece. -/
private lemma core_var_bound (δ va vb : ℝ)
    (hva : 0 < va) (hvb : 0 < vb)
    (hva_lo : 1/2 ≤ va) (hvb_hi : vb ≤ 3/2) (hab : va ≤ vb) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    cV * (vb - va)
      ≤ L1Norm (fun x =>
          (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) := by
  set g : ℝ → ℝ := fun x => (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x with hg
  set S : Set ℝ := Set.Icc (2:ℝ) 3 with hS
  have hS_meas : MeasurableSet S := measurableSet_Icc
  have hg_int : Integrable g volume := (density_integrable 0 vb hvb).sub (density_integrable (-δ) va hva)
  have hcV_gap_nn : 0 ≤ cV * (vb - va) := mul_nonneg cV_pos.le (by linarith)
  have h_pointwise : ∀ x ∈ S, cV * (vb - va) ≤ g x := by
    intro x hx
    rcases hx with ⟨hx2, hx3⟩
    -- mean piece ≥ 0
    have hM_nn : 0 ≤ (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, vb, hvb⟩ : GaussianPDF).density x := by
      rw [GaussianPDF.density_eq, GaussianPDF.density_eq]
      have hpf_pos : (0:ℝ) < 1 / Real.sqrt (2 * Real.pi * vb) := by positivity
      have hexp_le : Real.exp (-(x - 0)^2/(2*vb)) ≥ Real.exp (-(x - -δ)^2/(2*vb)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_div, neg_le_neg_iff]
        gcongr
        · linarith
        · nlinarith [hx2, hδ]
      have : (1 / Real.sqrt (2 * Real.pi * vb)) * Real.exp (-(x - -δ)^2/(2*vb))
          ≤ (1 / Real.sqrt (2 * Real.pi * vb)) * Real.exp (-(x - 0)^2/(2*vb)) :=
        mul_le_mul_of_nonneg_left hexp_le hpf_pos.le
      linarith
    -- variance piece ≥ cV·(vb−va) via translation + variance_piece_lower at u = x+δ
    have hV_lower : cV * (vb - va) ≤
        (⟨-δ, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x := by
      have htrans_vb : (⟨-δ, vb, hvb⟩ : GaussianPDF).density x = (⟨0, vb, hvb⟩ : GaussianPDF).density (x+δ) := by
        rw [GaussianPDF.density_eq, GaussianPDF.density_eq]; congr 2; ring
      have htrans_va : (⟨-δ, va, hva⟩ : GaussianPDF).density x = (⟨0, va, hva⟩ : GaussianPDF).density (x+δ) := by
        rw [GaussianPDF.density_eq, GaussianPDF.density_eq]; congr 2; ring
      rw [htrans_vb, htrans_va]
      have hu : 4 ≤ (x+δ)^2 := by nlinarith [hx2, hδ]
      have hu_hi : (x+δ)^2 ≤ 16 := by nlinarith [hx3, hδ1, hδ]
      exact variance_piece_lower (x+δ) va vb hva hvb hva_lo hvb_hi hab hu hu_hi
    have hg_eq : g x = ((⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, vb, hvb⟩ : GaussianPDF).density x)
        + ((⟨-δ, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) := by
      rw [hg]; ring
    rw [hg_eq]; linarith [hM_nn, hV_lower]
  have hL1_ge : (∫ x in S, |g x| ∂volume) ≤ L1Norm g :=
    Lemma35L1NormGeSetIntegral g S hS_meas hg_int
  have h_abs_ge : ∀ x ∈ S, cV * (vb - va) ≤ |g x| := by
    intro x hx
    have := h_pointwise x hx
    rw [abs_of_nonneg (le_trans hcV_gap_nn this)]; exact this
  have hg_abs_int_on : IntegrableOn (fun x => |g x|) S volume := (hg_int.abs).integrableOn
  have hS_vol_ne_top : volume S ≠ ⊤ := by rw [hS, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h_const_le : (∫ _ in S, cV * (vb - va) ∂volume) ≤ ∫ x in S, |g x| ∂volume := by
    apply MeasureTheory.setIntegral_mono_on (MeasureTheory.integrableOn_const hS_vol_ne_top)
      hg_abs_int_on hS_meas h_abs_ge
  have hS_vol_real : (volume.real S) = 1 := by
    rw [hS]; simp only [Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num
  have h_const_eq : (∫ _ in S, cV * (vb - va) ∂volume) = cV * (vb - va) := by
    rw [MeasureTheory.setIntegral_const, hS_vol_real]; ring
  rw [h_const_eq] at h_const_le
  linarith [hL1_ge, h_const_le]

/-! ## L1Norm invariances. -/

private lemma l1_swap (a b va vb : ℝ) (hva : 0 < va) (hvb : 0 < vb) :
    L1Norm (fun x => (⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x)
    = L1Norm (fun x => (⟨b, vb, hvb⟩ : GaussianPDF).density x - (⟨a, va, hva⟩ : GaussianPDF).density x) := by
  simp only [L1Norm_def]; congr 1; ext x; rw [abs_sub_comm]

private lemma l1_translation (a b va vb c : ℝ) (hva : 0 < va) (hvb : 0 < vb) :
    L1Norm (fun x => (⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x)
    = L1Norm (fun x => (⟨a - c, va, hva⟩ : GaussianPDF).density x - (⟨b - c, vb, hvb⟩ : GaussianPDF).density x) := by
  simp only [L1Norm_def]
  have key : ∀ x : ℝ, |(⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x|
      = (fun y => |(⟨a - c, va, hva⟩ : GaussianPDF).density y - (⟨b - c, vb, hvb⟩ : GaussianPDF).density y|) (x - c) := by
    intro x
    simp only [GaussianPDF.density_eq]
    congr 2 <;> ring_nf
  rw [show (∫ x, |(⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x| ∂volume)
        = ∫ x, (fun y => |(⟨a - c, va, hva⟩ : GaussianPDF).density y - (⟨b - c, vb, hvb⟩ : GaussianPDF).density y|) (x - c) ∂volume from by
      apply MeasureTheory.integral_congr_ae; exact Filter.Eventually.of_forall key]
  rw [MeasureTheory.integral_sub_right_eq_self
       (fun y => |(⟨a - c, va, hva⟩ : GaussianPDF).density y - (⟨b - c, vb, hvb⟩ : GaussianPDF).density y|) c]

private lemma l1_neg (a b va vb : ℝ) (hva : 0 < va) (hvb : 0 < vb) :
    L1Norm (fun x => (⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x)
    = L1Norm (fun x => (⟨-a, va, hva⟩ : GaussianPDF).density x - (⟨-b, vb, hvb⟩ : GaussianPDF).density x) := by
  simp only [L1Norm_def]
  have key : ∀ x : ℝ, |(⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x|
      = (fun y => |(⟨-a, va, hva⟩ : GaussianPDF).density y - (⟨-b, vb, hvb⟩ : GaussianPDF).density y|) (-x) := by
    intro x
    simp only [GaussianPDF.density_eq]
    congr 2 <;> ring_nf
  rw [show (∫ x, |(⟨a, va, hva⟩ : GaussianPDF).density x - (⟨b, vb, hvb⟩ : GaussianPDF).density x| ∂volume)
        = ∫ x, (fun y => |(⟨-a, va, hva⟩ : GaussianPDF).density y - (⟨-b, vb, hvb⟩ : GaussianPDF).density y|) (-x) ∂volume from by
      apply MeasureTheory.integral_congr_ae; exact Filter.Eventually.of_forall key]
  rw [MeasureTheory.integral_neg_eq_self
       (fun y => |(⟨-a, va, hva⟩ : GaussianPDF).density y - (⟨-b, vb, hvb⟩ : GaussianPDF).density y|)]

/-! ## Oriented core: smaller variance & nonneg mean offset, with both bounds. -/

/-- The positive mean-piece constant. -/
private noncomputable def cM : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * (3/2))) * Real.exp (-9) * (1 - Real.exp (-1))

private lemma cM_pos : 0 < cM := by
  unfold cM
  have hexp1_lt1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ) < 0); linarith
  apply mul_pos (mul_pos (by positivity) (Real.exp_pos _)); linarith

/-- For `δ ≥ 0`, `va ≤ vb`: combined bound `max(min δ 1, vb−va) ≤ C₀·L1(g)`,
    where `g = N(0,vb) − N(-δ,va)` and `C₀ = max (1/cM) (1/cV)`. -/
private lemma core_combined (δ va vb : ℝ)
    (hva : 0 < va) (hvb : 0 < vb)
    (hva_lo : 1/2 ≤ va) (hvb_hi : vb ≤ 3/2) (hab : va ≤ vb) (hδ : 0 ≤ δ) :
    max (min δ 1) (vb - va)
      ≤ (max (1 / cM) (1 / cV))
        * L1Norm (fun x =>
          (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) := by
  set L := L1Norm (fun x =>
    (⟨0, vb, hvb⟩ : GaussianPDF).density x - (⟨-δ, va, hva⟩ : GaussianPDF).density x) with hL
  have hL_nn : 0 ≤ L := by rw [hL, L1Norm_def]; positivity
  have hCm_pos : (0:ℝ) < 1 / cM := one_div_pos.mpr cM_pos
  have hCv_pos : (0:ℝ) < 1 / cV := one_div_pos.mpr cV_pos
  -- mean bound: cM · min δ 1 ≤ L ⟹ min δ 1 ≤ (1/cM) L
  have hmean : cM * min δ 1 ≤ L := by
    have := core_mean_bound δ va vb hva hvb hva_lo hvb_hi hab hδ
    rw [← hL] at this
    unfold cM; linarith [this]
  have hmean_bound : min δ 1 ≤ (1 / cM) * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ cM_pos]; linarith [hmean]
  -- var bound: cV · (vb−va) ≤ L (when δ ≤ 1); for δ > 1, vb−va ≤ 1 = min δ 1, dominated by mean.
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · have hvar : cV * (vb - va) ≤ L := by
      have := core_var_bound δ va vb hva hvb hva_lo hvb_hi hab hδ hδ1
      rw [← hL] at this; exact this
    have hvar_bound : (vb - va) ≤ (1 / cV) * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ cV_pos]; linarith [hvar]
    apply max_le
    · calc min δ 1 ≤ (1/cM) * L := hmean_bound
        _ ≤ max (1/cM) (1/cV) * L := by apply mul_le_mul_of_nonneg_right (le_max_left _ _) hL_nn
    · calc (vb - va) ≤ (1/cV) * L := hvar_bound
        _ ≤ max (1/cM) (1/cV) * L := by apply mul_le_mul_of_nonneg_right (le_max_right _ _) hL_nn
  · -- δ > 1: min δ 1 = 1 ≥ vb − va (since vb − va ≤ 1). max = 1 = min δ 1, handled by mean.
    have hmin1 : min δ 1 = 1 := min_eq_right (le_of_lt hδ1)
    have hvb_va_le1 : vb - va ≤ 1 := by linarith
    rw [hmin1]
    rw [show max (1:ℝ) (vb - va) = 1 from max_eq_left hvb_va_le1]
    calc (1:ℝ) = min δ 1 := hmin1.symm
      _ ≤ (1/cM) * L := hmean_bound
      _ ≤ max (1/cM) (1/cV) * L := by apply mul_le_mul_of_nonneg_right (le_max_left _ _) hL_nn

/-- Reduce to the oriented core when the FIRST Gaussian has the larger variance.
    `max(min |μ−μ'| 1, σSq − σ'Sq) ≤ C₀ · L1(N(μ,σSq) − N(μ',σ'Sq))`. -/
private lemma reduce_first_larger (μ μ' σSq σ'Sq : ℝ) (hσ : 0 < σSq) (hσ' : 0 < σ'Sq)
    (hσ_lo : 1/2 ≤ σ'Sq) (hσ_hi : σSq ≤ 3/2) (hge : σ'Sq ≤ σSq) :
    max (min |μ - μ'| 1) (σSq - σ'Sq)
      ≤ (max (1 / cM) (1 / cV))
        * L1Norm (fun x =>
          (⟨μ, σSq, hσ⟩ : GaussianPDF).density x - (⟨μ', σ'Sq, hσ'⟩ : GaussianPDF).density x) := by
  -- translate by μ: N(0,σSq) − N(μ'−μ, σ'Sq)
  rw [l1_translation μ μ' σSq σ'Sq μ hσ hσ']
  simp only [sub_self]
  set e : ℝ := μ' - μ with he
  have habs : |μ - μ'| = |e| := by rw [he]; rw [abs_sub_comm]
  rw [habs]
  -- orient mean to ≤ 0
  rcases le_or_gt e 0 with hle | hgt
  · -- e ≤ 0: write μ'−μ = -δ with δ = -e ≥ 0
    have hδ : 0 ≤ -e := by linarith
    have hc := core_combined (-e) σ'Sq σSq hσ' hσ hσ_lo hσ_hi hge hδ
    rw [show min (-e) 1 = min |e| 1 from by rw [abs_of_nonpos hle]] at hc
    rw [neg_neg] at hc
    exact hc
  · -- e > 0: negate both means → N(0,σSq) − N(-e, σ'Sq)
    rw [l1_neg 0 e σSq σ'Sq hσ hσ']
    simp only [neg_zero]
    have hδ : 0 ≤ e := le_of_lt hgt
    have hc := core_combined e σ'Sq σSq hσ' hσ hσ_lo hσ_hi hge hδ
    rw [show min e 1 = min |e| 1 from by rw [abs_of_pos hgt]] at hc
    exact hc

/-! ## Main theorem. -/

/--
Combined-gap L¹ lower bound (Lemma 5 Case 2b, Branch L linchpin).

There is an absolute constant `C₀ > 0` such that for all means `μ, μ'` and variances
`σ², σ'² ∈ [1/2, 3/2]`,

  `max(min |μ − μ'| 1, |σ² − σ'²|) / C₀ ≤ ‖N(μ,σ²,·) − N(μ',σ'²,·)‖₁`.

The `min |μ − μ'| 1` cap is necessary: `‖·‖₁ ≤ 2` always, so a bare `|μ − μ'|` is unbounded.
Since `|σ² − σ'²| ≤ 1` automatically for variances in `[1/2, 3/2]`, the variance coordinate
needs no cap. The proof uses the odd(mean-shift)/even(variance-shift) orthogonality: on a
far-right band `[2,3]` both perturbations raise the density, so the L¹ integrand dominates
each single-coordinate contribution separately (no reverse-triangle cancellation).
-/
theorem GaussianL1LowerBoundCombinedGap :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (μ μ' σSq σ'Sq : ℝ) (hσ : 0 < σSq) (hσ' : 0 < σ'Sq),
        (1 / 2 : ℝ) ≤ σSq → σSq ≤ (3 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ σ'Sq → σ'Sq ≤ (3 / 2 : ℝ) →
        max (min |μ - μ'| 1) |σSq - σ'Sq| / C₀ ≤
          L1Norm (fun x =>
            (⟨μ, σSq, hσ⟩ : GaussianPDF).density x
              - (⟨μ', σ'Sq, hσ'⟩ : GaussianPDF).density x) := by
  refine ⟨max (1 / cM) (1 / cV), ?_, ?_⟩
  · apply lt_max_of_lt_left; exact one_div_pos.mpr cM_pos
  intro μ μ' σSq σ'Sq hσ hσ' hσ_lo hσ_hi hσ'_lo hσ'_hi
  set C₀ := max (1 / cM) (1 / cV) with hC₀
  have hC₀_pos : 0 < C₀ := by rw [hC₀]; apply lt_max_of_lt_left; exact one_div_pos.mpr cM_pos
  rw [div_le_iff₀ hC₀_pos]
  -- bring constant to the left in core form: max(...) ≤ C₀ · L
  rcases le_or_gt σ'Sq σSq with hge | hlt
  · -- first has larger variance
    have := reduce_first_larger μ μ' σSq σ'Sq hσ hσ' hσ'_lo hσ_hi hge
    rw [show |σSq - σ'Sq| = σSq - σ'Sq from abs_of_nonneg (by linarith)]
    rw [hC₀]; linarith [this]
  · -- second has larger variance: swap
    rw [l1_swap μ μ' σSq σ'Sq hσ hσ']
    have := reduce_first_larger μ' μ σ'Sq σSq hσ' hσ hσ_lo hσ'_hi (le_of_lt hlt)
    rw [show |σSq - σ'Sq| = σ'Sq - σSq from by rw [abs_sub_comm, abs_of_nonneg (by linarith)]]
    rw [show |μ - μ'| = |μ' - μ| from abs_sub_comm μ μ']
    rw [hC₀]; linarith [this]

end Workspace.ProofLemmas
