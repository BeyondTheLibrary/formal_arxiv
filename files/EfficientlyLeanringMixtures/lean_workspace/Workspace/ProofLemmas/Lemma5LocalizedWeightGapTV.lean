import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory
open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureDeconvolution
open Workspace.Types.L1AndTVDistance

/-! ## Helper lemmas (all sorry-free, established via numina-lean LSP). -/

private lemma loc_aux_t_mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  have h1 : t ≤ Real.exp t := by have := Real.add_one_le_exp t; linarith
  have hexp_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right h1 hexp_pos.le
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  linarith

/-- Bridge: set integral of `G.density` over a measurable set equals the real
measure of that set under the corresponding `gaussianReal`. -/
private lemma loc_bridge (G : GaussianPDF) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, G.density x = (gaussianReal G.mean ⟨G.varSq, G.varSq_pos.le⟩).real s := by
  have hv : (⟨G.varSq, G.varSq_pos.le⟩ : NNReal) ≠ 0 := by
    have h0 : (0:NNReal) < ⟨G.varSq, G.varSq_pos.le⟩ := by
      rw [← NNReal.coe_lt_coe]; simpa using G.varSq_pos
    exact ne_of_gt h0
  have h : G.density = fun x => gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h, measureReal_def, gaussianReal_apply_eq_integral _ hv s, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg hs (fun x _ => gaussianPDFReal_nonneg _ _ _)

private lemma loc_subg_pm (μ : ℝ) (v : NNReal) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    HasSubgaussianMGF (fun x => s * (x - μ)) v (gaussianReal μ v) := by
  apply HasSubgaussianMGF.mk
  · intro t
    have heq : (fun x : ℝ => Real.exp (t * (s * (x - μ))))
        = (fun x => Real.exp (-(t*s*μ)) * Real.exp ((t*s) * x)) := by
      funext x; rw [← Real.exp_add]; congr 1; ring
    rw [heq]; exact (integrable_exp_mul_gaussianReal (t*s)).const_mul _
  · intro t
    have hs2 : s^2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
    have hmgf : mgf (fun x => s * (x - μ)) (gaussianReal μ v) t = Real.exp ((v:ℝ) * t ^ 2 / 2) := by
      have h1 : mgf (fun x => s * (x - μ)) (gaussianReal μ v) t
          = Real.exp (-(t*s*μ)) * mgf id (gaussianReal μ v) (t*s) := by
        unfold mgf; rw [← integral_const_mul]; congr 1; funext x
        rw [← Real.exp_add]; simp only [id_eq]; congr 1; ring
      rw [h1, mgf_id_gaussianReal, ← Real.exp_add]; congr 1
      have : (t*s)^2 = t^2 * s^2 := by ring
      rw [this, hs2]; ring
    rw [hmgf]

private lemma loc_right_tail (μ : ℝ) (v : NNReal) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianReal μ v).real {x | μ + R ≤ x} ≤ Real.exp (-R^2/(2*(v:ℝ))) := by
  have hsg := loc_subg_pm μ v 1 (Or.inl rfl)
  have htail := hsg.measure_ge_le (ε := R) hR
  have hset : {x | μ + R ≤ x} = {x | R ≤ (1:ℝ) * (x - μ)} := by
    ext x; simp only [Set.mem_setOf_eq, one_mul]; constructor <;> intro h <;> linarith
  rw [hset]; convert htail using 2

private lemma loc_left_tail (μ : ℝ) (v : NNReal) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianReal μ v).real {x | x ≤ μ - R} ≤ Real.exp (-R^2/(2*(v:ℝ))) := by
  have hsg := loc_subg_pm μ v (-1) (Or.inr rfl)
  have htail := hsg.measure_ge_le (ε := R) hR
  have hset : {x | x ≤ μ - R} = {x | R ≤ (-1:ℝ) * (x - μ)} := by
    ext x; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> nlinarith
  rw [hset]; convert htail using 2

/-- comp1 capture: window of half-width `R` around the mean captures
`≥ 1 − 2·exp(−R²/(2v))` of the mass. -/
private lemma loc_capture (G : GaussianPDF) (R : ℝ) (hR : 0 < R) :
    1 - 2 * Real.exp (-R^2/(2*G.varSq)) ≤ ∫ x in Set.Icc (G.mean - R) (G.mean + R), G.density x := by
  set μ := G.mean
  set v : NNReal := ⟨G.varSq, G.varSq_pos.le⟩ with hv_def
  have hvR : (v:ℝ) = G.varSq := rfl
  rw [loc_bridge G _ measurableSet_Icc]
  have hwin : MeasurableSet (Set.Icc (μ - R) (μ + R)) := measurableSet_Icc
  have hcompl : (Set.Icc (μ - R) (μ + R))ᶜ ⊆ {x | μ + R ≤ x} ∪ {x | x ≤ μ - R} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · right; simp only [Set.mem_setOf_eq]; linarith
    · left; simp only [Set.mem_setOf_eq]; linarith
  have hmono : (gaussianReal μ v).real (Set.Icc (μ - R) (μ + R))ᶜ
      ≤ (gaussianReal μ v).real {x | μ + R ≤ x} + (gaussianReal μ v).real {x | x ≤ μ - R} := by
    calc (gaussianReal μ v).real (Set.Icc (μ - R) (μ + R))ᶜ
        ≤ (gaussianReal μ v).real ({x | μ + R ≤ x} ∪ {x | x ≤ μ - R}) :=
          measureReal_mono hcompl (by apply MeasureTheory.measure_ne_top)
      _ ≤ _ := measureReal_union_le _ _
  have hcompl_eq : (gaussianReal μ v).real (Set.Icc (μ - R) (μ + R))ᶜ
      = 1 - (gaussianReal μ v).real (Set.Icc (μ - R) (μ + R)) := by
    rw [measureReal_compl hwin]; simp
  have hrt := loc_right_tail μ v R hR.le
  have hlt := loc_left_tail μ v R hR.le
  rw [hvR] at hrt hlt
  linarith [hmono, hcompl_eq, hrt, hlt]

/-- integrability of a Gaussian density on any set. -/
private lemma loc_int_on (G : GaussianPDF) (s : Set ℝ) :
    IntegrableOn G.density s volume := by
  have h : G.density = fun x => gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h]; exact (integrable_gaussianPDFReal _ _).integrableOn

/-- window integral ≤ B·(2c) when density ≤ B on the window. -/
private lemma loc_window_le (G : GaussianPDF) (a c B : ℝ) (hc : 0 < c)
    (hbound : ∀ x ∈ Set.Icc (a - c) (a + c), G.density x ≤ B) :
    ∫ x in Set.Icc (a - c) (a + c), G.density x ≤ B * (2 * c) := by
  have hcB : IntegrableOn (fun _ : ℝ => B) (Set.Icc (a - c) (a + c)) volume :=
    Continuous.integrableOn_Icc continuous_const
  have hmono : ∫ x in Set.Icc (a - c) (a + c), G.density x
      ≤ ∫ _ in Set.Icc (a - c) (a + c), B :=
    setIntegral_mono_on (loc_int_on G _) hcB measurableSet_Icc hbound
  rw [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hmono
  nlinarith [hmono]

/-- Density at distance ≥ r from the mean is ≤ 1/(r√(2π)) (Corollary 24, inlined). -/
private lemma loc_density_at_distance (G : GaussianPDF) (r : ℝ) (hr : 0 < r) (y : ℝ)
    (hry : r ≤ |y - G.mean|) :
    G.density y ≤ 1 / (r * Real.sqrt (2 * Real.pi)) := by
  set z := y - G.mean with hz
  have hσ2_pos : 0 < G.varSq := G.varSq_pos
  set σ := Real.sqrt G.varSq with hσ_def
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hσ2_pos
  have hσ_sq' : σ ^ 2 = G.varSq := by rw [sq]; exact Real.mul_self_sqrt hσ2_pos.le
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hz_pos : 0 < |z| := lt_of_lt_of_le hr hry
  have hsqrt_prod : Real.sqrt (2 * Real.pi * G.varSq) = Real.sqrt (2 * Real.pi) * σ := by
    rw [Real.sqrt_mul h2pi_pos.le]
  have hdensity : G.density y = Real.exp (-z^2 / (2 * G.varSq)) / (Real.sqrt (2 * Real.pi) * σ) := by
    rw [GaussianPDF.density_eq, hsqrt_prod, ← hz]; ring
  rw [hdensity]
  have step1 : 1 / (|z| * Real.sqrt (2 * Real.pi)) ≤ 1 / (r * Real.sqrt (2 * Real.pi)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right hry hsqrt_2pi_pos.le
  have step2 : Real.exp (-z^2 / (2 * G.varSq)) / (Real.sqrt (2 * Real.pi) * σ)
      ≤ 1 / (|z| * Real.sqrt (2 * Real.pi)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : |z| * Real.exp (-z^2 / (2 * G.varSq)) ≤ σ := by
      have ht_le_one : (z^2 / G.varSq) * Real.exp (-(z^2/G.varSq)) ≤ 1 :=
        loc_aux_t_mul_exp_neg_le_one (z^2/G.varSq)
      have sq_ineq : (|z| * Real.exp (-z^2 / (2 * G.varSq)))^2 ≤ σ^2 := by
        rw [mul_pow, sq_abs, hσ_sq']
        have hexp_sq : (Real.exp (-z^2 / (2 * G.varSq)))^2 = Real.exp (-z^2 / G.varSq) := by
          rw [sq, ← Real.exp_add]; congr 1; field_simp; ring
        rw [hexp_sq]
        have hstep := mul_le_mul_of_nonneg_left ht_le_one hσ2_pos.le
        rw [mul_one] at hstep
        have hrewrite : G.varSq * (z^2 / G.varSq * Real.exp (-(z^2 / G.varSq)))
            = z^2 * Real.exp (-z^2 / G.varSq) := by
          rw [show -(z^2 / G.varSq) = -z^2 / G.varSq from by ring]; field_simp
        rw [hrewrite] at hstep; exact hstep
      have hLHS_nonneg : 0 ≤ |z| * Real.exp (-z^2 / (2 * G.varSq)) := by positivity
      have := Real.sqrt_le_sqrt sq_ineq
      rwa [Real.sqrt_sq hLHS_nonneg, Real.sqrt_sq hσ_pos.le] at this
    nlinarith [key, hsqrt_2pi_pos, hz_pos, Real.exp_pos (-z^2 / (2 * G.varSq))]
  linarith

/-- peak density bound: `G.density y ≤ 1/√(2π v)`. -/
private lemma loc_density_le_peak (G : GaussianPDF) (y : ℝ) :
    G.density y ≤ 1 / Real.sqrt (2 * Real.pi * G.varSq) := by
  rw [GaussianPDF.density_eq]
  have hpos : 0 < Real.sqrt (2 * Real.pi * G.varSq) := by
    apply Real.sqrt_pos.mpr; have := G.varSq_pos; have := Real.pi_pos; positivity
  have hexp : Real.exp (-(y - G.mean) ^ 2 / (2 * G.varSq)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · have : (0:ℝ) ≤ (y - G.mean)^2 := sq_nonneg _; linarith
    · have := G.varSq_pos; positivity
  nlinarith [mul_le_mul_of_nonneg_left hexp (le_of_lt (by positivity : (0:ℝ) < 1 / Real.sqrt (2 * Real.pi * G.varSq)))]

/-- a single Gaussian density is integrable on all of ℝ. -/
private lemma loc_int (G : GaussianPDF) : Integrable G.density volume := by
  have h : G.density = fun x => gaussianPDFReal G.mean ⟨G.varSq, G.varSq_pos.le⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h]; exact integrable_gaussianPDFReal _ _

/-- a `GaussianMixture2` density is integrable on all of ℝ. -/
private lemma loc_mix_int (M : GaussianMixture2) : Integrable M.density volume := by
  rw [M.density_def]
  exact ((loc_int M.comp1).const_mul _).add ((loc_int M.comp2).const_mul _)

/-- subset monotonicity for nonnegative Gaussian density set integrals. -/
private lemma loc_setint_mono (G : GaussianPDF) (s t : Set ℝ) (hst : s ⊆ t) :
    ∫ x in s, G.density x ≤ ∫ x in t, G.density x := by
  apply setIntegral_mono_set (loc_int_on G t)
  · exact Filter.Eventually.of_forall (fun x => by
      rw [G.density_eq_gaussianPDFReal x]; exact gaussianPDFReal_nonneg _ _ _)
  · exact Filter.Eventually.of_forall (fun x hx => hst hx)

/-- super-polynomial decay: `2·exp(−1/(65536 ε²)) ≤ ε²/16` for `ε ≤ 1/100000`. -/
private lemma loc_decay (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/100000) :
    2 * Real.exp (-(1/(65536*ε^2))) ≤ ε^2/16 := by
  set s := 1/(65536*ε^2) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hdecay : Real.exp (-s) ≤ 24 / s^4 := by
    have hpow : s^4 / (Nat.factorial 4 : ℝ) ≤ Real.exp s := Real.pow_div_factorial_le_exp s hs_pos.le 4
    have hfact : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfact] at hpow
    have hexp_pos : 0 < Real.exp s := Real.exp_pos _
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hexp_pos]
    have hs4 : 0 < s^4 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hs4]; nlinarith [hpow, hexp_pos, hs4]
  have hs4_eq : s^4 = 1/((65536*ε^2)^4) := by rw [hs_def, div_pow]; norm_num
  have h24 : 24 / s^4 = 24 * (65536*ε^2)^4 := by rw [hs4_eq]; field_simp
  rw [h24] at hdecay
  have hbound : 2 * Real.exp (-s) ≤ 48 * (65536*ε^2)^4 := by nlinarith [hdecay, Real.exp_pos (-s)]
  refine le_trans hbound ?_
  have hexpand : 48 * (65536*ε^2)^4 = 48 * 65536^4 * ε^8 := by ring
  rw [hexpand]
  have hε6 : ε^6 ≤ (1/100000)^6 := pow_le_pow_left₀ hε.le hεsmall 6
  have hε8 : ε^8 = ε^6 * ε^2 := by ring
  rw [hε8]
  have hC : (48:ℝ) * 65536^4 * ((1/100000)^6) ≤ 1/16 := by norm_num
  nlinarith [hε6, mul_pos hε hε, sq_nonneg ε, hC, pow_pos hε 6]

/-- comp1 capture error (offset window): if the deconvolved comp1 has variance
`≤ 2ε⁸` and its mean lies within `6ε⁵` of `μ₁`, then over the window
`Icc(μ₁ − ε³/64, μ₁ + ε³/64)` it loses at most `ε²/16` of its mass. -/
private lemma loc_comp1_error
    (G1 : GaussianPDF) (μ₁ ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/100000)
    (hvar_le : G1.varSq ≤ 2 * ε^8)
    (hmean_close : |G1.mean - μ₁| ≤ 6 * ε^5) :
    1 - ε^2/16 ≤ ∫ x in Set.Icc (μ₁ - ε^3/64) (μ₁ + ε^3/64), G1.density x := by
  set h := ε^3/64 with hh_def
  -- effective half-width about G1.mean
  set R := h - 6 * ε^5 with hR_def
  have hh_pos : 0 < h := by rw [hh_def]; positivity
  have h6ε5_le : 6 * ε^5 ≤ h / 2 := by
    rw [hh_def]
    have hε2_le : 768 * ε^2 ≤ 1 := by nlinarith [hε.le, hεsmall, mul_pos hε hε]
    have hexp : ε^5 = ε^3 * ε^2 := by ring
    nlinarith [hε2_le, pow_pos hε 3, hexp, mul_pos (pow_pos hε 3) (mul_pos hε hε)]
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  -- sub-window around G1.mean is inside the μ₁-window
  have hsub : Set.Icc (G1.mean - R) (G1.mean + R) ⊆ Set.Icc (μ₁ - h) (μ₁ + h) := by
    intro x hx
    have habs : |G1.mean - μ₁| ≤ 6 * ε^5 := hmean_close
    rw [abs_le] at habs
    constructor
    · have := hx.1; rw [hR_def] at this; linarith [habs.1, habs.2]
    · have := hx.2; rw [hR_def] at this; linarith [habs.1, habs.2]
  have hcap := loc_capture G1 R hR_pos
  have hmono := loc_setint_mono G1 _ _ hsub
  -- 2·exp(−R²/2v) ≤ ε²/16 :  R ≥ h/2 = ε³/128, v ≤ 2ε⁸ ⟹ R²/2v ≥ 1/(16384 ε²)? check.
  -- R ≥ h - h/2 = h/2 = ε³/128. R² ≥ ε⁶/16384. 2v ≤ 4ε⁸. R²/2v ≥ ε⁶/(16384·4ε⁸)=1/(65536 ε²).
  have hR_ge : R ≥ h / 2 := by rw [hR_def]; linarith
  have hv_pos : 0 < G1.varSq := G1.varSq_pos
  have hexp_arg : -R^2/(2*G1.varSq) ≤ -(1/(65536*ε^2)) := by
    rw [neg_div]
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 1 * (2 G1.varSq) ≤ R^2 * 65536 ε^2
    have hR2 : R^2 ≥ (h/2)^2 := by nlinarith [hR_ge, hR_pos, hh_pos]
    have hh2 : (h/2)^2 = ε^6/16384 := by rw [hh_def]; ring
    have hv4 : 2 * G1.varSq ≤ 4 * ε^8 := by linarith [hvar_le]
    have hRlb : R^2 ≥ ε^6/16384 := by rw [← hh2]; exact hR2
    -- RHS = R^2*65536*ε^2 ≥ (ε^6/16384)*65536*ε^2 = 4ε^8 ≥ 2 G1.varSq
    have hε2_pos : 0 < ε^2 := by positivity
    nlinarith [hRlb, hv4, mul_le_mul_of_nonneg_right hRlb (le_of_lt (by positivity : (0:ℝ) < 65536*ε^2)), pow_pos hε 8]
  have hmono_exp : 2 * Real.exp (-R^2/(2*G1.varSq)) ≤ 2 * Real.exp (-(1/(65536*ε^2))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.exp_le_exp.mpr hexp_arg
  have hdec := loc_decay ε hε hεsmall
  linarith [hcap, hmono, hmono_exp, hdec]

/-- comp2 window-mass bound. With window half-width `h = ε³/64` centred at `μ₁`,
the deconvolved comp2 contributes `≤ ε²/8` mass, because the intra-mixture
separation forces it to be either wide in variance (`ε/4 ≤ varSq`) or far in
mean (`ε/4 ≤ |mean − μ₁|`). -/
private lemma loc_comp2_window
    (G2 : GaussianPDF) (μ₁ ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/100000)
    (hdisj : ε/4 ≤ G2.varSq ∨ ε/4 ≤ |G2.mean - μ₁|) :
    ∫ x in Set.Icc (μ₁ - ε^3/64) (μ₁ + ε^3/64), G2.density x ≤ ε^2/8 := by
  have hεle : ε ≤ 1 := by linarith
  have hh_pos : 0 < ε^3/64 := by positivity
  rcases hdisj with hvar | hmean
  · -- wide variance: peak density ≤ 1/√(2π·(ε/4))
    have hbound : ∀ x ∈ Set.Icc (μ₁ - ε^3/64) (μ₁ + ε^3/64),
        G2.density x ≤ 1 / Real.sqrt (2 * Real.pi * (ε/4)) := by
      intro x _
      refine le_trans (loc_density_le_peak G2 x) ?_
      apply one_div_le_one_div_of_le (by have := hε; positivity)
      apply Real.sqrt_le_sqrt
      nlinarith [hvar, Real.pi_pos]
    have hwin := loc_window_le G2 μ₁ (ε^3/64) (1 / Real.sqrt (2 * Real.pi * (ε/4))) hh_pos hbound
    refine le_trans hwin ?_
    -- arithmetic: (1/√(2π·(ε/4)))·(2·(ε³/64)) ≤ ε²/8
    have hπ : (1:ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hge : Real.sqrt (ε/4) ≤ Real.sqrt (2 * Real.pi * (ε/4)) := by
      apply Real.sqrt_le_sqrt; nlinarith [hε.le, hπ]
    have hsqrtε4_eq : Real.sqrt (ε/4) = Real.sqrt ε / 2 := by
      rw [show (ε/4) = ε * (1/2)^2 from by ring, Real.sqrt_mul hε.le, Real.sqrt_sq (by norm_num)]; ring
    have hsqrtε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hsqrtε4_pos : 0 < Real.sqrt (ε/4) := Real.sqrt_pos.mpr (by positivity)
    have hstep : 1 / Real.sqrt (2 * Real.pi * (ε/4)) ≤ 1 / Real.sqrt (ε/4) :=
      one_div_le_one_div_of_le hsqrtε4_pos hge
    have hmass_le : (1 / Real.sqrt (2 * Real.pi * (ε/4))) * (2 * (ε^3/64))
        ≤ (1 / Real.sqrt (ε/4)) * (2 * (ε^3/64)) :=
      mul_le_mul_of_nonneg_right hstep (by positivity)
    refine le_trans hmass_le ?_
    rw [hsqrtε4_eq]
    have hsqrtε_le1 : Real.sqrt ε ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hεle
    have hεeq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    rw [div_div_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_div_iff₀ hsqrtε_pos (by norm_num)]
    have hε3 : ε^3 = (ε^2 * Real.sqrt ε) * Real.sqrt ε := by rw [mul_assoc, hεeq]; ring
    have hkey : (ε^2 * Real.sqrt ε) * Real.sqrt ε ≤ (ε^2 * Real.sqrt ε) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hε3]; nlinarith [hkey, hsqrtε_pos, mul_pos hε hε]
  · -- far mean: every window point is at distance ≥ ε/8 from G2.mean
    have hh_le : ε^3/64 ≤ ε/8 := by nlinarith [hε.le, hεsmall, sq_nonneg ε, mul_pos hε hε]
    have hbound : ∀ x ∈ Set.Icc (μ₁ - ε^3/64) (μ₁ + ε^3/64),
        G2.density x ≤ 1 / (ε/8 * Real.sqrt (2 * Real.pi)) := by
      intro x hx
      have hdist : ε/8 ≤ |x - G2.mean| := by
        have hx1 : |x - μ₁| ≤ ε^3/64 := by
          rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
        have hrev : |x - G2.mean| ≥ |G2.mean - μ₁| - |x - μ₁| := by
          have := abs_sub_abs_le_abs_sub (G2.mean - μ₁) (x - μ₁)
          have heq : (G2.mean - μ₁) - (x - μ₁) = -(x - G2.mean) := by ring
          rw [heq, abs_neg] at this
          linarith
        linarith [hmean, hx1]
      exact loc_density_at_distance G2 (ε/8) (by positivity) x hdist
    have hwin := loc_window_le G2 μ₁ (ε^3/64) (1 / (ε/8 * Real.sqrt (2 * Real.pi))) hh_pos hbound
    refine le_trans hwin ?_
    -- arithmetic: (1/(ε/8·√(2π)))·(2·(ε³/64)) ≤ ε²/8.  √(2π) ≥ 2.
    have hsqrt_ge_two : (2:ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h4]
      apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_three]
    have hden_pos : 0 < ε/8 * Real.sqrt (2 * Real.pi) := by positivity
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ hden_pos (by norm_num)]
    -- (2*(ε³/64))*8 ≤ ε² * (ε/8 * √(2π)) ; RHS ≥ ε²·(ε/8·2)=ε³/4 ; LHS = ε³/4. equal-ish.
    have h1 : ε/8 * Real.sqrt (2 * Real.pi) ≥ ε/8 * 2 := by
      apply mul_le_mul_of_nonneg_left hsqrt_ge_two (by positivity)
    nlinarith [h1, hε.le, mul_pos hε hε, mul_pos (mul_pos hε hε) hε]

/-! ## Main theorem. -/

theorem Lemma5LocalizedWeightGapTV
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1)
    (h_std : Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε)
    (h12 : F.comp1.varSq ≤ F.comp2.varSq)
    (h1'1 : F.comp1.varSq ≤ F'.comp1.varSq)
    (h1'2 : F.comp1.varSq ≤ F'.comp2.varSq)
    (hCase2_var : F'.comp1.varSq - F.comp1.varSq < 16 * ε ^ 10)
    (hCase2_mean : |F'.comp1.mean - F.comp1.mean| < 6 * ε ^ 5)
    (hCase2a_w : ε ^ 2 ≤ |F.weight1 - F'.weight1|)
    (hε_small : ε ≤ 1 / 100000)
    (h₁ : F.comp1.varSq - ε ^ 8 < min F.comp1.varSq F.comp2.varSq)
    (h₂ : F.comp1.varSq - ε ^ 8 < min F'.comp1.varSq F'.comp2.varSq) :
    ε ^ 2 / 4 ≤
      Workspace.Types.L1AndTVDistance.TVDistance
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F (F.comp1.varSq - ε ^ 8) h₁)
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' (F.comp1.varSq - ε ^ 8) h₂) := by
  set α : ℝ := F.comp1.varSq - ε ^ 8 with hα
  set μ₁ : ℝ := F.comp1.mean with hμ₁
  set G := Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁ with hG
  set G' := Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂ with hG'
  set W := Set.Icc (μ₁ - ε^3/64) (μ₁ + ε^3/64) with hW
  have hε_nn := hε_pos.le
  -- component identifications
  have hG1m : G.comp1.mean = μ₁ := rfl
  have hG1v : G.comp1.varSq = ε^8 := by show F.comp1.varSq - α = ε^8; rw [hα]; ring
  have hG2m : G.comp2.mean = F.comp2.mean := rfl
  have hG2v : G.comp2.varSq = F.comp2.varSq - α := rfl
  have hGw1 : G.weight1 = F.weight1 := rfl
  have hGw2 : G.weight2 = F.weight2 := rfl
  have hG'1m : G'.comp1.mean = F'.comp1.mean := rfl
  have hG'1v : G'.comp1.varSq = F'.comp1.varSq - α := rfl
  have hG'2m : G'.comp2.mean = F'.comp2.mean := rfl
  have hG'2v : G'.comp2.varSq = F'.comp2.varSq - α := rfl
  have hG'w1 : G'.weight1 = F'.weight1 := rfl
  have hG'w2 : G'.weight2 = F'.weight2 := rfl
  -- weights bounds
  have hw1_nn : 0 ≤ F.weight1 := F.weight1_nonneg
  have hw2_nn : 0 ≤ F.weight2 := F.weight2_nonneg
  have hw1'_nn : 0 ≤ F'.weight1 := F'.weight1_nonneg
  have hw2'_nn : 0 ≤ F'.weight2 := F'.weight2_nonneg
  have hw1_le : F.weight1 ≤ 1 := by linarith [F.weight2_nonneg, F.weights_sum_one]
  have hw1'_le : F'.weight1 ≤ 1 := by linarith [F'.weight2_nonneg, F'.weights_sum_one]
  have hε8_pos : 0 < ε^8 := by positivity
  -- ===== comp1 capture errors =====
  -- G.comp1 : varSq = ε^8 ≤ 2ε^8, mean = μ₁ (offset 0)
  have hG1_err : 1 - ε^2/16 ≤ ∫ x in W, G.comp1.density x := by
    have hvar_le : G.comp1.varSq ≤ 2 * ε^8 := by rw [hG1v]; nlinarith [hε8_pos]
    have hmean_close : |G.comp1.mean - μ₁| ≤ 6 * ε^5 := by rw [hG1m]; simp; positivity
    exact loc_comp1_error G.comp1 μ₁ ε hε_pos hε_small hvar_le hmean_close
  -- G'.comp1 : varSq = F'.σ₁² - α = (F'.σ₁²-F.σ₁²)+ε^8 ≤ 16ε^10+ε^8 ≤ 2ε^8, mean μ₁' close to μ₁
  have hG'1_err : 1 - ε^2/16 ≤ ∫ x in W, G'.comp1.density x := by
    have hvar_le : G'.comp1.varSq ≤ 2 * ε^8 := by
      rw [hG'1v, hα]
      have : F'.comp1.varSq - (F.comp1.varSq - ε^8) = (F'.comp1.varSq - F.comp1.varSq) + ε^8 := by ring
      rw [this]
      have h16 : 16 * ε^10 ≤ ε^8 := by
        have hfac : ε^10 = ε^8 * ε^2 := by ring
        have hε2 : 16 * ε^2 ≤ 1 := by nlinarith [hε_small, hε_pos.le, mul_pos hε_pos hε_pos]
        rw [hfac]; nlinarith [hε8_pos, hε2]
      linarith [hCase2_var, h16]
    have hmean_close : |G'.comp1.mean - μ₁| ≤ 6 * ε^5 := by
      rw [hG'1m, hμ₁]; linarith [le_of_lt hCase2_mean]
    exact loc_comp1_error G'.comp1 μ₁ ε hε_pos hε_small hvar_le hmean_close
  -- upper bounds: each comp window mass ≤ 1 (total mass)
  have hG1_le1 : ∫ x in W, G.comp1.density x ≤ 1 := by
    rw [loc_bridge G.comp1 W measurableSet_Icc]
    exact measureReal_le_one
  have hG'1_le1 : ∫ x in W, G'.comp1.density x ≤ 1 := by
    rw [loc_bridge G'.comp1 W measurableSet_Icc]
    exact measureReal_le_one
  -- ===== comp2 window masses =====
  -- F comp2 disjunction
  have hG2_disj : ε/4 ≤ G.comp2.varSq ∨ ε/4 ≤ |G.comp2.mean - μ₁| := by
    have hintra := h_std.intra_sep_F
    -- |μ₁ - F.comp2.mean| + |F.σ₁² - F.σ₂²| ≥ ε
    rcases le_or_gt (ε/2) (|F.comp1.mean - F.comp2.mean|) with hm | hm
    · right
      rw [hG2m, hμ₁, abs_sub_comm]
      linarith
    · left
      rw [hG2v, hα]
      -- |F.σ₁² - F.σ₂²| ≥ ε/2 from intra (since the mean term < ε/2)
      have hvargap : ε/2 ≤ |F.comp1.varSq - F.comp2.varSq| := by linarith [hintra]
      have hpos : F.comp1.varSq - F.comp2.varSq ≤ 0 := by linarith [h12]
      rw [abs_of_nonpos hpos] at hvargap
      -- F.comp2.varSq - F.comp1.varSq ≥ ε/2
      nlinarith [hvargap, hε8_pos]
  have hG2_win : ∫ x in W, G.comp2.density x ≤ ε^2/8 :=
    loc_comp2_window G.comp2 μ₁ ε hε_pos hε_small hG2_disj
  -- F' comp2 disjunction
  have hG'2_disj : ε/4 ≤ G'.comp2.varSq ∨ ε/4 ≤ |G'.comp2.mean - μ₁| := by
    have hintra := h_std.intra_sep_F'
    -- triangle: |F.σ₁²-F'.σ₂²| + |μ₁-F'.μ₂| ≥ ε - 6ε⁵ - 16ε¹⁰ ≥ 3ε/4
    have hmclose : |F'.comp1.mean - F.comp1.mean| < 6 * ε^5 := hCase2_mean
    have hvclose : F'.comp1.varSq - F.comp1.varSq < 16 * ε^10 := hCase2_var
    have hvclose_abs : |F'.comp1.varSq - F.comp1.varSq| < 16 * ε^10 := by
      rw [abs_of_nonneg (by linarith [h1'1])]; exact hvclose
    -- |F.μ₁-F'.μ₂| ≥ |F'.μ₁-F'.μ₂| - |F'.μ₁-F.μ₁| ; similarly variances
    have hmean_tri : |F.comp1.mean - F'.comp2.mean| ≥ |F'.comp1.mean - F'.comp2.mean| - 6*ε^5 := by
      have hkey := abs_sub_abs_le_abs_sub (F'.comp1.mean - F'.comp2.mean) (F'.comp1.mean - F.comp1.mean)
      have heq : (F'.comp1.mean - F'.comp2.mean) - (F'.comp1.mean - F.comp1.mean)
          = F.comp1.mean - F'.comp2.mean := by ring
      rw [heq] at hkey; linarith [le_of_lt hmclose]
    have hvar_tri : |F.comp1.varSq - F'.comp2.varSq| ≥ |F'.comp1.varSq - F'.comp2.varSq| - 16*ε^10 := by
      have hkey := abs_sub_abs_le_abs_sub (F'.comp1.varSq - F'.comp2.varSq) (F'.comp1.varSq - F.comp1.varSq)
      have heq : (F'.comp1.varSq - F'.comp2.varSq) - (F'.comp1.varSq - F.comp1.varSq)
          = F.comp1.varSq - F'.comp2.varSq := by ring
      rw [heq] at hkey; linarith [hvclose_abs]
    have htotal : |F.comp1.mean - F'.comp2.mean| + |F.comp1.varSq - F'.comp2.varSq| ≥ ε - 6*ε^5 - 16*ε^10 := by
      linarith [hintra, hmean_tri, hvar_tri]
    have hslack : ε - 6*ε^5 - 16*ε^10 ≥ 3*ε/4 := by
      have h1 : 6 * ε^5 ≤ ε/8 := by
        have hfac : ε^5 = ε * ε^4 := by ring
        have he4 : 48 * ε^4 ≤ 1 := by nlinarith [hε_small, hε_pos.le, pow_pos hε_pos 4, pow_le_pow_left₀ hε_pos.le hε_small 4]
        rw [hfac]; nlinarith [he4, hε_pos.le, pow_pos hε_pos 4]
      have h2 : 16 * ε^10 ≤ ε/8 := by
        have hfac : ε^10 = ε * ε^9 := by ring
        have he9 : 128 * ε^9 ≤ 1 := by nlinarith [hε_small, hε_pos.le, pow_pos hε_pos 9, pow_le_pow_left₀ hε_pos.le hε_small 9]
        rw [hfac]; nlinarith [he9, hε_pos.le, pow_pos hε_pos 9]
      linarith
    rcases le_or_gt (3*ε/8) (|F.comp1.mean - F'.comp2.mean|) with hm | hm
    · right
      rw [hG'2m, hμ₁, abs_sub_comm]
      linarith
    · left
      rw [hG'2v, hα]
      have hvargap : 3*ε/8 ≤ |F.comp1.varSq - F'.comp2.varSq| := by linarith [htotal, hslack]
      have hpos : F.comp1.varSq - F'.comp2.varSq ≤ 0 := by linarith [h1'2]
      rw [abs_of_nonpos hpos] at hvargap
      nlinarith [hvargap, hε8_pos]
  have hG'2_win : ∫ x in W, G'.comp2.density x ≤ ε^2/8 :=
    loc_comp2_window G'.comp2 μ₁ ε hε_pos hε_small hG'2_disj
  -- comp2 window masses are nonneg
  have hG2_nn : 0 ≤ ∫ x in W, G.comp2.density x := by
    apply setIntegral_nonneg measurableSet_Icc
    intro x _; rw [G.comp2.density_eq_gaussianPDFReal x]; exact gaussianPDFReal_nonneg _ _ _
  have hG'2_nn : 0 ≤ ∫ x in W, G'.comp2.density x := by
    apply setIntegral_nonneg measurableSet_Icc
    intro x _; rw [G'.comp2.density_eq_gaussianPDFReal x]; exact gaussianPDFReal_nonneg _ _ _
  -- ===== integral decomposition =====
  -- integrability on W of each component
  have hWmeas : MeasurableSet W := measurableSet_Icc
  -- set integral of mixture density = w1·(comp1) + w2·(comp2)
  have hsplit_G : ∫ x in W, G.density x
      = G.weight1 * (∫ x in W, G.comp1.density x) + G.weight2 * (∫ x in W, G.comp2.density x) := by
    have heq : (fun x => G.density x)
        = (fun x => G.weight1 * G.comp1.density x + G.weight2 * G.comp2.density x) := by
      funext x; exact G.density_eq x
    rw [setIntegral_congr_fun hWmeas (fun x _ => G.density_eq x)]
    rw [integral_add ((loc_int_on G.comp1 W).const_mul _) ((loc_int_on G.comp2 W).const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  have hsplit_G' : ∫ x in W, G'.density x
      = G'.weight1 * (∫ x in W, G'.comp1.density x) + G'.weight2 * (∫ x in W, G'.comp2.density x) := by
    rw [setIntegral_congr_fun hWmeas (fun x _ => G'.density_eq x)]
    rw [integral_add ((loc_int_on G'.comp1 W).const_mul _) ((loc_int_on G'.comp2 W).const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  -- integrability of the mixture densities on ℝ
  have hG_int : Integrable G.density volume := loc_mix_int G
  have hG'_int : Integrable G'.density volume := loc_mix_int G'
  set f : ℝ → ℝ := fun x => G.density x - G'.density x with hf
  have hf_int : Integrable f volume := hG_int.sub hG'_int
  have hf_int_on : IntegrableOn f W volume := hf_int.integrableOn
  -- 2·TVDistance = ∫_ℝ |f|
  have hTV : 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' = ∫ x, |f x| := by
    rw [Workspace.Types.L1AndTVDistance.TVDistance_def,
        Workspace.Types.L1AndTVDistance.L1NormMixtureDiff_def,
        Workspace.Types.L1AndTVDistance.L1Norm_def]
    ring
  -- ∫_ℝ |f| ≥ ∫_W |f| ≥ |∫_W f|
  have habs_int : Integrable (fun x => |f x|) volume := hf_int.abs
  have hstep1 : ∫ x in W, |f x| ≤ ∫ x, |f x| := by
    apply setIntegral_le_integral habs_int
    exact Filter.Eventually.of_forall (fun x => abs_nonneg _)
  have hstep2 : |∫ x in W, f x| ≤ ∫ x in W, |f x| := MeasureTheory.abs_integral_le_integral_abs
  -- ∫_W f = (∫_W G.density) - (∫_W G'.density)
  have hfsplit : ∫ x in W, f x = (∫ x in W, G.density x) - (∫ x in W, G'.density x) := by
    rw [hf]
    exact integral_sub hG_int.integrableOn hG'_int.integrableOn
  -- the localized integral value
  have hval : ∫ x in W, f x
      = (F.weight1 * (∫ x in W, G.comp1.density x) + F.weight2 * (∫ x in W, G.comp2.density x))
        - (F'.weight1 * (∫ x in W, G'.comp1.density x) + F'.weight2 * (∫ x in W, G'.comp2.density x)) := by
    rw [hfsplit, hsplit_G, hsplit_G', hGw1, hGw2, hG'w1, hG'w2]
  -- weight2 upper bounds
  have hw2_le : F.weight2 ≤ 1 := by linarith [F.weight1_nonneg, F.weights_sum_one]
  have hw2'_le : F'.weight2 ≤ 1 := by linarith [F'.weight1_nonneg, F'.weights_sum_one]
  -- abbreviations
  set D1 := ∫ x in W, G.comp1.density x with hD1
  set D1' := ∫ x in W, G'.comp1.density x with hD1'
  set E2 := ∫ x in W, G.comp2.density x with hE2
  set E2' := ∫ x in W, G'.comp2.density x with hE2'
  -- ∫_W f = (w₁D1 - w₁'D1') + (w₂E2 - w₂'E2'), close to (w₁ - w₁')
  -- |∫_W f| ≥ |w₁ - w₁'| - 3ε²/16 ≥ ε² - 3ε²/16 ≥ ε²/2
  have hε2_nn : 0 ≤ ε^2 := by positivity
  -- bound the deviation
  have hdev : |(∫ x in W, f x) - (F.weight1 - F'.weight1)| ≤ 3*ε^2/16 := by
    rw [hval]
    rw [abs_le]
    constructor
    · -- lower: (w₁D1 + w₂E2 - w₁'D1' - w₂'E2') - (w₁ - w₁') ≥ -3ε²/16
      -- = w₁(D1-1) + w₂E2 - w₁'(D1'-1) - w₂'E2'
      -- w₁(D1-1) ≥ w₁·(-ε²/16) ≥ -ε²/16 ; w₂E2 ≥ 0 ; -w₁'(D1'-1) ≥ 0 ; -w₂'E2' ≥ -ε²/8
      nlinarith [hG1_err, hG1_le1, hG'1_err, hG'1_le1, hG2_win, hG2_nn, hG'2_win, hG'2_nn,
        hw1_nn, hw2_nn, hw1'_nn, hw2'_nn, hw1_le, hw2_le, hw1'_le, hw2'_le,
        mul_nonneg hw2_nn hG2_nn, mul_nonneg hw1'_nn (by linarith [hG'1_le1] : (0:ℝ) ≤ 1 - D1'),
        mul_le_of_le_one_left hG2_nn hw2_le,
        mul_le_of_le_one_left hG'2_nn hw2'_le,
        mul_nonneg hw1_nn (by linarith [hG1_err] : (0:ℝ) ≤ D1 - (1 - ε^2/16))]
    · nlinarith [hG1_err, hG1_le1, hG'1_err, hG'1_le1, hG2_win, hG2_nn, hG'2_win, hG'2_nn,
        hw1_nn, hw2_nn, hw1'_nn, hw2'_nn, hw1_le, hw2_le, hw1'_le, hw2'_le,
        mul_nonneg hw2'_nn hG'2_nn, mul_nonneg hw1_nn (by linarith [hG1_le1] : (0:ℝ) ≤ 1 - D1),
        mul_le_of_le_one_left hG2_nn hw2_le,
        mul_le_of_le_one_left hG'2_nn hw2'_le,
        mul_nonneg hw1'_nn (by linarith [hG'1_err] : (0:ℝ) ≤ D1' - (1 - ε^2/16))]
  -- hence |∫_W f| ≥ |w₁ - w₁'| - 3ε²/16
  have hval_abs : |∫ x in W, f x| ≥ |F.weight1 - F'.weight1| - 3*ε^2/16 := by
    -- |w₁-w₁'| - |∫_W f| ≤ |(w₁-w₁') - ∫_W f| = |∫_W f - (w₁-w₁')| ≤ 3ε²/16
    have htri := abs_sub_abs_le_abs_sub (F.weight1 - F'.weight1) (∫ x in W, f x)
    rw [abs_sub_comm (F.weight1 - F'.weight1) (∫ x in W, f x)] at htri
    linarith [htri, hdev]
  -- |∫_W f| ≥ ε² - 3ε²/16 = 13ε²/16 ≥ ε²/2
  have hwgap : |F.weight1 - F'.weight1| ≥ ε^2 := hCase2a_w
  have hfinal : |∫ x in W, f x| ≥ ε^2/2 := by
    have : |∫ x in W, f x| ≥ ε^2 - 3*ε^2/16 := by linarith [hval_abs, hwgap]
    linarith
  -- combine: 2·TV = ∫|f| ≥ ∫_W|f| ≥ |∫_W f| ≥ ε²/2, so TV ≥ ε²/4
  have h2TV : 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' ≥ ε^2/2 := by
    rw [hTV]; linarith [hstep1, hstep2, hfinal]
  linarith [h2TV]

end Workspace.ProofLemmas
