import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.ProofLemmas.Lemma29Assembly
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian
import Workspace.ProofLemmas.Lemma29BinomialAbsExpansionBound

open MeasureTheory ProbabilityTheory

namespace Workspace.ProofLemmas

set_option maxHeartbeats 16000000

open Workspace.Types.GaussianPDF

/-- The linear-scaling change of variables `x = √σSq · y` for the symmetric tail set.
This is the isolated hard step.  Proven (no `sorry`). -/
private theorem scaling_cov (μ σSq ε : ℝ) (i : ℕ) (hσSq_pos : 0 < σSq) (hε_pos : 0 < ε) :
    (∫ x in {x : ℝ | 2 / ε ≤ |x|},
        x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
              * Real.exp (-((x - μ)^2) / (2 * σSq)) ∂volume)
    = (Real.sqrt σSq) ^ i *
        ∫ x in {x : ℝ | 2 / (ε * Real.sqrt σSq) ≤ |x|},
          x ^ i * (1 / Real.sqrt (2 * Real.pi * 1))
                * Real.exp (-((x - μ / Real.sqrt σSq)^2) / (2 * 1)) ∂volume := by
  set s := Real.sqrt σSq with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hσSq_pos
  have hs_sq : s^2 = σSq := Real.sq_sqrt hσSq_pos.le
  set f : ℝ → ℝ := fun x => x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
            * Real.exp (-((x - μ)^2) / (2 * σSq)) with hf
  set g : ℝ → ℝ := fun x => ({x : ℝ | 2 / ε ≤ |x|}).indicator f x with hg
  set F : ℝ → ℝ := fun x => x ^ i * (1 / Real.sqrt (2 * Real.pi * 1))
            * Real.exp (-((x - μ/s)^2) / (2 * 1)) with hF
  set G : ℝ → ℝ := fun x => ({x : ℝ | 2 / (ε * s) ≤ |x|}).indicator F x with hG
  have hmeasS : MeasurableSet {x : ℝ | 2 / ε ≤ |x|} := by
    have heq : {x : ℝ | 2 / ε ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' (Set.Ici (2/ε)) := rfl
    rw [heq]; exact measurable_norm measurableSet_Ici
  have hmeasS' : MeasurableSet {x : ℝ | 2 / (ε*s) ≤ |x|} := by
    have heq : {x : ℝ | 2 / (ε*s) ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' (Set.Ici (2/(ε*s))) := rfl
    rw [heq]; exact measurable_norm measurableSet_Ici
  have hI : (∫ x in {x : ℝ | 2 / ε ≤ |x|}, f x ∂volume) = ∫ x, g x ∂volume := by
    rw [hg]; rw [MeasureTheory.integral_indicator hmeasS]
  have hI' : (∫ x in {x : ℝ | 2 / (ε*s) ≤ |x|}, F x ∂volume) = ∫ x, G x ∂volume := by
    rw [hG]; rw [MeasureTheory.integral_indicator hmeasS']
  have hscale : ∫ y, g y ∂volume = s * ∫ x, g (s * x) ∂volume := by
    have := MeasureTheory.Measure.integral_comp_mul_left g s
    rw [this, abs_of_pos (by positivity : (0:ℝ) < s⁻¹), smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hs_pos), one_mul]
  have hset_iff : ∀ x : ℝ, (2 / ε ≤ |s * x|) ↔ (2 / (ε * s) ≤ |x|) := by
    intro x
    rw [abs_mul, abs_of_pos hs_pos]
    rw [div_le_iff₀ hε_pos, div_le_iff₀ (by positivity : (0:ℝ) < ε * s)]
    constructor
    · intro h; nlinarith [hs_pos, abs_nonneg x]
    · intro h; nlinarith [hs_pos, abs_nonneg x]
  have hfun : ∀ x : ℝ, s * f (s * x) = s^i * F x := by
    intro x
    simp only [hf, hF, ← hs_sq]
    have hsqrt : Real.sqrt (2 * Real.pi * s^2) = Real.sqrt (2 * Real.pi) * s := by
      rw [show 2 * Real.pi * s^2 = (2 * Real.pi) * s^2 by ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs_pos.le]
    rw [hsqrt]
    have hexp : -((s*x - μ)^2) / (2 * s^2) = -((x - μ/s)^2) / (2 * 1) := by
      have hs2 : s^2 ≠ 0 := by positivity
      field_simp
    rw [hexp, mul_pow]
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have h2pi1 : Real.sqrt (2 * Real.pi * 1) = Real.sqrt (2 * Real.pi) := by norm_num
    rw [h2pi1]
    field_simp
  have hkey : ∀ x : ℝ, s * g (s * x) = s^i * G x := by
    intro x
    simp only [hg, hG, Set.indicator]
    by_cases hx : (2 / (ε * s) ≤ |x|)
    · have hx' : s * x ∈ {x : ℝ | 2 / ε ≤ |x|} := by
        simp only [Set.mem_setOf_eq]; exact (hset_iff x).mpr hx
      rw [if_pos hx', if_pos (show x ∈ {x : ℝ | 2 / (ε*s) ≤ |x|} from hx)]
      exact hfun x
    · have hx' : s * x ∉ {x : ℝ | 2 / ε ≤ |x|} := by
        simp only [Set.mem_setOf_eq]; rw [hset_iff x]; exact hx
      rw [if_neg hx', if_neg (show x ∉ {x : ℝ | 2 / (ε*s) ≤ |x|} from hx)]
      ring
  rw [hI, hscale]
  rw [show (s * ∫ x, g (s * x) ∂volume) = ∫ x, s * g (s * x) ∂volume from
        (MeasureTheory.integral_const_mul s (fun x => g (s*x))).symm]
  rw [show (∫ x, s * g (s * x) ∂volume) = ∫ x, s^i * G x ∂volume from by
        apply MeasureTheory.integral_congr_ae; filter_upwards with x; exact hkey x]
  rw [MeasureTheory.integral_const_mul]
  rw [← hI']

/-- The unit-variance absolute moment is bounded by an absolute constant for `|μ'| ≤ 1`,
`i ≤ 6`. Used for the Case-B2 regime (where `ε·√σSq > 1`). -/
private theorem caseB2_const_bound (μ' : ℝ) (i : ℕ) (hi : i ≤ 6) (hμ' : |μ'| ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) :
    |∫ x in S, x ^ i * (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((x - μ')^2) / (2 * 1)) ∂volume|
    ≤ (2:ℝ)^6 * (2 + ∫ z : ℝ, |z|^6 * (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((z - (0:ℝ))^2) / (2 * 1)) ∂volume) := by
  -- density of G (mean μ', var 1)
  let G : GaussianPDF := { mean := μ', varSq := 1, varSq_pos := by norm_num }
  set D : ℝ → ℝ := fun x => (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((x - μ')^2) / (2 * 1)) with hD
  have hGd : ∀ x, G.density x = D x := by
    intro x; simp only [GaussianPDF.density_eq, hD, G]
  have hDpos : ∀ x, 0 < D x := by
    intro x; rw [hD]; positivity
  -- centered density G0 (mean 0, var 1)
  let G0 : GaussianPDF := { mean := 0, varSq := 1, varSq_pos := by norm_num }
  set D0 : ℝ → ℝ := fun z => (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((z - (0:ℝ))^2) / (2 * 1)) with hD0
  have hG0d : ∀ x, G0.density x = D0 x := by
    intro x; simp only [GaussianPDF.density_eq, hD0, G0]
  have hD0pos : ∀ x, 0 < D0 x := by
    intro x; rw [hD0]; positivity
  -- densities integrate to 1
  have hv_ne : (⟨(1:ℝ), by norm_num⟩ : NNReal) ≠ 0 := by
    intro h
    have : ((⟨(1:ℝ), by norm_num⟩ : NNReal) : ℝ) = 0 := by rw [h]; rfl
    norm_num at this
  have hD_int_one : (∫ x, D x ∂volume) = 1 := by
    have hgr : (fun x => D x) = (fun x => gaussianPDFReal μ' ⟨1, by norm_num⟩ x) := by
      funext x
      rw [← hGd x, GaussianPDF.density_eq_gaussianPDFReal]
    rw [hgr]
    exact integral_gaussianPDFReal_eq_one μ' hv_ne
  have hD0_int_one : (∫ z, D0 z ∂volume) = 1 := by
    have hgr : (fun z => D0 z) = (fun z => gaussianPDFReal 0 ⟨1, by norm_num⟩ z) := by
      funext z
      rw [← hG0d z, GaussianPDF.density_eq_gaussianPDFReal]
    rw [hgr]
    exact integral_gaussianPDFReal_eq_one 0 hv_ne
  set f : ℝ → ℝ := fun x => x ^ i * D x with hf
  have habs_f : ∀ x, |f x| = |x|^i * D x := by
    intro x; rw [hf, abs_mul, abs_pow, abs_of_pos (hDpos x)]
  -- Integrability of x^i * D
  have hint_xi_D : Integrable (fun x => x^i * D x) volume := by
    have h := SublemmaIntegrabilityXPowGaussian G i
    have heq : (fun x : ℝ => x ^ i * G.density x) = (fun x => x^i * D x) := by
      funext x; rw [hGd x]
    rwa [heq] at h
  have hint_f : Integrable f volume := by rw [hf]; exact hint_xi_D
  have hint_absxi_D : Integrable (fun x => |x|^i * D x) volume := by
    have heq : (fun x => |x|^i * D x) = (fun x => |x^i * D x|) := by
      funext x; rw [abs_mul, abs_pow, abs_of_pos (hDpos x)]
    rw [heq]; exact hint_xi_D.abs
  -- Integrability of D itself (i = 0 instance)
  have hint_D : Integrable D volume := by
    have h := SublemmaIntegrabilityXPowGaussian G 0
    have heq : (fun x : ℝ => x ^ (0:ℕ) * G.density x) = D := by
      funext x; rw [hGd x, pow_zero, one_mul]
    rwa [heq] at h
  -- Integrability of |z|^i * D0 z
  have hint_abszi_D0 : Integrable (fun z => |z|^i * D0 z) volume := by
    have h := SublemmaIntegrabilityXPowGaussian G0 i
    have heq : (fun x : ℝ => x ^ i * G0.density x) = (fun x => x^i * D0 x) := by
      funext x; rw [hG0d x]
    rw [heq] at h
    have heq2 : (fun z => |z|^i * D0 z) = (fun z => |z^i * D0 z|) := by
      funext z; rw [abs_mul, abs_pow, abs_of_pos (hD0pos z)]
    rw [heq2]; exact h.abs
  -- Integrability of |x-μ'|^i * D x via translation
  have hint_absxmu_D : Integrable (fun x => |x - μ'|^i * D x) volume := by
    have h := hint_abszi_D0.comp_sub_right μ'
    -- h : Integrable (fun t => |t - μ'|^i * D0 (t - μ')) volume
    have heq : (fun t => |t - μ'|^i * D0 (t - μ')) = (fun x => |x - μ'|^i * D x) := by
      funext t
      congr 1
      rw [hD0, hD]
      congr 1
      norm_num
    rwa [heq] at h
  -- pointwise binomial: |x|^i ≤ 2^6 (|x - μ'|^i + 1)
  have hbino : ∀ x, |x|^i ≤ (2:ℝ)^6 * (|x - μ'|^i + 1) := by
    intro x
    have hb : |x|^i ≤ (2:ℝ)^i * (|x - μ'|^i + |μ'|^i) := by
      have := Lemma29BinomialAbsExpansionBound μ' (x - μ') i
      rwa [show (x - μ') + μ' = x by ring] at this
    have hμi : |μ'|^i ≤ 1 := by
      calc |μ'|^i ≤ 1^i := pow_le_pow_left₀ (abs_nonneg _) hμ' i
        _ = 1 := one_pow i
    have h2i : (2:ℝ)^i ≤ 2^6 := pow_le_pow_right₀ (by norm_num) hi
    have hnn : (0:ℝ) ≤ |x - μ'|^i + |μ'|^i := by positivity
    calc |x|^i ≤ (2:ℝ)^i * (|x - μ'|^i + |μ'|^i) := hb
      _ ≤ (2:ℝ)^6 * (|x - μ'|^i + |μ'|^i) := mul_le_mul_of_nonneg_right h2i hnn
      _ ≤ (2:ℝ)^6 * (|x - μ'|^i + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  -- Step A: |∫_S f| ≤ ∫_S |f|
  have hStepA : |∫ x in S, f x ∂volume| ≤ ∫ x in S, |f x| ∂volume := by
    exact abs_integral_le_integral_abs
  -- Step B: ∫_S |f| ≤ ∫_ℝ |f| = ∫ |x|^i D x
  have hStepB : (∫ x in S, |f x| ∂volume) ≤ ∫ x, |x|^i * D x ∂volume := by
    have h1 : (∫ x in S, |f x| ∂volume) ≤ ∫ x, |f x| ∂volume := by
      apply MeasureTheory.setIntegral_le_integral hint_f.abs
      filter_upwards with x using abs_nonneg _
    have h2 : (∫ x, |f x| ∂volume) = ∫ x, |x|^i * D x ∂volume := by
      apply MeasureTheory.integral_congr_ae; filter_upwards with x using habs_f x
    rw [h2] at h1; exact h1
  -- integrability of the dominating function (already needed)
  have hint_rhs0 : Integrable (fun x => (|x - μ'|^i + 1) * D x) volume := by
    have : (fun x => (|x - μ'|^i + 1) * D x)
         = (fun x => |x - μ'|^i * D x + D x) := by funext x; ring
    rw [this]; exact hint_absxmu_D.add hint_D
  have hint_rhs : Integrable (fun x => (2:ℝ)^6 * ((|x - μ'|^i + 1) * D x)) volume :=
    hint_rhs0.const_mul _
  -- Step C: ∫ |x|^i D x ≤ 2^6 ∫ (|x-μ'|^i + 1) D x
  have hStepC : (∫ x, |x|^i * D x ∂volume)
              ≤ (2:ℝ)^6 * ∫ x, (|x - μ'|^i + 1) * D x ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono hint_absxi_D hint_rhs
    intro x
    have := hbino x
    have hDx := (hDpos x).le
    calc |x|^i * D x ≤ ((2:ℝ)^6 * (|x - μ'|^i + 1)) * D x :=
          mul_le_mul_of_nonneg_right this hDx
      _ = (2:ℝ)^6 * ((|x - μ'|^i + 1) * D x) := by ring
  -- Step D: ∫ (|x-μ'|^i + 1) D x = (∫ |x-μ'|^i D x) + 1
  have hStepD : (∫ x, (|x - μ'|^i + 1) * D x ∂volume)
              = (∫ x, |x - μ'|^i * D x ∂volume) + 1 := by
    have hsplit : (fun x => (|x - μ'|^i + 1) * D x)
                = (fun x => |x - μ'|^i * D x + D x) := by funext x; ring
    rw [show (∫ x, (|x - μ'|^i + 1) * D x ∂volume)
          = ∫ x, (|x - μ'|^i * D x + D x) ∂volume from by rw [hsplit]]
    rw [MeasureTheory.integral_add hint_absxmu_D hint_D, hD_int_one]
  -- Step E (shift): ∫ |x-μ'|^i D x = ∫ |z|^i D0 z
  have hStepE : (∫ x, |x - μ'|^i * D x ∂volume) = ∫ z, |z|^i * D0 z ∂volume := by
    have hkey : (fun z => |(z + μ') - μ'|^i * D (z + μ')) = (fun z => |z|^i * D0 z) := by
      funext z
      have h1 : (z + μ') - μ' = z := by ring
      rw [h1]
      congr 1
      rw [hD, hD0]
      congr 1
      norm_num
    have := MeasureTheory.integral_add_right_eq_self
              (μ := volume) (fun x => |x - μ'|^i * D x) μ'
    rw [← this]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    exact congrFun hkey z
  -- Step F: ∫ |z|^i D0 z ≤ 1 + M6   (since |z|^i ≤ 1 + |z|^6 for i ≤ 6)
  have hStepF : (∫ z, |z|^i * D0 z ∂volume)
              ≤ 1 + ∫ z, |z|^6 * D0 z ∂volume := by
    have hint_abszt_D0 : Integrable (fun z => |z|^6 * D0 z) volume := by
      have h := SublemmaIntegrabilityXPowGaussian G0 6
      have heq : (fun x : ℝ => x ^ (6:ℕ) * G0.density x) = (fun x => x^6 * D0 x) := by
        funext x; rw [hG0d x]
      rw [heq] at h
      have heq2 : (fun z => |z|^6 * D0 z) = (fun z => |z^6 * D0 z|) := by
        funext z; rw [abs_mul, abs_pow, abs_of_pos (hD0pos z)]
      rw [heq2]; exact h.abs
    have hint_D0 : Integrable D0 volume := by
      have h := SublemmaIntegrabilityXPowGaussian G0 0
      have heq : (fun x : ℝ => x ^ (0:ℕ) * G0.density x) = D0 := by
        funext x; rw [hG0d x, pow_zero, one_mul]
      rwa [heq] at h
    have hint_rhsF : Integrable (fun z => (1 + |z|^6) * D0 z) volume := by
      have : (fun z => (1 + |z|^6) * D0 z) = (fun z => D0 z + |z|^6 * D0 z) := by
        funext z; ring
      rw [this]; exact hint_D0.add hint_abszt_D0
    have hptF : ∀ z, |z|^i * D0 z ≤ (1 + |z|^6) * D0 z := by
      intro z
      have hbz : |z|^i ≤ 1 + |z|^6 := by
        rcases le_total |z| 1 with hz | hz
        · have hle1 : |z|^i ≤ 1 := by
            calc |z|^i ≤ 1^i := pow_le_pow_left₀ (abs_nonneg _) hz i
              _ = 1 := one_pow i
          have hnn6 : (0:ℝ) ≤ |z|^6 := by positivity
          linarith
        · have hle6 : |z|^i ≤ |z|^6 := pow_le_pow_right₀ hz hi
          linarith
      exact mul_le_mul_of_nonneg_right hbz (hD0pos z).le
    calc (∫ z, |z|^i * D0 z ∂volume)
          ≤ ∫ z, (1 + |z|^6) * D0 z ∂volume :=
            MeasureTheory.integral_mono hint_abszi_D0 hint_rhsF hptF
      _ = ∫ z, (D0 z + |z|^6 * D0 z) ∂volume := by
            apply MeasureTheory.integral_congr_ae; filter_upwards with z; ring
      _ = (∫ z, D0 z ∂volume) + ∫ z, |z|^6 * D0 z ∂volume :=
            MeasureTheory.integral_add hint_D0 hint_abszt_D0
      _ = 1 + ∫ z, |z|^6 * D0 z ∂volume := by rw [hD0_int_one]
  -- Combine
  have hM6_eq : (∫ z, |z|^6 * D0 z ∂volume)
              = ∫ z : ℝ, |z|^6 * (1 / Real.sqrt (2 * Real.pi * 1))
                  * Real.exp (-((z - (0:ℝ))^2) / (2 * 1)) ∂volume := by
    apply MeasureTheory.integral_congr_ae; filter_upwards with z; simp only [hD0]; ring
  -- final assembly
  have hfinal : |∫ x in S, f x ∂volume|
              ≤ (2:ℝ)^6 * (2 + ∫ z, |z|^6 * D0 z ∂volume) := by
    calc |∫ x in S, f x ∂volume| ≤ ∫ x in S, |f x| ∂volume := hStepA
      _ ≤ ∫ x, |x|^i * D x ∂volume := hStepB
      _ ≤ (2:ℝ)^6 * ∫ x, (|x - μ'|^i + 1) * D x ∂volume := hStepC
      _ = (2:ℝ)^6 * ((∫ x, |x - μ'|^i * D x ∂volume) + 1) := by rw [hStepD]
      _ = (2:ℝ)^6 * ((∫ z, |z|^i * D0 z ∂volume) + 1) := by rw [hStepE]
      _ ≤ (2:ℝ)^6 * ((1 + ∫ z, |z|^6 * D0 z ∂volume) + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hStepF]
      _ = (2:ℝ)^6 * (2 + ∫ z, |z|^6 * D0 z ∂volume) := by ring
  -- rewrite goal integrand to f and M6
  have hgoal_lhs : (∫ x in S, x ^ i * (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((x - μ')^2) / (2 * 1)) ∂volume) = ∫ x in S, f x ∂volume := by
    apply MeasureTheory.setIntegral_congr_ae hS; filter_upwards with x _
    simp only [hf, hD]; ring
  rw [hgoal_lhs, ← hM6_eq]
  exact hfinal

theorem Lemma29TailMomentVarLeTwo :
    ∃ K_29' : ℝ, 0 < K_29' ∧
      ∀ (μ σSq ε : ℝ) (i : ℕ),
        0 < ε → ε ≤ 1 → 0 < σSq → σSq ≤ 2 → |μ| ≤ 1 / ε → i ≤ 6 →
        |∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
                  * Real.exp (-((x - μ)^2) / (2 * σSq)) ∂MeasureTheory.volume|
        ≤ K_29' * (1 / ε ^ (i + 6)) * Real.exp (-1 / (4 * ε ^ 2)) := by
  obtain ⟨K29, hK29_pos, hK29⟩ := Lemma29Assembly
  -- The absolute Case-B2 constant.
  set M6 : ℝ := ∫ z : ℝ, |z|^6 * (1 / Real.sqrt (2 * Real.pi * 1))
              * Real.exp (-((z - (0:ℝ))^2) / (2 * 1)) ∂volume with hM6
  have hM6_nonneg : 0 ≤ M6 := by
    rw [hM6]
    apply MeasureTheory.integral_nonneg
    intro z; positivity
  set CB2 : ℝ := (2:ℝ)^6 * (2 + M6) with hCB2
  have hCB2_nonneg : 0 ≤ CB2 := by rw [hCB2]; positivity
  set Kfinal : ℝ := K29 + 1 + 8 * CB2 * Real.exp (1/2) with hKfinal
  have hKfinal_pos : 0 < Kfinal := by rw [hKfinal]; positivity
  refine ⟨Kfinal, hKfinal_pos, ?_⟩
  intro μ σSq ε i hε_pos hε_le1 hσSq_pos hσSq_le2 hμ_bound hi_le6
  -- abbreviations
  have hε_inv_ge1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε_pos]; linarith
  have hε_sq_pos : 0 < ε ^ 2 := by positivity
  have hExp_pos : 0 < Real.exp (-1 / (4 * ε ^ 2)) := Real.exp_pos _
  -- (1/ε)^(i+6) ≥ (1/ε)^i  and  ≥ 1
  have h_inv_pow_eq : (1 : ℝ) / ε ^ (i + 6) = (1 / ε) ^ (i + 6) := by rw [div_pow, one_pow]
  set E2 : ℝ := Real.exp (-1 / (4 * ε ^ 2)) with hE2
  have hE2_pos : 0 < E2 := Real.exp_pos _
  by_cases hσSq_le1 : σSq ≤ 1
  · -- Case A: σSq ≤ 1.  Use Lemma29Assembly directly.
    have hA := hK29 μ σSq ε i hε_pos hε_le1 hσSq_pos hσSq_le1 hμ_bound hi_le6
    -- hA : |∫ ...| ≤ K29 * (1 / ε^i) * exp(-1/(2 ε²))
    -- Bound the RHS by Kfinal * (1/ε^(i+6)) * exp(-1/(4 ε²)).
    refine hA.trans ?_
    -- exp(-1/(2ε²)) ≤ exp(-1/(4ε²))
    have hexp_le : Real.exp (-1 / (2 * ε ^ 2)) ≤ E2 := by
      rw [hE2]; apply Real.exp_le_exp.mpr
      have h1 : -1 / (2 * ε^2) = -(1 / (2 * ε^2)) := by ring
      have h2 : -1 / (4 * ε^2) = -(1 / (4 * ε^2)) := by ring
      rw [h1, h2]; apply neg_le_neg
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    -- 1/ε^i ≤ 1/ε^(i+6)
    have h_pow_le : (1 : ℝ) / ε ^ i ≤ 1 / ε ^ (i + 6) := by
      rw [show (1 : ℝ) / ε ^ i = (1/ε)^i by rw [div_pow, one_pow],
          h_inv_pow_eq]
      exact pow_le_pow_right₀ hε_inv_ge1 (by omega)
    have hK29nn : 0 ≤ K29 := hK29_pos.le
    have hstep1 : K29 * (1 / ε ^ i) * Real.exp (-1 / (2 * ε ^ 2))
                ≤ K29 * (1 / ε ^ (i+6)) * E2 := by
      have hnn1 : 0 ≤ K29 * (1 / ε ^ i) := by
        apply mul_nonneg hK29nn; positivity
      have hnn2 : 0 ≤ (1 : ℝ) / ε ^ (i+6) := by positivity
      calc K29 * (1 / ε ^ i) * Real.exp (-1 / (2 * ε ^ 2))
            ≤ K29 * (1 / ε ^ i) * E2 := by
              apply mul_le_mul_of_nonneg_left hexp_le hnn1
        _ ≤ K29 * (1 / ε ^ (i+6)) * E2 := by
              apply mul_le_mul_of_nonneg_right _ hE2_pos.le
              apply mul_le_mul_of_nonneg_left h_pow_le hK29nn
    refine hstep1.trans ?_
    apply mul_le_mul_of_nonneg_right _ hE2_pos.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hKfinal]; nlinarith [hCB2_nonneg, Real.exp_pos (1/2 : ℝ), hM6_nonneg]
  · -- Case B: 1 < σSq ≤ 2.
    push_neg at hσSq_le1
    set s := Real.sqrt σSq with hs
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hσSq_pos
    have hs_sq : s ^ 2 = σSq := Real.sq_sqrt hσSq_pos.le
    have hs_gt1 : 1 < s := by
      rw [hs]; rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) hσSq_le1
    have hs_le_sqrt2 : s ≤ Real.sqrt 2 := by
      rw [hs]; exact Real.sqrt_le_sqrt hσSq_le2
    -- reduce via scaling_cov
    rw [scaling_cov μ σSq ε i hσSq_pos hε_pos]
    set μ' : ℝ := μ / s with hμ'
    set ε' : ℝ := ε * s with hε'
    have hε'_pos : 0 < ε' := by rw [hε']; positivity
    have hμ'_bound : |μ'| ≤ 1 / ε' := by
      rw [hμ', hε', abs_div, abs_of_pos hs_pos]
      rw [div_le_div_iff₀ hs_pos (by positivity)]
      have hmb : |μ| ≤ 1 / ε := hμ_bound
      rw [le_div_iff₀ hε_pos] at hmb
      nlinarith [hs_pos.le]
    -- s^i bound: s ≤ √2, so s^i ≤ (√2)^i ≤ (√2)^6 = 8
    have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
    have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have hsi_le8 : s ^ i ≤ 8 := by
      calc s ^ i ≤ (Real.sqrt 2) ^ i := pow_le_pow_left₀ hs_pos.le hs_le_sqrt2 i
        _ ≤ (Real.sqrt 2) ^ 6 := pow_le_pow_right₀ hsqrt2_ge1 hi_le6
        _ = 8 := by
              have : (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
              rw [this, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have hsi_nonneg : 0 ≤ s ^ i := by positivity
    -- name the reduced inner integral I'
    set I' : ℝ := ∫ x in {x : ℝ | 2 / ε' ≤ |x|},
          x ^ i * (1 / Real.sqrt (2 * Real.pi * 1))
                * Real.exp (-((x - μ')^2) / (2 * 1)) ∂volume with hI'
    -- The goal currently has √σSq in place of s; fold it back.
    rw [show (Real.sqrt σSq) = s from rfl]
    -- |s^i * I'| = s^i * |I'|
    rw [abs_mul, abs_of_nonneg hsi_nonneg]
    by_cases hε'_le1 : ε' ≤ 1
    · -- Case B1: ε' ≤ 1.  Apply Lemma29Assembly with variance 1, mean μ', threshold scale ε'.
      have hB := hK29 μ' 1 ε' i hε'_pos hε'_le1 (by norm_num) (by norm_num)
                    hμ'_bound hi_le6
      -- hB : |I'| ≤ K29 * (1 / ε'^i) * exp(-1/(2 ε'²))
      rw [← hI'] at hB
      -- s^i * |I'| ≤ s^i * (K29 * (1/ε'^i) * exp(-1/(2ε'²)))
      have hstep : s ^ i * |I'|
                 ≤ s ^ i * (K29 * (1 / ε' ^ i) * Real.exp (-1 / (2 * ε' ^ 2))) := by
        apply mul_le_mul_of_nonneg_left hB hsi_nonneg
      refine hstep.trans ?_
      -- Rewrite s^i / ε'^i = 1/ε^i:  s^i * (1/ε'^i) = s^i / (ε^i * s^i) = 1/ε^i
      have hε'_pow : ε' ^ i = ε ^ i * s ^ i := by rw [hε']; rw [mul_pow]
      have hsi_pos : 0 < s ^ i := by positivity
      have hεi_pos : 0 < ε ^ i := by positivity
      have h_si_div : s ^ i * (1 / ε' ^ i) = 1 / ε ^ i := by
        rw [hε'_pow]
        field_simp
      -- exp(-1/(2 ε'²)) ≤ exp(-1/(4 ε²)):  ε'² = ε² σSq ≤ 2 ε²
      have hε'_sq : ε' ^ 2 = ε ^ 2 * σSq := by rw [hε', mul_pow, hs_sq]
      have hexpB : Real.exp (-1 / (2 * ε' ^ 2)) ≤ E2 := by
        rw [hE2]; apply Real.exp_le_exp.mpr
        rw [hε'_sq]
        have h1 : -1 / (2 * (ε^2 * σSq)) = -(1 / (2 * (ε^2 * σSq))) := by ring
        have h2 : -1 / (4 * ε^2) = -(1 / (4 * ε^2)) := by ring
        rw [h1, h2]; apply neg_le_neg
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hσSq_le2, hε_sq_pos]
      -- assemble
      have hbound1 : 1 / ε ^ i ≤ 1 / ε ^ (i + 6) := by
        rw [show (1 : ℝ) / ε ^ i = (1/ε)^i by rw [div_pow, one_pow], h_inv_pow_eq]
        exact pow_le_pow_right₀ hε_inv_ge1 (by omega)
      have hK29nn : 0 ≤ K29 := hK29_pos.le
      calc s ^ i * (K29 * (1 / ε' ^ i) * Real.exp (-1 / (2 * ε' ^ 2)))
            = K29 * (s ^ i * (1 / ε' ^ i)) * Real.exp (-1 / (2 * ε' ^ 2)) := by ring
        _ = K29 * (1 / ε ^ i) * Real.exp (-1 / (2 * ε' ^ 2)) := by rw [h_si_div]
        _ ≤ K29 * (1 / ε ^ i) * E2 := by
              apply mul_le_mul_of_nonneg_left hexpB
              apply mul_nonneg hK29nn; positivity
        _ ≤ K29 * (1 / ε ^ (i + 6)) * E2 := by
              apply mul_le_mul_of_nonneg_right _ hE2_pos.le
              apply mul_le_mul_of_nonneg_left hbound1 hK29nn
        _ ≤ Kfinal * (1 / ε ^ (i + 6)) * E2 := by
              apply mul_le_mul_of_nonneg_right _ hE2_pos.le
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [hKfinal]; nlinarith [hCB2_nonneg, Real.exp_pos (1/2 : ℝ)]
    · -- Case B2: ε' > 1.  Then |μ'| ≤ 1/ε' < 1, so use caseB2_const_bound.
      push_neg at hε'_le1
      have hμ'_le1 : |μ'| ≤ 1 := by
        refine hμ'_bound.trans ?_
        rw [div_le_one hε'_pos]; linarith
      have hmeasS' : MeasurableSet {x : ℝ | 2 / ε' ≤ |x|} := by
        have heq : {x : ℝ | 2 / ε' ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' (Set.Ici (2/ε')) := rfl
        rw [heq]; exact measurable_norm measurableSet_Ici
      have hB2 := caseB2_const_bound μ' i hi_le6 hμ'_le1 {x : ℝ | 2 / ε' ≤ |x|} hmeasS'
      rw [← hM6, ← hI', ← hCB2] at hB2
      -- s^i * |I'| ≤ 8 * CB2
      have hstep : s ^ i * |I'| ≤ 8 * CB2 := by
        calc s ^ i * |I'| ≤ s ^ i * CB2 := by
                apply mul_le_mul_of_nonneg_left hB2 hsi_nonneg
          _ ≤ 8 * CB2 := by apply mul_le_mul_of_nonneg_right hsi_le8 hCB2_nonneg
      refine hstep.trans ?_
      -- 8 * CB2 ≤ Kfinal * (1/ε^(i+6)) * E2 using exp(-1/2) ≤ E2 and 1 ≤ 1/ε^(i+6)
      -- ε' = ε s > 1, s ≤ √2 ⇒ ε > 1/√2 ⇒ ε² > 1/2 ⇒ 1/(4ε²) < 1/2 ⇒ exp(-1/2) ≤ E2
      -- ε' = ε s > 1, s ≤ √2 ⇒ ε s > 1 and (ε s)² ≤ ε² · 2 ⇒ 1 < ε s ≤ ... ⇒ ε² > 1/2
      have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hε_sq_gt : ε ^ 2 > 1 / 2 := by
        -- (ε s)^2 = ε² σSq ≤ ε² · 2, and (ε s)^2 > 1, so 2 ε² > 1
        have hes_sq : (ε * s) ^ 2 = ε ^ 2 * σSq := by rw [mul_pow, hs_sq]
        have hes_gt1 : (ε * s) ^ 2 > 1 := by
          have : (1:ℝ) < ε * s := hε'_le1
          nlinarith [hε'_pos]
        rw [hes_sq] at hes_gt1
        nlinarith [hσSq_le2, hε_sq_pos]
      have hexp_half : Real.exp (-1/2 : ℝ) ≤ E2 := by
        rw [hE2]; apply Real.exp_le_exp.mpr
        have h1 : (-1 : ℝ)/2 = -(1/2) := by ring
        have h2 : -1 / (4 * ε^2) = -(1 / (4 * ε^2)) := by ring
        rw [h1, h2]; apply neg_le_neg
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith [hε_sq_gt]
      have h_inv_ge1 : (1 : ℝ) ≤ 1 / ε ^ (i + 6) := by
        rw [le_div_iff₀ (by positivity)]
        rw [one_mul]
        calc ε ^ (i + 6) ≤ 1 ^ (i + 6) := by
              apply pow_le_pow_left₀ hε_pos.le hε_le1
          _ = 1 := one_pow _
      calc (8 : ℝ) * CB2
            = (8 * CB2 * Real.exp (1/2)) * Real.exp (-1/2) := by
              rw [mul_assoc, ← Real.exp_add]; norm_num
        _ ≤ Kfinal * Real.exp (-1/2) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              rw [hKfinal]; nlinarith [hK29_pos, hCB2_nonneg, Real.exp_pos (1/2 : ℝ)]
        _ ≤ Kfinal * E2 := by apply mul_le_mul_of_nonneg_left hexp_half hKfinal_pos.le
        _ ≤ Kfinal * (1 / ε ^ (i + 6)) * E2 := by
              rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left _ hKfinal_pos.le
              calc E2 = 1 * E2 := (one_mul _).symm
                _ ≤ (1 / ε ^ (i + 6)) * E2 := by
                      apply mul_le_mul_of_nonneg_right h_inv_ge1 hE2_pos.le

end Workspace.ProofLemmas
