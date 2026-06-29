import Mathlib
import Workspace.Types.L1AndTVDistance

open MeasureTheory Real Set
open scoped ENNReal NNReal

set_option maxHeartbeats 4000000

namespace PinskerDPIProof

/-! ### The core continuous log-sum inequality

For nonneg `f, g` and a measurable set `S` with `∫_S g > 0` and `g > 0` a.e.,
we have `p · log(p/q) ≤ ∫_S f · log(f/g)` where `p = ∫_S f`, `q = ∫_S g`.

Proof via `InformationTheory.mul_log_le_toReal_klDiv` applied to the measures
  `μ := (volume.restrict S).withDensity (ofReal ∘ f)` (so `μ.real univ = p`)
  `ν := (volume.restrict S).withDensity (ofReal ∘ g)` (so `ν.real univ = q`). -/

private lemma log_sum_on_set
    {f g : ℝ → ℝ} {S : Set ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_int_S : IntegrableOn f S volume)
    (hg_int_S : IntegrableOn g S volume)
    (hg_pos_ae : ∀ᵐ x ∂volume, 0 < g x)
    (hflogfg_int_S : IntegrableOn (fun x => f x * Real.log (f x / g x)) S volume)
    (hS : MeasurableSet S)
    (hq_pos : 0 < ∫ x in S, g x ∂volume) :
    (∫ x in S, f x ∂volume) *
      Real.log ((∫ x in S, f x ∂volume) / (∫ x in S, g x ∂volume))
    ≤ ∫ x in S, f x * Real.log (f x / g x) ∂volume := by
  set p := ∫ x in S, f x ∂volume with hp_def
  set q := ∫ x in S, g x ∂volume with hq_def
  -- p ≥ 0
  have hp_nn : 0 ≤ p := by
    rw [hp_def]
    exact integral_nonneg fun x => hf_nn x
  -- Case split on p = 0 or p > 0
  rcases eq_or_lt_of_le hp_nn with hp_eq_zero | hp_pos
  · -- Case p = 0
    -- Then f = 0 a.e. on S
    have hf_zero_ae : f =ᵐ[volume.restrict S] 0 := by
      have h_int_eq : ∫ x in S, f x ∂volume = 0 := by rw [← hp_def]; linarith
      rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hf_nn) hf_int_S] at h_int_eq
      exact h_int_eq
    -- So both sides are 0
    have h_lhs : p * Real.log (p / q) = 0 := by rw [← hp_eq_zero]; ring
    have h_rhs : ∫ x in S, f x * Real.log (f x / g x) ∂volume = 0 := by
      rw [show ∫ x in S, f x * Real.log (f x / g x) ∂volume =
          ∫ x, f x * Real.log (f x / g x) ∂(volume.restrict S) from rfl]
      apply integral_eq_zero_of_ae
      filter_upwards [hf_zero_ae] with x hx
      simp [hx]
    rw [h_lhs, h_rhs]
  · -- Case p > 0
    -- Pointwise inequality: for x with g(x) > 0:
    -- f(x) * log(f(x)/g(x)) ≥ f(x) * log(p/q) + f(x) - g(x) * (p/q)
    have hpq_pos : 0 < p / q := div_pos hp_pos hq_pos
    have h_pointwise : ∀ᵐ x ∂(volume.restrict S),
        f x * Real.log (p / q) + f x - g x * (p / q) ≤ f x * Real.log (f x / g x) := by
      have hg_pos_S : ∀ᵐ x ∂(volume.restrict S), 0 < g x := ae_restrict_of_ae hg_pos_ae
      filter_upwards [hg_pos_S] with x hgx
      -- Case on f x = 0 vs f x > 0
      rcases eq_or_lt_of_le (hf_nn x) with hfx_eq | hfx_pos
      · -- f x = 0
        rw [← hfx_eq]
        simp
        have : 0 ≤ g x * (p / q) := mul_nonneg (le_of_lt hgx) (le_of_lt hpq_pos)
        linarith
      · -- f x > 0
        -- log(f/g) - log(p/q) = log((f/g) / (p/q)) = log(f*q / (g*p)) ≥ 1 - g*p/(f*q)
        -- So f * (log(f/g) - log(p/q)) ≥ f * (1 - g*p/(f*q)) = f - g*p/q
        have hfgx_pos : 0 < f x / g x := div_pos hfx_pos hgx
        have h_ratio_pos : 0 < (f x / g x) / (p / q) :=
          div_pos hfgx_pos hpq_pos
        have h_log_ineq : 1 - ((f x / g x) / (p / q))⁻¹ ≤
            Real.log ((f x / g x) / (p / q)) :=
          Real.one_sub_inv_le_log_of_pos h_ratio_pos
        -- (f/g)/(p/q) = f*q/(g*p)
        -- Its inverse is g*p/(f*q)
        -- log((f/g)/(p/q)) = log(f/g) - log(p/q)
        have h_log_split : Real.log ((f x / g x) / (p / q)) =
            Real.log (f x / g x) - Real.log (p / q) := by
          rw [Real.log_div (ne_of_gt hfgx_pos) (ne_of_gt hpq_pos)]
        rw [h_log_split] at h_log_ineq
        -- ((f/g)/(p/q))⁻¹ = g*p/(f*q)
        have hgx_ne : g x ≠ 0 := ne_of_gt hgx
        have hfx_ne : f x ≠ 0 := ne_of_gt hfx_pos
        have hp_ne : p ≠ 0 := ne_of_gt hp_pos
        have hq_ne : q ≠ 0 := ne_of_gt hq_pos
        have h_inv : ((f x / g x) / (p / q))⁻¹ = g x * p / (f x * q) := by
          field_simp
        rw [h_inv] at h_log_ineq
        -- Now h_log_ineq: 1 - g*p/(f*q) ≤ log(f/g) - log(p/q)
        -- Multiply by f (positive):
        -- f - f*g*p/(f*q) ≤ f * (log(f/g) - log(p/q))
        -- f - g*p/q ≤ f*log(f/g) - f*log(p/q)
        -- So f*log(p/q) + f - g*p/q ≤ f*log(f/g)  ✓
        have h_mul := (mul_le_mul_of_nonneg_left h_log_ineq (le_of_lt hfx_pos))
        -- h_mul : f * (1 - g*p/(f*q)) ≤ f * (log(f/g) - log(p/q))
        have h_lhs_simp : f x * (1 - g x * p / (f x * q)) = f x - g x * (p / q) := by
          field_simp
        have h_rhs_simp : f x * (Real.log (f x / g x) - Real.log (p / q)) =
            f x * Real.log (f x / g x) - f x * Real.log (p / q) := by ring
        rw [h_lhs_simp, h_rhs_simp] at h_mul
        linarith
    -- Integrate the pointwise inequality
    -- LHS integral: ∫_S (f * log(p/q) + f - g * (p/q)) = p*log(p/q) + p - q*(p/q) = p*log(p/q)
    have hf_logpq_int : IntegrableOn (fun x => f x * Real.log (p / q)) S volume := by
      simpa [mul_comm] using hf_int_S.const_mul (Real.log (p / q))
    have hg_pq_int : IntegrableOn (fun x => g x * (p / q)) S volume := by
      simpa [mul_comm] using hg_int_S.const_mul (p / q)
    have h_sum_int : IntegrableOn
        (fun x => f x * Real.log (p / q) + f x) S volume := hf_logpq_int.add hf_int_S
    have h_lhs_integrable : IntegrableOn
        (fun x => f x * Real.log (p / q) + f x - g x * (p / q)) S volume :=
      h_sum_int.sub hg_pq_int
    have h_lhs_int : ∫ x in S, (f x * Real.log (p / q) + f x - g x * (p / q)) ∂volume
        = p * Real.log (p / q) := by
      rw [integral_sub h_sum_int hg_pq_int,
          integral_add hf_logpq_int hf_int_S]
      have e1 : ∫ x in S, f x * Real.log (p / q) ∂volume = p * Real.log (p / q) := by
        rw [integral_mul_const]
      have e2 : ∫ x in S, g x * (p / q) ∂volume = q * (p / q) := by
        rw [integral_mul_const]
      rw [e1, e2]
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      field_simp; rw [← hp_def]; ring
    have h_mono := setIntegral_mono_ae_restrict h_lhs_integrable hflogfg_int_S h_pointwise
    rw [h_lhs_int] at h_mono
    exact h_mono

end PinskerDPIProof

open PinskerDPIProof

theorem PinskerDataProcessingInequality :
    ∀ (f g : ℝ → ℝ) (A : Set ℝ),
      Measurable f → Measurable g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      Integrable f volume → Integrable g volume →
      (∫ x, f x ∂volume) = 1 → (∫ x, g x ∂volume) = 1 →
      (∀ᵐ x ∂volume, 0 < g x) →
      Integrable (fun x => f x * Real.log (f x / g x)) volume →
      MeasurableSet A →
      let p := ∫ x in A, f x ∂volume
      let q := ∫ x in A, g x ∂volume
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        ∫ x, f x * Real.log (f x / g x) ∂volume := by
  intro f g A hfm hgm hf_nn hg_nn hf_int hg_int hf_total hg_total hg_pos_ae
        hflogfg_int hA
  simp only
  set p := ∫ x in A, f x ∂volume with hp_def
  set q := ∫ x in A, g x ∂volume with hq_def
  -- Compute 1 - p = ∫_{Aᶜ} f, 1 - q = ∫_{Aᶜ} g.
  have hp_aux : 1 - p = ∫ x in Aᶜ, f x ∂volume := by
    have h := integral_add_compl hA hf_int
    rw [hp_def]
    linarith [h.trans hf_total]
  have hq_aux : 1 - q = ∫ x in Aᶜ, g x ∂volume := by
    have h := integral_add_compl hA hg_int
    rw [hq_def]
    linarith [h.trans hg_total]
  -- Also: q > 0 since g > 0 a.e. and ∫_A g = something, but only if vol(A) > 0.
  -- In general one of q, 1-q can be zero. Handle by cases.
  by_cases hq : 0 < q
  · by_cases h1q : 0 < 1 - q
    · -- both q > 0 and 1 - q > 0
      have hf_intOn_A : IntegrableOn f A volume := hf_int.integrableOn
      have hg_intOn_A : IntegrableOn g A volume := hg_int.integrableOn
      have hflogfg_intOn_A : IntegrableOn (fun x => f x * Real.log (f x / g x)) A volume :=
        hflogfg_int.integrableOn
      have hf_intOn_Ac : IntegrableOn f Aᶜ volume := hf_int.integrableOn
      have hg_intOn_Ac : IntegrableOn g Aᶜ volume := hg_int.integrableOn
      have hflogfg_intOn_Ac : IntegrableOn (fun x => f x * Real.log (f x / g x)) Aᶜ volume :=
        hflogfg_int.integrableOn
      have hAc : MeasurableSet Aᶜ := hA.compl
      have key_A : p * Real.log (p / q) ≤ ∫ x in A, f x * Real.log (f x / g x) ∂volume := by
        have h := log_sum_on_set hfm hgm hf_nn hg_nn hf_intOn_A hg_intOn_A hg_pos_ae
          hflogfg_intOn_A hA hq
        rw [← hp_def, ← hq_def] at h
        exact h
      have key_Ac : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
          ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume := by
        have h := log_sum_on_set hfm hgm hf_nn hg_nn hf_intOn_Ac hg_intOn_Ac hg_pos_ae
          hflogfg_intOn_Ac hAc (by rw [← hq_aux]; exact h1q)
        rw [← hp_aux, ← hq_aux] at h
        exact h
      have h_split : ∫ x, f x * Real.log (f x / g x) ∂volume =
          (∫ x in A, f x * Real.log (f x / g x) ∂volume) +
          ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume :=
        (integral_add_compl hA hflogfg_int).symm
      linarith
    · -- 1 - q ≤ 0
      have h1q_nn : 0 ≤ 1 - q := by
        have hq_le_1 : q ≤ 1 := by
          rw [hq_def]
          have h := integral_add_compl hA hg_int
          have hAcq_nn : 0 ≤ ∫ x in Aᶜ, g x ∂volume :=
            integral_nonneg fun x => hg_nn x
          linarith [h.trans hg_total]
        linarith
      have h1q_zero : 1 - q = 0 := le_antisymm (not_lt.mp h1q) h1q_nn
      -- 1 - q = 0 means ∫_{Aᶜ} g = 0; combined with g > 0 a.e., vol(Aᶜ) = 0.
      have h_int_Ac_g : ∫ x in Aᶜ, g x ∂volume = 0 := by linarith [hq_aux]
      have hg_zero_ae_Ac : g =ᵐ[volume.restrict Aᶜ] 0 := by
        rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg_nn) hg_int.integrableOn] at h_int_Ac_g
        exact h_int_Ac_g
      -- Combined with g > 0 a.e., vol(Aᶜ) = 0.
      have hAc_vol_zero : volume Aᶜ = 0 := by
        have h : ∀ᵐ x ∂volume.restrict Aᶜ, 0 < g x := ae_restrict_of_ae hg_pos_ae
        have h2 : ∀ᵐ x ∂volume.restrict Aᶜ, g x = 0 := hg_zero_ae_Ac
        have h3 : ∀ᵐ x ∂volume.restrict Aᶜ, False := by
          filter_upwards [h, h2] with x hpos hzero
          linarith
        -- A measure under which False holds a.e. must be 0.
        have := (ae_iff (μ := volume.restrict Aᶜ) (p := fun _ => False)).mp h3
        simp at this
        exact this
      have hAc_vol_zero' : volume.restrict Aᶜ = 0 := by
        rw [Measure.restrict_eq_zero]; exact hAc_vol_zero
      -- Therefore 1 - p = ∫_{Aᶜ} f = 0 as well.
      have h1p_zero : 1 - p = 0 := by
        rw [hp_aux]
        rw [show (fun x => f x) = fun x => f x by rfl]
        rw [show ∫ x in Aᶜ, f x ∂volume = ∫ x, f x ∂(volume.restrict Aᶜ) from rfl]
        rw [hAc_vol_zero']
        simp
      have hp_eq : p = 1 := by linarith
      have hq_eq : q = 1 := by linarith
      -- The LHS becomes 1 * log(1/1) + 0 * log(0/0) = 0.
      rw [hp_eq, hq_eq]
      simp
      -- Need: 0 ≤ ∫ f * log(f/g). This is ∫_A only (since vol(Aᶜ) = 0).
      -- And ∫_A f * log(f/g) is exactly the KL divergence which is ≥ 0.
      -- For now, use log_sum_on_set on A.
      have key_A : (1 : ℝ) * Real.log ((1 : ℝ) / (1 : ℝ)) ≤
          ∫ x in A, f x * Real.log (f x / g x) ∂volume := by
        have := log_sum_on_set hfm hgm hf_nn hg_nn hf_int.integrableOn hg_int.integrableOn
          hg_pos_ae hflogfg_int.integrableOn hA (by rw [← hq_def, hq_eq]; norm_num)
        rw [← hp_def, ← hq_def, hp_eq, hq_eq] at this
        exact this
      have h_int_split : ∫ x, f x * Real.log (f x / g x) ∂volume =
          ∫ x in A, f x * Real.log (f x / g x) ∂volume := by
        have h := integral_add_compl hA hflogfg_int
        have h2 : ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume = 0 := by
          rw [show ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume =
            ∫ x, f x * Real.log (f x / g x) ∂(volume.restrict Aᶜ) from rfl]
          rw [hAc_vol_zero']; simp
        linarith
      rw [h_int_split]
      simp at key_A
      exact key_A
  · -- q ≤ 0
    have hq_nn : 0 ≤ q := by
      rw [hq_def]; exact integral_nonneg fun x => hg_nn x
    have hq_zero : q = 0 := le_antisymm (not_lt.mp hq) hq_nn
    -- Similar to above, but on A: vol(A) = 0, so p = 0.
    have hg_zero_ae_A : g =ᵐ[volume.restrict A] 0 := by
      have : ∫ x in A, g x ∂volume = 0 := by rw [← hq_def]; exact hq_zero
      rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg_nn) hg_int.integrableOn] at this
      exact this
    have hA_vol_zero : volume A = 0 := by
      have h : ∀ᵐ x ∂volume.restrict A, 0 < g x := ae_restrict_of_ae hg_pos_ae
      have h2 : ∀ᵐ x ∂volume.restrict A, g x = 0 := hg_zero_ae_A
      have h3 : ∀ᵐ x ∂volume.restrict A, False := by
        filter_upwards [h, h2] with x hpos hzero
        linarith
      have := (ae_iff (μ := volume.restrict A) (p := fun _ => False)).mp h3
      simp at this
      exact this
    have hA_vol_zero' : volume.restrict A = 0 := by
      rw [Measure.restrict_eq_zero]; exact hA_vol_zero
    have hp_zero : p = 0 := by
      rw [hp_def, show ∫ x in A, f x ∂volume = ∫ x, f x ∂(volume.restrict A) from rfl]
      rw [hA_vol_zero']; simp
    have h1p_eq : (1 - p) = 1 := by linarith
    have h1q_eq : (1 - q) = 1 := by linarith
    rw [h1p_eq, h1q_eq, hp_zero, hq_zero]
    simp
    -- Need 0 ≤ ∫ f * log(f/g) = ∫_{Aᶜ} f * log(f/g)
    have hAc : MeasurableSet Aᶜ := hA.compl
    have key_Ac : (1 : ℝ) * Real.log ((1 : ℝ) / (1 : ℝ)) ≤
        ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume := by
      have h_q_Ac_pos : 0 < ∫ x in Aᶜ, g x ∂volume := by
        rw [← hq_aux, h1q_eq]; norm_num
      have := log_sum_on_set hfm hgm hf_nn hg_nn hf_int.integrableOn hg_int.integrableOn
        hg_pos_ae hflogfg_int.integrableOn hAc h_q_Ac_pos
      rw [← hp_aux, ← hq_aux, h1p_eq, h1q_eq] at this
      exact this
    have h_int_split : ∫ x, f x * Real.log (f x / g x) ∂volume =
        ∫ x in Aᶜ, f x * Real.log (f x / g x) ∂volume := by
      have h := integral_add_compl hA hflogfg_int
      have h2 : ∫ x in A, f x * Real.log (f x / g x) ∂volume = 0 := by
        rw [show ∫ x in A, f x * Real.log (f x / g x) ∂volume =
          ∫ x, f x * Real.log (f x / g x) ∂(volume.restrict A) from rfl]
        rw [hA_vol_zero']; simp
      linarith
    rw [h_int_split]
    simp at key_Ac
    exact key_Ac
