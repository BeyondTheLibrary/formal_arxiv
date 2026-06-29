-- Cited from: Moitra-Valiant, 'Settling the Polynomial Learnability of Mixtures of Gaussians' (FOCS 2010), Claims 27 and 28 (page 29). The half-line j-th moment of a centred Gaussian density on [a, ∞) for a > 0. Standard analysis result: by integration by parts, the half-Gaussian moments admit a closed form in terms of the upper incomplete Gamma function Γ((j+1)/2, a²/(2σ²)); for j ≤ 6 the result is a polynomial in a, σ times exp(-a²/(2σ²)).
-- Paper label: Half-Gaussian j-th moment bound (Moitra-Valiant 2010, page 29, supporting Lemma 29 via Claims 27, 28)
-- NL statement: There exists an absolute constant K_{27} > 0 such that for every variance σ² ∈ (0, 1], every a > 0, and every integer j ∈ {0, …, 6}, the half-Gaussian moment satisfies ∫_{[a, ∞)} u^j · (1/√(2π σ²)) · exp(-u²/(2σ²)) du ≤ K_{27} · (a^j + σ^j + 1)/a · exp(-a²/(2σ²)).

import Mathlib
import Workspace.Types.GaussianPDF

namespace Workspace.ProofLemmas

open MeasureTheory Real

namespace HGMHelper

-- ===== base integral lemmas =====
theorem laplace_int (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^j * rexp (-(r * t)) = (Nat.factorial j : ℝ) / r^(j+1) := by
  have hq : (-1:ℝ) < (j:ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (j:ℝ)) (b := r) (by norm_num) hq hr
  have hcongr : ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^j * rexp (-(r * t))
      = ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^(j:ℝ) * rexp (-r * t^(1:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht; simp only [Set.mem_Ioi] at ht; simp only []
    rw [Real.rpow_natCast, Real.rpow_one]; ring_nf
  rw [hcongr, h]
  rw [show Real.Gamma (((j:ℝ)+1)/1) = (Nat.factorial j : ℝ) by rw [div_one, Real.Gamma_nat_eq_factorial]]
  rw [show r ^ (-((j:ℝ)+1)/1) = 1 / r^(j+1) by
    rw [div_one, Real.rpow_neg hr.le, show ((j:ℝ)+1) = ((j+1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, one_div]]
  ring

theorem laplace_integrable (r : ℝ) (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun t => (t:ℝ)^j * rexp (-(r * t))) (Set.Ioi 0) volume := by
  have hq : (-1:ℝ) < (j:ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j:ℝ)) (b := r) hq (by norm_num) hr
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht; simp only [Set.mem_Ioi] at ht; simp only []
  rw [Real.rpow_natCast, Real.rpow_one]; ring_nf

theorem gauss_int (σSq : ℝ) (hσ : 0 < σSq) (j : ℕ) :
    ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^j * rexp (-(t^2)/(2*σSq))
      = (1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2) := by
  have hb : (0:ℝ) < 1/(2*σSq) := by positivity
  have hq : (-1:ℝ) < (j:ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hcongr : ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^j * rexp (-(t^2)/(2*σSq))
      = ∫ t in Set.Ioi (0:ℝ), (t:ℝ)^(j:ℝ) * rexp (-(1/(2*σSq)) * t^(2:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht; simp only [Set.mem_Ioi] at ht; simp only []
    rw [Real.rpow_natCast, Real.rpow_two]; congr 2; field_simp
  rw [hcongr]
  exact integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (j:ℝ)) (b := 1/(2*σSq)) (by norm_num) hq hb

theorem gauss_integrable (σSq : ℝ) (hσ : 0 < σSq) (j : ℕ) :
    IntegrableOn (fun t => (t:ℝ)^j * rexp (-(t^2)/(2*σSq))) (Set.Ioi 0) volume := by
  have hb : (0:ℝ) < 1/(2*σSq) := by positivity
  have hq : (-1:ℝ) < (j:ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := (j:ℝ)) (b := 1/(2*σSq)) hq (by norm_num) hb
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht; simp only [Set.mem_Ioi] at ht; simp only []
  rw [Real.rpow_natCast, Real.rpow_two]; congr 2; field_simp

theorem gamma_half_le_four (j : ℕ) (hj : j ≤ 6) : Real.Gamma (((j:ℝ)+1)/2) ≤ 4 := by
  have hsp : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; exact Real.pi_le_four
  have hsp0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  interval_cases j
  · rw [show ((0:ℕ):ℝ)+1 = 1 by norm_num, show (1:ℝ)/2 = 1/2 by norm_num, Real.Gamma_one_half_eq]; linarith
  · norm_num
  · rw [show ((2:ℕ):ℝ)+1 = 3 by norm_num]
    rw [show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; nlinarith
  · norm_num
  · rw [show ((4:ℕ):ℝ)+1 = 5 by norm_num]
    rw [show (5:ℝ)/2 = 3/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; nlinarith
  · norm_num
  · rw [show ((6:ℕ):ℝ)+1 = 7 by norm_num]
    rw [show (7:ℝ)/2 = 5/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [show (5:ℝ)/2 = 3/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; nlinarith

-- ===== Reduction: original half-line integral to shifted factored form =====
theorem reduce (σSq a : ℝ) (hσ : 0 < σSq) (j : ℕ) :
    (∫ u in Set.Ici a, u ^ j * (1 / Real.sqrt (2 * Real.pi * σSq))
        * Real.exp (-(u^2) / (2 * σSq)))
    = (1 / Real.sqrt (2 * Real.pi * σSq)) * Real.exp (-(a^2) / (2*σSq)) *
        ∫ t in Set.Ioi (0:ℝ), (t + a) ^ j *
          (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hshift : (∫ u in Set.Ioi a, u ^ j * (1 / Real.sqrt (2 * Real.pi * σSq))
        * Real.exp (-(u^2) / (2 * σSq)))
      = ∫ t in Set.Ioi (0:ℝ), (t + a) ^ j * (1 / Real.sqrt (2 * Real.pi * σSq))
        * Real.exp (-((t+a)^2) / (2 * σSq)) := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) a
    have hemb : MeasurableEmbedding (fun t : ℝ => t + a) :=
      (Homeomorph.addRight a).measurableEmbedding
    have key := hmp.setIntegral_preimage_emb hemb
      (fun u => u ^ j * (1 / Real.sqrt (2 * Real.pi * σSq)) * Real.exp (-(u^2) / (2 * σSq)))
      (Set.Ioi a)
    have hpre : (fun t : ℝ => t + a) ⁻¹' Set.Ioi a = Set.Ioi 0 := by ext x; simp [Set.mem_Ioi]
    rw [hpre] at key; exact key.symm
  rw [hshift, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht; simp only [Set.mem_Ioi] at ht; simp only []
  have hfac : Real.exp (-((t+a)^2) / (2 * σSq))
      = Real.exp (-(a^2)/(2*σSq)) * (Real.exp (-(t^2)/(2*σSq)) * Real.exp (-(a/σSq)*t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  rw [hfac]; ring

-- ===== Case a ≥ 1 =====
theorem caseLarge_bound (σSq a : ℝ) (hσ : 0 < σSq) (ha : 0 < a) (j : ℕ) :
    (∫ t in Set.Ioi (0:ℝ), (t + a) ^ j *
        (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)))
    ≤ (2:ℝ)^j * ((Nat.factorial j : ℝ) * σSq^(j+1) / a^(j+1) + a^j * (σSq/a)) := by
  set r := a/σSq with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  set M : ℝ → ℝ := fun t => (2:ℝ)^j * ((t:ℝ)^j * rexp (-(r*t)) + a^j * rexp (-(r*t))) with hM
  have hmono : ∀ t ∈ Set.Ioi (0:ℝ),
      (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) ≤ M t := by
    intro t ht; simp only [Set.mem_Ioi] at ht
    have hexpG : Real.exp (-(t^2)/(2*σSq)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [sq_nonneg t]
      · positivity
    have hadd : (t + a)^j ≤ (2:ℝ)^j * (t^j + a^j) := by
      have := add_pow_le ht.le ha.le j
      calc (t+a)^j ≤ 2^(j-1)*(t^j+a^j) := this
        _ ≤ 2^j*(t^j+a^j) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
    simp only [hM]
    have hLeq : Real.exp (-(a/σSq) * t) = rexp (-(r*t)) := by rw [hr_def]; ring_nf
    rw [hLeq]
    have hexpLr_nonneg : 0 ≤ rexp (-(r*t)) := (Real.exp_pos _).le
    have hinner : Real.exp (-(t^2)/(2*σSq)) * rexp (-(r*t)) ≤ 1 * rexp (-(r*t)) :=
      mul_le_mul hexpG le_rfl hexpLr_nonneg (by norm_num)
    calc (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * rexp (-(r*t)))
        ≤ ((2:ℝ)^j * (t^j + a^j)) * (1 * rexp (-(r*t))) := by
          apply mul_le_mul hadd hinner (by positivity) (by positivity)
      _ = (2:ℝ)^j * (t^j * rexp (-(r*t)) + a^j * rexp (-(r*t))) := by ring
  have hint_tj := laplace_integrable r hr j
  have hint_0 := laplace_integrable r hr 0
  have hintM : IntegrableOn M (Set.Ioi 0) volume := by
    apply Integrable.const_mul
    apply Integrable.add hint_tj
    have : (fun t => a^j * rexp (-(r*t))) = (fun t => a^j * ((t:ℝ)^0 * rexp (-(r*t)))) := by funext t; simp
    rw [this]; exact (hint_0.const_mul (a^j))
  have hintLHS : IntegrableOn (fun t => (t + a) ^ j *
        (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t))) (Set.Ioi 0) volume := by
    apply MeasureTheory.Integrable.mono' hintM
    · apply Measurable.aestronglyMeasurable; fun_prop
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      apply Filter.Eventually.of_forall
      intro t ht; simp only [Set.mem_Ioi] at ht
      have hnn : 0 ≤ (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) := by
        apply mul_nonneg (pow_nonneg (by linarith) j) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]; exact hmono t ht
  have hmono_int := setIntegral_mono_on hintLHS hintM measurableSet_Ioi hmono
  have hMval : ∫ t in Set.Ioi 0, M t
      = (2:ℝ)^j * ((Nat.factorial j : ℝ) * σSq^(j+1) / a^(j+1) + a^j * (σSq/a)) := by
    simp only [hM]
    rw [integral_const_mul]
    have hsplit : ∫ t in Set.Ioi (0:ℝ), ((t:ℝ)^j * rexp (-(r*t)) + a^j * rexp (-(r*t)))
        = (∫ t in Set.Ioi (0:ℝ), (t:ℝ)^j * rexp (-(r*t)))
          + ∫ t in Set.Ioi (0:ℝ), a^j * rexp (-(r*t)) := by
      apply integral_add hint_tj
      have : (fun t => a^j * rexp (-(r*t))) = (fun t => a^j * ((t:ℝ)^0 * rexp (-(r*t)))) := by funext t; simp
      rw [this]; exact (hint_0.const_mul (a^j))
    rw [hsplit, laplace_int r hr j]
    have hI0 : ∫ t in Set.Ioi (0:ℝ), a^j * rexp (-(r*t)) = a^j * (σSq / a) := by
      have heq : (fun t => a^j * rexp (-(r*t))) = (fun t => a^j * ((t:ℝ)^0 * rexp (-(r*t)))) := by funext t; simp
      rw [heq, integral_const_mul, laplace_int r hr 0]
      simp only [Nat.factorial_zero, Nat.cast_one, pow_one, zero_add]
      rw [hr_def]; have ha' : a ≠ 0 := ne_of_gt ha; have hσ' : σSq ≠ 0 := ne_of_gt hσ; field_simp
    rw [hI0]
    have hrpow : (Nat.factorial j : ℝ) / r^(j+1) = (Nat.factorial j : ℝ) * σSq^(j+1) / a^(j+1) := by
      rw [hr_def, div_pow]; have ha' : a ≠ 0 := ne_of_gt ha; have hσ' : σSq ≠ 0 := ne_of_gt hσ; field_simp
    rw [hrpow]
  rw [hMval] at hmono_int; exact hmono_int

-- ===== Case a ≤ 1 =====
theorem caseSmall_bound (σSq a : ℝ) (hσ : 0 < σSq) (ha : 0 < a) (j : ℕ) :
    (∫ t in Set.Ioi (0:ℝ), (t + a) ^ j *
        (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)))
    ≤ (2:ℝ)^j * ((1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2))
      + (2:ℝ)^j * (a^j * (σSq/a)) := by
  set r := a/σSq with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  set MG : ℝ → ℝ := fun t => (2:ℝ)^j * ((t:ℝ)^j * rexp (-(t^2)/(2*σSq))) with hMG
  set ML : ℝ → ℝ := fun t => (2:ℝ)^j * (a^j * rexp (-(r*t))) with hML
  have hmono : ∀ t ∈ Set.Ioi (0:ℝ),
      (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) ≤ MG t + ML t := by
    intro t ht; simp only [Set.mem_Ioi] at ht
    have hEG : (0:ℝ) ≤ Real.exp (-(t^2)/(2*σSq)) := (Real.exp_pos _).le
    have hEL : (0:ℝ) ≤ Real.exp (-(a/σSq) * t) := (Real.exp_pos _).le
    have hEGle : Real.exp (-(t^2)/(2*σSq)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [sq_nonneg t]
      · positivity
    have hELle : Real.exp (-(a/σSq) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hnn : 0 ≤ (a/σSq) * t := by positivity
      linarith
    have hadd : (t + a)^j ≤ (2:ℝ)^j * (t^j + a^j) := by
      have := add_pow_le ht.le ha.le j
      calc (t+a)^j ≤ 2^(j-1)*(t^j+a^j) := this
        _ ≤ 2^j*(t^j+a^j) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
    simp only [hMG, hML]
    have hLeq : Real.exp (-(a/σSq) * t) = rexp (-(r*t)) := by rw [hr_def]; ring_nf
    calc (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t))
        ≤ ((2:ℝ)^j * (t^j + a^j)) * (Real.exp (-(t^2)/(2*σSq)) * Real.exp (-(a/σSq)*t)) := by
          apply mul_le_mul_of_nonneg_right hadd (by positivity)
      _ = (2:ℝ)^j * (t^j * (Real.exp (-(t^2)/(2*σSq)) * Real.exp (-(a/σSq)*t)))
          + (2:ℝ)^j * (a^j * (Real.exp (-(t^2)/(2*σSq)) * Real.exp (-(a/σSq)*t))) := by ring
      _ ≤ (2:ℝ)^j * (t^j * (Real.exp (-(t^2)/(2*σSq)) * 1))
          + (2:ℝ)^j * (a^j * (1 * Real.exp (-(a/σSq)*t))) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hELle hEG
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hEGle hEL
      _ = (2:ℝ)^j * (t^j * rexp (-(t^2)/(2*σSq))) + (2:ℝ)^j * (a^j * rexp (-(r*t))) := by
          rw [hLeq]; ring
  have hintMG : IntegrableOn MG (Set.Ioi 0) volume := (gauss_integrable σSq hσ j).const_mul _
  have hintML : IntegrableOn ML (Set.Ioi 0) volume := by
    have h0 := laplace_integrable r hr 0
    have heq : (fun t => a^j * rexp (-(r*t))) = (fun t => a^j * ((t:ℝ)^0 * rexp (-(r*t)))) := by funext t; simp
    apply Integrable.const_mul; rw [heq]; exact h0.const_mul _
  have hintsum : IntegrableOn (fun t => MG t + ML t) (Set.Ioi 0) volume := hintMG.add hintML
  have hintLHS : IntegrableOn (fun t => (t + a) ^ j *
        (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t))) (Set.Ioi 0) volume := by
    apply MeasureTheory.Integrable.mono' hintsum
    · apply Measurable.aestronglyMeasurable; fun_prop
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      apply Filter.Eventually.of_forall
      intro t ht; simp only [Set.mem_Ioi] at ht
      have hnn : 0 ≤ (t + a) ^ j * (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) := by
        apply mul_nonneg (pow_nonneg (by linarith) j) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]; exact hmono t ht
  have hmono_int := setIntegral_mono_on hintLHS hintsum measurableSet_Ioi hmono
  have hval : ∫ t in Set.Ioi 0, (MG t + ML t)
      = (2:ℝ)^j * ((1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2))
        + (2:ℝ)^j * (a^j * (σSq/a)) := by
    rw [integral_add hintMG hintML]
    congr 1
    · simp only [hMG]; rw [integral_const_mul, gauss_int σSq hσ j]
    · simp only [hML]; rw [integral_const_mul]
      have heq : (fun t => a^j * rexp (-(r*t))) = (fun t => a^j * ((t:ℝ)^0 * rexp (-(r*t)))) := by funext t; simp
      rw [heq, integral_const_mul, laplace_int r hr 0]
      simp only [Nat.factorial_zero, Nat.cast_one, pow_one, zero_add]
      rw [hr_def]; have ha' : a ≠ 0 := ne_of_gt ha; have hσ' : σSq ≠ 0 := ne_of_gt hσ; field_simp
  rw [hval] at hmono_int; exact hmono_int

theorem gauss_moment_const_bound (σSq : ℝ) (hσ : 0 < σSq) (hσ1 : σSq ≤ 1) (j : ℕ) (hj : j ≤ 6)
    (hΓ : Real.Gamma (((j:ℝ)+1)/2) ≤ 4) :
    (1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2)
      ≤ 24 * (Real.sqrt σSq)^(j+1) := by
  have hrw1 : (1/(2*σSq)) ^ (-((j:ℝ)+1)/2) = (2*σSq) ^ (((j:ℝ)+1)/2) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]; congr 1; ring
  have hrw2 : (2*σSq) ^ (((j:ℝ)+1)/2) = (2:ℝ)^(((j:ℝ)+1)/2) * (Real.sqrt σSq)^(j+1) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]; congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (σSq ^ ((1:ℝ)/2)) (j+1), ← Real.rpow_mul hσ.le]
    congr 1; push_cast; ring
  rw [hrw1, hrw2]
  have hsq0 : 0 ≤ (Real.sqrt σSq)^(j+1) := by positivity
  have h2pow : (2:ℝ)^(((j:ℝ)+1)/2) ≤ 12 := by
    have hle : ((j:ℝ)+1)/2 ≤ 7/2 := by
      have : (j:ℝ) ≤ 6 := by exact_mod_cast hj
      linarith
    calc (2:ℝ)^(((j:ℝ)+1)/2) ≤ (2:ℝ)^((7:ℝ)/2) := by
          apply Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hle
      _ ≤ 12 := by
          have h128 : (2:ℝ)^((7:ℝ)/2) = Real.sqrt 128 := by
            rw [Real.sqrt_eq_rpow,
                show (128:ℝ) = 2^(7:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 7, ← Real.rpow_mul (by norm_num)]
            congr 1; push_cast; ring
          rw [h128, show (12:ℝ) = Real.sqrt 144 by
                rw [show (144:ℝ)=12^2 by norm_num, Real.sqrt_sq (by norm_num)]]
          apply Real.sqrt_le_sqrt; norm_num
  have hΓ0 : 0 ≤ Real.Gamma (((j:ℝ)+1)/2) := by
    have := Real.Gamma_pos_of_pos (show (0:ℝ) < ((j:ℝ)+1)/2 by positivity); linarith
  nlinarith [mul_nonneg hsq0 hΓ0, h2pow, hΓ, hsq0, hΓ0,
             mul_nonneg (mul_nonneg hsq0 hΓ0) (by norm_num : (0:ℝ) ≤ 1),
             Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (((j:ℝ)+1)/2)]

theorem sqrt_two_pi_ge_two : (2:ℝ) ≤ Real.sqrt (2*Real.pi) := by
  have h4 : (2:ℝ) = Real.sqrt 4 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]; apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_three]

theorem final_small (s a : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) (j : ℕ) (hj : j ≤ 6)
    (G : ℝ) (hG : G ≤ 24 * s^(j+1)) (hG0 : 0 ≤ G) :
    (1/(Real.sqrt (2*Real.pi) * s)) * ((2:ℝ)^j * G + (2:ℝ)^j * (a^j * (s^2/a)))
      ≤ 100000 * ((a^j + s^j + 1)/a) := by
  have hsp2 := sqrt_two_pi_ge_two
  have h2j : (2:ℝ)^j ≤ 64 := by
    calc (2:ℝ)^j ≤ 2^6 := pow_le_pow_right₀ (by norm_num) hj
      _ = 64 := by norm_num
  have hX0 : 0 ≤ (2:ℝ)^j * G + (2:ℝ)^j * (a^j * (s^2/a)) := by positivity
  have h2s : 0 < 2*s := by positivity
  have hinv : 1/(Real.sqrt (2*Real.pi) * s) ≤ 1/(2*s) := by
    apply one_div_le_one_div_of_le h2s; nlinarith [hs, hsp2]
  have step1 : (1/(Real.sqrt (2*Real.pi) * s)) * ((2:ℝ)^j * G + (2:ℝ)^j * (a^j * (s^2/a)))
      ≤ (1/(2*s)) * ((2:ℝ)^j * (24 * s^(j+1)) + (2:ℝ)^j * (a^j * (s^2/a))) := by
    refine le_trans (mul_le_mul_of_nonneg_right hinv hX0) ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hXY : (2:ℝ)^j * G ≤ (2:ℝ)^j * (24 * s^(j+1)) := mul_le_mul_of_nonneg_left hG (by positivity)
    gcongr
  refine le_trans step1 ?_
  have hsimp : (1/(2*s)) * ((2:ℝ)^j * (24 * s^(j+1)) + (2:ℝ)^j * (a^j * (s^2/a)))
      = 12 * (2:ℝ)^j * s^j + (2:ℝ)^j * a^j * s / (2*a) := by
    have hs' : s ≠ 0 := ne_of_gt hs
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp; ring
  rw [hsimp]
  have hRHS : 100000 * ((a^j + s^j + 1)/a) = 100000*a^j/a + 100000*s^j/a + 100000/a := by
    field_simp
  rw [hRHS]
  have hsj0 : 0 ≤ s^j := by positivity
  have haj0 : 0 ≤ a^j := by positivity
  have hterm1 : 12 * (2:ℝ)^j * s^j ≤ 100000*s^j/a := by
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_right h2j hsj0,
               mul_nonneg (mul_nonneg hsj0 (by norm_num : (0:ℝ)≤768)) (by linarith : (0:ℝ) ≤ 1 - a)]
  have hterm2 : (2:ℝ)^j * a^j * s / (2*a) ≤ 100000*a^j/a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    -- goal: 2^j * a^j * s * a ≤ 100000 * a^j * (2*a)
    have hsa : (2:ℝ)^j * a^j * s * a ≤ 64 * a^j * a := by
      have h1 : (2:ℝ)^j * a^j * s * a ≤ 64 * a^j * s * a := by
        nlinarith [mul_le_mul_of_nonneg_right h2j haj0, mul_nonneg haj0 (le_of_lt hs),
                   mul_nonneg (mul_nonneg haj0 (le_of_lt hs)) (le_of_lt ha)]
      have h2 : 64 * a^j * s * a ≤ 64 * a^j * a := by
        nlinarith [mul_nonneg (mul_nonneg haj0 (le_of_lt ha)) (by linarith : (0:ℝ) ≤ 1 - s)]
      linarith
    nlinarith [hsa, mul_nonneg (mul_nonneg haj0 (le_of_lt ha)) (by norm_num : (0:ℝ) ≤ 1)]
  have h1a : (0:ℝ) ≤ 100000/a := by positivity
  linarith [hterm1, hterm2, h1a]

theorem fact_le (j : ℕ) (hj : j ≤ 6) : (Nat.factorial j : ℝ) ≤ 720 := by
  interval_cases j <;> norm_num [Nat.factorial]

theorem final_large (s a : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (ha1 : 1 ≤ a) (j : ℕ) (hj : j ≤ 6) :
    (1/(Real.sqrt (2*Real.pi) * s)) *
      ((2:ℝ)^j * ((Nat.factorial j : ℝ) * (s^2)^(j+1) / a^(j+1) + a^j * ((s^2)/a)))
      ≤ 100000 * ((a^j + s^j + 1)/a) := by
  have hsp2 := sqrt_two_pi_ge_two
  have h2j : (2:ℝ)^j ≤ 64 := by
    calc (2:ℝ)^j ≤ 2^6 := pow_le_pow_right₀ (by norm_num) hj
      _ = 64 := by norm_num
  have hfact := fact_le j hj
  have hX0 : 0 ≤ (2:ℝ)^j * ((Nat.factorial j : ℝ) * (s^2)^(j+1) / a^(j+1) + a^j * ((s^2)/a)) := by
    positivity
  have h2s : 0 < 2*s := by positivity
  have hinv : 1/(Real.sqrt (2*Real.pi) * s) ≤ 1/(2*s) := by
    apply one_div_le_one_div_of_le h2s; nlinarith [hs, hsp2]
  refine le_trans (mul_le_mul_of_nonneg_right hinv hX0) ?_
  -- simplify (1/(2s)) * 2^j * (j! s^{2(j+1)}/a^{j+1} + a^j s^2/a)
  have hsimp : (1/(2*s)) * ((2:ℝ)^j * ((Nat.factorial j : ℝ) * (s^2)^(j+1) / a^(j+1) + a^j * ((s^2)/a)))
      = (2:ℝ)^j * (Nat.factorial j : ℝ) * (s^2)^(j+1) / (2*s*a^(j+1))
        + (2:ℝ)^j * a^j * s / (2*a) := by
    have hs' : s ≠ 0 := ne_of_gt hs
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp
  rw [hsimp]
  have hRHS : 100000 * ((a^j + s^j + 1)/a) = 100000*a^j/a + 100000*s^j/a + 100000/a := by field_simp
  rw [hRHS]
  have hsj0 : 0 ≤ s^j := by positivity
  have haj0 : 0 ≤ a^j := by positivity
  -- term1: 2^j j! s^{2(j+1)}/(2 s a^{j+1}) ≤ 100000 s^j/a
  have hterm1 : (2:ℝ)^j * (Nat.factorial j : ℝ) * (s^2)^(j+1) / (2*s*a^(j+1)) ≤ 100000*s^j/a := by
    -- (s^2)^(j+1) = s^(2j+2); /(s) = s^(2j+1) ; bound s^(2j+1) ≤ s^j (s≤1)
    have hpow : (s^2)^(j+1) = s^(2*j+1) * s := by
      rw [← pow_mul]; rw [show 2*(j+1) = (2*j+1)+1 by ring, pow_succ]
    have hs2j1 : s^(2*j+1) ≤ s^j := by
      apply pow_le_pow_of_le_one (le_of_lt hs) hs1; omega
    have haj1 : (1:ℝ)/a^(j+1) ≤ 1/a := by
      apply one_div_le_one_div_of_le ha
      calc a = a^1 := (pow_one a).symm
        _ ≤ a^(j+1) := pow_le_pow_right₀ ha1 (by omega)
    rw [hpow]
    -- 2^j j! s^(2j+1) s / (2 s a^{j+1}) = 2^j j! s^(2j+1) /(2 a^{j+1})
    have hrw : (2:ℝ)^j * (Nat.factorial j : ℝ) * (s^(2*j+1) * s) / (2*s*a^(j+1))
        = (2:ℝ)^j * (Nat.factorial j : ℝ) * s^(2*j+1) / (2*a^(j+1)) := by
      have hs' : s ≠ 0 := ne_of_gt hs
      field_simp
    rw [hrw]
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ ha]
    -- 2^j j! s^(2j+1) * a ≤ 100000 s^j * (2 a^{j+1})
    have hapow : (1:ℝ) ≤ a^j := one_le_pow₀ ha1
    have hkey : (2:ℝ)^j * (Nat.factorial j : ℝ) * s^(2*j+1) ≤ 64 * 720 * s^j := by
      have hprodle : (2:ℝ)^j * (Nat.factorial j : ℝ) ≤ 64 * 720 :=
        mul_le_mul h2j hfact (by positivity) (by norm_num)
      have hprodnn : 0 ≤ (2:ℝ)^j * (Nat.factorial j : ℝ) := by positivity
      have hspow_nn : 0 ≤ s^(2*j+1) := by positivity
      calc (2:ℝ)^j * (Nat.factorial j : ℝ) * s^(2*j+1)
          ≤ (64 * 720) * s^(2*j+1) := mul_le_mul_of_nonneg_right hprodle hspow_nn
        _ ≤ (64 * 720) * s^j := by
            apply mul_le_mul_of_nonneg_left hs2j1 (by norm_num)
        _ = 64 * 720 * s^j := by ring
    -- goal: 2^j*j!*s^(2j+1) * a ≤ 100000 * s^j * (2 * a^(j+1))
    have hale : a ≤ a^(j+1) := by
      calc a = a^1 := (pow_one a).symm
        _ ≤ a^(j+1) := pow_le_pow_right₀ ha1 (by omega)
    have hkeya : (2:ℝ)^j * (Nat.factorial j : ℝ) * s^(2*j+1) * a ≤ 64 * 720 * s^j * a :=
      mul_le_mul_of_nonneg_right hkey (le_of_lt ha)
    have hstep : (64:ℝ) * 720 * s^j * a ≤ 100000 * s^j * (2 * a^(j+1)) := by
      have hsja : 0 ≤ s^j * a := mul_nonneg hsj0 (le_of_lt ha)
      nlinarith [mul_nonneg hsj0 (by linarith [hale] : (0:ℝ) ≤ a^(j+1) - a), hsja,
                 mul_nonneg hsj0 (by positivity : (0:ℝ) ≤ a^(j+1))]
    linarith [hkeya, hstep]
  -- term2: 2^j a^j s/(2a) ≤ 100000 a^j/a (same as small case)
  have hterm2 : (2:ℝ)^j * a^j * s / (2*a) ≤ 100000*a^j/a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    have hsa : (2:ℝ)^j * a^j * s * a ≤ 64 * a^j * a := by
      have h1 : (2:ℝ)^j * a^j * s * a ≤ 64 * a^j * s * a := by
        nlinarith [mul_le_mul_of_nonneg_right h2j haj0, mul_nonneg haj0 (le_of_lt hs),
                   mul_nonneg (mul_nonneg haj0 (le_of_lt hs)) (le_of_lt ha)]
      have h2 : 64 * a^j * s * a ≤ 64 * a^j * a := by
        nlinarith [mul_nonneg (mul_nonneg haj0 (le_of_lt ha)) (by linarith : (0:ℝ) ≤ 1 - s)]
      linarith
    nlinarith [hsa, mul_nonneg (mul_nonneg haj0 (le_of_lt ha)) (by norm_num : (0:ℝ) ≤ 1)]
  have h1a : (0:ℝ) ≤ 100000/a := by positivity
  linarith [hterm1, hterm2, h1a]

end HGMHelper

open HGMHelper in

/--
**Prior work** (Moitra-Valiant 2010, supporting Lemma 29 via Claims 27, 28
on page 29): the j-th absolute moment of a centred Gaussian density,
integrated over the half-line `[a, ∞)`, admits a polynomial-times-exponential
upper bound for j ≤ 6.

For some absolute `K_27 > 0`, for every `σ² ∈ (0, 1]`, every `a > 0`, and every
`j ∈ {0, …, 6}`,

  `∫_{u ∈ Set.Ici a} u^j · (1/√(2π σ²)) · exp(-u²/(2σ²)) du
    ≤ K_27 * ((a^j + √σ² ^ j + 1) / a) * exp(-(a²)/(2σ²))`.

This subsumes the Mills-ratio bound (j = 0) and the half-Gaussian polynomial
moment recurrence (j ≥ 1).
-/
theorem HalfGaussianMomentBound :
    ∃ K27 : ℝ, 0 < K27 ∧
      ∀ (σSq a : ℝ) (j : ℕ),
        0 < σSq → σSq ≤ 1 → 0 < a → j ≤ 6 →
        ∫ u in Set.Ici a,
            u ^ j * (1 / Real.sqrt (2 * Real.pi * σSq))
                  * Real.exp (-(u^2) / (2 * σSq)) ∂MeasureTheory.volume
        ≤ K27 * ((a ^ j + Real.sqrt σSq ^ j + 1) / a)
              * Real.exp (-(a^2) / (2 * σSq)) := by

  refine ⟨100000, by norm_num, ?_⟩
  intro σSq a j hσ hσ1 ha hj
  set s := Real.sqrt σSq with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hσ
  have hs1 : s ≤ 1 := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt hσ1
  have hs2 : s^2 = σSq := Real.sq_sqrt hσ.le
  -- reduce the integral
  rw [reduce σSq a hσ j]
  -- exp factor positive
  have hEpos : 0 < Real.exp (-(a^2) / (2*σSq)) := Real.exp_pos _
  -- √(2π σSq) = √(2π) * s
  have hsplit : Real.sqrt (2 * Real.pi * σSq) = Real.sqrt (2*Real.pi) * s := by
    rw [hs_def, ← Real.sqrt_mul (by positivity)]
  -- goal: C * E * I_shift ≤ 100000 * ((a^j+s^j+1)/a) * E
  -- rearrange to (C * I_shift) * E ≤ (100000*((a^j+s^j+1)/a)) * E
  rw [hsplit]
  -- It suffices to prove C * I_shift ≤ 100000 * ((a^j+s^j+1)/a)
  set Ish := ∫ t in Set.Ioi (0:ℝ), (t + a) ^ j *
      (Real.exp (-(t^2) / (2 * σSq)) * Real.exp (-(a/σSq) * t)) with hIsh_def
  have hIsh0 : 0 ≤ Ish := by
    rw [hIsh_def]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht; simp only [Set.mem_Ioi] at ht
    apply mul_nonneg (pow_nonneg (by linarith) j) (by positivity)
  have hCI : (1 / (Real.sqrt (2*Real.pi) * s)) * Ish ≤ 100000 * ((a^j + s^j + 1)/a) := by
    rcases le_or_gt a 1 with hale | hagt
    · -- case a ≤ 1
      have hcb := caseSmall_bound σSq a hσ ha j
      rw [← hIsh_def] at hcb
      have hGb : (1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2)
          ≤ 24 * s^(j+1) := by
        rw [hs_def]; exact gauss_moment_const_bound σSq hσ hσ1 j hj (gamma_half_le_four j hj)
      -- caseSmall_bound RHS: 2^j * G + 2^j*(a^j*(σSq/a)); rewrite σSq = s^2
      have hcb' : Ish ≤ (2:ℝ)^j * ((1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2))
            + (2:ℝ)^j * (a^j * (s^2/a)) := by rw [hs2]; exact hcb
      -- multiply by C ≥ 0
      have hCnn : 0 ≤ 1 / (Real.sqrt (2*Real.pi) * s) := by positivity
      calc (1 / (Real.sqrt (2*Real.pi) * s)) * Ish
          ≤ (1 / (Real.sqrt (2*Real.pi) * s)) *
              ((2:ℝ)^j * ((1/(2*σSq)) ^ (-((j:ℝ)+1)/2) * (1/2) * Real.Gamma (((j:ℝ)+1)/2))
              + (2:ℝ)^j * (a^j * (s^2/a))) := mul_le_mul_of_nonneg_left hcb' hCnn
        _ ≤ (1 / (Real.sqrt (2*Real.pi) * s)) *
              ((2:ℝ)^j * (24 * s^(j+1)) + (2:ℝ)^j * (a^j * (s^2/a))) := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              gcongr
        _ ≤ 100000 * ((a^j + s^j + 1)/a) := final_small s a hs hs1 ha hale j hj (24 * s^(j+1)) (le_refl _) (by positivity)
    · -- case a > 1
      have hcb := caseLarge_bound σSq a hσ ha j
      rw [← hIsh_def] at hcb
      have hcb' : Ish ≤ (2:ℝ)^j * ((Nat.factorial j : ℝ) * (s^2)^(j+1) / a^(j+1) + a^j * ((s^2)/a)) := by
        rw [hs2]; exact hcb
      have hCnn : 0 ≤ 1 / (Real.sqrt (2*Real.pi) * s) := by positivity
      calc (1 / (Real.sqrt (2*Real.pi) * s)) * Ish
          ≤ (1 / (Real.sqrt (2*Real.pi) * s)) *
              ((2:ℝ)^j * ((Nat.factorial j : ℝ) * (s^2)^(j+1) / a^(j+1) + a^j * ((s^2)/a))) :=
              mul_le_mul_of_nonneg_left hcb' hCnn
        _ ≤ 100000 * ((a^j + s^j + 1)/a) := final_large s a hs hs1 ha (le_of_lt hagt) j hj
  -- conclude: (C * Ish) * E ≤ (100000*(...)) * E
  calc 1 / (Real.sqrt (2*Real.pi) * s) * Real.exp (-(a^2) / (2*σSq)) * Ish
      = (1 / (Real.sqrt (2*Real.pi) * s) * Ish) * Real.exp (-(a^2) / (2*σSq)) := by ring
    _ ≤ (100000 * ((a^j + s^j + 1)/a)) * Real.exp (-(a^2) / (2*σSq)) :=
        mul_le_mul_of_nonneg_right hCI (le_of_lt hEpos)

end Workspace.ProofLemmas
