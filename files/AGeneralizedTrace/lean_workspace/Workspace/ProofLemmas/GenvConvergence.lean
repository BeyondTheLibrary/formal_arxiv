import Mathlib
import Workspace.ProofLemmas.T4ToCircPowRPeriodic
import Workspace.ProofLemmas.MGFOfHbBoundGaussian
import Workspace.ProofLemmas.PerFactorFTModulus
import Workspace.ProofLemmas.PerFactorFourierModulus

open scoped Real Complex
open MeasureTheory intervalIntegral

set_option maxHeartbeats 4000000

/-!
# L¹ (integral) convergence of the periodic envelope `Genv`

This file discharges the three open hypotheses of
`T4ToCircPowRPeriodic.T4_modulus_le_circPowR` (Lemma 7):
`Continuous (Genv n)`, and the two `b`-series summabilities
`hsum_norm` / `hsum_Genv`.

The key obstruction (recorded in `lean_knowledge.md`, F44/G3) is that the bare
pointwise bound `circPowR (Bbase n) (b+1) η ≤ 1` only gives the *divergent*
series `∑ α^(b+1)` for large `n` (since `α = c'√n ≥ 1`).  The correct
convergence is in **L¹**: the integral of the base modulus
`g := ∫_{-π}^{π} Bbase n` is small, `g ≤ √(8π/n)` (Wallis/Gaussian), so that
`α · g ≤ α · √(8π/n) = 1/(2 e²) < 1` (the calibration identity already proved in
`PerFactorFourierModulus`).  Because the circular self-power obeys the sup-norm
recurrence

  `sup (circPowR g (m+1)) ≤ (G/2π) · sup (circPowR g m)`,

(`G := ∫_{-π}^{π} Bbase`, using that `∫_{-π}^{π} Bbase(ξ-·) = G` by `2π`-periodicity),
we get the **uniform** pointwise bound `circPowR (Bbase n) m ξ ≤ (G/2π)^(m-1)`,
hence `α^(b+1) · circPowR (Bbase n) (b+1) η ≤ α · (α·G/2π)^b`, a convergent
geometric series (`α·G/2π ≤ 1/(4π e²) < 1`).  This yields all three hypotheses.
-/

namespace GenvConvergence

open T4ToCircPowRPeriodic
open PerFactorFTModulus
open PerFactorFourierModulus
open PeriodicBaseKfoldPeriodisation
open CircConvInfra
open KFoldConvolutionTheorem
open FTConvPow
open PerFactorFTEnvelope

/-! ## `Bbase ≤ 1` pointwise. -/

/-- `Bbase n η ≤ 1` for every `η`.  On `[-π,π]` it equals `|cos(η/2)|^n ≤ 1`;
elsewhere we use periodicity to reduce to a point of `[-π,π]`.  We give the
unconditional bound directly from the closed form on a fundamental domain — but
for the L¹ argument we actually only need `Bbase ≤ 1` on `[-π,π]`, proved below
as `Bbase_le_one_on`. -/
theorem Bbase_le_one_on (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : |η| ≤ Real.pi) :
    Bbase n η ≤ 1 := by
  unfold Bbase
  rw [FT_pBinC n hn η hη, norm_mul]
  have h_phase : ‖Complex.exp (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [h_phase, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)

/-- On `[-π,π]`, `Bbase n η = cos(η/2)^n` (cosine is nonnegative there, so the
absolute value drops). -/
theorem Bbase_eq_cos_pow (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : |η| ≤ Real.pi) :
    Bbase n η = (Real.cos (η / 2)) ^ n := by
  unfold Bbase
  rw [FT_pBinC n hn η hη, norm_mul]
  have h_phase : ‖Complex.exp (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [h_phase, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hcos_nn : 0 ≤ Real.cos (η / 2) := by
    have habs2 : |η / 2| ≤ Real.pi / 2 := by
      rw [abs_div]; simp; linarith [hη]
    rw [abs_le] at habs2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [habs2.1]) habs2.2
  rw [abs_of_nonneg hcos_nn]

/-! ## `Bbase ≤ 1` everywhere (via the Fourier triangle inequality). -/

/-- The summand `s ↦ pBinC n s · e^{-iηs}` has norm equal to the real `pBinC`
value (the exponential is unit-modulus). -/
theorem pBinC_summand_norm (n : ℕ) (η : ℝ) (s : ℤ) :
    ‖pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖
      = (if 0 ≤ s ∧ s ≤ (n : ℤ) then ((Nat.choose n s.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) else 0) := by
  rw [norm_mul]
  have hexp : ‖Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (η : ℂ) * (s : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [hexp, mul_one]
  unfold pBinC
  split_ifs with h
  · rw [norm_mul, Complex.norm_natCast]
    rw [show ((2 : ℂ) ^ n)⁻¹ = (((2 ^ n : ℝ) : ℂ))⁻¹ by push_cast; ring]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rw [norm_zero]

/-- `∑'_s ‖pBinC n s · e^{-iηs}‖ = 1` (the binomial probabilities sum to one). -/
theorem pBinC_summand_norm_tsum (n : ℕ) (η : ℝ) :
    ∑' s : ℤ, ‖pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖ = 1 := by
  have hcongr : (fun s : ℤ => ‖pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖)
      = (fun s : ℤ => if 0 ≤ s ∧ s ≤ (n : ℤ)
          then ((Nat.choose n s.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) else 0) := by
    funext s; exact pBinC_summand_norm n η s
  rw [hcongr]
  rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) (n : ℤ))]
  · -- reindex Icc(0,n)ℤ to range(n+1)ℕ
    rw [show Finset.Icc (0 : ℤ) (n : ℤ)
          = Finset.map ⟨fun k : ℕ => (k : ℤ), fun a b h => by simpa using h⟩
              (Finset.range (n + 1)) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨x.toNat, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩; exact ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hk⟩]
    rw [Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have hsum : ∀ k ∈ Finset.range (n + 1),
        (if 0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ)
          then ((Nat.choose n ((k : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) else 0)
          = (Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹ := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [if_pos ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hk⟩]
      congr 2
    rw [Finset.sum_congr rfl hsum]
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    field_simp
  · intro s hs
    rw [Finset.mem_Icc, not_and_or] at hs
    rw [if_neg (by omega)]

/-- **`Bbase n η ≤ 1` for every `η`.**  Triangle inequality on the Fourier sum:
`‖∑' s, pBinC s · e^{-iηs}‖ ≤ ∑' s, ‖pBinC s‖ = 1`. -/
theorem Bbase_le_one (n : ℕ) (η : ℝ) : Bbase n η ≤ 1 := by
  unfold Bbase FT
  have hsummable : Summable
      (fun s : ℤ => ‖pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) (n : ℤ))
    intro s hs
    rw [pBinC_summand_norm n η s]
    rw [Finset.mem_Icc, not_and_or] at hs
    rw [if_neg (by omega)]
  calc ‖∑' s : ℤ, pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖
      ≤ ∑' s : ℤ, ‖pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ = 1 := pBinC_summand_norm_tsum n η

/-! ## The integral `Gint n := ∫_{-π}^{π} Bbase n` and the bound `g ≤ √(8π/n)`. -/

/-- The L¹ (period) mass of the base modulus, `Gint n := ∫_{-π}^{π} Bbase n η dη`. -/
noncomputable def Gint (n : ℕ) : ℝ := ∫ η in (-Real.pi)..Real.pi, Bbase n η

/-- `Gint n ≥ 0`. -/
theorem Gint_nonneg (n : ℕ) : 0 ≤ Gint n := by
  unfold Gint
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro η _
  exact Bbase_nonneg n η

/-- The indicator full-line integral equals the interval integral, both of
`cos(η/2)^n`. -/
theorem cos_pow_indicator_eq_interval (n : ℕ) (hn : 1 ≤ n) :
    (∫ ξ : ℝ, (if |ξ| ≤ Real.pi then (Real.cos (ξ / 2)) ^ n else 0))
      = ∫ ξ in (-Real.pi)..Real.pi, (Real.cos (ξ / 2)) ^ n := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  funext ξ
  rw [Set.indicator_apply]
  by_cases h : ξ ∈ Set.Ioc (-Real.pi) Real.pi
  · rw [if_pos h, if_pos (by rw [Set.mem_Ioc] at h; rw [abs_le]; exact ⟨le_of_lt h.1, h.2⟩)]
  · rw [if_neg h]
    by_cases h2 : |ξ| ≤ Real.pi
    · -- |ξ| ≤ π but ξ ∉ Ioc(-π,π]: only possible at ξ = -π (a null set), so values agree there too
      rw [if_pos h2]
      rw [Set.mem_Ioc, not_and_or] at h
      rw [abs_le] at h2
      have hxeq : ξ = -Real.pi := by
        rcases h with h | h
        · linarith [h2.1]
        · linarith [h2.2]
      rw [hxeq]
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two,
        zero_pow (by omega : n ≠ 0)]
    · rw [if_neg h2]

/-- **`g`-bound (Step 1): `Gint n ≤ √(8π/n)`.**  The period mass of `Bbase`
equals `∫_{-π}^{π} cos(η/2)^n`, which `MGFOfHbBoundGaussian` (at `t = 0`) bounds
by `√(8π/n)` (the Wallis/Gaussian integral). -/
theorem Gint_le_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Gint n ≤ Real.sqrt (8 * Real.pi / (n : ℝ)) := by
  -- Gint n = ∫_{-π}^π cos(η/2)^n
  have hGint_eq : Gint n = ∫ η in (-Real.pi)..Real.pi, (Real.cos (η / 2)) ^ n := by
    unfold Gint
    apply intervalIntegral.integral_congr
    intro η hη
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hη
    exact Bbase_eq_cos_pow n hn η (by rw [abs_le]; exact ⟨hη.1, hη.2⟩)
  rw [hGint_eq, ← cos_pow_indicator_eq_interval n hn]
  have hmgf := MGFOfHbBoundGaussian n hn 0
  have hsimp : (2 * (0:ℝ) ^ 2 / (n : ℝ)) = 0 := by ring
  rw [hsimp, Real.exp_zero, mul_one] at hmgf
  refine le_trans (le_of_eq ?_) hmgf
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  simp only [zero_mul, Real.exp_zero, mul_one]

/-- The calibration identity `α · √(8π/n) = 1/(2 e²)`. -/
theorem alphaC_sqrt_eq (n : ℕ) (hn : 1 ≤ n) :
    alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) = 1 / (2 * Real.exp 2) := by
  have h_calib := MGFCalibrationAtSqrtN n hn
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hexp_ne : Real.exp 2 ≠ 0 := ne_of_gt hexp_pos
  have h_pre : alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) * Real.exp 2 = 1 / 2 := by
    unfold alphaC; linarith [h_calib]
  have h_div := congrArg (fun x => x / Real.exp 2) h_pre
  simp only at h_div
  rw [mul_div_assoc, div_self hexp_ne, mul_one] at h_div
  rw [h_div]; field_simp

/-- **Step 2: `α · g ≤ 1/2`.**  Combines `g ≤ √(8π/n)` (`Gint_le_sqrt`) with the
calibration identity `α · √(8π/n) = 1/(2 e²) ≤ 1/2`. -/
theorem alphaG_le_half (n : ℕ) (hn : 1 ≤ n) : alphaC n * Gint n ≤ 1 / 2 := by
  have hα_nn : 0 ≤ alphaC n := alphaC_nonneg n
  have hg_le : Gint n ≤ Real.sqrt (8 * Real.pi / (n : ℝ)) := Gint_le_sqrt n hn
  have hstep : alphaC n * Gint n ≤ alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hg_le hα_nn
  rw [alphaC_sqrt_eq n hn] at hstep
  refine le_trans hstep ?_
  have hexp_ge : (1 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2; linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hexp_ge]

/-! ## The *weighted* single-factor MGF `g(√n) := ∫_{-π}^{π} e^{√n η} Bbase n η`. -/

/-- The weighted version of `cos_pow_indicator_eq_interval`: the whole-line
indicator integral of `cos(η/2)^n · e^{tη}` equals the interval integral over
`[-π,π]`. -/
theorem cos_pow_weight_indicator_eq_interval (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (∫ ξ : ℝ, (if |ξ| ≤ Real.pi then (Real.cos (ξ / 2)) ^ n else 0) * Real.exp (t * ξ))
      = ∫ ξ in (-Real.pi)..Real.pi, (Real.cos (ξ / 2)) ^ n * Real.exp (t * ξ) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  funext ξ
  rw [Set.indicator_apply]
  by_cases h : ξ ∈ Set.Ioc (-Real.pi) Real.pi
  · rw [if_pos h,
      if_pos (by rw [Set.mem_Ioc] at h; rw [abs_le]; exact ⟨le_of_lt h.1, h.2⟩)]
  · rw [if_neg h]
    by_cases h2 : |ξ| ≤ Real.pi
    · rw [if_pos h2]
      rw [Set.mem_Ioc, not_and_or] at h
      rw [abs_le] at h2
      have hxeq : ξ = -Real.pi := by
        rcases h with h | h
        · linarith [h2.1]
        · linarith [h2.2]
      rw [hxeq]
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two,
        zero_pow (by omega : n ≠ 0), zero_mul]
    · rw [if_neg h2, zero_mul]

/-- The weighted single-factor MGF mass, `g(t) := ∫_{-π}^{π} e^{t η} Bbase n η dη`. -/
noncomputable def Gweight (n : ℕ) (t : ℝ) : ℝ :=
  ∫ η in (-Real.pi)..Real.pi, Real.exp (t * η) * Bbase n η

theorem Gweight_nonneg (n : ℕ) (t : ℝ) : 0 ≤ Gweight n t := by
  unfold Gweight
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro η _
  exact mul_nonneg (Real.exp_pos _).le (Bbase_nonneg n η)

/-- **Weighted g-bound (paper eq g-bound, Step 1).**  At `t = √n`,
`g(√n) = ∫_{-π}^{π} e^{√n η} Bbase n η dη ≤ e² · √(8π/n)`.
Uses `MGFOfHbBoundGaussian` at `t = √n` (its Gaussian exponent `2 t²/n` becomes
`2·n/n = 2`, giving the factor `e²`). -/
theorem Gweight_le (n : ℕ) (hn : 1 ≤ n) :
    Gweight n (Real.sqrt (n : ℝ)) ≤ Real.exp 2 * Real.sqrt (8 * Real.pi / (n : ℝ)) := by
  set t : ℝ := Real.sqrt (n : ℝ) with ht_def
  -- Rewrite Gweight as the interval integral of cos(η/2)^n · e^{tη}.
  have hGw_eq : Gweight n t = ∫ η in (-Real.pi)..Real.pi, (Real.cos (η / 2)) ^ n * Real.exp (t * η) := by
    unfold Gweight
    apply intervalIntegral.integral_congr
    intro η hη
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hη
    simp only
    rw [Bbase_eq_cos_pow n hn η (by rw [abs_le]; exact ⟨hη.1, hη.2⟩), mul_comm]
  rw [hGw_eq, ← cos_pow_weight_indicator_eq_interval n hn t]
  have hmgf := MGFOfHbBoundGaussian n hn t
  -- The Gaussian exponent 2 t² / n = 2 (since t = √n ⇒ t² = n).
  have ht_sq : t ^ 2 = (n : ℝ) := by
    rw [ht_def, Real.sq_sqrt (by positivity)]
  have hexp_eq : (2 : ℝ) * t ^ 2 / (n : ℝ) = 2 := by
    rw [ht_sq]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hexp_eq] at hmgf
  rw [mul_comm (Real.exp 2)]
  exact hmgf

/-- **Calibration (Step 2): `α · g(√n) ≤ 1/2`.**  With `α = c'·√n`, the factor
`e²` from the weighted bound cancels exactly: `α · e² · √(8π/n) = 1/2`. -/
theorem alphaGweight_le_half (n : ℕ) (hn : 1 ≤ n) :
    alphaC n * Gweight n (Real.sqrt (n : ℝ)) ≤ 1 / 2 := by
  have hα_nn : 0 ≤ alphaC n := alphaC_nonneg n
  have hg_le : Gweight n (Real.sqrt (n : ℝ))
      ≤ Real.exp 2 * Real.sqrt (8 * Real.pi / (n : ℝ)) := Gweight_le n hn
  have hstep : alphaC n * Gweight n (Real.sqrt (n : ℝ))
      ≤ alphaC n * (Real.exp 2 * Real.sqrt (8 * Real.pi / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hg_le hα_nn
  refine le_trans hstep (le_of_eq ?_)
  -- α · (e² · √(8π/n)) = (α · √(8π/n)) · e² = (1/(2e²)) · e² = 1/2.
  have hcal : alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) = 1 / (2 * Real.exp 2) :=
    alphaC_sqrt_eq n hn
  have hexp_ne : Real.exp 2 ≠ 0 := ne_of_gt (Real.exp_pos 2)
  rw [show alphaC n * (Real.exp 2 * Real.sqrt (8 * Real.pi / (n : ℝ)))
      = (alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ))) * Real.exp 2 by ring, hcal]
  field_simp

/-- The geometric ratio `q := α · g / (2π)` of the circular-power series.  It
satisfies `0 ≤ q` and `q < 1` (in fact `q ≤ 1/(4π e²)`). -/
theorem alphaG_div_two_pi_lt_one (n : ℕ) (hn : 1 ≤ n) :
    alphaC n * Gint n / (2 * Real.pi) < 1 := by
  have hαg : alphaC n * Gint n ≤ 1 / 2 := alphaG_le_half n hn
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [div_lt_one (by positivity)]
  linarith

theorem alphaG_div_two_pi_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ alphaC n * Gint n / (2 * Real.pi) := by
  apply div_nonneg
  · exact mul_nonneg (alphaC_nonneg n) (Gint_nonneg n)
  · positivity

/-! ## The uniform sup bound `circPowR (Bbase n) m ξ ≤ (Gint n / 2π)^(m-1)`. -/

/-- `Bbase n` is `2π`-periodic, packaged as a `Function.Periodic`. -/
theorem Bbase_periodic' (n : ℕ) : Function.Periodic (Bbase n) (2 * Real.pi) := by
  intro x; exact Bbase_periodic n x

/-- **Period-shift integral.**  For every `ξ`,
`∫_{-π}^{π} Bbase n (ξ - η) dη = Gint n` (the period mass is shift-invariant by
`2π`-periodicity). -/
theorem Bbase_shift_integral (n : ℕ) (ξ : ℝ) :
    (∫ η in (-Real.pi)..Real.pi, Bbase n (ξ - η)) = Gint n := by
  rw [intervalIntegral.integral_comp_sub_left (Bbase n) ξ]
  rw [show ξ - -Real.pi = ξ + Real.pi by ring]
  -- ∫ x in (ξ-π)..(ξ+π), Bbase n x = ∫ x in -π..π, Bbase n x
  have hper := (Bbase_periodic' n).intervalIntegral_add_eq (ξ - Real.pi) (-Real.pi)
  rw [show ξ - Real.pi + 2 * Real.pi = ξ + Real.pi by ring] at hper
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hper
  rw [hper]
  rfl

/-- **Sup bound on the circular self-power.**  For every `m ≥ 1` and every `ξ`,
`circPowR (Bbase n) m ξ ≤ (Gint n / (2π))^(m-1)`.

Proof by induction on `m`: the base case `m = 1` is `Bbase n ξ ≤ 1` (`Bbase_le_one`);
the step uses `circPowR g (m+1) ξ = (1/2π) ∫_{-π}^{π} circPowR g m η · Bbase n (ξ-η) dη`,
bounding `circPowR g m η ≤ M` by the IH (uniform sup) and pulling it out, leaving
`(1/2π) · M · ∫ Bbase n (ξ-·) = (1/2π) · M · Gint n`. -/
theorem circPowR_Bbase_sup_bound (n : ℕ) (hn : 1 ≤ n) :
    ∀ m, 1 ≤ m → ∀ ξ, circPowR (Bbase n) m ξ ≤ (Gint n / (2 * Real.pi)) ^ (m - 1) := by
  have hBbase_cont := Bbase_continuous n
  have hGint_nn := Gint_nonneg n
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [circPowR_one]
      simpa using Bbase_le_one n ξ
    · -- m ≥ 1, so m + 1 = (m-1) + 2
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      have ihbound : ∀ x, circPowR (Bbase n) (m' + 1) x ≤ (Gint n / (2 * Real.pi)) ^ m' := by
        intro x
        have := ih (by omega) x
        simpa using this
      rw [circPowR_succ_succ]
      simp only [circConvR]
      -- (1/2π) ∫_{-π}^π circPowR (Bbase n) (m'+1) η · Bbase n (ξ-η) dη
      --   ≤ (1/2π) · M · Gint n  where M = (Gint/2π)^m'
      have hπ : (0:ℝ) < 2 * Real.pi := by positivity
      have hM_nn : 0 ≤ (Gint n / (2 * Real.pi)) ^ m' :=
        pow_nonneg (div_nonneg hGint_nn (le_of_lt hπ)) m'
      -- bound the integrand pointwise by M · Bbase n (ξ-η)
      have hintegrand_le : ∀ η ∈ Set.Icc (-Real.pi) Real.pi,
          circPowR (Bbase n) (m' + 1) η * Bbase n (ξ - η)
            ≤ (Gint n / (2 * Real.pi)) ^ m' * Bbase n (ξ - η) := by
        intro η _
        exact mul_le_mul_of_nonneg_right (ihbound η) (Bbase_nonneg n (ξ - η))
      -- integrability of both sides
      have hcpr_cont : Continuous (fun η => circPowR (Bbase n) (m' + 1) η) :=
        circPowR_continuous (Bbase n) hBbase_cont (m' + 1) (by omega)
      have hshift_cont : Continuous (fun η => Bbase n (ξ - η)) :=
        hBbase_cont.comp (continuous_const.sub continuous_id)
      have hLHS_int : IntervalIntegrable
          (fun η => circPowR (Bbase n) (m' + 1) η * Bbase n (ξ - η))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (hcpr_cont.mul hshift_cont).intervalIntegrable _ _
      have hRHS_int : IntervalIntegrable
          (fun η => (Gint n / (2 * Real.pi)) ^ m' * Bbase n (ξ - η))
          MeasureTheory.volume (-Real.pi) Real.pi :=
        (continuous_const.mul hshift_cont).intervalIntegrable _ _
      have hint_mono : (∫ η in (-Real.pi)..Real.pi,
            circPowR (Bbase n) (m' + 1) η * Bbase n (ξ - η))
          ≤ ∫ η in (-Real.pi)..Real.pi,
            (Gint n / (2 * Real.pi)) ^ m' * Bbase n (ξ - η) :=
        intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hLHS_int hRHS_int
          hintegrand_le
      -- compute the RHS integral
      have hRHS_eq : (∫ η in (-Real.pi)..Real.pi,
            (Gint n / (2 * Real.pi)) ^ m' * Bbase n (ξ - η))
          = (Gint n / (2 * Real.pi)) ^ m' * Gint n := by
        rw [intervalIntegral.integral_const_mul, Bbase_shift_integral n ξ]
      -- assemble
      calc (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi,
              circPowR (Bbase n) (m' + 1) η * Bbase n (ξ - η)
          ≤ (1 / (2 * Real.pi)) * ((Gint n / (2 * Real.pi)) ^ m' * Gint n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hRHS_eq] at hint_mono; exact hint_mono
        _ = (Gint n / (2 * Real.pi)) ^ (m' + 1) := by
            rw [pow_succ]
            field_simp

/-! ## Geometric domination, summability, and continuity. -/

/-- The uniform geometric majorant `u b := α^(b+1) · (Gint/2π)^b = α · q^b`. -/
private noncomputable def umaj (n : ℕ) (b : ℕ) : ℝ :=
  alphaC n ^ (b + 1) * (Gint n / (2 * Real.pi)) ^ b

/-- `umaj` is a (summable) geometric series: `umaj n b = α · q^b` with
`q = α·Gint/2π < 1`. -/
theorem umaj_summable (n : ℕ) (hn : 1 ≤ n) : Summable (umaj n) := by
  have hq_lt : alphaC n * Gint n / (2 * Real.pi) < 1 := alphaG_div_two_pi_lt_one n hn
  have hq_nn : 0 ≤ alphaC n * Gint n / (2 * Real.pi) := alphaG_div_two_pi_nonneg n hn
  have hrw : umaj n = fun b => alphaC n * (alphaC n * Gint n / (2 * Real.pi)) ^ b := by
    funext b
    unfold umaj
    rw [mul_div_assoc, mul_pow, div_pow, pow_succ]
    ring
  rw [hrw]
  apply Summable.mul_left
  exact summable_geometric_of_lt_one hq_nn hq_lt

/-- The `Genv`-series term is dominated by `umaj`, uniformly in `η`. -/
theorem Genv_term_le_umaj (n : ℕ) (hn : 1 ≤ n) (b : ℕ) (η : ℝ) :
    alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η ≤ umaj n b := by
  unfold umaj
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (alphaC_nonneg n) _)
  have := circPowR_Bbase_sup_bound n hn (b + 1) (by omega) η
  simpa using this

/-- The `Genv`-series term is nonnegative. -/
theorem Genv_term_nonneg (n : ℕ) (b : ℕ) (η : ℝ) :
    0 ≤ alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η :=
  mul_nonneg (pow_nonneg (alphaC_nonneg n) _)
    (circPowR_nonneg (Bbase n) (Bbase_nonneg n) (b + 1) (by omega) η)

/-- **Hypothesis 2/3 discharged: `hsum_Genv`.**  The `Genv`-defining `b`-series is
summable at every `η`, by geometric domination. -/
theorem hsum_Genv_proof (n : ℕ) (hn : 1 ≤ n) (η : ℝ) :
    Summable (fun b : ℕ => alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η) := by
  apply Summable.of_nonneg_of_le (fun b => Genv_term_nonneg n b η)
    (fun b => Genv_term_le_umaj n hn b η) (umaj_summable n hn)

/-- **Hypothesis 1/3 discharged: `hsum_norm`.**  The norm series of the per-factor
circular-geometric expansion is summable at every `η`.  The norm of each term is
`α^(b+1) · ‖circPow (FT binAtom) (b+1) η‖ ≤ α^(b+1) · circPowR (Bbase n) (b+1) η`
(iterated modulus-triangle + ℓj-independence), dominated by `umaj`. -/
theorem hsum_norm_proof (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ) :
    Summable (fun b : ℕ =>
      ‖(alphaC n : ℂ) ^ (b + 1)
        * circPow (FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ))) (b + 1) η‖) := by
  have hF_cont : Continuous (fun η : ℝ => FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η) :=
    FT_continuous_of_finite_support _
      (Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                  ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))))
      (binAtomC_support n ℓj)
  have hF_per : ∀ x, FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) (x + 2 * Real.pi)
      = FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) x :=
    fun x => FT_periodic _ x
  apply Summable.of_nonneg_of_le (fun b => norm_nonneg _) _ (umaj_summable n hn)
  intro b
  -- ‖α^(b+1)·circPow...‖ = α^(b+1)·‖circPow...‖ ≤ α^(b+1)·circPowR(Bbase)(b+1) η ≤ umaj
  rw [norm_mul]
  have hα : ‖(alphaC n : ℂ) ^ (b + 1)‖ = alphaC n ^ (b + 1) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (alphaC_nonneg n)]
  rw [hα]
  refine le_trans ?_ (Genv_term_le_umaj n hn b η)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (alphaC_nonneg n) _)
  -- ‖circPow (FT binAtom) (b+1) η‖ ≤ circPowR (Bbase n) (b+1) η
  have htri := circPow_norm_le_circPowR
    (fun η => FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η) hF_cont hF_per (b + 1) (by omega) η
  have hbase : (fun x => ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) x‖) = Bbase n := by
    funext x
    exact FT_binAtom_norm_eq_Bbase n ℓj x
  rw [hbase] at htri
  exact htri

/-- **Hypothesis 3/3 discharged: `Continuous (Genv n)`.**  Uniform-limit of
continuous partial sums: each `b`-term is continuous and uniformly dominated by the
summable geometric majorant `umaj`. -/
theorem Genv_continuous (n : ℕ) (hn : 1 ≤ n) : Continuous (Genv n) := by
  unfold Genv
  apply continuous_tsum
    (f := fun b η => alphaC n ^ (b + 1) * circPowR (Bbase n) (b + 1) η)
    (u := umaj n)
  · intro b
    apply Continuous.mul continuous_const
    exact circPowR_continuous (Bbase n) (Bbase_continuous n) (b + 1) (by omega)
  · exact umaj_summable n hn
  · intro b η
    rw [Real.norm_eq_abs, abs_of_nonneg (Genv_term_nonneg n b η)]
    exact Genv_term_le_umaj n hn b η

/-- **`Genv n` is `2π`-periodic.**  Termwise: each `circPowR (Bbase n) (b+1)` is
`2π`-periodic (`circPowR_periodic`, from `Bbase_periodic'`), so the `b`-series is. -/
theorem Genv_periodic (n : ℕ) (η : ℝ) : Genv n (η + 2 * Real.pi) = Genv n η := by
  unfold Genv
  apply tsum_congr
  intro b
  rw [circPowR_periodic (Bbase n) (Bbase_periodic n) (b + 1) (by omega) η]

/-- **Lemma 7 (unconditional).**  Instantiating the three discharged hypotheses
into `T4_modulus_le_circPowR` gives the k-fold circular-modulus bound with NO
side-conditions: for `n, k ≥ 1` and every `ξ`,
`‖∑' r, (∏ j, factor n (ℓ j) r) · e^{-iξr}‖ ≤ circPowR (Genv n) k ξ`. -/
theorem T4_modulus_le_circPowR_uncond (n k : ℕ) (ℓ : Fin k → ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (ξ : ℝ) :
    ‖∑' r : ℤ, (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
      ≤ circPowR (Genv n) k ξ :=
  T4_modulus_le_circPowR n k ℓ hn hk (Genv_continuous n hn)
    (fun ℓj η => hsum_norm_proof n hn ℓj η)
    (fun η => hsum_Genv_proof n hn η) ξ

end GenvConvergence
