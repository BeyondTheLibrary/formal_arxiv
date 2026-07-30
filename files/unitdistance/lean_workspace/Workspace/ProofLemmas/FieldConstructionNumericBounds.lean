import Mathlib
import Workspace.Types.DiscriminantsClassNumber

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 2000000 in
/-- **Proposition 3.8, Step 4 / P6 (numeric closers).** -/
theorem FieldConstructionNumericBounds :
    ∀ (C_class : ℝ), 0 < C_class →
    ∀ (C : ℝ), 0 < C →
    ∃ C' : ℝ, 0 < C' ∧ ∃ L₀ : ℕ, 0 < L₀ ∧
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ∀ (F : Type) [Field F] [NumberField F],
          NumberField.IsTotallyReal F →
          Module.finrank ℚ F = 3 →
          Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) →
          0 < (2 * rootDiscriminant F) ^ (2 * C_class) ∧
          Real.log ((2 * rootDiscriminant F) ^ (2 * C_class)) ≤
              C' * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
          0 < (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) * Real.log 2 -
                Real.log ((2 * rootDiscriminant F) ^ (2 * C_class)) := by
  intro C_class hC_class C hC
  -- constants
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L2 := Real.log 2 with hL2def
  set K := 2 * C_class * C with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  set a := 400 * K / L2 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  set D := 2 * C_class * L2 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  -- the threshold L₀
  refine ⟨K + 1, by positivity,
    max 4 (max ⌈D⌉₊ (max ⌈800 * K * a / L2⌉₊ ⌈800 * (D + L2 + 1) / L2⌉₊)),
    lt_of_lt_of_le (by norm_num : (0:ℕ) < 4) (le_max_left _ _), ?_⟩
  intro ℓ hℓ F _ _ _hTR _hrank hlogrd
  -- unpack the threshold
  simp only [max_le_iff] at hℓ
  obtain ⟨h4, hnD, hnA, hnB⟩ := hℓ
  have hℓ4 : (4:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h4
  have hℓpos : (0:ℝ) < (ℓ:ℝ) := by linarith
  have h1le : 1 ≤ ℓ := by omega
  have hD_le : D ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil D) (by exact_mod_cast hnD)
  have hA_le : 800 * K * a / L2 ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnA)
  have hB_le : 800 * (D + L2 + 1) / L2 ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnB)
  -- root discriminant positivity
  have hrd : 0 < rootDiscriminant F := by
    unfold rootDiscriminant
    apply Real.rpow_pos_of_pos
    have h : ((NumberField.discr F : ℝ)) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
    positivity
  set rd := rootDiscriminant F with hrddef
  have h2rd : (0:ℝ) < 2 * rd := by linarith
  -- log ℓ facts
  have hlogℓ_nonneg : 0 ≤ Real.log (ℓ:ℝ) := Real.log_nonneg (by linarith)
  have hlogℓ_ge1 : 1 ≤ Real.log (ℓ:ℝ) := by
    rw [Real.le_log_iff_exp_le hℓpos]
    have := Real.exp_one_lt_d9
    linarith
  -- log H equation
  set logH := Real.log ((2 * rd) ^ (2 * C_class)) with hlogHdef
  have hlogH_eq : logH = 2 * C_class * (L2 + Real.log rd) := by
    rw [hlogHdef, Real.log_rpow h2rd, Real.log_mul (by norm_num) (ne_of_gt hrd)]
  -- upper bound in ℓ·log ℓ form
  have hlogH_le1 : logH ≤ D + K * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by
    rw [hlogH_eq, hDdef]
    have h2c : (0:ℝ) < 2 * C_class := by positivity
    have hstep : 2 * C_class * (L2 + Real.log rd) ≤ 2 * C_class * (L2 + C * (ℓ:ℝ) * Real.log (ℓ:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hlogrd]) (le_of_lt h2c)
    have hexp : 2 * C_class * (L2 + C * (ℓ:ℝ) * Real.log (ℓ:ℝ))
        = 2 * C_class * L2 + K * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by rw [hKdef]; ring
    linarith [hstep, hexp.le, hexp.ge]
  -- goal 2 : logH ≤ (K+1)·ℓ·log ℓ
  have hgoal2 : logH ≤ (K + 1) * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by
    have hDlll : D ≤ (ℓ:ℝ) * Real.log (ℓ:ℝ) := by nlinarith [hlogℓ_ge1, hℓpos, hD_le]
    nlinarith [hlogH_le1, hDlll]
  -- tangent bound for log ℓ
  have hlogℓ_tan : Real.log (ℓ:ℝ) ≤ (ℓ:ℝ) / a + a := by
    have e1 : Real.log ((ℓ:ℝ) / a) ≤ (ℓ:ℝ) / a - 1 := Real.log_le_sub_one_of_pos (div_pos hℓpos ha)
    have e2 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha
    have e3 : Real.log (ℓ:ℝ) = Real.log a + Real.log ((ℓ:ℝ) / a) := by
      rw [← Real.log_mul (ne_of_gt ha) (ne_of_gt (div_pos hℓpos ha))]
      congr 1
      field_simp
    rw [e3]; linarith
  -- K·log ℓ ≤ (L2/400)·ℓ + K·a
  have hKa_eq : K * ((ℓ:ℝ) / a) = (L2 / 400) * (ℓ:ℝ) := by
    rw [hadef]; field_simp
  have hKlog : K * Real.log (ℓ:ℝ) ≤ (L2 / 400) * (ℓ:ℝ) + K * a := by
    have h := mul_le_mul_of_nonneg_left hlogℓ_tan (le_of_lt hK)
    have : K * ((ℓ:ℝ) / a + a) = (L2 / 400) * (ℓ:ℝ) + K * a := by rw [← hKa_eq]; ring
    linarith [h, this.le, this.ge]
  -- upper bound in ℓ² form
  have hstep2 : K * (ℓ:ℝ) * Real.log (ℓ:ℝ) ≤ (L2 / 400) * (ℓ:ℝ)^2 + K * a * (ℓ:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hKlog (le_of_lt hℓpos)
    nlinarith [h]
  have hlogH_le2 : logH ≤ D + (L2 / 400) * (ℓ:ℝ)^2 + K * a * (ℓ:ℝ) := by
    linarith [hlogH_le1, hstep2]
  -- lower bound on t (the nat-division floor)
  have hnat_div : ∀ n : ℕ, (n : ℝ) / 100 - 1 ≤ ((n / 100 : ℕ) : ℝ) := by
    intro n
    have hdm : 100 * (n / 100) + n % 100 = n := Nat.div_add_mod n 100
    have hmod : n % 100 < 100 := Nat.mod_lt n (by norm_num)
    have h1 : (100 : ℝ) * ((n / 100 : ℕ) : ℝ) + ((n % 100 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
    have h2 : ((n % 100 : ℕ) : ℝ) < 100 := by exact_mod_cast hmod
    linarith
  set t := (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) with htdef
  have hcast : (((ℓ - 1) ^ 2 : ℕ) : ℝ) = ((ℓ:ℝ) - 1)^2 := by
    push_cast [Nat.cast_sub h1le]
    ring
  have ht_lb : ((ℓ:ℝ) - 1)^2 / 100 - 1 ≤ t := by
    have h := hnat_div ((ℓ - 1) ^ 2)
    rw [htdef, ← hcast]
    exact h
  -- (ℓ-1)² ≥ ℓ²/2 for ℓ ≥ 4
  have hquad : (ℓ:ℝ)^2 / 2 ≤ ((ℓ:ℝ) - 1)^2 := by nlinarith [hℓ4]
  have ht_ell2 : (ℓ:ℝ)^2 / 200 - 1 ≤ t := by nlinarith [ht_lb, hquad]
  -- threshold consequences
  have hAfin : K * a * (ℓ:ℝ) ≤ (L2 / 800) * (ℓ:ℝ)^2 := by
    have h800 : 800 * K * a ≤ (ℓ:ℝ) * L2 := by rw [div_le_iff₀ hL2] at hA_le; exact hA_le
    nlinarith [mul_le_mul_of_nonneg_right h800 (le_of_lt hℓpos), hℓpos]
  have hBfin : D + L2 + 1 ≤ (L2 / 800) * (ℓ:ℝ)^2 := by
    have h800 : 800 * (D + L2 + 1) ≤ (ℓ:ℝ) * L2 := by rw [div_le_iff₀ hL2] at hB_le; exact hB_le
    have hℓsq : (ℓ:ℝ) ≤ (ℓ:ℝ)^2 := by nlinarith [hℓ4]
    nlinarith [h800, hℓsq, hL2]
  -- assemble the three goals
  refine ⟨Real.rpow_pos_of_pos h2rd _, hgoal2, ?_⟩
  -- P6
  have htL2 : ((ℓ:ℝ)^2 / 200 - 1) * L2 ≤ t * L2 :=
    mul_le_mul_of_nonneg_right ht_ell2 (le_of_lt hL2)
  -- work with s = ℓ² as an opaque nonneg atom to keep the final step linear
  have htL2' : L2 * (ℓ:ℝ)^2 / 200 - L2 ≤ t * L2 := by nlinarith [htL2]
  have hAfin' : K * a * (ℓ:ℝ) ≤ L2 * (ℓ:ℝ)^2 / 800 := by nlinarith [hAfin]
  have hBfin' : D + L2 + 1 ≤ L2 * (ℓ:ℝ)^2 / 800 := by nlinarith [hBfin]
  have hlogH_le2' : logH ≤ D + L2 * (ℓ:ℝ)^2 / 400 + K * a * (ℓ:ℝ) := by nlinarith [hlogH_le2]
  linarith [htL2', hAfin', hBfin', hlogH_le2']
