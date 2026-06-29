import Mathlib
import Workspace.Types.AlternatingSumExpression

set_option maxHeartbeats 32000000

open Workspace.Types.AlternatingSumExpression

namespace AtypicalZTailBoundProof

-- Helper lemma: binomial weighted sum identity
-- For m : ℕ and 0 ≤ p ≤ 1:
--   ∑ z ∈ range (m+1), C(m,z) · (p/2)^z · (1-p)^(m-z) = (p/2 + (1-p))^m
lemma weighted_binomial_sum (m : ℕ) (p : ℝ) :
    (∑ z ∈ Finset.range (m+1), (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z))
      = (p/2 + (1-p))^m := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro z _
  ring

-- Lemma: for z ≤ m, binPMF m p z = C(m,z) p^z (1-p)^(m-z)
lemma binPMF_mul_two_pow (m z : ℕ) (p : ℝ) (hz : z ≤ m) :
    binPMF m p z = (m.choose z : ℝ) * p^z * (1-p)^(m-z) := by
  unfold binPMF
  rw [if_pos hz]

-- For real p ∈ [0,1] and any z, binPMF m p z ≥ 0.
lemma binPMF_nonneg (m z : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMF m p z := by
  unfold binPMF
  split_ifs with h
  · apply mul_nonneg
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg hp _
    · exact pow_nonneg (by linarith) _
  · exact le_refl 0

-- The sum ∑ z, C(m,z) · (p/2)^z · (1-p)^(m-z) = (1 - p/2)^m for p ≤ 1
lemma sum_two_pow_neg_binPMF (m : ℕ) (p : ℝ) (_hp : 0 ≤ p) (_hp1 : p ≤ 1) :
    (∑ z ∈ Finset.range (m+1), (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z))
      = (1 - p/2)^m := by
  rw [weighted_binomial_sum]
  congr 1
  ring

lemma one_sub_p_half_le (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    1 - p/2 ≤ 3/4 := by linarith

lemma one_sub_p_half_nonneg (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ 1 - p/2 := by linarith

-- For z ≤ m:
--   binPMF m p z = (C(m,z) · (p/2)^z · (1-p)^(m-z)) · 2^z
lemma binPMF_eq_two_pow_factored (m z : ℕ) (p : ℝ) (hz : z ≤ m) :
    binPMF m p z = (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) * (2:ℝ)^z := by
  rw [binPMF_mul_two_pow m z p hz]
  rw [div_pow]
  field_simp

-- Main Chernoff-style bound:
-- For p ∈ [1/2, 1], k ≤ m + 1:
-- ∑ z < k, binPMF m p z ≤ 2^k · (3/4)^m
lemma chernoff_lower_tail_bound
    (m k : ℕ) (p : ℝ)
    (hp_lb : 1/2 ≤ p) (hp_ub : p ≤ 1)
    (_hk_le_m : k ≤ m + 1) :
    (∑ z ∈ Finset.range k, binPMF m p z)
      ≤ (2 : ℝ)^k * (3/4)^m := by
  have h1 : (∑ z ∈ Finset.range k, binPMF m p z)
        ≤ (2 : ℝ)^k * ∑ z ∈ Finset.range k, (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    rw [Finset.mem_range] at hz
    by_cases hzm : z ≤ m
    · rw [binPMF_eq_two_pow_factored m z p hzm]
      have hzk : z ≤ k := Nat.le_of_lt hz
      have h2pow : (2:ℝ)^z ≤ (2:ℝ)^k :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hzk
      have hC_nonneg : (0:ℝ) ≤ (m.choose z : ℝ) := by exact_mod_cast Nat.zero_le _
      have hp2_nonneg : (0:ℝ) ≤ (p/2)^z := pow_nonneg (by linarith) _
      have h1mp_nonneg : (0:ℝ) ≤ (1-p)^(m-z) := pow_nonneg (by linarith) _
      have hbase_nonneg : (0:ℝ) ≤ (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := by
        apply mul_nonneg
        apply mul_nonneg hC_nonneg hp2_nonneg
        exact h1mp_nonneg
      calc (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) * 2^z
          ≤ (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) * (2:ℝ)^k := by
            apply mul_le_mul_of_nonneg_left h2pow hbase_nonneg
        _ = (2:ℝ)^k * ((m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z)) := by ring
    · -- z > m, so binPMF m p z = 0 and RHS ≥ 0
      push_neg at hzm
      have hLHS : binPMF m p z = 0 := by
        unfold binPMF
        rw [if_neg (by omega)]
      rw [hLHS]
      have h2k_nn : (0:ℝ) ≤ (2:ℝ)^k := pow_nonneg (by norm_num) _
      have hC_nonneg : (0:ℝ) ≤ (m.choose z : ℝ) := by exact_mod_cast Nat.zero_le _
      have hp2_nonneg : (0:ℝ) ≤ (p/2)^z := pow_nonneg (by linarith) _
      have h1mp_nonneg : (0:ℝ) ≤ (1-p)^(m-z) := pow_nonneg (by linarith) _
      have hbase_nonneg : (0:ℝ) ≤ (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := by
        apply mul_nonneg
        apply mul_nonneg hC_nonneg hp2_nonneg
        exact h1mp_nonneg
      exact mul_nonneg h2k_nn hbase_nonneg
  have h2 : (∑ z ∈ Finset.range k, (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z))
        ≤ ∑ z ∈ Finset.range (m+1), (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_range] at *
      omega
    · intros z _ _
      apply mul_nonneg
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact pow_nonneg (by linarith) _
      · exact pow_nonneg (by linarith) _
  have h3 := sum_two_pow_neg_binPMF m p (by linarith : (0:ℝ) ≤ p) hp_ub
  calc (∑ z ∈ Finset.range k, binPMF m p z)
      ≤ (2 : ℝ)^k * ∑ z ∈ Finset.range k, (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := h1
    _ ≤ (2 : ℝ)^k * ∑ z ∈ Finset.range (m+1), (m.choose z : ℝ) * (p/2)^z * (1-p)^(m-z) := by
        apply mul_le_mul_of_nonneg_left h2
        exact pow_nonneg (by norm_num) _
    _ = (2 : ℝ)^k * (1 - p/2)^m := by rw [h3]
    _ ≤ (2 : ℝ)^k * (3/4)^m := by
        apply mul_le_mul_of_nonneg_left
        · apply pow_le_pow_left₀
          · exact one_sub_p_half_nonneg p hp_lb hp_ub
          · exact one_sub_p_half_le p hp_lb hp_ub
        · exact pow_nonneg (by norm_num) _

-- Numerical fact: exp(1/7) ≤ 32/27.
lemma exp_one_seventh_le_thirty_two_over_twenty_seven :
    Real.exp (1/7) ≤ 32/27 := by
  have hx_nn : (0:ℝ) ≤ 1/7 := by norm_num
  have hx_le : (1/7:ℝ) ≤ 1 := by norm_num
  have h := Real.exp_bound' hx_nn hx_le (n := 5) (by norm_num : 0 < 5)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.factorial, zero_add]
  norm_num

-- log(32/27) ≥ 1/7
lemma log_thirty_two_over_twenty_seven_ge_one_seventh :
    (1:ℝ)/7 ≤ Real.log (32/27) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 32/27)]
  exact exp_one_seventh_le_thirty_two_over_twenty_seven

-- exp(1/3) ≥ 4/3 (equivalently log(4/3) ≤ 1/3)
-- We show 4/3 ≤ exp(1/3) using a simple lower bound: exp x ≥ 1 + x.
lemma exp_one_third_ge_four_thirds :
    (4:ℝ)/3 ≤ Real.exp (1/3) := by
  -- Use Real.add_one_le_exp: 1 + x ≤ exp x for all x.
  have h := Real.add_one_le_exp (1/3 : ℝ)
  linarith

-- log(4/3) ≤ 1/3
lemma log_four_thirds_le_one_third :
    Real.log (4/3) ≤ (1:ℝ)/3 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 4/3)]
  exact exp_one_third_ge_four_thirds

-- log(4/3) > 0
lemma log_four_thirds_pos :
    (0:ℝ) < Real.log (4/3) := by
  apply Real.log_pos
  norm_num

-- Cast inequality: ((n/16 : ℕ) : ℝ) ≤ (n : ℝ) / 16
lemma cast_div_16_le (n : ℕ) : ((n / 16 : ℕ) : ℝ) ≤ (n : ℝ) / 16 := by
  exact_mod_cast Nat.cast_div_le

-- Cast inequality: (n : ℝ)/16 ≤ ((n/16 : ℕ) : ℝ) + 1, i.e., (n/16 : ℕ) ≥ n/16 - 1.
lemma cast_div_16_ge (n : ℕ) : (n : ℝ) / 16 - 1 ≤ ((n / 16 : ℕ) : ℝ) := by
  have h : 16 * (n / 16) + 16 > n := by
    have := Nat.div_add_mod n 16
    have hmod : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
    omega
  have h_real : 16 * ((n / 16 : ℕ) : ℝ) + 16 > (n : ℝ) := by exact_mod_cast h
  linarith

-- 2^k * (3/4)^m ≤ exp(-n/128) under n ≥ 10^12, k ≤ n/16, m + 4 ≥ 3*(n/16)
lemma two_pow_three_quarters_pow_le_exp
    (n m k : ℕ) (hn : (10^12 : ℕ) ≤ n)
    (hk : k ≤ n / 16)
    (hm : 3 * (n / 16) ≤ m + 4) :
    (2 : ℝ)^k * (3/4)^m ≤ Real.exp (-((n : ℝ) / 128)) := by
  set L := Real.log (2^k * (3/4)^m) with hL_def
  have hpos : (0:ℝ) < 2^k * (3/4)^m := by
    apply mul_pos
    · exact pow_pos (by norm_num) _
    · exact pow_pos (by norm_num) _
  rw [show (2:ℝ)^k * (3/4)^m = Real.exp L from (Real.exp_log hpos).symm]
  rw [Real.exp_le_exp]
  have hL_eq : L = (k : ℝ) * Real.log 2 + (m : ℝ) * Real.log (3/4) := by
    rw [hL_def]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
  rw [hL_eq]
  -- Need: k log 2 + m log(3/4) ≤ -n/128
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog34_neg : Real.log (3/4) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlog34_eq : Real.log (3/4) = - Real.log (4/3) := by
    rw [show (3:ℝ)/4 = (4/3)⁻¹ from by ring, Real.log_inv]
  have hlog43_pos : (0:ℝ) < Real.log (4/3) := log_four_thirds_pos
  have hlog43_le : Real.log (4/3) ≤ (1:ℝ)/3 := log_four_thirds_le_one_third
  -- Useful: log 2 + 3 log(3/4) = log(2 * (3/4)^3) = log(54/64) = log(27/32) = -log(32/27)
  have hkey_eq : Real.log 2 + 3 * Real.log (3/4) = - Real.log (32/27) := by
    have h1 : Real.log 2 + 3 * Real.log (3/4) = Real.log 2 + Real.log ((3/4)^3) := by
      rw [Real.log_pow]; ring
    rw [h1]
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity)]
    have h2 : (2:ℝ) * (3/4)^3 = 27/32 := by norm_num
    rw [h2]
    rw [show (27:ℝ)/32 = (32/27)⁻¹ from by norm_num, Real.log_inv]
  have hlog3227 : (1:ℝ)/7 ≤ Real.log (32/27) :=
    log_thirty_two_over_twenty_seven_ge_one_seventh
  -- Cast bounds
  have hk_real : (k : ℝ) ≤ (n : ℝ) / 16 := by
    have h1 : (k : ℝ) ≤ ((n / 16 : ℕ) : ℝ) := by exact_mod_cast hk
    have h2 : ((n / 16 : ℕ) : ℝ) ≤ (n : ℝ) / 16 := cast_div_16_le n
    linarith
  have hm_real : 3 * (n : ℝ) / 16 - 7 ≤ (m : ℝ) := by
    -- 3 * (n/16) ≤ m + 4. Cast: 3 * ((n/16 : ℕ) : ℝ) ≤ (m : ℝ) + 4
    have h2 : (3 : ℝ) * ((n / 16 : ℕ) : ℝ) ≤ (m : ℝ) + 4 := by
      have hh : ((3 * (n / 16) : ℕ) : ℝ) ≤ ((m + 4 : ℕ) : ℝ) := by exact_mod_cast hm
      push_cast at hh
      linarith
    -- Use cast_div_16_ge: (n : ℝ)/16 - 1 ≤ ((n/16:ℕ) : ℝ)
    have h3 : (n : ℝ) / 16 - 1 ≤ ((n / 16 : ℕ) : ℝ) := cast_div_16_ge n
    -- 3 * ((n:ℝ)/16 - 1) ≤ 3 * ((n/16:ℕ):ℝ) ≤ m + 4
    have h4 : 3 * ((n : ℝ) / 16 - 1) ≤ (m : ℝ) + 4 := by nlinarith [h2, h3]
    linarith
  -- Now bound: (k : ℝ) * log 2 + (m : ℝ) * log(3/4)
  -- log(3/4) < 0, so (m : ℝ) * log(3/4) is decreasing in m. We use lower bound on m.
  -- (m : ℝ) ≥ 3n/16 - 4, so (m : ℝ) * log(3/4) ≤ (3n/16 - 4) * log(3/4)
  -- (k : ℝ) ≤ n/16, log 2 > 0, so k * log 2 ≤ (n/16) * log 2
  have h_upper : (k : ℝ) * Real.log 2 + (m : ℝ) * Real.log (3/4)
                  ≤ (n : ℝ)/16 * Real.log 2 + (3 * (n : ℝ)/16 - 7) * Real.log (3/4) := by
    have hk_term : (k : ℝ) * Real.log 2 ≤ (n : ℝ)/16 * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right hk_real (le_of_lt hlog2_pos)
    have hm_term : (m : ℝ) * Real.log (3/4) ≤ (3 * (n : ℝ)/16 - 7) * Real.log (3/4) := by
      have : (3 * (n : ℝ)/16 - 7) * Real.log (3/4) - (m : ℝ) * Real.log (3/4)
              = ((3 * (n : ℝ)/16 - 7) - (m : ℝ)) * Real.log (3/4) := by ring
      have hsub_neg : (3 * (n : ℝ)/16 - 7) - (m : ℝ) ≤ 0 := by linarith
      nlinarith [hlog34_neg, hsub_neg]
    linarith
  -- Simplify (n/16) * log 2 + (3n/16 - 7) * log(3/4) = (n/16) * (log 2 + 3 log(3/4)) - 7 * log(3/4)
  --   = -(n/16) * log(32/27) + 7 * log(4/3)
  have h_simplify : (n : ℝ)/16 * Real.log 2 + (3 * (n : ℝ)/16 - 7) * Real.log (3/4)
                    = -((n : ℝ)/16) * Real.log (32/27) + 7 * Real.log (4/3) := by
    have : (n : ℝ)/16 * Real.log 2 + (3 * (n : ℝ)/16 - 7) * Real.log (3/4)
            = (n : ℝ)/16 * (Real.log 2 + 3 * Real.log (3/4)) - 7 * Real.log (3/4) := by ring
    rw [this, hkey_eq, hlog34_eq]
    ring
  rw [h_simplify] at h_upper
  have hn_real : (10^12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Step: -(n/16) * log(32/27) ≤ -(n/16) * (1/7) = -n/112
  have h_small_log : -((n : ℝ)/16) * Real.log (32/27) ≤ -((n : ℝ)/16) * (1/7) := by
    have hn16_nn : (0:ℝ) ≤ (n : ℝ)/16 := by positivity
    nlinarith [hlog3227, hn16_nn]
  -- Step: 7 * log(4/3) ≤ 7 * (1/3) = 7/3
  have h_log43_bound : 7 * Real.log (4/3) ≤ 7 * (1/3 : ℝ) := by
    nlinarith [hlog43_le]
  -- Combine
  have h_combined : -((n : ℝ)/16) * Real.log (32/27) + 7 * Real.log (4/3)
                      ≤ -((n : ℝ)/16) * (1/7) + 7 * (1/3) := by
    linarith
  -- Now: -((n:ℝ)/16) * (1/7) + 7/3 = -n/112 + 7/3
  -- Need: -n/112 + 7/3 ≤ -n/128
  -- iff: n/128 + 7/3 ≤ n/112
  -- iff: 7/3 ≤ n/112 - n/128 = n/896
  -- iff: n ≥ 7 * 896 / 3 ≈ 2090.67. Since n ≥ 10^12, ✓
  have h_final : -((n : ℝ)/16) * (1/7) + 7 * (1/3 : ℝ) ≤ -((n : ℝ) / 128) := by
    have : (n : ℝ) ≥ 10^12 := hn_real
    nlinarith [this]
  linarith

-- Helper: convert binPMFInt (m : ℕ) p (z : ℤ) where z = (z' : ℕ) and z' ≤ m to binPMF.
lemma binPMFInt_of_nat_le (m : ℕ) (p : ℝ) (z : ℕ) (hz : z ≤ m) :
    binPMFInt m p (z : ℤ) = binPMF m p z := by
  unfold binPMFInt
  have h0 : (0 : ℤ) ≤ (z : ℤ) := Int.ofNat_nonneg z
  have h1 : (z : ℤ) ≤ (m : ℤ) := by exact_mod_cast hz
  rw [if_pos ⟨h0, h1⟩]
  simp [Int.toNat_natCast]

-- Helper for nonneg of binPMFInt
lemma binPMFInt_nonneg (m : ℕ) (p : ℝ) (z : ℤ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMFInt m p z := by
  unfold binPMFInt
  split_ifs with h
  · exact binPMF_nonneg m z.toNat p hp hp1
  · exact le_refl 0

end AtypicalZTailBoundProof

-- Theorem statements byte-identical to formalization:

theorem AtypicalZTailBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
      ∀ (r : ℤ),
        -((n : ℤ) / 8) + ((n : ℤ) / 16) ≤ r → r ≤ ((n : ℤ) / 4) →
        (∑ z ∈ Finset.range (n / 16),
            Workspace.Types.AlternatingSumExpression.binPMFInt
              ((n / 4 : ℤ) + r).toNat (1 - δ) z)
          ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn _hn8 δ hδ_pos hδ_half r hr_lb _hr_ub
  -- Set m and p
  set m : ℕ := ((n / 4 : ℤ) + r).toNat with hm_def
  set p : ℝ := 1 - δ with hp_def
  -- p ∈ [1/2, 1]
  have hp_lb : (1:ℝ)/2 ≤ p := by rw [hp_def]; linarith
  have hp_ub : p ≤ 1 := by rw [hp_def]; linarith
  have hp_nonneg : (0:ℝ) ≤ p := by linarith
  -- Show (n/4 + r : ℤ) ≥ 0 so toNat preserves it
  have h_n4_int : (0 : ℤ) ≤ (n : ℤ)/4 := by positivity
  have h_n8_int : (0 : ℤ) ≤ (n : ℤ)/8 := by positivity
  have h_n16_int : (0 : ℤ) ≤ (n : ℤ)/16 := by positivity
  -- (n/4 : ℤ) + r ≥ (n/4) - (n/8) + (n/16) ≥ 0 (we'll need this)
  have hr_lb' : (n : ℤ)/4 + r ≥ (n : ℤ)/4 - (n : ℤ)/8 + (n : ℤ)/16 := by linarith
  have h_pos_sum : (0 : ℤ) ≤ (n : ℤ)/4 - (n : ℤ)/8 + (n : ℤ)/16 := by
    -- For n ≥ 10^12, 4n/16 - 2n/16 + n/16 = 3n/16 ≥ 0
    -- More precisely, n/4 ≥ n/8 always (omega proves)
    have : (n : ℤ)/4 ≥ (n : ℤ)/8 := by
      have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    linarith
  have h_n4r_nonneg : (0 : ℤ) ≤ (n : ℤ)/4 + r := by linarith
  -- Now m = (n/4 + r).toNat with (m : ℤ) = (n/4 + r)
  have hm_int : (m : ℤ) = (n : ℤ)/4 + r := by
    rw [hm_def]
    exact Int.toNat_of_nonneg h_n4r_nonneg
  -- Bound on m: m ≥ 3n/16 - small
  have hm_ge : 3 * (n / 16) ≤ m + 4 := by
    -- (m : ℤ) = n/4 + r ≥ n/4 - n/8 + n/16
    -- We need: 3 * (n/16) ≤ m + 4 (in ℕ)
    have h1 : ((3 * (n / 16) : ℕ) : ℤ) ≤ (m : ℤ) + 4 := by
      have hm_lb_int : (n : ℤ)/4 - (n : ℤ)/8 + (n : ℤ)/16 ≤ (m : ℤ) := by linarith
      have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h_cast_eq : ((3 * (n / 16) : ℕ) : ℤ) = 3 * ((n : ℤ)/16) := by
        push_cast; ring
      rw [h_cast_eq]
      omega
    -- Cast back to ℕ
    have h2 : (3 * (n / 16) : ℕ) ≤ (m : ℕ) + 4 := by
      have := h1
      omega
    exact h2
  -- Bound on m for chernoff: need n/16 ≤ m + 1
  have hk_le_m : (n / 16 : ℕ) ≤ m + 1 := by
    -- m ≥ 3 * (n/16) - 4 (from hm_ge), so m + 1 ≥ 3 * (n/16) - 3
    -- For n ≥ 10^12, 3*(n/16) ≥ 3 * 10^11 ≫ n/16 + 3, so n/16 ≤ m + 1.
    -- We'll prove via natural number arithmetic.
    have h1 : 3 * (n / 16) ≤ m + 4 := hm_ge
    -- Need: n/16 ≤ m + 1, i.e., n/16 + 3 ≤ m + 4. Given 3*(n/16) ≤ m+4, need 3*(n/16) ≥ n/16+3
    -- iff 2*(n/16) ≥ 3 iff n/16 ≥ 2 (since n ≥ 32 say). True since n ≥ 10^12.
    have h_n16 : 2 ≤ n / 16 := by
      have : 32 ≤ n := by linarith
      omega
    omega
  -- Step 1: rewrite the sum using binPMFInt = binPMF
  have h_sum_eq : (∑ z ∈ Finset.range (n / 16),
                    Workspace.Types.AlternatingSumExpression.binPMFInt m (1 - δ) (z : ℤ))
                = (∑ z ∈ Finset.range (n / 16),
                    Workspace.Types.AlternatingSumExpression.binPMF m (1 - δ) z) := by
    apply Finset.sum_congr rfl
    intros z hz
    rw [Finset.mem_range] at hz
    have hzm : z ≤ m := by
      have : z < n / 16 := hz
      have : z + 1 ≤ n / 16 := this
      have h2 : n / 16 ≤ m + 1 := hk_le_m
      omega
    exact AtypicalZTailBoundProof.binPMFInt_of_nat_le m (1 - δ) z hzm
  -- Apply the chernoff bound
  rw [h_sum_eq]
  have h_chernoff := AtypicalZTailBoundProof.chernoff_lower_tail_bound m (n/16) p hp_lb hp_ub hk_le_m
  have h_final := AtypicalZTailBoundProof.two_pow_three_quarters_pow_le_exp n m (n/16) hn (le_refl _) hm_ge
  -- p = 1 - δ
  show (∑ z ∈ Finset.range (n / 16),
          Workspace.Types.AlternatingSumExpression.binPMF m (1 - δ) z)
        ≤ Real.exp (-((n : ℝ) / 128))
  calc (∑ z ∈ Finset.range (n / 16),
          Workspace.Types.AlternatingSumExpression.binPMF m (1 - δ) z)
      = (∑ z ∈ Finset.range (n / 16),
          Workspace.Types.AlternatingSumExpression.binPMF m p z) := by
        apply Finset.sum_congr rfl; intros; rfl
    _ ≤ (2 : ℝ)^(n / 16) * (3/4)^m := h_chernoff
    _ ≤ Real.exp (-((n : ℝ) / 128)) := h_final

theorem AtypicalZPlusTailBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
      ∀ (r : ℤ),
        -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 8) - ((n : ℤ) / 16) →
        (∑ z ∈ Finset.range (n / 16),
            Workspace.Types.AlternatingSumExpression.binPMFInt
              ((n / 4 : ℤ) - r).toNat (1 - δ) z)
          ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn hn8 δ hδ_pos hδ_half r _hr_lb hr_ub
  -- Apply AtypicalZTailBound with r' = -r
  -- (n/4 - r) = (n/4 + (-r))
  -- The hypothesis r ≤ (n/8) - (n/16) gives -r ≥ -(n/8) + (n/16)
  -- The hypothesis r ≥ -(n/4) gives -r ≤ n/4
  have h_neg_r_lb : -((n : ℤ) / 8) + ((n : ℤ) / 16) ≤ -r := by linarith
  have h_neg_r_ub : -r ≤ ((n : ℤ) / 4) := by linarith
  have h := AtypicalZTailBound n hn hn8 δ hδ_pos hδ_half (-r) h_neg_r_lb h_neg_r_ub
  -- (n/4 + (-r)) = (n/4 - r)
  have h_eq : ((n / 4 : ℤ) + (-r)) = ((n / 4 : ℤ) - r) := by ring
  rw [h_eq] at h
  exact h
