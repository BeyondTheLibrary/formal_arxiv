import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide

/-!
# Path4CentralCDF — left-tail CDF of a fair Bin(n) up to 3n/8

We prove that the cumulative probability `Bin(n, 1/2) ≤ 3n/8` is at most
`exp(-n/128)`. This is a left deviation of `n/8` from the mean `n/2`; the
optimal Chernoff bound here gives roughly `exp(-n/32)`, so `exp(-n/128)`
holds with ample slack.

Strategy (reuse the Chernoff machinery from `CentralBinomialLowerTailWide`):
* `chernoff_optimal_bound n K : ∑_{k<K} binPMF n (1/2) k ≤ (9/7)^K · (8/9)^n`.
* Take `q := n/8`, so `8q ≤ n` and `3*n/8 + 1 ≤ 3q + 3`. Extend the sum to
  `Finset.range (3q+3)`.
* `(9/7)^(3q+3) · (8/9)^n ≤ (9/7)^3 · ((9/7)^3 · (8/9)^8)^q`.
* Numerical: `(9/7)^3 · (8/9)^8 ≤ exp(-1/8)`.
* So LHS `≤ 6 · exp(-q/8)`, and `6 · exp(-q/8) ≤ exp(-n/128)` since
  `q = n/8 ≥ n/16 + 8·log 6` for `n ≥ 10^12`.
-/

set_option maxHeartbeats 4000000

open Workspace.Types.AlternatingSumExpression

namespace Workspace.ProofLemmas.Path4CentralCDF

open CentralBinomialLowerTailWideProof

-- Numerical base fact: (9/7)^3 · (8/9)^8 ≤ exp(-1/8).
-- (9/7)^3 · (8/9)^8 = 729·16777216 / (343·43046721)
--                   = 12230590464 / 14765025303 ≈ 0.82835.
-- Inverse = 14765025303 / 12230590464 ≈ 1.20722.
-- exp(1/8) = exp(0.125) ≈ 1.13315 ≤ 1.20722. ✓
lemma base_le_exp_neg_eighth :
    (9/7:ℝ)^3 * (8/9:ℝ)^8 ≤ Real.exp (-(1/8)) := by
  have h_exp_le : Real.exp (1/8) ≤ 14765025303/12230590464 := by
    have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1/8)
                              (by norm_num : (1/8:ℝ) ≤ 1) (n := 4) (by norm_num : 0 < 4)
    refine h.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
      Nat.factorial, zero_add]
    norm_num
  have h_exp_pos : (0:ℝ) < Real.exp (1/8) := Real.exp_pos _
  rw [Real.exp_neg]
  have h_lhs_pos : (0:ℝ) < (9/7:ℝ)^3 * (8/9:ℝ)^8 := by positivity
  rw [le_inv_comm₀ h_lhs_pos h_exp_pos]
  refine le_trans h_exp_le ?_
  rw [show ((9/7:ℝ)^3 * (8/9:ℝ)^8)⁻¹ = 14765025303/12230590464 from by
    rw [show (9/7:ℝ)^3 * (8/9:ℝ)^8 = 12230590464/14765025303 from by norm_num]
    rw [inv_div]]

theorem central_binomial_left_cdf_le (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    ∑ k ∈ Finset.range (3 * n / 8 + 1),
        Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- q := n/8.
  set q : ℕ := n / 8 with hq_def
  have h8q_le : 8 * q ≤ n := by rw [hq_def]; exact Nat.mul_div_le n 8
  have hq_real_ge : (n : ℝ)/8 - 1 ≤ (q : ℝ) := by
    have h : 8 * (n / 8) + 8 > n := by
      have := Nat.div_add_mod n 8
      have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    have h_real : 8 * ((n / 8 : ℕ) : ℝ) + 8 > (n : ℝ) := by exact_mod_cast h
    rw [hq_def]; linarith
  -- Step 0: 3*n/8 + 1 ≤ 3*q + 3, so range (3n/8+1) ⊆ range (3q+3).
  have h_range_le : 3 * n / 8 + 1 ≤ 3 * q + 3 := by
    rw [hq_def]
    have := Nat.div_add_mod n 8
    have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  -- Step 1: extend the sum to range (3q+3).
  have h_step_bound :
      (∑ k ∈ Finset.range (3 * n / 8 + 1),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
        ≤ (∑ k ∈ Finset.range (3 * q + 3),
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_range] at *
      exact lt_of_lt_of_le hx h_range_le
    · intros k _ _
      exact binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)
  -- Step 2: Chernoff.
  have h_chernoff : (∑ k ∈ Finset.range (3 * q + 3),
                      Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
                    ≤ (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n :=
    chernoff_optimal_bound n (3 * q + 3)
  -- Step 3a: (9/7)^{3q+3} · (8/9)^n ≤ (9/7)^3 · ((9/7)^3 · (8/9)^8)^q.
  have h_step3a : (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
                ≤ (9/7:ℝ)^3 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := by
    have hk_split : (9/7:ℝ)^(3*q+3) = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) := by
      rw [← pow_add]; congr 1; ring
    rw [hk_split]
    have h_n_split : (8/9:ℝ)^n = (8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q) := by
      rw [← pow_add]; congr 1; omega
    rw [h_n_split]
    have h_89_le1 : (8/9:ℝ)^(n - 8*q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h_97q_nn : (0:ℝ) ≤ (9/7:ℝ)^(3*q) := pow_nonneg (by norm_num) _
    have h_89_8q_nn : (0:ℝ) ≤ (8/9:ℝ)^(8*q) := pow_nonneg (by norm_num) _
    have h_97_three_nn : (0:ℝ) ≤ (9/7:ℝ)^3 := pow_nonneg (by norm_num) _
    have hrhs_eq : ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q = (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by
      rw [mul_pow]
      have e1 : ((9/7:ℝ)^3)^q = (9/7:ℝ)^(3*q) := by rw [← pow_mul]
      have e2 : ((8/9:ℝ)^8)^q = (8/9:ℝ)^(8*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * ((8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q))
              = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) * (8/9:ℝ)^(n - 8*q) := by ring
    rw [hbase]
    have hbase2 : (9/7:ℝ)^3 * ((9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q))
                = (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (9/7:ℝ)^3 * (9/7:ℝ)^(3*q) * (8/9:ℝ)^(8*q) := by
      apply mul_nonneg
      apply mul_nonneg h_97_three_nn h_97q_nn
      exact h_89_8q_nn
    have := mul_le_mul_of_nonneg_left h_89_le1 hcoef_nn
    linarith
  -- Step 3b: ((9/7)^3 · (8/9)^8)^q ≤ exp(-q/8).
  have h_step3b : ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q ≤ Real.exp (-((q:ℝ) / 8)) := by
    have h_base_nn : (0:ℝ) ≤ (9/7:ℝ)^3 * (8/9:ℝ)^8 := by positivity
    have h_pow := pow_le_pow_left₀ h_base_nn base_le_exp_neg_eighth q
    rw [← Real.exp_nat_mul] at h_pow
    rw [show ((q:ℝ) * -(1/8)) = -((q:ℝ) / 8) from by ring] at h_pow
    exact h_pow
  -- Step 3c: (9/7)^3 ≤ 6.
  have h_97_three_le_6 : (9/7:ℝ)^3 ≤ 6 := by norm_num
  -- Combine: LHS ≤ 6 · exp(-q/8).
  have h_combined : (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
                ≤ 6 * Real.exp (-((q:ℝ) / 8)) := by
    calc (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n
        ≤ (9/7:ℝ)^3 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := h_step3a
      _ ≤ 6 * ((9/7:ℝ)^3 * (8/9:ℝ)^8)^q := by
          apply mul_le_mul_of_nonneg_right h_97_three_le_6
          exact pow_nonneg (by positivity) _
      _ ≤ 6 * Real.exp (-((q:ℝ) / 8)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 6)
  -- Step 4: 6 · exp(-q/8) ≤ exp(-n/128).
  -- Need q/8 ≥ n/128 + log 6.  q ≥ n/8 - 1.
  have h_log6_le : Real.log 6 ≤ 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have h_6_le_exp : (6 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_le_exp.mpr h_log6_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 6)] at h
  have h_step4 : 6 * Real.exp (-((q:ℝ) / 8)) ≤ Real.exp (-((n:ℝ)/128)) := by
    have h_exp_combined : Real.exp 5 * Real.exp (-((q:ℝ) / 8))
                        = Real.exp (5 - (q:ℝ) / 8) := by
      rw [← Real.exp_add]; ring_nf
    have h_lhs_le : 6 * Real.exp (-((q:ℝ) / 8))
                  ≤ Real.exp 5 * Real.exp (-((q:ℝ) / 8)) := by
      apply mul_le_mul_of_nonneg_right h_6_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    apply Real.exp_le_exp.mpr
    -- Need: 5 - q/8 ≤ -n/128.
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    nlinarith [hq_real_ge, h_n_large]
  -- Combine all.
  calc (∑ k ∈ Finset.range (3 * n / 8 + 1),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
      ≤ (∑ k ∈ Finset.range (3 * q + 3),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(3 * q + 3) * (8/9:ℝ)^n := h_chernoff
    _ ≤ 6 * Real.exp (-((q:ℝ) / 8)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4

end Workspace.ProofLemmas.Path4CentralCDF
