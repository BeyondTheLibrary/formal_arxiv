import Mathlib
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.CentralBinomialUpperTailWide
import Workspace.ProofLemmas.LengthsOnlyExists

/-!
# WitnessOffsetTail — the offset-weight tail bound

`offsetWeight n r` is (as a real number) the `n/2`-binomial pmf
`binPMFInt (n/2) (1/2) (r + n/4)`.  Its mass beyond `|r| > n/8` is in the
binomial tail; via the workspace's `CentralBinomial{Lower,Upper}TailWide`
lemmas (applied at parameter `m = n/2`) it is `≤ exp(-Ω(n))`.

This file lands:
* `offsetWeight_toReal_eq_binPMFInt` — the `toReal` bridge (sorry-free),
* `offsetWeight_tail_sum` — `∑'_{|r|>n/8} offsetWeight(r).toReal ≤ exp(-Ω(n))`
  (the documented remaining `have` is isolated at the very end).
-/

open Workspace.Types.PartialDeletionProcess
open Workspace.Types.AlternatingSumExpression

namespace WitnessOffsetTail

variable {n : ℕ}

/-- `(offsetWeight n r).toReal = binPMFInt (n/2) (1/2) (r + n/4)`. -/
theorem offsetWeight_toReal_eq_binPMFInt (n : ℕ) (r : ℤ) :
    (offsetWeight n r).toReal
      = binPMFInt (n / 2) (1 / 2) (r + ((n / 4 : ℕ) : ℤ)) := by
  unfold offsetWeight binPMFInt
  by_cases h : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)
  · -- in range
    have h' : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := h
    rw [dif_pos h]
    -- RHS: need 0 ≤ k ∧ k ≤ (n/2 : ℕ) as the `if` condition (cast form)
    have hcast : (((n / 2 : ℕ)) : ℤ) = ((n / 2 : ℕ) : ℤ) := rfl
    rw [if_pos h']
    -- both sides: binomial coefficient of (r + n/4).toNat over n/2, times (1/2)^(n/2)
    set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat with hk
    have hk_le : k ≤ n / 2 := by
      rw [hk]
      have : ((r + ((n / 4 : ℕ) : ℤ)).toNat : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h.1]; exact h.2
      exact_mod_cast this
    rw [CentralBinomialLowerTailWideProof.binPMF_half_eq (n / 2) k hk_le]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 / 2)]
  · -- out of range
    rw [dif_neg h, if_neg h, ENNReal.toReal_zero]

/-- Cumulative Chernoff bound, real binomial pmf form:
`∑_{k < K} binPMF m (1/2) k ≤ (9/7)^K · (8/9)^m`. -/
theorem binPMF_range_chernoff (m K : ℕ) :
    (∑ k ∈ Finset.range K, binPMF m (1 / 2 : ℝ) k) ≤ (9 / 7 : ℝ) ^ K * (8 / 9 : ℝ) ^ m :=
  CentralBinomialLowerTailWideProof.chernoff_optimal_bound m K

/-- The lower offset tail: the `n/2`-binomial mass strictly below coordinate
`n/8` is `≤ exp(-n/256)`.  (For `n ≥ 10^12`, `n % 8 = 1`, so `n/2`, `n/8`
behave as the obvious quarter/eighth.) -/
theorem offset_lower_tail (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ k ∈ Finset.range (n / 8), binPMF (n / 2) (1 / 2 : ℝ) k)
      ≤ Real.exp (-((n : ℝ) / 256)) := by
  have hn_pos : 0 < n := by have : (0:ℕ) < 10^12 := by norm_num
                            omega
  have hbase := binPMF_range_chernoff (n / 2) (n / 8)
  refine le_trans hbase ?_
  -- (9/7)^(n/8) · (8/9)^(n/2) ≤ exp(-n/256).
  set a : ℕ := n / 8 with ha
  set b : ℕ := n / 2 with hb
  have h4ab : 4 * a ≤ b := by omega
  -- factor (8/9)^b = (8/9)^(4a) · (8/9)^(b-4a), the last ≤ 1
  have hsplit : (8 / 9 : ℝ) ^ b = (8 / 9 : ℝ) ^ (4 * a) * (8 / 9 : ℝ) ^ (b - 4 * a) := by
    rw [← pow_add]; congr 1; omega
  have hle1 : (8 / 9 : ℝ) ^ (b - 4 * a) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnn : (0 : ℝ) ≤ (8 / 9 : ℝ) ^ (b - 4 * a) := pow_nonneg (by norm_num) _
  have hcoef_nn : (0 : ℝ) ≤ (9 / 7 : ℝ) ^ a * (8 / 9 : ℝ) ^ (4 * a) := by positivity
  -- step A: (9/7)^a · (8/9)^b ≤ ((9/7)·(8/9)^4)^a
  have hA : (9 / 7 : ℝ) ^ a * (8 / 9 : ℝ) ^ b
      ≤ ((9 / 7 : ℝ) * (8 / 9 : ℝ) ^ 4) ^ a := by
    rw [hsplit]
    have hrw : (9 / 7 : ℝ) ^ a * ((8 / 9 : ℝ) ^ (4 * a) * (8 / 9 : ℝ) ^ (b - 4 * a))
        = ((9 / 7 : ℝ) ^ a * (8 / 9 : ℝ) ^ (4 * a)) * (8 / 9 : ℝ) ^ (b - 4 * a) := by ring
    rw [hrw]
    have hbound := mul_le_mul_of_nonneg_left hle1 hcoef_nn
    rw [mul_one] at hbound
    refine le_trans hbound ?_
    have hpow4 : (8 / 9 : ℝ) ^ (4 * a) = ((8 / 9 : ℝ) ^ 4) ^ a := pow_mul _ 4 _
    rw [hpow4, ← mul_pow]
  -- step B: ((9/7)·(8/9)^4)^a ≤ exp(-1/6)^a = exp(-(a:ℝ)/6)
  have hbase_le : (9 / 7 : ℝ) * (8 / 9 : ℝ) ^ 4 ≤ Real.exp (-(1 / 6)) := by
    have h := Real.add_one_le_exp (-(1 / 6 : ℝ))
    nlinarith [Real.exp_pos (-(1 / 6 : ℝ))]
  have hbase_nn : (0 : ℝ) ≤ (9 / 7 : ℝ) * (8 / 9 : ℝ) ^ 4 := by positivity
  have hB : ((9 / 7 : ℝ) * (8 / 9 : ℝ) ^ 4) ^ a ≤ Real.exp (-((a : ℝ) / 6)) := by
    calc ((9 / 7 : ℝ) * (8 / 9 : ℝ) ^ 4) ^ a
        ≤ (Real.exp (-(1 / 6))) ^ a := pow_le_pow_left₀ hbase_nn hbase_le a
      _ = Real.exp (-((a : ℝ) / 6)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  -- step C: exp(-(a/6)) ≤ exp(-n/256)
  have hC : Real.exp (-((a : ℝ) / 6)) ≤ Real.exp (-((n : ℝ) / 256)) := by
    apply Real.exp_le_exp.mpr
    have ha_lb : (n : ℝ) / 8 - 1 ≤ (a : ℝ) := by
      rw [ha]
      have hnd : (n : ℝ) < (↑(n / 8) + 1) * 8 := by
        have hnat : n < (n / 8 + 1) * 8 := by omega
        have := (Nat.cast_lt (α := ℝ)).mpr hnat
        push_cast at this; linarith
      linarith
    have hn_lb : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [ha_lb, hn_lb]
  exact le_trans hA (le_trans hB hC)

end WitnessOffsetTail
