import Mathlib
import Workspace.Types.AlternatingSumExpression

/-!
# CentralBinomialLowerTailWide — Proof attempt 1

Hoeffding lower-tail of Bin(n, 1/2) on r ∈ [-n/4, -n/16 - 1] ≤ exp(-n/128).

Strategy (optimal Chernoff with c = 9/7):
1. Reindex k = r + n/2; sum becomes ∑_{k ∈ [n/4, 7n/16-1]∩ℤ} bin(n, 1/2, k).
2. Extend to ∑_{k=0..(7n/16 - 1)} bin(n, 1/2, k) (bounded above since terms are ≥ 0).
3. Chernoff with c = 9/7: ∑_{k<K} bin(m,1/2,k) · (9/7)^{K-k} extends to ∑ all k:
   = (9/7)^K · (1/2 · 7/9 + 1/2)^m = (9/7)^K · (8/9)^m.
   (Justification: c · (1/2) + (1/2)/(c+1)... actually:
    mgf E[c^X] for X ∼ Bin(n, 1/2) flipped: ∑_k C(n,k)·c^{n-k}·(1/2)^n = ((c+1)/2)^n.
    For lower tail with c < 1: bound becomes c^K · ((c+1)/(2c))^n... wait.
   ACTUAL: ∑_{k<K} c^{K-k} · binPMF(k) = c^K · ∑_{k<K} (m,k)·(c^{-1}·(1/2))^k·(1/2)^{m-k}/(2)^m factor...
   Direct: c=9/7 means we set 1/c = 7/9.
   ∑_{k<K} (m choose k)·(1/2)^m ≤ ∑_{k<K} (m choose k)·(7/9)^{K-k}·(1/2)^k·(1/2)^{m-k}·(9/7)^{K-k}/(7/9)^{K-k}·.
   Just mirror the original proof: bound binPMF m (1/2) k ≤ (9/7)^{K-k} · binPMF m (1/2) k.
   Wait, original used: binPMF m (1/2) k ≤ (5/3)^{K-k} · ((m choose k) · (3/10)^k · (1/2)^{m-k}) for k < K,
   then summed and used add_pow.
   Here: binPMF m (1/2) k ≤ (9/7)^{K-k} · ((m choose k) · (7/18)^k · (1/2)^{m-k}) for k < K.
   Combine: (9/7)^k · (7/18)^k = (1/2)^k.  ✓
   Full: (9/7)^K · ((m choose k) · (7/18)^k · (1/2)^{m-k}) when summed over all k=0..m gives
     (9/7)^K · ((7/18) + (1/2))^m = (9/7)^K · (8/9)^m. ✓
   (since 7/18 + 1/2 = 7/18 + 9/18 = 16/18 = 8/9)

4. Numerical: (9/7)^7 · (8/9)^{16} ≤ exp(-1251/10000) with slack.
   We prove (9/7)^7 · (8/9)^{16} ≤ exp(-1251/10000), then raise to (n/16)-th power.
-/

set_option maxHeartbeats 32000000

open Workspace.Types.AlternatingSumExpression

namespace CentralBinomialLowerTailWideProof

-- For z ≤ m, binPMF m (1/2) z = C(m, z) · (1/2)^m.
lemma binPMF_half_eq (m z : ℕ) (hz : z ≤ m) :
    binPMF m (1/2 : ℝ) z = (m.choose z : ℝ) * (1/2)^m := by
  unfold binPMF
  rw [if_pos hz]
  have h1 : (1 - (1/2 : ℝ)) = 1/2 := by ring
  rw [h1]
  have hpow : (1/2:ℝ)^z * (1/2:ℝ)^(m-z) = (1/2:ℝ)^m := by
    rw [← pow_add]; congr 1; omega
  calc (m.choose z : ℝ) * (1/2)^z * (1/2)^(m-z)
      = (m.choose z : ℝ) * ((1/2)^z * (1/2)^(m-z)) := by ring
    _ = (m.choose z : ℝ) * (1/2)^m := by rw [hpow]

-- For real p, binPMF m p z ≥ 0 when 0 ≤ p ≤ 1.
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

-- Optimal Chernoff lower-tail bound for Bin(m, 1/2) with c = 9/7.
-- For any K (no upper bound on K needed since sum extended over [0, m]):
--   ∑_{k < K} bin(m, 1/2, k) ≤ (9/7)^K · (8/9)^m
lemma chernoff_optimal_bound (m K : ℕ) :
    (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k) ≤ (9/7:ℝ)^K * (8/9:ℝ)^m := by
  have h97_pos : (0:ℝ) < 9/7 := by norm_num
  have h97_ge1 : (1:ℝ) ≤ 9/7 := by norm_num
  -- Step 1: ∑_{k<K} binPMF m (1/2) k ≤ (9/7)^K · ∑_{k<K} C(m,k) · (7/18)^k · (1/2)^{m-k}
  have h_step1 :
      (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k)
        ≤ (9/7:ℝ)^K *
            (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hkm : k ≤ m
    · rw [binPMF_half_eq m k hkm]
      have hC_nn : (0:ℝ) ≤ (m.choose k : ℝ) := by exact_mod_cast Nat.zero_le _
      have hkK : k ≤ K := Nat.le_of_lt hk
      have h_97Kk_ge1 : (1:ℝ) ≤ (9/7:ℝ)^(K - k) := one_le_pow₀ h97_ge1
      have h_half_split : (1/2:ℝ)^m = (1/2:ℝ)^k * (1/2:ℝ)^(m-k) := by
        rw [← pow_add]; congr 1; omega
      rw [h_half_split]
      have hsplit : (9/7:ℝ)^K = (9/7:ℝ)^k * (9/7:ℝ)^(K - k) := by
        rw [← pow_add]; congr 1; omega
      have h_combine : (9/7:ℝ)^k * (7/18:ℝ)^k = (1/2:ℝ)^k := by
        rw [← mul_pow]; congr 1; norm_num
      have h_pos : (0:ℝ) ≤ (1/2:ℝ)^(m - k) := pow_nonneg (by norm_num) _
      have hbase_nn : (0:ℝ) ≤ (m.choose k : ℝ) * (9/7:ℝ)^k * (7/18:ℝ)^k * (1/2:ℝ)^(m-k) := by
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg hC_nn
        · exact pow_nonneg (le_of_lt h97_pos) _
        · exact pow_nonneg (by norm_num) _
        · exact h_pos
      calc (m.choose k : ℝ) * ((1/2:ℝ)^k * (1/2:ℝ)^(m - k))
          = (m.choose k : ℝ) * ((9/7:ℝ)^k * (7/18:ℝ)^k) * (1/2:ℝ)^(m-k) := by
            rw [h_combine]; ring
        _ = (m.choose k : ℝ) * (9/7:ℝ)^k * (7/18:ℝ)^k * (1/2:ℝ)^(m-k) := by ring
        _ ≤ (m.choose k : ℝ) * (9/7:ℝ)^k * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)
              * (9/7:ℝ)^(K - k) := by
            have := mul_le_mul_of_nonneg_left h_97Kk_ge1 hbase_nn
            linarith
        _ = (9/7:ℝ)^K * ((m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) := by
            rw [hsplit]; ring
    · push_neg at hkm
      have : binPMF m (1/2 : ℝ) k = 0 := by
        unfold binPMF; rw [if_neg (by omega)]
      rw [this]
      apply mul_nonneg
      · exact pow_nonneg (le_of_lt h97_pos) _
      · apply mul_nonneg
        apply mul_nonneg
        · exact_mod_cast Nat.zero_le _
        · exact pow_nonneg (by norm_num) _
        · exact pow_nonneg (by norm_num) _
  -- Step 2: ∑_{k<K} ... ≤ ∑_{k<m+1} ...
  have h_step2 :
      (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k))
        ≤ (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_range] at *; exact lt_of_lt_of_le hx (le_max_left _ _)
    · intros k _ _
      apply mul_nonneg
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact pow_nonneg (by norm_num) _
      · exact pow_nonneg (by norm_num) _
  -- Step 3: ∑_{k<m+1} ... = (8/9)^m. Sum over k > m: 0 (since C(m,k) = 0).
  have h_step3 :
      (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k))
        = (8/9:ℝ)^m := by
    have h_split : Finset.range (max K (m+1))
        = Finset.range (m+1) ∪ ((Finset.range (max K (m+1))) \ Finset.range (m+1)) := by
      rw [Finset.union_sdiff_of_subset]
      intro x hx
      rw [Finset.mem_range] at *
      exact lt_of_lt_of_le hx (le_max_right _ _)
    rw [h_split]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    have h_second_zero : (∑ k ∈ ((Finset.range (max K (m+1))) \ Finset.range (m+1)),
                           (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hk
      have hk_gt : m + 1 ≤ k := by omega
      have h_choose_zero : m.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h_choose_zero]
      simp
    rw [h_second_zero, add_zero]
    have h_addpow := add_pow (7/18 : ℝ) (1/2) m
    rw [show (7/18:ℝ) + 1/2 = 8/9 from by norm_num] at h_addpow
    rw [h_addpow]
    apply Finset.sum_congr rfl
    intros k _; ring
  calc (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k)
      ≤ (9/7:ℝ)^K *
          (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) := h_step1
    _ ≤ (9/7:ℝ)^K *
          (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (7/18:ℝ)^k * (1/2:ℝ)^(m-k)) := by
        apply mul_le_mul_of_nonneg_left h_step2 (pow_nonneg (le_of_lt h97_pos) _)
    _ = (9/7:ℝ)^K * (8/9:ℝ)^m := by rw [h_step3]

-- Numerical: exp(1251/10000) ≤ 148523/131072 (using Real.exp_bound' n=4 at x=1/8 plus adjustment).
-- Actually, simpler: exp(1251/10000) ≤ 113318/100000? Let's check:
-- exp(0.1251) ≈ 1.13326. We need bound ≥ 1.13326.
-- From Real.exp_bound' n=4 at x=1251/10000:
-- 1 + x + x²/2 + x³/6 + x^4·5/(24·4)
-- = 1 + 0.1251 + 0.00782... + 0.0003261... + ...
-- ≈ 1.13328. So 1.13329 should work.

-- Goal: prove (9/7)^7 · (8/9)^{16} ≤ exp(-1251/10000).
-- Equivalent: exp(1251/10000) ≤ 1/((9/7)^7 · (8/9)^{16}) = (7/9)^7 · (9/8)^{16} = 7^7·9^9/2^{48}.
-- Compute: 7^7 = 823543, 9^9 = 387420489. Product = 319057431772527.
-- 2^{48} = 281474976710656.
-- Target: 319057431772527 / 281474976710656 ≈ 1.13352.

-- Use Real.exp_bound' with n = 4 at x = 1251/10000:
-- bound = 1 + 1251/10000 + (1251)²/(2·10000²) + (1251)³/(6·10000³) + (1251)^4·5/(24·10000^4·4)
-- ≈ 1.13327
-- Need ≤ 319057431772527 / 281474976710656 ≈ 1.13352. ✓

lemma exp_1251_10000_le : Real.exp (1251/10000) ≤ 319057431772527/281474976710656 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1251/10000)
                            (by norm_num : (1251/10000:ℝ) ≤ 1) (n := 4) (by norm_num : 0 < 4)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.factorial, zero_add]
  norm_num

-- (9/7)^7 · (8/9)^16 ≤ exp(-1251/10000).
lemma nine_sevenths_seventh_eight_ninths_sixteenth_le_exp_neg_1251_10000 :
    (9/7:ℝ)^7 * (8/9:ℝ)^16 ≤ Real.exp (-(1251/10000)) := by
  have h_exp_pos : (0:ℝ) < Real.exp (1251/10000) := Real.exp_pos _
  have h_exp_le : Real.exp (1251/10000) ≤ 319057431772527/281474976710656 := exp_1251_10000_le
  rw [Real.exp_neg]
  have h_lhs_pos : (0:ℝ) < (9/7:ℝ)^7 * (8/9:ℝ)^16 := by positivity
  rw [le_inv_comm₀ h_lhs_pos h_exp_pos]
  refine le_trans h_exp_le ?_
  -- Want: 319057431772527/281474976710656 ≤ ((9/7)^7 · (8/9)^16)⁻¹
  -- (9/7)^7 · (8/9)^16 = 9^7·8^16/(7^7·9^16) = 8^16/(7^7·9^9) = 2^48/(7^7·9^9)
  --                   = 281474976710656/319057431772527.
  -- So inverse = 319057431772527/281474976710656. So we need equality, in fact.
  rw [show ((9/7:ℝ)^7 * (8/9:ℝ)^16)⁻¹ = 319057431772527/281474976710656 from by
    rw [show (9/7:ℝ)^7 * (8/9:ℝ)^16 = 281474976710656/319057431772527 from by norm_num]
    rw [inv_div]]

-- Now raise to q-th power: ((9/7)^7 · (8/9)^16)^q ≤ exp(-q · 1251/10000).
lemma chernoff_pow_bound_1251 (q : ℕ) :
    (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) ≤ Real.exp (-((q : ℝ) * 1251/10000)) := by
  have h_base : (9/7:ℝ)^7 * (8/9:ℝ)^16 ≤ Real.exp (-(1251/10000)) :=
    nine_sevenths_seventh_eight_ninths_sixteenth_le_exp_neg_1251_10000
  have h_base_nn : (0:ℝ) ≤ (9/7:ℝ)^7 * (8/9:ℝ)^16 := by positivity
  have h_pow := pow_le_pow_left₀ h_base_nn h_base q
  rw [← Real.exp_nat_mul] at h_pow
  rw [show ((q:ℝ) * -(1251/10000)) = -((q:ℝ) * 1251/10000) from by ring] at h_pow
  refine le_trans ?_ h_pow
  rw [mul_pow]
  have e1 : (9/7:ℝ)^(7*q) = ((9/7:ℝ)^7)^q := by rw [← pow_mul]
  have e2 : (8/9:ℝ)^(16*q) = ((8/9:ℝ)^16)^q := by rw [← pow_mul]
  rw [e1, e2]

-- Cast inequality: (n : ℝ)/16 - 1 ≤ ((n/16 : ℕ) : ℝ).
lemma cast_div_16_ge (n : ℕ) : (n : ℝ) / 16 - 1 ≤ ((n / 16 : ℕ) : ℝ) := by
  have h : 16 * (n / 16) + 16 > n := by
    have := Nat.div_add_mod n 16
    have hmod : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
    omega
  have h_real : 16 * ((n / 16 : ℕ) : ℝ) + 16 > (n : ℝ) := by exact_mod_cast h
  linarith

end CentralBinomialLowerTailWideProof

theorem CentralBinomialLowerTailWide :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n →
      ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2)
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Set q := n / 16 (Nat).
  set q : ℕ := n / 16 with hq_def
  have h16q_le : 16 * q ≤ n := by rw [hq_def]; exact Nat.mul_div_le n 16
  have hq_real_ge : (n : ℝ)/16 - 1 ≤ (q : ℝ) := by
    rw [hq_def]
    exact CentralBinomialLowerTailWideProof.cast_div_16_ge n
  have hq_pos : 1 ≤ q := by
    rw [hq_def]
    have h100 : 100 ≤ n / 16 := by
      have : 1600 ≤ n := by linarith
      omega
    omega
  -- Step 1: Bound the sum by ∑ k ∈ Finset.range (7q+7), binPMF n (1/2) k.
  -- For r ∈ [-(n/4), -(n/16)-1], k = r + n/2 ∈ [n/4, 7n/16 - 1].
  -- For n = 16q + s, s ∈ [0,15]:
  --   (n/16 : ℤ) = q. (n/2 : ℤ) = (8q + s/2 : ℕ) where s/2 is Nat division.
  --   For s ∈ {0,1}: n/2 = 8q. ... For s ∈ {14,15}: n/2 = 8q+7.
  --   Upper bound on k: -q - 1 + (8q + (s/2 : ℕ)) = 7q + (s/2 : ℕ) - 1 ≤ 7q + 6.
  -- So K_max ≤ 7q + 6 (upper bound on k); we use Finset.range (7q + 7).
  have h_step_bound :
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (7 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
    let shift : ℤ → ℕ := fun r => (r + (n : ℤ) / 2).toNat
    have h_eq : (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
                  Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
                = (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
                    Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      obtain ⟨hr_lo, hr_hi⟩ := hr
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ (n : ℤ) := by
        have h_n2 : (n : ℤ)/2 ≤ (n : ℤ) := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        have h_n16_pos : (0 : ℤ) ≤ (n : ℤ)/16 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      unfold Workspace.Types.AlternatingSumExpression.binPMFInt
      rw [if_pos ⟨hr_plus_lo, hr_plus_hi⟩]
    rw [h_eq]
    have h_shift_inj : Set.InjOn shift (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1)) := by
      intro r1 hr1 r2 hr2 h_eq_shift
      rw [Finset.mem_coe, Finset.mem_Icc] at hr1 hr2
      simp only [shift] at h_eq_shift
      have hr1_plus_lo : (0 : ℤ) ≤ r1 + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith [hr1.1]
      have hr2_plus_lo : (0 : ℤ) ≤ r2 + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith [hr2.1]
      have h1_eq : (r1 + (n : ℤ) / 2 : ℤ) = (r2 + (n : ℤ) / 2 : ℤ) := by
        have hh := congrArg (fun (m : ℕ) => (m : ℤ)) h_eq_shift
        simp only at hh
        rw [Int.toNat_of_nonneg hr1_plus_lo, Int.toNat_of_nonneg hr2_plus_lo] at hh
        exact hh
      linarith
    have h_image_sum :
        (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r))
        = (∑ k ∈ (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1)).image shift,
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
      rw [Finset.sum_image]
      intro r1 hr1 r2 hr2 h_eq_shift
      exact h_shift_inj hr1 hr2 h_eq_shift
    rw [h_image_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨r, hr_in, hr_eq⟩ := hk
      rw [Finset.mem_Icc] at hr_in
      rw [Finset.mem_range]
      simp only [shift] at hr_eq
      have hr_lo : -((n : ℤ)/4) ≤ r := hr_in.1
      have hr_hi : r ≤ -((n : ℤ)/16) - 1 := hr_in.2
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ -((n : ℤ)/16) - 1 + (n : ℤ)/2 := by linarith
      -- Bound: -(n/16 : ℤ) - 1 + (n/2 : ℤ) ≤ 7q + 6.
      have hbound : -((n : ℤ)/16) - 1 + (n : ℤ)/2 ≤ 7 * (q : ℤ) + 6 := by
        have hn_def : n = 16 * q + n % 16 := by
          rw [hq_def]; omega
        have hmod : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
        have hq_int : (q : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le q
        have hn_int : (n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
        omega
      have h_kint_bound : (k : ℤ) ≤ 7 * (q : ℤ) + 6 := by
        rw [← hr_eq]
        have h_toNat_eq : ((r + (n : ℤ)/2).toNat : ℤ) = r + (n : ℤ)/2 :=
          Int.toNat_of_nonneg hr_plus_lo
        rw [h_toNat_eq]
        linarith
      have hk_le : k ≤ 7 * q + 6 := by
        have := h_kint_bound
        have : (k : ℤ) ≤ ((7 * q + 6 : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this
      omega
    · intros k _ _
      exact CentralBinomialLowerTailWideProof.binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)
  -- Step 2: Apply Chernoff.
  have h_chernoff : (∑ k ∈ Finset.range (7 * q + 7),
                      Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
                    ≤ (9/7:ℝ)^(7 * q + 7) * (8/9:ℝ)^n :=
    CentralBinomialLowerTailWideProof.chernoff_optimal_bound n (7 * q + 7)
  -- Step 3a: (9/7)^{7q+7} · (8/9)^n ≤ (9/7)^7 · ((9/7)^7 · (8/9)^16)^q.
  have h_step3a : (9/7:ℝ)^(7 * q + 7) * (8/9:ℝ)^n
                ≤ (9/7:ℝ)^7 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := by
    have hk_split : (9/7:ℝ)^(7*q+7) = (9/7:ℝ)^7 * (9/7:ℝ)^(7*q) := by
      rw [← pow_add]; congr 1; ring
    rw [hk_split]
    have h_n_split : (8/9:ℝ)^n = (8/9:ℝ)^(16*q) * (8/9:ℝ)^(n - 16*q) := by
      rw [← pow_add]; congr 1; omega
    rw [h_n_split]
    have h_89_le1 : (8/9:ℝ)^(n - 16*q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h_89_pos : (0:ℝ) ≤ (8/9:ℝ)^(n - 16*q) := pow_nonneg (by norm_num) _
    have h_97q_nn : (0:ℝ) ≤ (9/7:ℝ)^(7*q) := pow_nonneg (by norm_num) _
    have h_89_16q_nn : (0:ℝ) ≤ (8/9:ℝ)^(16*q) := pow_nonneg (by norm_num) _
    have h_97_seven_nn : (0:ℝ) ≤ (9/7:ℝ)^7 := pow_nonneg (by norm_num) _
    have hrhs_eq : ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q = (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by
      rw [mul_pow]
      have e1 : ((9/7:ℝ)^7)^q = (9/7:ℝ)^(7*q) := by rw [← pow_mul]
      have e2 : ((8/9:ℝ)^16)^q = (8/9:ℝ)^(16*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (9/7:ℝ)^7 * (9/7:ℝ)^(7*q) * ((8/9:ℝ)^(16*q) * (8/9:ℝ)^(n - 16*q))
              = (9/7:ℝ)^7 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) * (8/9:ℝ)^(n - 16*q) := by ring
    rw [hbase]
    have hbase2 : (9/7:ℝ)^7 * ((9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q))
                = (9/7:ℝ)^7 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (9/7:ℝ)^7 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by
      apply mul_nonneg
      apply mul_nonneg h_97_seven_nn h_97q_nn
      exact h_89_16q_nn
    have := mul_le_mul_of_nonneg_left h_89_le1 hcoef_nn
    linarith
  -- Step 3b: ((9/7)^7 · (8/9)^16)^q ≤ exp(-q · 1251/10000).
  have h_step3b : ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q ≤ Real.exp (-((q:ℝ) * 1251/10000)) := by
    have h_base : (9/7:ℝ)^7 * (8/9:ℝ)^16 ≤ Real.exp (-(1251/10000)) :=
      CentralBinomialLowerTailWideProof.nine_sevenths_seventh_eight_ninths_sixteenth_le_exp_neg_1251_10000
    have h_base_nn : (0:ℝ) ≤ (9/7:ℝ)^7 * (8/9:ℝ)^16 := by positivity
    have h_pow := pow_le_pow_left₀ h_base_nn h_base q
    rw [← Real.exp_nat_mul] at h_pow
    rw [show ((q:ℝ) * -(1251/10000)) = -((q:ℝ) * 1251/10000) from by ring] at h_pow
    exact h_pow
  -- Step 3c: (9/7)^7 ≤ 6.
  -- (9/7)^7 = 9^7/7^7 = 4782969/823543 ≈ 5.808.
  have h_97_seven_le_6 : (9/7:ℝ)^7 ≤ 6 := by norm_num
  -- Combine: LHS ≤ 6 · exp(-q · 1251/10000).
  have h_combined : (9/7:ℝ)^(7 * q + 7) * (8/9:ℝ)^n
                ≤ 6 * Real.exp (-((q:ℝ) * 1251/10000)) := by
    calc (9/7:ℝ)^(7 * q + 7) * (8/9:ℝ)^n
        ≤ (9/7:ℝ)^7 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := h_step3a
      _ ≤ 6 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := by
          apply mul_le_mul_of_nonneg_right h_97_seven_le_6
          exact pow_nonneg (by positivity) _
      _ ≤ 6 * Real.exp (-((q:ℝ) * 1251/10000)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 6)
  -- Step 4: 6 · exp(-q · 1251/10000) ≤ exp(-n/128).
  -- log 6 ≤ 5 (using log x ≤ x - 1).
  -- Need: q · 1251/10000 ≥ n/128 + log 6.
  -- q ≥ n/16 - 1, so q · 1251/10000 ≥ (n/16 - 1) · 1251/10000.
  -- (n/16 - 1) · 1251/10000 ≥ n/128 + 5
  -- ↔ n · (1251/160000 - 1/128) ≥ 5 + 1251/10000
  -- 1251/160000 - 1250/160000 = 1/160000.
  -- n · 1/160000 ≥ 5.1251 = 51251/10000
  -- n ≥ 160000 · 51251/10000 = 16 · 51251 = 820016.
  -- For n ≥ 10^12, ✓.
  have h_log6_le : Real.log 6 ≤ 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have h_6_le_exp : (6 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_le_exp.mpr h_log6_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 6)] at h
  have h_step4 : 6 * Real.exp (-((q:ℝ) * 1251/10000)) ≤ Real.exp (-((n:ℝ)/128)) := by
    have h_exp_combined : Real.exp 5 * Real.exp (-((q:ℝ) * 1251/10000))
                        = Real.exp (5 - (q:ℝ) * 1251/10000) := by
      rw [← Real.exp_add]
      ring_nf
    have h_lhs_le : 6 * Real.exp (-((q:ℝ) * 1251/10000))
                  ≤ Real.exp 5 * Real.exp (-((q:ℝ) * 1251/10000)) := by
      apply mul_le_mul_of_nonneg_right h_6_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    apply Real.exp_le_exp.mpr
    -- Need: 5 - q · 1251/10000 ≤ -n/128.
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    have h_q_lb : (q : ℝ) * 1251/10000 ≥ ((n : ℝ)/16 - 1) * 1251/10000 := by
      have h1251_pos : (0:ℝ) ≤ 1251/10000 := by norm_num
      nlinarith [hq_real_ge, h1251_pos]
    nlinarith [h_q_lb, h_n_large]
  -- Combine all
  calc (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (7 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(7 * q + 7) * (8/9:ℝ)^n := h_chernoff
    _ ≤ 6 * Real.exp (-((q:ℝ) * 1251/10000)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4

theorem CentralBinomialLowerTailWideHalf :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4)
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn hmod8
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- m := n/2 trial count.  q := n/32.
  set m : ℕ := n / 2 with hm_def
  set q : ℕ := n / 32 with hq_def
  have h16q_le_m : 16 * q ≤ m := by
    rw [hq_def, hm_def]; omega
  have h16q_le_n : 16 * q ≤ n := by
    rw [hq_def]; omega
  have hq_real_ge : (n : ℝ)/32 - 1 ≤ (q : ℝ) := by
    have h : 32 * (n / 32) + 32 > n := by
      have := Nat.div_add_mod n 32
      have hmod : n % 32 < 32 := Nat.mod_lt _ (by norm_num)
      omega
    have h_real : 32 * ((n / 32 : ℕ) : ℝ) + 32 > (n : ℝ) := by exact_mod_cast h
    rw [hq_def]; linarith
  -- Step 1: bound the sum by ∑ k ∈ range (6q+7), binPMF (n/2) (1/2) k.
  -- For r ∈ [-(n/4), -(n/16)-1], k = r + n/4 ∈ [0, -(n/16)-1+n/4] ⊆ [0, 6q+6].
  have h_step_bound :
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
      ≤ (∑ k ∈ Finset.range (6 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k) := by
    let shift : ℤ → ℕ := fun r => (r + (n : ℤ) / 4).toNat
    have h_eq : (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
                  Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
                = (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
                    Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) (shift r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      obtain ⟨hr_lo, hr_hi⟩ := hr
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 4 := by linarith
      have hr_plus_hi : r + (n : ℤ) / 4 ≤ ((n / 2 : ℕ) : ℤ) := by
        have h_n16_pos : (0 : ℤ) ≤ (n : ℤ)/16 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        have h_n4_le_n2 : (n : ℤ)/4 ≤ ((n / 2 : ℕ) : ℤ) := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          have hcast : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
            push_cast [Nat.cast_div]; omega
          omega
        linarith
      unfold Workspace.Types.AlternatingSumExpression.binPMFInt
      rw [if_pos ⟨hr_plus_lo, hr_plus_hi⟩]
    rw [h_eq]
    have h_shift_inj : Set.InjOn shift (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1)) := by
      intro r1 hr1 r2 hr2 h_eq_shift
      rw [Finset.mem_coe, Finset.mem_Icc] at hr1 hr2
      simp only [shift] at h_eq_shift
      have hr1_plus_lo : (0 : ℤ) ≤ r1 + (n : ℤ) / 4 := by linarith [hr1.1]
      have hr2_plus_lo : (0 : ℤ) ≤ r2 + (n : ℤ) / 4 := by linarith [hr2.1]
      have h1_eq : (r1 + (n : ℤ) / 4 : ℤ) = (r2 + (n : ℤ) / 4 : ℤ) := by
        have hh := congrArg (fun (z : ℕ) => (z : ℤ)) h_eq_shift
        simp only at hh
        rw [Int.toNat_of_nonneg hr1_plus_lo, Int.toNat_of_nonneg hr2_plus_lo] at hh
        exact hh
      linarith
    have h_image_sum :
        (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) (shift r))
        = (∑ k ∈ (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1)).image shift,
            Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k) := by
      rw [Finset.sum_image]
      intro r1 hr1 r2 hr2 h_eq_shift
      exact h_shift_inj hr1 hr2 h_eq_shift
    rw [h_image_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨r, hr_in, hr_eq⟩ := hk
      rw [Finset.mem_Icc] at hr_in
      rw [Finset.mem_range]
      simp only [shift] at hr_eq
      have hr_lo : -((n : ℤ)/4) ≤ r := hr_in.1
      have hr_hi : r ≤ -((n : ℤ)/16) - 1 := hr_in.2
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 4 := by linarith
      -- Bound: -(n/16 : ℤ) - 1 + (n/4 : ℤ) ≤ 6q + 6.
      have hbound : -((n : ℤ)/16) - 1 + (n : ℤ)/4 ≤ 6 * (q : ℤ) + 6 := by
        have hn_def : n = 32 * q + n % 32 := by rw [hq_def]; omega
        have hmod : n % 32 < 32 := Nat.mod_lt _ (by norm_num)
        have hq_int : (q : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le q
        have hn_int : (n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
        have hmod8 : n % 8 = 1 := hmod8
        omega
      have h_kint_bound : (k : ℤ) ≤ 6 * (q : ℤ) + 6 := by
        rw [← hr_eq]
        have h_toNat_eq : ((r + (n : ℤ)/4).toNat : ℤ) = r + (n : ℤ)/4 :=
          Int.toNat_of_nonneg hr_plus_lo
        rw [h_toNat_eq]
        linarith
      have hk_le : k ≤ 6 * q + 6 := by
        have : (k : ℤ) ≤ ((6 * q + 6 : ℕ) : ℤ) := by push_cast; linarith [h_kint_bound]
        exact_mod_cast this
      omega
    · intros k _ _
      exact CentralBinomialLowerTailWideProof.binPMF_nonneg (n / 2) k (1/2) (by norm_num) (by norm_num)
  -- Step 2: Apply Chernoff with m := n/2, K := 6q+7.
  have h_chernoff : (∑ k ∈ Finset.range (6 * q + 7),
                      Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k)
                    ≤ (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2) :=
    CentralBinomialLowerTailWideProof.chernoff_optimal_bound (n / 2) (6 * q + 7)
  -- Numerical sub-fact: (9/7)^6 · (8/9)^16 ≤ exp(-3/10).
  have h_base630 : (9/7:ℝ)^6 * (8/9:ℝ)^16 ≤ Real.exp (-(3/10)) := by
    have h_exp_le : Real.exp (3/10) ≤ 410216697993249/281474976710656 := by
      have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 3/10)
                                (by norm_num : (3/10:ℝ) ≤ 1) (n := 3) (by norm_num : 0 < 3)
      refine h.trans ?_
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial, zero_add]
      norm_num
    have h_exp_pos : (0:ℝ) < Real.exp (3/10) := Real.exp_pos _
    rw [Real.exp_neg]
    have h_lhs_pos : (0:ℝ) < (9/7:ℝ)^6 * (8/9:ℝ)^16 := by positivity
    rw [le_inv_comm₀ h_lhs_pos h_exp_pos]
    refine le_trans h_exp_le ?_
    rw [show ((9/7:ℝ)^6 * (8/9:ℝ)^16)⁻¹ = 410216697993249/281474976710656 from by
      rw [show (9/7:ℝ)^6 * (8/9:ℝ)^16 = 281474976710656/410216697993249 from by norm_num]
      rw [inv_div]]
  -- Step 3a: (9/7)^{6q+7} · (8/9)^{n/2} ≤ (9/7)^7 · ((9/7)^6 · (8/9)^16)^q.
  have h_step3a : (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2)
                ≤ (9/7:ℝ)^7 * ((9/7:ℝ)^6 * (8/9:ℝ)^16)^q := by
    have hk_split : (9/7:ℝ)^(6*q+7) = (9/7:ℝ)^7 * (9/7:ℝ)^(6*q) := by
      rw [← pow_add]; congr 1; ring
    rw [hk_split]
    have h_n_split : (8/9:ℝ)^(n / 2) = (8/9:ℝ)^(16*q) * (8/9:ℝ)^(n / 2 - 16*q) := by
      rw [← pow_add]; congr 1; omega
    rw [h_n_split]
    have h_89_le1 : (8/9:ℝ)^(n / 2 - 16*q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h_97q_nn : (0:ℝ) ≤ (9/7:ℝ)^(6*q) := pow_nonneg (by norm_num) _
    have h_89_16q_nn : (0:ℝ) ≤ (8/9:ℝ)^(16*q) := pow_nonneg (by norm_num) _
    have h_97_seven_nn : (0:ℝ) ≤ (9/7:ℝ)^7 := pow_nonneg (by norm_num) _
    have hrhs_eq : ((9/7:ℝ)^6 * (8/9:ℝ)^16)^q = (9/7:ℝ)^(6*q) * (8/9:ℝ)^(16*q) := by
      rw [mul_pow]
      have e1 : ((9/7:ℝ)^6)^q = (9/7:ℝ)^(6*q) := by rw [← pow_mul]
      have e2 : ((8/9:ℝ)^16)^q = (8/9:ℝ)^(16*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (9/7:ℝ)^7 * (9/7:ℝ)^(6*q) * ((8/9:ℝ)^(16*q) * (8/9:ℝ)^(n / 2 - 16*q))
              = (9/7:ℝ)^7 * (9/7:ℝ)^(6*q) * (8/9:ℝ)^(16*q) * (8/9:ℝ)^(n / 2 - 16*q) := by ring
    rw [hbase]
    have hbase2 : (9/7:ℝ)^7 * ((9/7:ℝ)^(6*q) * (8/9:ℝ)^(16*q))
                = (9/7:ℝ)^7 * (9/7:ℝ)^(6*q) * (8/9:ℝ)^(16*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (9/7:ℝ)^7 * (9/7:ℝ)^(6*q) * (8/9:ℝ)^(16*q) := by
      apply mul_nonneg
      apply mul_nonneg h_97_seven_nn h_97q_nn
      exact h_89_16q_nn
    have := mul_le_mul_of_nonneg_left h_89_le1 hcoef_nn
    linarith
  -- Step 3b: ((9/7)^6 · (8/9)^16)^q ≤ exp(-q · 3/10).
  have h_step3b : ((9/7:ℝ)^6 * (8/9:ℝ)^16)^q ≤ Real.exp (-((q:ℝ) * 3/10)) := by
    have h_base_nn : (0:ℝ) ≤ (9/7:ℝ)^6 * (8/9:ℝ)^16 := by positivity
    have h_pow := pow_le_pow_left₀ h_base_nn h_base630 q
    rw [← Real.exp_nat_mul] at h_pow
    rw [show ((q:ℝ) * -(3/10)) = -((q:ℝ) * 3/10) from by ring] at h_pow
    exact h_pow
  -- Step 3c: (9/7)^7 ≤ 6.
  have h_97_seven_le_6 : (9/7:ℝ)^7 ≤ 6 := by norm_num
  -- Combine: LHS ≤ 6 · exp(-q · 3/10).
  have h_combined : (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2)
                ≤ 6 * Real.exp (-((q:ℝ) * 3/10)) := by
    calc (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2)
        ≤ (9/7:ℝ)^7 * ((9/7:ℝ)^6 * (8/9:ℝ)^16)^q := h_step3a
      _ ≤ 6 * ((9/7:ℝ)^6 * (8/9:ℝ)^16)^q := by
          apply mul_le_mul_of_nonneg_right h_97_seven_le_6
          exact pow_nonneg (by positivity) _
      _ ≤ 6 * Real.exp (-((q:ℝ) * 3/10)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 6)
  -- Step 4: 6 · exp(-q · 3/10) ≤ exp(-n/128).
  -- Need q · 3/10 ≥ n/128 + log 6.  q ≥ n/32 - 1.
  have h_log6_le : Real.log 6 ≤ 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have h_6_le_exp : (6 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_le_exp.mpr h_log6_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 6)] at h
  have h_step4 : 6 * Real.exp (-((q:ℝ) * 3/10)) ≤ Real.exp (-((n:ℝ)/128)) := by
    have h_exp_combined : Real.exp 5 * Real.exp (-((q:ℝ) * 3/10))
                        = Real.exp (5 - (q:ℝ) * 3/10) := by
      rw [← Real.exp_add]; ring_nf
    have h_lhs_le : 6 * Real.exp (-((q:ℝ) * 3/10))
                  ≤ Real.exp 5 * Real.exp (-((q:ℝ) * 3/10)) := by
      apply mul_le_mul_of_nonneg_right h_6_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    apply Real.exp_le_exp.mpr
    -- Need: 5 - q · 3/10 ≤ -n/128.
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    have h_q_lb : (q : ℝ) * 3/10 ≥ ((n : ℝ)/32 - 1) * 3/10 := by
      have h3_pos : (0:ℝ) ≤ 3/10 := by norm_num
      nlinarith [hq_real_ge, h3_pos]
    nlinarith [h_q_lb, h_n_large]
  -- Combine all
  calc (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
      ≤ (∑ k ∈ Finset.range (6 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2) := h_chernoff
    _ ≤ 6 * Real.exp (-((q:ℝ) * 3/10)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4
