import Mathlib
import Workspace.Types.AlternatingSumExpression

/-!
# CentralBinomialLowerTail — Proof attempt 4

Hoeffding lower-tail of Bin(n, 1/2) on r ∈ [-n/4, -n/8 - 1] ≤ exp(-n/32).

Strategy (optimal Chernoff with c = 5/3):
1. Reindex k = r + n/2; sum becomes ∑_{k ∈ [n/4, 3n/8-1]∩ℤ} bin(n, 1/2, k).
2. Extend to ∑_{k=0..(3n/8 - 1)} bin(n, 1/2, k) (bounded above since terms are ≥ 0).
3. Chernoff with c = 5/3: ∑_{k<K} bin(m,1/2,k) · (5/3)^{K-k} extends to ∑ all k:
   = (5/3)^K · (3/10 + 1/2)^m = (5/3)^K · (4/5)^m.
4. Numerical: (5/3)^{3n/8} · (4/5)^n ≤ exp(-n/32) for n ≥ 10^12.
   We prove (5/3)^3 · (4/5)^8 ≤ exp(-1/4 - δ) for some small δ, then raise to (n/8)-th power.

To handle Nat-division gracefully:
- Set q := n / 8 (Nat), so 8q ≤ n ≤ 8q + 7.
- (5/3)^{K} · (4/5)^n: for K ≤ 3q (achievable since k ≤ 3n/8 - 1 ≤ 3q + (3·7)/8 - 1 ≈ 3q + 1.6),
  and (4/5)^n ≤ (4/5)^{8q} (since 4/5 ≤ 1 and n ≥ 8q).
- So (5/3)^K · (4/5)^n ≤ ((5/3)^3 · (4/5)^8)^q ≤ exp(-q · δ) for some δ > 1/4 + slack.
- For n ≥ 10^12, q ≥ 10^12/8 - 1, so q/4 ≥ n/32 - 1/4 (approx), and the slack from q vs n/8 is tiny.

For simplicity, handle the upper bound K ≤ 3q + 2 (a few extra terms are fine since terms are ≥ 0).
-/

set_option maxHeartbeats 32000000

open Workspace.Types.AlternatingSumExpression

namespace CentralBinomialLowerTailProof

-- For z ≤ m, binPMF m (1/2) z = C(m, z) · (1/2)^m.
lemma binPMF_half_eq (m z : ℕ) (hz : z ≤ m) :
    binPMF m (1/2 : ℝ) z = (m.choose z : ℝ) * (1/2)^m := by
  unfold binPMF
  rw [if_pos hz]
  have h1 : (1 - (1/2 : ℝ)) = 1/2 := by ring
  rw [h1]
  have hpow : (1/2:ℝ)^z * (1/2:ℝ)^(m-z) = (1/2:ℝ)^m := by
    rw [← pow_add]; congr 1; omega
  -- Goal: (m.choose z) * (1/2)^z * (1/2)^(m-z) = (m.choose z) * (1/2)^m
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

-- binPMFInt = binPMF when index in range
lemma binPMFInt_of_nat_le (m : ℕ) (p : ℝ) (z : ℕ) (hz : z ≤ m) :
    binPMFInt m p (z : ℤ) = binPMF m p z := by
  unfold binPMFInt
  have h0 : (0 : ℤ) ≤ (z : ℤ) := Int.ofNat_nonneg z
  have h1 : (z : ℤ) ≤ (m : ℤ) := by exact_mod_cast hz
  rw [if_pos ⟨h0, h1⟩]
  simp [Int.toNat_natCast]

-- nonneg of binPMFInt
lemma binPMFInt_nonneg (m : ℕ) (p : ℝ) (z : ℤ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMFInt m p z := by
  unfold binPMFInt
  split_ifs with h
  · exact binPMF_nonneg m z.toNat p hp hp1
  · exact le_refl 0

-- Optimal Chernoff lower-tail bound for Bin(m, 1/2).
-- For any K (no upper bound on K needed since sum extended over [0, m]):
--   ∑_{k < K} bin(m, 1/2, k) ≤ (5/3)^K · (4/5)^m
lemma chernoff_optimal_bound (m K : ℕ) :
    (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k) ≤ (5/3:ℝ)^K * (4/5:ℝ)^m := by
  have h53_pos : (0:ℝ) < 5/3 := by norm_num
  have h53_ge1 : (1:ℝ) ≤ 5/3 := by norm_num
  -- Step 1: ∑_{k<K} binPMF m (1/2) k ≤ (5/3)^K · ∑_{k<K} C(m,k) · (3/10)^k · (1/2)^{m-k}
  have h_step1 :
      (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k)
        ≤ (5/3:ℝ)^K *
            (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hkm : k ≤ m
    · rw [binPMF_half_eq m k hkm]
      have hC_nn : (0:ℝ) ≤ (m.choose k : ℝ) := by exact_mod_cast Nat.zero_le _
      have hkK : k ≤ K := Nat.le_of_lt hk
      have h_53Kk_ge1 : (1:ℝ) ≤ (5/3:ℝ)^(K - k) := one_le_pow₀ h53_ge1
      have h_half_split : (1/2:ℝ)^m = (1/2:ℝ)^k * (1/2:ℝ)^(m-k) := by
        rw [← pow_add]; congr 1; omega
      rw [h_half_split]
      have hsplit : (5/3:ℝ)^K = (5/3:ℝ)^k * (5/3:ℝ)^(K - k) := by
        rw [← pow_add]; congr 1; omega
      have h_combine : (5/3:ℝ)^k * (3/10:ℝ)^k = (1/2:ℝ)^k := by
        rw [← mul_pow]; congr 1; norm_num
      have h_pos : (0:ℝ) ≤ (1/2:ℝ)^(m - k) := pow_nonneg (by norm_num) _
      have hbase_nn : (0:ℝ) ≤ (m.choose k : ℝ) * (5/3:ℝ)^k * (3/10:ℝ)^k * (1/2:ℝ)^(m-k) := by
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg hC_nn
        · exact pow_nonneg (le_of_lt h53_pos) _
        · exact pow_nonneg (by norm_num) _
        · exact h_pos
      calc (m.choose k : ℝ) * ((1/2:ℝ)^k * (1/2:ℝ)^(m - k))
          = (m.choose k : ℝ) * ((5/3:ℝ)^k * (3/10:ℝ)^k) * (1/2:ℝ)^(m-k) := by
            rw [h_combine]; ring
        _ = (m.choose k : ℝ) * (5/3:ℝ)^k * (3/10:ℝ)^k * (1/2:ℝ)^(m-k) := by ring
        _ ≤ (m.choose k : ℝ) * (5/3:ℝ)^k * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)
              * (5/3:ℝ)^(K - k) := by
            have := mul_le_mul_of_nonneg_left h_53Kk_ge1 hbase_nn
            linarith
        _ = (5/3:ℝ)^K * ((m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) := by
            rw [hsplit]; ring
    · push_neg at hkm
      have : binPMF m (1/2 : ℝ) k = 0 := by
        unfold binPMF; rw [if_neg (by omega)]
      rw [this]
      apply mul_nonneg
      · exact pow_nonneg (le_of_lt h53_pos) _
      · apply mul_nonneg
        apply mul_nonneg
        · exact_mod_cast Nat.zero_le _
        · exact pow_nonneg (by norm_num) _
        · exact pow_nonneg (by norm_num) _
  -- Step 2: ∑_{k<K} ... ≤ ∑_{k<m+1} ...
  have h_step2 :
      (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k))
        ≤ (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_range] at *; exact lt_of_lt_of_le hx (le_max_left _ _)
    · intros k _ _
      apply mul_nonneg
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact pow_nonneg (by norm_num) _
      · exact pow_nonneg (by norm_num) _
  -- Step 3: ∑_{k<m+1} ... = (4/5)^m. Sum over k > m: contributions are 0 (since C(m,k) = 0).
  have h_step3 :
      (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k))
        = (4/5:ℝ)^m := by
    -- Split the sum at m+1
    have h_split : Finset.range (max K (m+1))
        = Finset.range (m+1) ∪ ((Finset.range (max K (m+1))) \ Finset.range (m+1)) := by
      rw [Finset.union_sdiff_of_subset]
      intro x hx
      rw [Finset.mem_range] at *
      exact lt_of_lt_of_le hx (le_max_right _ _)
    rw [h_split]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    -- Second part: sum over k > m of C(m,k) · ... = 0 since C(m,k) = 0 for k > m.
    have h_second_zero : (∑ k ∈ ((Finset.range (max K (m+1))) \ Finset.range (m+1)),
                           (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hk
      have hk_gt : m + 1 ≤ k := by omega
      have h_choose_zero : m.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h_choose_zero]
      simp
    rw [h_second_zero, add_zero]
    -- First part: ∑_{k < m+1} C(m,k) · (3/10)^k · (1/2)^{m-k} = (4/5)^m
    have h_addpow := add_pow (3/10 : ℝ) (1/2) m
    rw [show (3/10:ℝ) + 1/2 = 4/5 from by norm_num] at h_addpow
    rw [h_addpow]
    apply Finset.sum_congr rfl
    intros k _; ring
  -- Combine
  calc (∑ k ∈ Finset.range K, binPMF m (1/2 : ℝ) k)
      ≤ (5/3:ℝ)^K *
          (∑ k ∈ Finset.range K, (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) := h_step1
    _ ≤ (5/3:ℝ)^K *
          (∑ k ∈ Finset.range (max K (m+1)), (m.choose k : ℝ) * (3/10:ℝ)^k * (1/2:ℝ)^(m-k)) := by
        apply mul_le_mul_of_nonneg_left h_step2 (pow_nonneg (le_of_lt h53_pos) _)
    _ = (5/3:ℝ)^K * (4/5:ℝ)^m := by rw [h_step3]

-- Numerical: exp(1/4) ≤ 65/50 = 13/10. We use Real.exp_bound'.
-- exp(1/4) ≈ 1.28403, and 13/10 = 1.3. So exp(1/4) ≤ 13/10 with 1.5% slack.
lemma exp_quarter_le_thirteen_tenths : Real.exp (1/4) ≤ 13/10 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1/4)
                            (by norm_num : (1/4:ℝ) ≤ 1) (n := 4) (by norm_num : 0 < 4)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.factorial, zero_add]
  norm_num

-- Lemma: (5/3)^3 · (4/5)^8 ≤ exp(-1/4) · 1.
-- Numerical: (5/3)^3 · (4/5)^8 = 8192000/10546875 ≈ 0.7767.
-- exp(-1/4) ≥ 10/13 ≈ 0.7692. 0.7692 < 0.7767, so (5/3)^3 · (4/5)^8 > exp(-1/4) · 10/13?
-- Wait — we need (5/3)^3 · (4/5)^8 ≤ exp(-1/4). exp(-1/4) ≈ 0.7788. 0.7767 < 0.7788 ✓.
-- We have exp(-1/4) ≥ 10/13 = 0.7692... only gives the WEAKER bound.
-- Need: exp(-1/4) ≥ specific lower bound that exceeds (5/3)^3 · (4/5)^8.

-- Use Real.add_one_le_exp twice for a lower bound on exp(-1/4):
-- exp(-1/4) ≥ 1 - 1/4 = 3/4? No, that's too weak (3/4 = 0.75 < 0.7767).
-- Use a better lower bound: exp(x) ≥ 1 + x + x²/2 for ALL x (no!)
-- Actually exp(x) = ∑ x^k/k!, and for x < 0, alternating series bounds work in a different way.

-- For x ≥ 0: exp(x) ≥ 1 + x + x²/2 + x³/6 + ... + x^n/n! (truncating gives lower bound, since
-- all terms are nonneg).
-- For x < 0: this is alternating; partial sums alternate around exp(x).

-- For x = 1/4 (positive): exp(1/4) ≥ 1 + 1/4 + 1/32 = 41/32 = 1.28125.
-- We have exp(1/4) ≤ 13/10 = 1.3.
-- exp(-1/4) = 1/exp(1/4) ∈ [10/13, 32/41] ≈ [0.7692, 0.7805].
-- We need exp(-1/4) ≥ 0.7767, so we need lower bound > 0.7767.
-- 32/41 ≈ 0.7805 — but that's the UPPER bound on exp(-1/4) (from lower bound on exp(1/4)).
-- We want lower bound on exp(-1/4): exp(-1/4) ≥ 1/exp(1/4) ≥ 1/(13/10) = 10/13 ≈ 0.7692. Insufficient.

-- We need TIGHTER upper bound on exp(1/4). Try exp(1/4) ≤ ratio where 1/ratio ≥ (5/3)^3 · (4/5)^8.
-- (5/3)^3 · (4/5)^8 = 8192000/10546875.
-- We need exp(1/4) ≤ 10546875/8192000 ≈ 1.28744.
-- Use Real.exp_bound' with n = 5: exp(1/4) ≤ 1 + 1/4 + 1/32 + 1/384 + 1/6144 + (1/4)^5 · 6/(120·5)
--   = 1 + 0.25 + 0.03125 + 0.002604 + 0.0001628 + (1/1024) · 6/600
--   = 1.284015 + 0.0009766·0.01 ≈ 1.28406.
-- Wait the last term: (1/4)^5 · 6 / (120 · 5) = (1/1024) · 6/600 = 6/(1024·600) = 1/102400 ≈ 9.77e-6.
-- Total ≈ 1.28403. 1.28403 < 1.28744 ✓.
-- So with n = 5: exp(1/4) ≤ 1.28406 + a tiny tail bound = approximately 1.28406 in Real.exp_bound'.

-- Actually the bound from Real.exp_bound' n=5 is exactly:
--   ∑_{k=0..4} x^k/k! + x^5 · 6/(120·5)
--   For x = 1/4: 1 + 1/4 + 1/32 + 1/384 + 1/6144 + 1/(1024·100)
--   = (let me compute using common denom for numericals)
-- We just need a rational upper bound less than 10546875/8192000.
-- Try 1.286 = 1286/1000 = 643/500. 1.286 < 1.28744 ✓.
-- Verify exp_bound' with n=5 ≤ 643/500:
-- 1 + 1/4 + 1/32 + 1/384 + 1/6144 + (1/4)^5 · 6/(120·5)
-- = 1 + 1/4 + 1/32 + 1/384 + 1/6144 + 6/(1024·600)
-- = 1 + 1/4 + 1/32 + 1/384 + 1/6144 + 1/102400
-- LCM = 102400: 102400/102400 + 25600/102400 + 3200/102400 + 266.66.../102400 + ... messy.
-- Use norm_num decision procedure.

-- Actually, let me set ratio = 643/500 and check:
-- Want: ∑_{k=0..4} (1/4)^k/k! + (1/4)^5·6/(120·5) ≤ 643/500.
-- = 1 + 1/4 + 1/32 + 1/384 + 1/6144 + 6/614400
-- = 1 + 1/4 + 1/32 + 1/384 + 1/6144 + 1/102400

-- norm_num should handle this. Let me write the proof.

lemma exp_quarter_le_643_500 : Real.exp (1/4) ≤ 643/500 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1/4)
                            (by norm_num : (1/4:ℝ) ≤ 1) (n := 5) (by norm_num : 0 < 5)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.factorial, zero_add]
  norm_num

-- exp(251/1000) ≤ 12874/10000 = 1.2874.
-- Numerical: actual exp(0.251) ≈ 1.28529 < 1.2874.
-- Use Real.exp_bound' with n = 6.
lemma exp_251_1000_le : Real.exp (251/1000) ≤ 12874/10000 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 251/1000)
                            (by norm_num : (251/1000:ℝ) ≤ 1) (n := 6) (by norm_num : 0 < 6)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
    Nat.factorial, zero_add]
  norm_num

-- (5/3)^3 · (4/5)^8 ≤ exp(-251/1000).
lemma five_thirds_cubed_four_fifths_eighth_le_exp_neg_251_1000 :
    (5/3:ℝ)^3 * (4/5:ℝ)^8 ≤ Real.exp (-(251/1000)) := by
  have h_exp_pos : (0:ℝ) < Real.exp (251/1000) := Real.exp_pos _
  have h_exp_le : Real.exp (251/1000) ≤ 12874/10000 := exp_251_1000_le
  rw [Real.exp_neg]
  rw [le_inv_comm₀ (by positivity : (0:ℝ) < (5/3:ℝ)^3 * (4/5:ℝ)^8) h_exp_pos]
  refine le_trans h_exp_le ?_
  -- Want: 12874/10000 ≤ ((5/3)^3 · (4/5)^8)⁻¹ = 10546875/8192000.
  rw [show ((5/3:ℝ)^3 * (4/5:ℝ)^8)⁻¹ = 10546875/8192000 from by
    rw [show (5/3:ℝ)^3 * (4/5:ℝ)^8 = 8192000/10546875 from by norm_num]
    rw [inv_div]]
  -- 12874/10000 ≤ 10546875/8192000
  -- ↔ 12874 · 8192000 ≤ 10546875 · 10000
  -- 12874 · 8192000 = 105463808000.
  -- 10546875 · 10000 = 105468750000.
  -- 105463808000 ≤ 105468750000 ✓.
  norm_num

-- Now raise to (q := n/8)-th power: ((5/3)^3 · (4/5)^8)^q ≤ exp(-q · 251/1000).
lemma chernoff_pow_bound_251 (q : ℕ) :
    (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) ≤ Real.exp (-((q : ℝ) * 251/1000)) := by
  have h_base : (5/3:ℝ)^3 * (4/5:ℝ)^8 ≤ Real.exp (-(251/1000)) :=
    five_thirds_cubed_four_fifths_eighth_le_exp_neg_251_1000
  have h_base_nn : (0:ℝ) ≤ (5/3:ℝ)^3 * (4/5:ℝ)^8 := by positivity
  have h_pow := pow_le_pow_left₀ h_base_nn h_base q
  rw [← Real.exp_nat_mul] at h_pow
  rw [show ((q:ℝ) * -(251/1000)) = -((q:ℝ) * 251/1000) from by ring] at h_pow
  refine le_trans ?_ h_pow
  rw [mul_pow]
  have e1 : (5/3:ℝ)^(3*q) = ((5/3:ℝ)^3)^q := by rw [← pow_mul]
  have e2 : (4/5:ℝ)^(8*q) = ((4/5:ℝ)^8)^q := by rw [← pow_mul]
  rw [e1, e2]

-- Now (5/3)^3 · (4/5)^8 ≤ 500/643 ≤ exp(-1/4)?
-- 500/643 ≈ 0.7776. (5/3)^3 · (4/5)^8 ≈ 0.7767. So 0.7767 < 0.7776 ✓.
-- 8192000/10546875 ≤ 500/643 ↔ 8192000 · 643 ≤ 10546875 · 500.
-- 8192000 · 643 = ?
-- 8192000 · 600 = 4915200000
-- 8192000 · 43 = 352256000
-- Sum: 5267456000.
-- 10546875 · 500 = 5273437500.
-- 5267456000 ≤ 5273437500 ✓.

lemma five_thirds_cubed_four_fifths_eighth_le_exp_neg_quarter :
    (5/3:ℝ)^3 * (4/5:ℝ)^8 ≤ Real.exp (-(1/4)) := by
  have h_exp_pos : (0:ℝ) < Real.exp (1/4) := Real.exp_pos _
  have h_exp_le : Real.exp (1/4) ≤ 643/500 := exp_quarter_le_643_500
  rw [Real.exp_neg]
  rw [le_inv_comm₀ (by positivity : (0:ℝ) < (5/3:ℝ)^3 * (4/5:ℝ)^8) h_exp_pos]
  refine le_trans h_exp_le ?_
  -- Want: 643/500 ≤ ((5/3)^3 · (4/5)^8)⁻¹ = 10546875/8192000.
  rw [show ((5/3:ℝ)^3 * (4/5:ℝ)^8)⁻¹ = 10546875/8192000 from by
    rw [show (5/3:ℝ)^3 * (4/5:ℝ)^8 = 8192000/10546875 from by norm_num]
    rw [inv_div]]
  norm_num

-- Now raise to (q := n/8)-th power: ((5/3)^3 · (4/5)^8)^q = (5/3)^{3q} · (4/5)^{8q} ≤ exp(-q/4).
lemma chernoff_pow_bound (q : ℕ) :
    (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) ≤ Real.exp (-((q : ℝ)/4)) := by
  have h_base : (5/3:ℝ)^3 * (4/5:ℝ)^8 ≤ Real.exp (-(1/4)) :=
    five_thirds_cubed_four_fifths_eighth_le_exp_neg_quarter
  have h_base_nn : (0:ℝ) ≤ (5/3:ℝ)^3 * (4/5:ℝ)^8 := by positivity
  have h_pow := pow_le_pow_left₀ h_base_nn h_base q
  rw [← Real.exp_nat_mul] at h_pow
  rw [show ((q:ℝ) * -(1/4)) = -((q:ℝ)/4) from by ring] at h_pow
  refine le_trans ?_ h_pow
  -- Want: (5/3)^{3q} · (4/5)^{8q} ≤ ((5/3)^3 · (4/5)^8)^q
  rw [mul_pow]
  have e1 : (5/3:ℝ)^(3*q) = ((5/3:ℝ)^3)^q := by rw [← pow_mul]
  have e2 : (4/5:ℝ)^(8*q) = ((4/5:ℝ)^8)^q := by rw [← pow_mul]
  rw [e1, e2]

-- Cast inequality: (n : ℝ)/8 - 1 ≤ ((n/8 : ℕ) : ℝ).
lemma cast_div_8_ge (n : ℕ) : (n : ℝ) / 8 - 1 ≤ ((n / 8 : ℕ) : ℝ) := by
  have h : 8 * (n / 8) + 8 > n := by
    have := Nat.div_add_mod n 8
    have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  have h_real : 8 * ((n / 8 : ℕ) : ℝ) + 8 > (n : ℝ) := by exact_mod_cast h
  linarith

-- For n ≥ 10^12, (n / 8 : ℕ) / 4 ≥ n / 32 (in Real).
-- Equivalently: (n / 8 : ℕ) · 8 ≥ n (no!) — use cast_div_8_ge: (n / 8 : ℕ) ≥ n/8 - 1.
-- So ((n / 8 : ℕ) : ℝ) / 4 ≥ (n/8 - 1)/4 = n/32 - 1/4.
-- Want ≥ n/32. So need extra n/32 stuff, but we have a deficit of 1/4. Fix using n ≥ 10^12.

-- Final assembly: (5/3)^K · (4/5)^n ≤ exp(-q/4) for q = n/8 (Nat).
-- Then exp(-q/4) ≤ exp(-n/32) requires q/4 ≥ n/32.
-- q = n/8 (Nat) ≥ n/8 - 1 (Real). q/4 ≥ n/32 - 1/4.
-- We need n/32 - 1/4 ≥ n/32? No! We need q/4 ≥ n/32, i.e., (n/8 - 1)/4 ≥ n/32.
-- Equiv: n/32 - 1/4 ≥ n/32, equivalent to -1/4 ≥ 0, FALSE!
-- So we need a tighter base bound to absorb the slack.

-- So we DO need exp(-1/4 - δ) base bound for δ > 0. Let's use exp(-1/4 - 1/2000) = exp(-251/1000).
-- (5/3)^3 · (4/5)^8 = 8192000/10546875.
-- exp(-251/1000) needs: (5/3)^3 · (4/5)^8 ≤ exp(-251/1000).
-- 1/exp(251/1000) ≤ 1/exp(1/4) — wait, larger exponent gives smaller exp.
-- exp(251/1000) > exp(1/4) (since 251/1000 = 0.251 > 0.25).
-- exp(0.251) ≈ 1.2853.
-- 1/exp(0.251) ≈ 0.7780.
-- (5/3)^3 · (4/5)^8 ≈ 0.7767 < 0.7780 ✓.

-- Continue with exp(0.251) ≤ ratio that fits. Want (5/3)^3 · (4/5)^8 ≤ 1/ratio, i.e., ratio ≤ 10546875/8192000.

-- Actually let me just compute more carefully. We have 8192000/10546875 ≈ 0.776701.
-- We want exp(-c) ≥ 0.776701 for our chosen c.
-- exp(-c) ≥ 0.776701 ⟺ c ≤ -ln(0.776701) ≈ 0.25286.
-- So any c ≤ 0.25286 works.

-- For our final goal, we want q · c ≥ n/32, i.e., c · n/8 ≥ n/32 → c ≥ 1/4.
-- BUT q ≤ n/8 (real, since q = n/8 floored), more precisely q ≥ n/8 - 1.
-- So q · c ≥ (n/8 - 1) · c.
-- Want: (n/8 - 1) · c ≥ n/32.
-- ↔ n · c/8 - c ≥ n/32
-- ↔ n · (c/8 - 1/32) ≥ c
-- ↔ n · (4c - 1)/32 ≥ c
-- ↔ n ≥ 32c / (4c - 1) for 4c > 1, i.e., c > 1/4.
-- For c just above 1/4: 32c/(4c-1) is huge.
-- For c = 1/4 + ε: 32(1/4 + ε)/(4·(1/4 + ε) - 1) = (8 + 32ε)/(4ε) = 2/ε + 8. For ε = 0.001, n ≥ 2008.
-- For ε = 0.001: c = 0.251.
-- Verify (5/3)^3 · (4/5)^8 ≤ exp(-0.251)?
-- 0.776701 ≤ exp(-0.251) = 0.778...? Let me compute exp(-0.251):
-- exp(-0.251) = 1/exp(0.251). exp(0.251) ≈ 1 + 0.251 + 0.251²/2 + 0.251³/6 + ... ≈ 1.28529.
-- 1/1.28529 ≈ 0.7780. So exp(-0.251) ≈ 0.7780. 0.7767 < 0.7780 ✓ (slack ~0.13%).

-- So strategy:
-- (a) Prove (5/3)^3 · (4/5)^8 ≤ exp(-251/1000).
-- (b) Then for q = n/8 (Nat): (5/3)^{3q} · (4/5)^{8q} ≤ exp(-251q/1000).
-- (c) For K ≤ 3q + d for some small d, and 8q ≤ n: (5/3)^K · (4/5)^n ≤ (5/3)^{3q+d} · (4/5)^{8q}
--     = (5/3)^d · (5/3)^{3q} · (4/5)^{8q} ≤ (5/3)^d · exp(-251q/1000).
-- (d) For n ≥ 10^12 and q ≥ n/8 - 1, 251q/1000 ≥ 251(n/8 - 1)/1000 = 251n/8000 - 251/1000.
--     We want (5/3)^d · exp(-251q/1000) ≤ exp(-n/32).
--     Take logs: d · log(5/3) - 251q/1000 ≤ -n/32, i.e., 251q/1000 ≥ n/32 + d · log(5/3).
--     log(5/3) ≤ 1 (very loose), so RHS ≤ n/32 + d.
--     LHS = 251q/1000. q ≥ n/8 - 1, so LHS ≥ 251(n/8 - 1)/1000 = 251n/8000 - 251/1000.
--     Need: 251n/8000 - 251/1000 ≥ n/32 + d
--     ↔ n · (251/8000 - 1/32) ≥ d + 251/1000
--     ↔ n · (251/8000 - 250/8000) = n · 1/8000 ≥ d + 251/1000
--     ↔ n ≥ 8000 · (d + 251/1000) = 8000d + 2008.
--     For n ≥ 10^12 and d a small bounded constant (say d ≤ 10), n ≥ 10^12 ≫ 8000·10 + 2008 = 82008. ✓.

-- Let me reconsider step (c): need K ≤ 3q + d. From the original sum, k_max ≤ 3n/8 - 1 (in some integer sense),
-- but Nat division gives K = K_max + 1 (the upper bound on Finset.range), and we need K ≤ 3q + ?
-- The upper bound on k is kHi := -(n/8 : ℤ) - 1 + (n/2 : ℤ).
-- For arbitrary n: -(n/8 : ℤ) - 1 + (n/2 : ℤ). With Nat division: n = 8q + r, r ∈ [0,7].
--   n/8 (Nat) = q. n/2 (Nat) = 4q + r/2 (Nat) = 4q + (r/2 : ℕ).
--   So kHi = -q - 1 + 4q + (r/2 : ℕ) = 3q - 1 + (r/2 : ℕ). For r ∈ [0,7], (r/2 : ℕ) ∈ {0,0,1,1,2,2,3,3}.
--   So kHi ∈ {3q-1, 3q-1, 3q, 3q, 3q+1, 3q+1, 3q+2, 3q+2}.
--   Max is 3q + 2 (when r ∈ {6, 7}).
-- So range of k: K = kHi + 1 ≤ 3q + 3. For sum bound, use K ≤ 3q + 3.

-- Now (5/3)^K · (4/5)^n ≤ (5/3)^{3q+3} · (4/5)^n ≤ (5/3)^{3q+3} · (4/5)^{8q}
--   = (5/3)^3 · ((5/3)^3 · (4/5)^8)^q ≤ (125/27) · exp(-251q/1000).
-- Want ≤ exp(-n/32). Take logs: log(125/27) - 251q/1000 ≤ -n/32.
-- log(125/27) ≈ 1.5325.
-- 251q/1000 ≥ 251(n/8 - 1)/1000 = 251n/8000 - 251/1000.
-- Want: 1.5325 - 251n/8000 + 251/1000 ≤ -n/32 = -250n/8000.
-- ↔ 1.5325 + 0.251 ≤ 251n/8000 - 250n/8000 = n/8000
-- ↔ 1.7835 ≤ n/8000 ↔ n ≥ 14268.
-- For n ≥ 10^12 ≫ 14268 ✓.

-- We don't need log(125/27); we can bound (5/3)^3 directly as a real number.
-- (5/3)^3 = 125/27 < 5. So (5/3)^3 · exp(-251q/1000) ≤ 5 · exp(-251q/1000).
-- Want ≤ exp(-n/32). 5 · exp(-251q/1000) ≤ exp(-n/32) ↔ ln(5) - 251q/1000 ≤ -n/32.
-- ln 5 ≤ 5/3 (very loose; ln(5) ≈ 1.61). Actually more precisely, just use ln 5 < 2.
-- 2 - 251q/1000 ≤ -n/32 → 251q/1000 ≥ n/32 + 2.
-- 251q/1000 ≥ 251(n/8 - 1)/1000.
-- Want: 251(n/8 - 1)/1000 ≥ n/32 + 2, i.e., 251n/8000 - 251/1000 ≥ n/32 + 2.
-- ↔ n(251/8000 - 1/32) ≥ 2 + 251/1000 = 2251/1000.
-- 251/8000 - 1/32 = 251/8000 - 250/8000 = 1/8000.
-- So n/8000 ≥ 2251/1000 ↔ n ≥ 2251 · 8 = 18008. For n ≥ 10^12 ✓.

-- Even more crudely: (5/3)^3 ≤ 5, exp(2) ≤ 8, so (5/3)^3 ≤ exp(2). Then
-- (5/3)^3 · exp(-251q/1000) ≤ exp(2 - 251q/1000) ≤ exp(-n/32) iff
-- 2 - 251q/1000 ≤ -n/32, etc. Same as above.

-- Even simpler: (5/3)^K ≤ (5/3)^{3q+3} and we directly want
-- (5/3)^{3q+3} · (4/5)^n ≤ (4/5)^{anything} = something easily bounded.

-- Plan: do the full computation symbolically using just inequalities and `nlinarith` with
-- explicit bounds.

end CentralBinomialLowerTailProof

theorem CentralBinomialLowerTail :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n →
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ Real.exp (-((n : ℝ) / 32)) := by
  intro n hn
  -- Basic facts.
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Set q := n / 8 (Nat).
  set q : ℕ := n / 8 with hq_def
  -- 8q ≤ n
  have h8q_le : 8 * q ≤ n := by rw [hq_def]; exact Nat.mul_div_le n 8
  -- q ≥ n/8 - 1 (Real)
  have hq_real_ge : (n : ℝ)/8 - 1 ≤ (q : ℝ) := by
    rw [hq_def]
    exact CentralBinomialLowerTailProof.cast_div_8_ge n
  -- For n ≥ 10^12, q ≥ 10^12 / 8 - 1 ≥ 100.
  have hq_pos : 1 ≤ q := by
    rw [hq_def]
    have h100 : 100 ≤ n / 8 := by
      have : 800 ≤ n := by linarith
      omega
    omega
  -- We will bound K_max := the cardinality of the index set.
  -- The original Icc has cardinality (b - a + 1) where a = -(n/4), b = -(n/8) - 1.
  -- b - a + 1 = -(n/8) - 1 + (n/4) + 1 = (n/4) - (n/8) = (n/8) (Nat-wise approx).
  -- But we'll directly bound by showing each index k = (r + n/2).toNat is in [0, 3n/8].
  -- For r ∈ [-(n/4), -(n/8)-1], k = r + n/2 ∈ [n/2 - n/4, n/2 - n/8 - 1] = [n/4, 3n/8 - 1].
  -- In Nat division: bounds vary, but we'll use upper bound 3q + 3 (since 3n/8 ≤ 3q + 3 when n = 8q + r).
  -- Actually, the upper bound on k is:
  --   k = r + (n/2 : ℤ) ≤ -(n/8 : ℤ) - 1 + (n/2 : ℤ).
  -- For n = 8q + s with s ∈ [0,7]:
  --   (n/8 : ℤ) = q. (n/2 : ℤ) = (4q + s/2 : ℕ) where s/2 is Nat division.
  --   Specifically, for s ∈ {0,1}: n/2 = 4q. For s ∈ {2,3}: n/2 = 4q+1. ... s ∈ {6,7}: n/2 = 4q+3.
  --   So upper bound on k: -q - 1 + (4q + (s/2 : ℕ)) = 3q + (s/2 : ℕ) - 1 ≤ 3q + 2.
  -- So K_max ≤ 3q + 2 (upper bound on k); the range of k is in [0, 3q+2].
  -- We use Finset.range (3q + 3) as a covering range.

  -- Step 1: Bound the sum by ∑ k ∈ Finset.range (3q+3), binPMF n (1/2) k.
  have h_step_bound :
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (3 * q + 3),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
    -- Map: r ↦ (r + n/2).toNat. This is an injection on the Icc.
    -- The image lies in [0, 3q+2] (i.e., Finset.range (3q+3)).
    -- For each r in our range, binPMFInt n (1/2) (r + n/2) = binPMF n (1/2) (r + n/2).toNat
    --   (provided 0 ≤ r + n/2 ≤ n).
    -- Then we sum over the image and bound by the sum over range.
    -- Define the shift function:
    let shift : ℤ → ℕ := fun r => (r + (n : ℤ) / 2).toNat
    -- Show: ∑ r ∈ Icc, binPMFInt n (1/2) (r + n/2) = ∑ r ∈ Icc, binPMF n (1/2) (shift r).
    have h_eq : (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
                  Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
                = (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
                    Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      obtain ⟨hr_lo, hr_hi⟩ := hr
      -- We need: binPMFInt n (1/2) (r + n/2) = binPMF n (1/2) (r + n/2).toNat.
      -- This holds iff 0 ≤ r + n/2 ≤ n. For our range:
      -- r ≥ -(n/4 : ℤ), so r + (n/2 : ℤ) ≥ -(n/4 : ℤ) + (n/2 : ℤ) = (n/2 : ℤ) - (n/4 : ℤ).
      -- (n/2 : ℤ) - (n/4 : ℤ) ≥ 0 (Nat division: floor(n/4) ≤ floor(n/2)).
      -- r ≤ -(n/8 : ℤ) - 1, so r + (n/2 : ℤ) ≤ -(n/8 : ℤ) - 1 + (n/2 : ℤ) ≤ (n/2 : ℤ) ≤ n.
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ (n : ℤ) := by
        have h_n2 : (n : ℤ)/2 ≤ (n : ℤ) := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        have h_n8_pos : (0 : ℤ) ≤ (n : ℤ)/8 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      -- Apply binPMFInt definition.
      unfold Workspace.Types.AlternatingSumExpression.binPMFInt
      rw [if_pos ⟨hr_plus_lo, hr_plus_hi⟩]
    rw [h_eq]
    -- Now bound: ∑ r ∈ Icc, binPMF n (1/2) (shift r) ≤ ∑ k ∈ Finset.range (3q+3), binPMF n (1/2) k.
    -- Use Finset.sum_le_sum_of_inj or sum_le_sum_of_subset_of_nonneg via Finset.image.
    -- shift is injective on Icc since r ↦ r + n/2 is injective.
    have h_shift_inj : Set.InjOn shift (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1)) := by
      intro r1 hr1 r2 hr2 h_eq_shift
      rw [Finset.mem_coe, Finset.mem_Icc] at hr1 hr2
      simp only [shift] at h_eq_shift
      -- (r1 + n/2).toNat = (r2 + n/2).toNat.
      -- For r in our range, r + n/2 ≥ 0 (proved above).
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
    -- Sum over Icc = sum over image (using injectivity).
    have h_image_sum :
        (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r))
        = (∑ k ∈ (Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1)).image shift,
            Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
      rw [Finset.sum_image]
      intro r1 hr1 r2 hr2 h_eq_shift
      exact h_shift_inj hr1 hr2 h_eq_shift
    rw [h_image_sum]
    -- Now bound by sum over Finset.range (3q + 3).
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨r, hr_in, hr_eq⟩ := hk
      rw [Finset.mem_Icc] at hr_in
      rw [Finset.mem_range]
      simp only [shift] at hr_eq
      -- shift r = (r + n/2).toNat. We need to show this < 3q + 3.
      have hr_lo : -((n : ℤ)/4) ≤ r := hr_in.1
      have hr_hi : r ≤ -((n : ℤ)/8) - 1 := hr_in.2
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by
        have h1 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by
          have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ -((n : ℤ)/8) - 1 + (n : ℤ)/2 := by linarith
      -- Bound: -(n/8 : ℤ) - 1 + (n/2 : ℤ) ≤ 3q + 2, where q = n/8.
      -- We have (n/2 : ℤ) - (n/8 : ℤ) = ? . With n = 8q + s, s ∈ [0, 7]:
      --   (n/8 : ℤ) = q. (n/2 : ℤ) = (4q + s/2 : ℕ).
      --   So (n/2 : ℤ) - (n/8 : ℤ) = 3q + (s/2 : ℕ). Max is 3q + 3 (when s = 6 or 7).
      --   So bound is 3q + 3 - 1 = 3q + 2.
      have hbound : -((n : ℤ)/8) - 1 + (n : ℤ)/2 ≤ 3 * (q : ℤ) + 2 := by
        -- (n/2 : ℤ) - (n/8 : ℤ) - 1 ≤ 3q + 2.
        -- n/2 = (n - n%2)/2; n/8 = (n - n%8)/8.
        -- Actually use omega via n = 8q + s with s = n % 8.
        have hn_def : n = 8 * q + n % 8 := by
          rw [hq_def]; omega
        have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
        -- Convert to Int
        have hq_int : (q : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le q
        have hn_int : (n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
        omega
      have h_kint_bound : (k : ℤ) ≤ 3 * (q : ℤ) + 2 := by
        rw [← hr_eq]
        have h_toNat_eq : ((r + (n : ℤ)/2).toNat : ℤ) = r + (n : ℤ)/2 :=
          Int.toNat_of_nonneg hr_plus_lo
        rw [h_toNat_eq]
        linarith
      -- Cast to Nat
      have hk_le : k ≤ 3 * q + 2 := by
        have := h_kint_bound
        have : (k : ℤ) ≤ ((3 * q + 2 : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this
      omega
    · intros k _ _
      exact CentralBinomialLowerTailProof.binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)
  -- Step 2: Apply Chernoff.
  have h_chernoff : (∑ k ∈ Finset.range (3 * q + 3),
                      Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
                    ≤ (5/3:ℝ)^(3 * q + 3) * (4/5:ℝ)^n :=
    CentralBinomialLowerTailProof.chernoff_optimal_bound n (3 * q + 3)
  -- Step 3: (5/3)^{3q+3} · (4/5)^n ≤ exp(-n/32).
  -- (5/3)^{3q+3} · (4/5)^n = (5/3)^3 · (5/3)^{3q} · (4/5)^{8q} · (4/5)^{n - 8q}
  -- ≤ (5/3)^3 · exp(-q/4) · 1 = (125/27) · exp(-q/4).
  -- Now (125/27) · exp(-q/4) ≤ exp(-n/32) iff log(125/27) - q/4 ≤ -n/32
  -- iff q/4 ≥ n/32 + log(125/27).
  -- log(125/27) ≤ 2 (since 125/27 < e²).
  -- For n ≥ 10^12, q ≥ n/8 - 1, so q/4 ≥ n/32 - 1/4. Need n/32 - 1/4 ≥ n/32 + 2: NEEDS slack.
  -- We need to use a stronger base bound: exp(-1/4 - δ) for some δ > 0 to get extra exponential decay.

  -- Plan: use the cleaner bound (5/3)^3 · (4/5)^8 ≤ exp(-1/4) (proven above),
  -- AND use the EXTRA factor of slack from n ≥ 10^12.
  -- (5/3)^{3q+3} · (4/5)^n ≤ (5/3)^3 · ((5/3)^3 · (4/5)^8)^q · 1
  --   ≤ 5 · exp(-q/4)  (since (5/3)^3 = 125/27 < 5)
  -- For n ≥ 10^12, q/4 ≥ (n/8 - 1)/4 = n/32 - 1/4.
  -- So 5 · exp(-q/4) ≤ 5 · exp(-n/32 + 1/4) = 5 · exp(1/4) · exp(-n/32).
  -- 5 · exp(1/4) < 5 · 1.3 = 6.5. To get ≤ exp(-n/32), need 5 · exp(1/4) · exp(-n/32) ≤ exp(-n/32).
  -- That requires 5 · exp(1/4) ≤ 1, FALSE.
  -- So we need to "absorb" 5 · exp(1/4) into exp's tail using n's huge size.

  -- Use slightly tighter Chernoff: 251/1000 instead of 1/4.
  -- (5/3)^3 · (4/5)^8 ≤ exp(-251/1000)? 251/1000 = 0.251. exp(-0.251) = 1/exp(0.251).
  -- exp(0.251) < 13/10 (we can prove: exp(0.251) ≤ 1.286 < 1.3).
  -- 1/exp(0.251) > 10/13 ≈ 0.7692. We have (5/3)^3 · (4/5)^8 ≈ 0.7767.
  -- So 0.7767 ≤ 0.7692? NO, 0.7767 > 0.7692. FAILS.

  -- Try exp(0.251) ≤ ratio: need (5/3)^3 · (4/5)^8 · exp(0.251) ≤ 1.
  -- (5/3)^3 · (4/5)^8 = 8192000 / 10546875 ≈ 0.7767.
  -- 0.7767 · exp(0.251) ≤ 1 ↔ exp(0.251) ≤ 1/0.7767 = 1.2875.
  -- exp(0.251) < ? We need exp(0.251) ≤ 1.2875. exp(0.251) ≈ 1.2853, so ≤ 1.2875 ✓.

  -- OK proving (5/3)^3 · (4/5)^8 ≤ exp(-251/1000) requires showing exp(251/1000) ≤ 10546875/8192000.
  -- Use Real.exp_bound' with sufficient n. Numerical work.

  -- Let's just use a CRUDE bound that has lots of slack.
  -- We want: (5/3)^{3q+3} · (4/5)^n ≤ exp(-n/32) for n ≥ 10^12.
  -- Equivalent: (3q+3) · log(5/3) + n · log(4/5) ≤ -n/32.
  -- log(5/3) > 0, log(4/5) < 0. Let A = log(5/3), B = -log(4/5) = log(5/4).
  -- (3q+3) · A - n · B ≤ -n/32.
  -- ↔ n · B ≥ (3q+3) · A + n/32.
  -- q ≤ n/8, so 3q+3 ≤ 3n/8 + 3.
  -- ↔ n · B ≥ (3n/8 + 3) · A + n/32, suffices n · B ≥ (3n/8) · A + 3A + n/32.
  -- ↔ n · (B - 3A/8 - 1/32) ≥ 3A.
  -- B - 3A/8 - 1/32 = log(5/4) - (3/8) log(5/3) - 1/32 ≈ 0.2231 - 0.1916 - 0.03125 = 0.0003.
  -- So n · 0.0003 ≥ 3 · log(5/3) ≈ 3 · 0.5108 = 1.5324.
  -- n ≥ 1.5324 / 0.0003 ≈ 5108. For n ≥ 10^12 ≫ 5108, ✓.

  -- This is quite tight. We need fairly precise log bounds: B - 3A/8 - 1/32 > some specific positive quantity.

  -- Alternative: use the explicit calculation (5/3)^3 · (4/5)^8 ≤ exp(-1/4).
  -- Then (5/3)^{3q+3} · (4/5)^n = (5/3)^3 · (5/3)^{3q} · (4/5)^n ≤ (5/3)^3 · ((5/3)^3 · (4/5)^8)^q · (4/5)^{n - 8q}
  --   ≤ 5 · exp(-q/4) · 1 = 5 · exp(-q/4).
  -- Now use that exp(-q/4) decays much faster than exp(-n/32) when q ≥ n/8 - 1.
  -- We'd need 5 · exp(-q/4) ≤ exp(-n/32). For q ≥ n/8 - 1: -q/4 ≤ -(n/8 - 1)/4 = -n/32 + 1/4.
  -- So 5 · exp(-q/4) ≤ 5 · exp(-n/32 + 1/4) = 5 · exp(1/4) · exp(-n/32).
  -- 5 · exp(1/4) ≈ 6.42.
  -- We need to absorb this 6.42 factor.
  -- This requires q · 1/4 to be larger than n/32 + log(6.42) ≈ n/32 + 1.86.
  -- q · 1/4 ≥ n/32 + 1.86 ↔ q ≥ n/8 + 7.44. But q ≤ n/8! Contradiction.
  -- So this approach fails with constant 1/4.

  -- We need a tighter constant. Use base bound (5/3)^3 · (4/5)^8 ≤ exp(-c) with c > 1/4.
  -- We proved (5/3)^3 · (4/5)^8 ≤ exp(-1/4) (where actual ≈ exp(-0.2528)).
  -- We want c = 1/4 + ε for some ε > 0, with the slack working out.

  -- Plan: prove (5/3)^3 · (4/5)^8 ≤ exp(-2515/10000) (i.e., c = 0.2515).
  -- Then 5 · exp(-q · 2515/10000) ≤ exp(-n/32) iff
  -- log 5 - q · 2515/10000 ≤ -n/32 iff q · 2515/10000 ≥ n/32 + log 5.
  -- q ≥ n/8 - 1, so q · 2515/10000 ≥ (n/8 - 1) · 2515/10000 = n · 2515/80000 - 2515/10000.
  -- Want: n · 2515/80000 - 2515/10000 ≥ n/32 + log 5.
  -- n · (2515/80000 - 1/32) ≥ log 5 + 2515/10000.
  -- 2515/80000 - 2500/80000 = 15/80000 = 3/16000.
  -- n · 3/16000 ≥ log 5 + 2515/10000.
  -- log 5 ≤ 2 (loose), so log 5 + 2515/10000 ≤ 2.2515.
  -- n ≥ 2.2515 · 16000/3 ≈ 12008. For n ≥ 10^12, ✓.

  -- This works. Let me implement it. (Need to prove (5/3)^3 · (4/5)^8 ≤ exp(-2515/10000) and log 5 ≤ 2.)
  -- Step 3a: (5/3)^{3q+3} · (4/5)^n ≤ (5/3)^3 · ((5/3)^3 · (4/5)^8)^q.
  have h_step3a : (5/3:ℝ)^(3 * q + 3) * (4/5:ℝ)^n
                ≤ (5/3:ℝ)^3 * ((5/3:ℝ)^3 * (4/5:ℝ)^8)^q := by
    -- (5/3)^{3q+3} = (5/3)^3 · (5/3)^{3q}.
    have hk_split : (5/3:ℝ)^(3*q+3) = (5/3:ℝ)^3 * (5/3:ℝ)^(3*q) := by
      rw [← pow_add]; congr 1; ring
    rw [hk_split]
    -- (4/5)^n = (4/5)^{8q} · (4/5)^{n - 8q}, and (4/5)^{n - 8q} ≤ 1.
    have h_n_split : (4/5:ℝ)^n = (4/5:ℝ)^(8*q) * (4/5:ℝ)^(n - 8*q) := by
      rw [← pow_add]; congr 1; omega
    rw [h_n_split]
    -- Goal: (5/3)^3 · (5/3)^{3q} · ((4/5)^{8q} · (4/5)^{n - 8q})
    --       ≤ (5/3)^3 · ((5/3)^3 · (4/5)^8)^q
    have h_45_le1 : (4/5:ℝ)^(n - 8*q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have h_45_pos : (0:ℝ) ≤ (4/5:ℝ)^(n - 8*q) := pow_nonneg (by norm_num) _
    have h_53q_nn : (0:ℝ) ≤ (5/3:ℝ)^(3*q) := pow_nonneg (by norm_num) _
    have h_45_8q_nn : (0:ℝ) ≤ (4/5:ℝ)^(8*q) := pow_nonneg (by norm_num) _
    have h_53cube_nn : (0:ℝ) ≤ (5/3:ℝ)^3 := pow_nonneg (by norm_num) _
    -- (5/3)^3 · (5/3)^{3q} · (4/5)^{8q} · (4/5)^{n - 8q} ≤ (5/3)^3 · (5/3)^{3q} · (4/5)^{8q} · 1
    -- = (5/3)^3 · ((5/3)^{3q} · (4/5)^{8q})
    -- = (5/3)^3 · ((5/3)^3 · (4/5)^8)^q
    have hrhs_eq : ((5/3:ℝ)^3 * (4/5:ℝ)^8)^q = (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) := by
      rw [mul_pow]
      have e1 : ((5/3:ℝ)^3)^q = (5/3:ℝ)^(3*q) := by rw [← pow_mul]
      have e2 : ((4/5:ℝ)^8)^q = (4/5:ℝ)^(8*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (5/3:ℝ)^3 * (5/3:ℝ)^(3*q) * ((4/5:ℝ)^(8*q) * (4/5:ℝ)^(n - 8*q))
              = (5/3:ℝ)^3 * (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) * (4/5:ℝ)^(n - 8*q) := by ring
    rw [hbase]
    have hbase2 : (5/3:ℝ)^3 * ((5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q))
                = (5/3:ℝ)^3 * (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (5/3:ℝ)^3 * (5/3:ℝ)^(3*q) * (4/5:ℝ)^(8*q) := by
      apply mul_nonneg
      apply mul_nonneg h_53cube_nn h_53q_nn
      exact h_45_8q_nn
    -- Goal: A · (4/5)^{n - 8q} ≤ A · 1 = A, where A ≥ 0 and (4/5)^{n - 8q} ≤ 1.
    have := mul_le_mul_of_nonneg_left h_45_le1 hcoef_nn
    linarith
  -- Step 3b: ((5/3)^3 · (4/5)^8)^q ≤ exp(-q · 251/1000).
  have h_step3b : ((5/3:ℝ)^3 * (4/5:ℝ)^8)^q ≤ Real.exp (-((q:ℝ) * 251/1000)) := by
    have h_base : (5/3:ℝ)^3 * (4/5:ℝ)^8 ≤ Real.exp (-(251/1000)) :=
      CentralBinomialLowerTailProof.five_thirds_cubed_four_fifths_eighth_le_exp_neg_251_1000
    have h_base_nn : (0:ℝ) ≤ (5/3:ℝ)^3 * (4/5:ℝ)^8 := by positivity
    have h_pow := pow_le_pow_left₀ h_base_nn h_base q
    rw [← Real.exp_nat_mul] at h_pow
    rw [show ((q:ℝ) * -(251/1000)) = -((q:ℝ) * 251/1000) from by ring] at h_pow
    exact h_pow
  -- Step 3c: (5/3)^3 ≤ 5.
  have h_53_cube_le_5 : (5/3:ℝ)^3 ≤ 5 := by norm_num
  -- Combine 3a, 3b, 3c: LHS ≤ 5 · exp(-q · 251/1000).
  have h_combined : (5/3:ℝ)^(3 * q + 3) * (4/5:ℝ)^n
                ≤ 5 * Real.exp (-((q:ℝ) * 251/1000)) := by
    calc (5/3:ℝ)^(3 * q + 3) * (4/5:ℝ)^n
        ≤ (5/3:ℝ)^3 * ((5/3:ℝ)^3 * (4/5:ℝ)^8)^q := h_step3a
      _ ≤ 5 * ((5/3:ℝ)^3 * (4/5:ℝ)^8)^q := by
          apply mul_le_mul_of_nonneg_right h_53_cube_le_5
          exact pow_nonneg (by positivity) _
      _ ≤ 5 * Real.exp (-((q:ℝ) * 251/1000)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 5)
  -- Step 4: 5 · exp(-q · 251/1000) ≤ exp(-n/32).
  -- ↔ log 5 - q · 251/1000 ≤ -n/32.
  -- ↔ q · 251/1000 ≥ n/32 + log 5.
  -- log 5 ≤ 4 (very crude, from log x ≤ x - 1).
  -- q ≥ n/8 - 1, so q · 251/1000 ≥ (n/8 - 1) · 251/1000.
  -- (n/8 - 1) · 251/1000 ≥ n/32 + 4 ↔ n · (251/8000 - 1/32) ≥ 251/1000 + 4 ↔ n · (1/8000) ≥ 4.251 ↔ n ≥ 34008.
  -- For n ≥ 10^12, ✓.
  have h_log5_le : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
    linarith
  have h_5_le_exp : (5 : ℝ) ≤ Real.exp 4 := by
    have h := Real.exp_le_exp.mpr h_log5_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 5)] at h
  -- Now: 5 · exp(-q · 251/1000) ≤ exp 4 · exp(-q · 251/1000) = exp(4 - q · 251/1000).
  -- Need 4 - q · 251/1000 ≤ -n/32, i.e., q · 251/1000 ≥ n/32 + 4.
  have h_step4 : 5 * Real.exp (-((q:ℝ) * 251/1000)) ≤ Real.exp (-((n:ℝ)/32)) := by
    have h_exp_combined : Real.exp 4 * Real.exp (-((q:ℝ) * 251/1000))
                        = Real.exp (4 - (q:ℝ) * 251/1000) := by
      rw [← Real.exp_add]
      ring_nf
    have h_lhs_le : 5 * Real.exp (-((q:ℝ) * 251/1000))
                  ≤ Real.exp 4 * Real.exp (-((q:ℝ) * 251/1000)) := by
      apply mul_le_mul_of_nonneg_right h_5_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    -- Need: exp(4 - q · 251/1000) ≤ exp(-n/32).
    apply Real.exp_le_exp.mpr
    -- Need: 4 - q · 251/1000 ≤ -n/32.
    -- ↔ q · 251/1000 ≥ n/32 + 4.
    -- q ≥ n/8 - 1, so q · 251/1000 ≥ (n/8 - 1) · 251/1000 = n · 251/8000 - 251/1000.
    -- We need n · 251/8000 - 251/1000 ≥ n/32 + 4.
    -- n · (251/8000 - 1/32) ≥ 4 + 251/1000.
    -- 251/8000 - 250/8000 = 1/8000.
    -- n/8000 ≥ 4 + 251/1000 = 4251/1000 = 4.251.
    -- n ≥ 8000 · 4.251 = 34008.
    -- For n ≥ 10^12, n ≥ 34008. ✓
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    have h_q_lb : (q : ℝ) * 251/1000 ≥ ((n : ℝ)/8 - 1) * 251/1000 := by
      have h251_pos : (0:ℝ) ≤ 251/1000 := by norm_num
      nlinarith [hq_real_ge, h251_pos]
    nlinarith [h_q_lb, h_n_large]
  -- Combine all
  calc (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 8) - 1),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (3 * q + 3),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := h_step_bound
    _ ≤ (5/3:ℝ)^(3 * q + 3) * (4/5:ℝ)^n := h_chernoff
    _ ≤ 5 * Real.exp (-((q:ℝ) * 251/1000)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/32)) := h_step4
