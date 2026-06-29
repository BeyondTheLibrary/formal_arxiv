import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide

/-!
# CentralBinomialUpperTailWide — Proof attempt 1

Hoeffding upper-tail of Bin(n, 1/2) on r ∈ [n/16+1, n/4] ≤ exp(-n/128).

Strategy: same Chernoff bound as `CentralBinomialLowerTailWide`, but
applied after a binomial-symmetry reindex k ↦ n - k.
For r ∈ Icc(n/16+1, n/4), set k = r + n/2 ∈ [9n/16 + 1, 3n/4].
By binomial symmetry, binPMF n (1/2) k = binPMF n (1/2) (n-k).
As k ranges over [9n/16+1, 3n/4], n-k ranges over [n/4, 7n/16-1].
This is a sum bounded above by ∑_{k' < 7q + 7} binPMF n (1/2) k', q = n/16.
Apply `chernoff_optimal_bound`.
-/

set_option maxHeartbeats 8000000

open Workspace.Types.AlternatingSumExpression

namespace CentralBinomialUpperTailWideProof

-- Binomial symmetry on the underlying binPMF: for k ≤ m, binPMF m (1/2) k = binPMF m (1/2) (m - k).
lemma binPMF_half_symm (m k : ℕ) (hk : k ≤ m) :
    binPMF m (1/2 : ℝ) k = binPMF m (1/2 : ℝ) (m - k) := by
  rw [CentralBinomialLowerTailWideProof.binPMF_half_eq m k hk,
      CentralBinomialLowerTailWideProof.binPMF_half_eq m (m - k) (Nat.sub_le m k)]
  congr 1
  exact_mod_cast (Nat.choose_symm hk).symm

-- Binomial symmetry for binPMFInt: for 0 ≤ k ≤ n, binPMFInt n (1/2) k = binPMFInt n (1/2) (n - k).
lemma binPMFInt_half_symm (n : ℕ) (k : ℤ) (hk_lo : 0 ≤ k) (hk_hi : k ≤ (n : ℤ)) :
    binPMFInt n (1/2 : ℝ) k = binPMFInt n (1/2 : ℝ) ((n : ℤ) - k) := by
  unfold binPMFInt
  rw [if_pos ⟨hk_lo, hk_hi⟩]
  have h_nk_lo : (0 : ℤ) ≤ (n : ℤ) - k := by linarith
  have h_nk_hi : (n : ℤ) - k ≤ (n : ℤ) := by linarith
  rw [if_pos ⟨h_nk_lo, h_nk_hi⟩]
  -- Now need: binPMF n (1/2) k.toNat = binPMF n (1/2) ((n : ℤ) - k).toNat.
  -- Set kn := k.toNat. Then kn ≤ n and ((n : ℤ) - k).toNat = n - kn.
  have h_kn_le : k.toNat ≤ n := Int.toNat_le.mpr hk_hi
  have h_eq : ((n : ℤ) - k).toNat = n - k.toNat := by
    have hk_int : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk_lo
    have h1 : ((n : ℤ) - k) = ((n - k.toNat : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h_kn_le, hk_int]
      rfl
    rw [h1]
    exact Int.toNat_natCast _
  rw [h_eq]
  exact binPMF_half_symm n k.toNat h_kn_le

end CentralBinomialUpperTailWideProof

theorem CentralBinomialUpperTailWide :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n →
      ∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2)
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set q : ℕ := n / 16 with hq_def
  have h16q_le : 16 * q ≤ n := by rw [hq_def]; exact Nat.mul_div_le n 16
  have hq_real_ge : (n : ℝ)/16 - 1 ≤ (q : ℝ) := by
    rw [hq_def]
    exact CentralBinomialLowerTailWideProof.cast_div_16_ge n
  have hq_pos : 1 ≤ q := by
    rw [hq_def]
    have : 1600 ≤ n := by linarith
    omega
  have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n

  -- Step 1: bound the upper-tail sum by a Finset.range sum over k via symmetry.
  -- We'll use the substitution k = n - (r + n/2), valid since r + n/2 ∈ [0, n].
  -- Each term: binPMFInt n (1/2) (r + n/2) = binPMFInt n (1/2) (n - (r + n/2)) (= binPMF n (1/2) k).
  -- As r ∈ Icc(n/16+1, n/4), k = n - r - n/2 ∈ Icc(n - n/4 - n/2, n - n/16 - 1 - n/2)
  --                         = Icc(n/2 - n/4, n/2 - n/16 - 1).
  -- For our purposes, we just need k ≤ 7q + 6 (matching the lower-tail bound).
  -- Specifically: n - r - n/2 ≤ n - (n/16 + 1) - n/2 = n/2 - n/16 - 1 ≤ 7q + 6 (similarly).

  have h_step_bound :
      (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (7 * q + 8),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := by
    -- shift map: r ↦ (n - (r + n/2)).toNat
    let shift : ℤ → ℕ := fun r => ((n : ℤ) - (r + (n : ℤ) / 2)).toNat
    have h_eq : (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
                  Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
                = (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
                    Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      obtain ⟨hr_lo, hr_hi⟩ := hr
      -- r + n/2 ∈ [0, n].
      have h_n4_le_n : (n : ℤ)/4 ≤ (n : ℤ)/2 := by omega
      have h_n2_le_n : (n : ℤ)/2 ≤ (n : ℤ) := by omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ (n : ℤ) := by omega
      -- Apply binPMFInt_half_symm to get binPMFInt n (1/2) (r + n/2) = binPMFInt n (1/2) (n - (r + n/2)).
      rw [CentralBinomialUpperTailWideProof.binPMFInt_half_symm n (r + (n : ℤ)/2) hr_plus_lo hr_plus_hi]
      -- Now want: binPMFInt n (1/2) (n - (r + n/2)) = binPMF n (1/2) (shift r).
      have h_shift_lo : (0 : ℤ) ≤ (n : ℤ) - (r + (n : ℤ) / 2) := by linarith
      have h_shift_hi : (n : ℤ) - (r + (n : ℤ) / 2) ≤ (n : ℤ) := by linarith
      unfold Workspace.Types.AlternatingSumExpression.binPMFInt
      rw [if_pos ⟨h_shift_lo, h_shift_hi⟩]
    rw [h_eq]
    -- Now bound the sum by the range-sum.
    have h_shift_inj : Set.InjOn shift (Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4)) := by
      intro r1 hr1 r2 hr2 h_eq_shift
      rw [Finset.mem_coe, Finset.mem_Icc] at hr1 hr2
      simp only [shift] at h_eq_shift
      have h_n4_le_n : (n : ℤ)/4 ≤ (n : ℤ)/2 := by omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have hr1_plus_lo : (0 : ℤ) ≤ r1 + (n : ℤ) / 2 := by linarith [hr1.1]
      have hr2_plus_lo : (0 : ℤ) ≤ r2 + (n : ℤ) / 2 := by linarith [hr2.1]
      have hr1_plus_hi : r1 + (n : ℤ) / 2 ≤ (n : ℤ) := by omega
      have hr2_plus_hi : r2 + (n : ℤ) / 2 ≤ (n : ℤ) := by omega
      have h_shift1_nn : (0 : ℤ) ≤ (n : ℤ) - (r1 + (n : ℤ) / 2) := by linarith
      have h_shift2_nn : (0 : ℤ) ≤ (n : ℤ) - (r2 + (n : ℤ) / 2) := by linarith
      have h1_eq : ((n : ℤ) - (r1 + (n : ℤ) / 2) : ℤ) = ((n : ℤ) - (r2 + (n : ℤ) / 2) : ℤ) := by
        have hh := congrArg (fun (m : ℕ) => (m : ℤ)) h_eq_shift
        simp only at hh
        rw [Int.toNat_of_nonneg h_shift1_nn, Int.toNat_of_nonneg h_shift2_nn] at hh
        exact hh
      linarith
    have h_image_sum :
        (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) (shift r))
        = (∑ k ∈ (Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4)).image shift,
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
      have hr_lo : (n : ℤ)/16 + 1 ≤ r := hr_in.1
      have hr_hi : r ≤ (n : ℤ)/4 := hr_in.2
      have h_n4_le_n2 : (n : ℤ)/4 ≤ (n : ℤ)/2 := by omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 2 := by linarith
      have hr_plus_hi : r + (n : ℤ) / 2 ≤ (n : ℤ) := by omega
      have h_shift_nn : (0 : ℤ) ≤ (n : ℤ) - (r + (n : ℤ) / 2) := by linarith
      -- Bound: n - (r + n/2) ≤ n - (n/16 + 1 + n/2) = n - n/2 - n/16 - 1.
      -- For n = 16q + s with s ∈ [0, 15]:
      --   n/2 = 8q + s/2 (Nat), n/16 = q.
      --   n - n/2 = 8q + (s - s/2) = 8q + s_upper_half. n - n/2 ≤ 8q + 8 ... no wait,
      --   n is the original Nat, but we treat it as ℤ. For ℤ-valued (n : ℤ)/2 with n nat,
      --   it equals (n / 2 : ℕ) cast to ℤ. So n - n/2 = n - (n/2 cast). n/2 (Int from Nat) = n/2 (Nat).
      --   And n - n/2 (Nat) = (n+1)/2 ≤ 8q + 8.
      -- We need: (n - r - n/2) ≤ 7q + 6. Since r ≥ n/16 + 1 = q + 1, we get
      -- n - r - n/2 ≤ n - q - 1 - n/2 = (n - n/2) - q - 1 ≤ 8q + 8 - q - 1 = 7q + 7. Hmm, off by 1.
      -- Tighter: n - n/2 ≤ 8q + 7? Let's see. n - n/2 = n - (n/2 floor).
      --   n = 16q + s, s ∈ [0, 15]. n/2 = (16q + s)/2 = 8q + s/2 (floor).
      --   So n - n/2 = 16q + s - 8q - s/2 = 8q + s - s/2 = 8q + ⌈s/2⌉.
      --   ⌈s/2⌉ for s ∈ [0,15]: max is ⌈15/2⌉ = 8. So n - n/2 ≤ 8q + 8.
      -- Then n - r - n/2 ≤ 8q + 8 - q - 1 = 7q + 7. So we need range (7q + 8). Adjust.
      -- Actually let's check: when r = n/16 + 1 = q + 1, k = n - r - n/2 = (n - n/2) - q - 1.
      --   For n = 16q + 15: n - n/2 = 8q + 8, k = 8q + 8 - q - 1 = 7q + 7. So k = 7q + 7 is achievable.
      -- So we should use `Finset.range (7q + 8)` to be safe.
      -- BUT: for n ≥ 10^12, n is much larger than 16q + 15, so let's just check this case-by-case.
      -- Wait actually we set q := n/16, so 16q ≤ n < 16(q+1) = 16q + 16. So n ∈ [16q, 16q + 15].
      -- So for any n, k can be up to 7q + 7 (when r is at its lower bound). Hmm.
      -- Then we need range (7q + 8). Let's check: chernoff_optimal_bound is for arbitrary K, so 7q+8 works.
      -- Wait but the lower-tail proof uses range (7q+7). Let me re-examine.
      --
      -- Original lower-tail: k_max = -(n/16) - 1 + n/2. For n = 16q + s, n/16 = q (Int from Nat), n/2 = 8q + s/2.
      --   k_max = -q - 1 + 8q + s/2 = 7q - 1 + s/2 (Nat).
      --   For s = 15: s/2 = 7. k_max = 7q + 6. So range (7q + 7) works.
      -- For upper-tail: k_max = n - (n/16 + 1) - n/2 = n - n/2 - n/16 - 1
      --                = (n - n/2) - q - 1.
      -- (n - n/2) for n = 16q + s: n - n/2 (Int) = (16q + s) - (8q + s/2) = 8q + s - s/2.
      --   s - s/2 = ⌈s/2⌉. For s = 15: 15 - 7 = 8. So n - n/2 = 8q + 8. k_max = 7q + 7.
      -- Hmm, off by 1. To use chernoff_optimal_bound at K = 7q + 8.
      -- Combination: bound (9/7)^(7q+8) · (8/9)^n vs. exp(-n/128).
      -- (9/7)^(7q+8) = (9/7)^(7q+7) · (9/7). So we just have an extra (9/7) factor ≈ 1.29 vs. (9/7)^7 ≈ 5.8.
      -- Combined factor ≤ 7.5 ≤ exp(2.02), still fine vs. our slack.

      have hbound : (n : ℤ) - (r + (n : ℤ) / 2) ≤ 7 * (q : ℤ) + 7 := by
        have hn_def : n = 16 * q + n % 16 := by
          rw [hq_def]; omega
        have hmod : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
        have hq_int : (q : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le q
        omega
      have h_kint_bound : (k : ℤ) ≤ 7 * (q : ℤ) + 7 := by
        rw [← hr_eq]
        have h_toNat_eq : (((n : ℤ) - (r + (n : ℤ) / 2)).toNat : ℤ) = (n : ℤ) - (r + (n : ℤ) / 2) :=
          Int.toNat_of_nonneg h_shift_nn
        rw [h_toNat_eq]
        exact hbound
      have hk_le : k ≤ 7 * q + 7 := by
        have hh : (k : ℤ) ≤ ((7 * q + 7 : ℕ) : ℤ) := by push_cast; linarith [h_kint_bound]
        exact_mod_cast hh
      -- Goal: k < 7 * q + 8
      omega
    · intros k _ _
      exact CentralBinomialLowerTailWideProof.binPMF_nonneg n k (1/2) (by norm_num) (by norm_num)

  -- Step 2: Apply Chernoff (over range (7q + 8)).
  have h_chernoff : (∑ k ∈ Finset.range (7 * q + 8),
                      Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k)
                    ≤ (9/7:ℝ)^(7 * q + 8) * (8/9:ℝ)^n :=
    CentralBinomialLowerTailWideProof.chernoff_optimal_bound n (7 * q + 8)

  -- Step 3a: (9/7)^{7q+8} · (8/9)^n ≤ (9/7)^8 · ((9/7)^7 · (8/9)^16)^q.
  have h_step3a : (9/7:ℝ)^(7 * q + 8) * (8/9:ℝ)^n
                ≤ (9/7:ℝ)^8 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := by
    have hk_split : (9/7:ℝ)^(7*q+8) = (9/7:ℝ)^8 * (9/7:ℝ)^(7*q) := by
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
    have h_97_eight_nn : (0:ℝ) ≤ (9/7:ℝ)^8 := pow_nonneg (by norm_num) _
    have hrhs_eq : ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q = (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by
      rw [mul_pow]
      have e1 : ((9/7:ℝ)^7)^q = (9/7:ℝ)^(7*q) := by rw [← pow_mul]
      have e2 : ((8/9:ℝ)^16)^q = (8/9:ℝ)^(16*q) := by rw [← pow_mul]
      rw [e1, e2]
    rw [hrhs_eq]
    have hbase : (9/7:ℝ)^8 * (9/7:ℝ)^(7*q) * ((8/9:ℝ)^(16*q) * (8/9:ℝ)^(n - 16*q))
              = (9/7:ℝ)^8 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) * (8/9:ℝ)^(n - 16*q) := by ring
    rw [hbase]
    have hbase2 : (9/7:ℝ)^8 * ((9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q))
                = (9/7:ℝ)^8 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by ring
    rw [hbase2]
    have hcoef_nn : (0:ℝ) ≤ (9/7:ℝ)^8 * (9/7:ℝ)^(7*q) * (8/9:ℝ)^(16*q) := by
      apply mul_nonneg
      apply mul_nonneg h_97_eight_nn h_97q_nn
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

  -- Step 3c: (9/7)^8 ≤ 8.
  have h_97_eight_le_8 : (9/7:ℝ)^8 ≤ 8 := by norm_num

  -- Combine: LHS ≤ 8 · exp(-q · 1251/10000).
  have h_combined : (9/7:ℝ)^(7 * q + 8) * (8/9:ℝ)^n
                ≤ 8 * Real.exp (-((q:ℝ) * 1251/10000)) := by
    calc (9/7:ℝ)^(7 * q + 8) * (8/9:ℝ)^n
        ≤ (9/7:ℝ)^8 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := h_step3a
      _ ≤ 8 * ((9/7:ℝ)^7 * (8/9:ℝ)^16)^q := by
          apply mul_le_mul_of_nonneg_right h_97_eight_le_8
          exact pow_nonneg (by positivity) _
      _ ≤ 8 * Real.exp (-((q:ℝ) * 1251/10000)) := by
          apply mul_le_mul_of_nonneg_left h_step3b (by norm_num : (0:ℝ) ≤ 8)

  -- Step 4: 8 · exp(-q · 1251/10000) ≤ exp(-n/128).
  have h_log8_le : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)
    linarith
  have h_8_le_exp : (8 : ℝ) ≤ Real.exp 7 := by
    have h := Real.exp_le_exp.mpr h_log8_le
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 8)] at h
  have h_step4 : 8 * Real.exp (-((q:ℝ) * 1251/10000)) ≤ Real.exp (-((n:ℝ)/128)) := by
    have h_exp_combined : Real.exp 7 * Real.exp (-((q:ℝ) * 1251/10000))
                        = Real.exp (7 - (q:ℝ) * 1251/10000) := by
      rw [← Real.exp_add]
      ring_nf
    have h_lhs_le : 8 * Real.exp (-((q:ℝ) * 1251/10000))
                  ≤ Real.exp 7 * Real.exp (-((q:ℝ) * 1251/10000)) := by
      apply mul_le_mul_of_nonneg_right h_8_le_exp
      exact (Real.exp_pos _).le
    rw [h_exp_combined] at h_lhs_le
    refine le_trans h_lhs_le ?_
    apply Real.exp_le_exp.mpr
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    have h_q_lb : (q : ℝ) * 1251/10000 ≥ ((n : ℝ)/16 - 1) * 1251/10000 := by
      have h1251_pos : (0:ℝ) ≤ 1251/10000 := by norm_num
      nlinarith [hq_real_ge, h1251_pos]
    nlinarith [h_q_lb, h_n_large]

  -- Combine all
  calc (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) (r + (n : ℤ) / 2))
      ≤ (∑ k ∈ Finset.range (7 * q + 8),
          Workspace.Types.AlternatingSumExpression.binPMF n (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(7 * q + 8) * (8/9:ℝ)^n := h_chernoff
    _ ≤ 8 * Real.exp (-((q:ℝ) * 1251/10000)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4

set_option maxHeartbeats 32000000 in
theorem CentralBinomialUpperTailWideHalf :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4)
      ≤ Real.exp (-((n : ℝ) / 128)) := by
  intro n hn hmod8
  have hn_pos : 0 < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set m : ℕ := n / 2 with hm_def
  set q : ℕ := n / 32 with hq_def
  have h16q_le_m : 16 * q ≤ m := by rw [hq_def, hm_def]; omega
  have hq_real_ge : (n : ℝ)/32 - 1 ≤ (q : ℝ) := by
    have h : 32 * (n / 32) + 32 > n := by
      have := Nat.div_add_mod n 32
      have hmod : n % 32 < 32 := Nat.mod_lt _ (by norm_num)
      omega
    have h_real : 32 * ((n / 32 : ℕ) : ℝ) + 32 > (n : ℝ) := by exact_mod_cast h
    rw [hq_def]; linarith
  have hm_int_nn : (0 : ℤ) ≤ ((m : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le m
  -- Step 1: bound the upper-tail sum by ∑ k ∈ range (6q+7), binPMF (n/2) (1/2) k via symmetry.
  have h_step_bound :
      (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
      ≤ (∑ k ∈ Finset.range (6 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k) := by
    -- shift map: r ↦ ((n/2 : ℤ) - (r + n/4)).toNat
    let shift : ℤ → ℕ := fun r => (((m : ℕ) : ℤ) - (r + (n : ℤ) / 4)).toNat
    have h_eq : (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
                  Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
                = (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
                    Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) (shift r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_Icc] at hr
      obtain ⟨hr_lo, hr_hi⟩ := hr
      have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h_mcast : ((m : ℕ) : ℤ) = (n : ℤ) / 2 := by rw [hm_def]; push_cast [Nat.cast_div]; omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have h_n4_le_m : (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have h_2n4_le_m : (n : ℤ)/4 + (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 4 := by linarith
      have hr_plus_hi : r + (n : ℤ) / 4 ≤ ((m : ℕ) : ℤ) := by linarith
      -- Apply binPMFInt_half_symm to get binPMFInt (n/2) (1/2) (r+n/4) = binPMFInt (n/2) (1/2) (m - (r+n/4)).
      rw [CentralBinomialUpperTailWideProof.binPMFInt_half_symm (n / 2) (r + (n : ℤ)/4) hr_plus_lo hr_plus_hi]
      have h_shift_lo : (0 : ℤ) ≤ ((m : ℕ) : ℤ) - (r + (n : ℤ) / 4) := by linarith
      have h_shift_hi : ((m : ℕ) : ℤ) - (r + (n : ℤ) / 4) ≤ ((m : ℕ) : ℤ) := by linarith
      unfold Workspace.Types.AlternatingSumExpression.binPMFInt
      rw [if_pos ⟨h_shift_lo, h_shift_hi⟩]
    rw [h_eq]
    have h_shift_inj : Set.InjOn shift (Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4)) := by
      intro r1 hr1 r2 hr2 h_eq_shift
      rw [Finset.mem_coe, Finset.mem_Icc] at hr1 hr2
      simp only [shift] at h_eq_shift
      have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h_mcast : ((m : ℕ) : ℤ) = (n : ℤ) / 2 := by rw [hm_def]; push_cast [Nat.cast_div]; omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have h_n4_le_m : (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have h_2n4_le_m : (n : ℤ)/4 + (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have hr1_plus_lo : (0 : ℤ) ≤ r1 + (n : ℤ) / 4 := by linarith [hr1.1]
      have hr2_plus_lo : (0 : ℤ) ≤ r2 + (n : ℤ) / 4 := by linarith [hr2.1]
      have hr1_plus_hi : r1 + (n : ℤ) / 4 ≤ ((m : ℕ) : ℤ) := by linarith [hr1.2]
      have hr2_plus_hi : r2 + (n : ℤ) / 4 ≤ ((m : ℕ) : ℤ) := by linarith [hr2.2]
      have h_shift1_nn : (0 : ℤ) ≤ ((m : ℕ) : ℤ) - (r1 + (n : ℤ) / 4) := by linarith
      have h_shift2_nn : (0 : ℤ) ≤ ((m : ℕ) : ℤ) - (r2 + (n : ℤ) / 4) := by linarith
      have h1_eq : (((m : ℕ) : ℤ) - (r1 + (n : ℤ) / 4) : ℤ) = (((m : ℕ) : ℤ) - (r2 + (n : ℤ) / 4) : ℤ) := by
        have hh := congrArg (fun (z : ℕ) => (z : ℤ)) h_eq_shift
        simp only at hh
        rw [Int.toNat_of_nonneg h_shift1_nn, Int.toNat_of_nonneg h_shift2_nn] at hh
        exact hh
      linarith
    have h_image_sum :
        (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) (shift r))
        = (∑ k ∈ (Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4)).image shift,
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
      have hr_lo : (n : ℤ)/16 + 1 ≤ r := hr_in.1
      have hr_hi : r ≤ (n : ℤ)/4 := hr_in.2
      have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h_mcast : ((m : ℕ) : ℤ) = (n : ℤ) / 2 := by rw [hm_def]; push_cast [Nat.cast_div]; omega
      have h_n16_nn : (0 : ℤ) ≤ (n : ℤ)/16 := by omega
      have h_n4_le_m : (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have h_2n4_le_m : (n : ℤ)/4 + (n : ℤ)/4 ≤ ((m : ℕ) : ℤ) := by rw [h_mcast]; omega
      have hr_plus_lo : (0 : ℤ) ≤ r + (n : ℤ) / 4 := by linarith
      have hr_plus_hi : r + (n : ℤ) / 4 ≤ ((m : ℕ) : ℤ) := by linarith
      have h_shift_nn : (0 : ℤ) ≤ ((m : ℕ) : ℤ) - (r + (n : ℤ) / 4) := by linarith
      -- Bound: m - (r + n/4) ≤ m - (n/16 + 1 + n/4) ≤ 6q + 6.
      have hbound : ((m : ℕ) : ℤ) - (r + (n : ℤ) / 4) ≤ 6 * (q : ℤ) + 6 := by
        have hn_def : n = 32 * q + n % 32 := by rw [hq_def]; omega
        have hmod : n % 32 < 32 := Nat.mod_lt _ (by norm_num)
        have hq_int : (q : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le q
        have hmod8 : n % 8 = 1 := hmod8
        rw [h_mcast]
        omega
      have h_kint_bound : (k : ℤ) ≤ 6 * (q : ℤ) + 6 := by
        rw [← hr_eq]
        have h_toNat_eq : ((((m : ℕ) : ℤ) - (r + (n : ℤ) / 4)).toNat : ℤ) = ((m : ℕ) : ℤ) - (r + (n : ℤ) / 4) :=
          Int.toNat_of_nonneg h_shift_nn
        rw [h_toNat_eq]
        exact hbound
      have hk_le : k ≤ 6 * q + 6 := by
        have hh : (k : ℤ) ≤ ((6 * q + 6 : ℕ) : ℤ) := by push_cast; linarith [h_kint_bound]
        exact_mod_cast hh
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
    have h16q_le_n2 : 16 * q ≤ n / 2 := by rw [← hm_def]; exact h16q_le_m
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
    have h_n_large : (n : ℝ) ≥ 10^12 := hn_real_ge
    have h_q_lb : (q : ℝ) * 3/10 ≥ ((n : ℝ)/32 - 1) * 3/10 := by
      have h3_pos : (0:ℝ) ≤ 3/10 := by norm_num
      nlinarith [hq_real_ge, h3_pos]
    nlinarith [h_q_lb, h_n_large]
  -- Combine all
  calc (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        Workspace.Types.AlternatingSumExpression.binPMFInt (n / 2) (1/2) (r + (n : ℤ) / 4))
      ≤ (∑ k ∈ Finset.range (6 * q + 7),
          Workspace.Types.AlternatingSumExpression.binPMF (n / 2) (1/2) k) := h_step_bound
    _ ≤ (9/7:ℝ)^(6 * q + 7) * (8/9:ℝ)^(n / 2) := h_chernoff
    _ ≤ 6 * Real.exp (-((q:ℝ) * 3/10)) := h_combined
    _ ≤ Real.exp (-((n:ℝ)/128)) := h_step4
