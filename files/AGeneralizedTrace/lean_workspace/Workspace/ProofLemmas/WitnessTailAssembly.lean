import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LengthsOnlyExists
import Workspace.ProofLemmas.WitnessOffsetTail
import Workspace.ProofLemmas.WitnessOffsetTailFull
import Workspace.ProofLemmas.WitnessBitProb
import Workspace.ProofLemmas.WitnessPrefixSuffixTailTonelli
import Workspace.ProofLemmas.WitnessPrefixSuffixTailSupport

/-!
# WitnessTailAssembly — the r-split and final numeric bound (Parts C & D)

Assembles the proved component bounds into the master inequality

  `∑_b w b · g(b) ≤ (1/4)·exp(-√n/2)`,

where `w b = (cfd.toPMF b).toReal`, `g(b) = ∑'_r [bitPred b r]·offsetWeight(r).toReal`.

Strategy:
* convert the inner `r`-`tsum` to a finite sum over `Icc(-n/4, n/4)`;
* split `r` into `|r| ≤ n/8` (bit tail, via `WitnessBitProb.bitPred_prob_le`) and
  `|r| > n/8` (offset tail, via `WitnessOffsetTailFull`);
* combine `2√n·exp(-n/256) + 2·exp(-n/256) ≤ (1/4)exp(-√n/2)`.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess Workspace.Types.AlternatingSumExpression
open WitnessPrefixSuffixTailTonelli
open scoped Classical

namespace WitnessTailAssembly

variable {n : ℕ}

/-- `(offsetWeight n r).toReal ≥ 0`. -/
theorem ow_toReal_nonneg (n : ℕ) (r : ℤ) : 0 ≤ (offsetWeight n r).toReal :=
  ENNReal.toReal_nonneg

/-- `offsetWeight n r ≠ ⊤`. -/
theorem ow_ne_top (n : ℕ) (r : ℤ) : offsetWeight n r ≠ ⊤ := by
  unfold offsetWeight
  by_cases h : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)
  · rw [dif_pos h]
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · apply ENNReal.pow_ne_top; exact ENNReal.ofReal_ne_top
  · rw [dif_neg h]; exact ENNReal.zero_ne_top

/-- The total real offset mass over the support window equals `1`. -/
theorem offset_total_eq_one (hn8 : n % 8 = 1) :
    (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
        (offsetWeight n r).toReal) = 1 := by
  have htsum_top : (∑' r : ℤ, offsetWeight n r) ≠ ⊤ := by
    rw [LengthsOnlyExistsScratch.offsetWeight_tsum n]; exact ENNReal.one_ne_top
  have hkey : (∑' r : ℤ, (offsetWeight n r).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (ow_ne_top n), LengthsOnlyExistsScratch.offsetWeight_tsum n,
        ENNReal.toReal_one]
  -- the real tsum collapses to the finite sum over the support window
  have hsupp : (∑' r : ℤ, (offsetWeight n r).toReal)
      = ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
          (offsetWeight n r).toReal := by
    apply tsum_eq_sum
    intro r hr
    rw [Finset.mem_Icc] at hr
    push_neg at hr
    have hout : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r := by
      by_contra hc; push_neg at hc; exact absurd (hr hc.1) (not_lt.mpr hc.2)
    rw [WitnessPrefixSuffixTailSupport.offsetWeight_toReal_zero_of_out_of_range hn8 r hout]
  rw [hsupp] at hkey
  exact hkey

theorem offset_total_le_one (hn8 : n % 8 = 1) :
    (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
        (offsetWeight n r).toReal) ≤ 1 :=
  le_of_eq (offset_total_eq_one hn8)

/-- Reindex the offset-window sum (over `r ∈ Icc(-n/4, n/4)`) to a sum over
`k ∈ range(n/2 + 1)`, with `ow.toReal(r) = binPMF (n/2) (1/2) k` and the offset
condition `|r| > n/8` translating to `k < n/8 ∨ n/2 - n/8 < k`. -/
theorem offset_tail_le (hn8 : n % 8 = 1) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
        (if (r < -((n / 8 : ℕ) : ℤ) ∨ ((n / 8 : ℕ) : ℤ) < r)
         then (offsetWeight n r).toReal else 0))
      ≤ 2 * Real.exp (-((n : ℝ) / 256)) := by
  classical
  -- reindex r ↦ k = (r + n/4).toNat onto range (n/2 + 1)
  have hreidx :
      (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
          (if (r < -((n / 8 : ℕ) : ℤ) ∨ ((n / 8 : ℕ) : ℤ) < r)
           then (offsetWeight n r).toReal else 0))
        = ∑ k ∈ Finset.range (n / 2 + 1),
            (if (k < n / 8 ∨ n / 2 - n / 8 < k)
             then binPMF (n / 2) (1 / 2 : ℝ) k else 0) := by
    apply Finset.sum_nbij' (fun r => (r + ((n / 4 : ℕ) : ℤ)).toNat)
      (fun k => (k : ℤ) - ((n / 4 : ℕ) : ℤ))
    · intro r hr
      rw [Finset.mem_Icc] at hr
      rw [Finset.mem_range]
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro r hr
      rw [Finset.mem_Icc] at hr
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      omega
    · intro r hr
      rw [Finset.mem_Icc] at hr
      -- value: ow.toReal r = binPMF (n/2) (1/2) (r+n/4).toNat, and conditions match
      have hk_eq : ((r + ((n / 4 : ℕ) : ℤ)).toNat : ℤ) = r + ((n / 4 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg]; omega
      rw [WitnessOffsetTail.offsetWeight_toReal_eq_binPMFInt n r]
      have hbin : binPMFInt (n / 2) (1 / 2 : ℝ) (r + ((n / 4 : ℕ) : ℤ))
          = binPMF (n / 2) (1 / 2 : ℝ) (r + ((n / 4 : ℕ) : ℤ)).toNat := by
        unfold binPMFInt
        rw [if_pos ⟨by omega, by omega⟩]
      rw [hbin]
      -- the two if-conditions agree
      congr 1
      apply propext
      constructor
      · rintro (h | h)
        · left; omega
        · right; omega
      · rintro (h | h)
        · left; omega
        · right; omega
  rw [hreidx]
  -- split range (n/2+1) into low tail (k < n/8) and high tail (n/2-n/8 < k)
  refine le_trans (Finset.sum_le_sum (g := fun k =>
      (if k < n / 8 then binPMF (n / 2) (1 / 2 : ℝ) k else 0)
        + (if n / 2 - n / 8 < k then binPMF (n / 2) (1 / 2 : ℝ) k else 0)) ?_) ?_
  · intro k _
    simp only
    by_cases hlow : k < n / 8
    · have hhigh : ¬ (n / 2 - n / 8 < k) := by omega
      rw [if_pos (Or.inl hlow), if_pos hlow, if_neg hhigh, add_zero]
    · by_cases hhigh : n / 2 - n / 8 < k
      · rw [if_pos (Or.inr hhigh), if_neg hlow, if_pos hhigh, zero_add]
      · rw [if_neg (by push_neg; exact ⟨by omega, by omega⟩), if_neg hlow, if_neg hhigh, add_zero]
  · rw [Finset.sum_add_distrib]
    have hlow_eq : (∑ k ∈ Finset.range (n / 2 + 1),
          (if k < n / 8 then binPMF (n / 2) (1 / 2 : ℝ) k else 0))
        = ∑ k ∈ Finset.range (n / 8), binPMF (n / 2) (1 / 2 : ℝ) k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hhigh_eq : (∑ k ∈ Finset.range (n / 2 + 1),
          (if n / 2 - n / 8 < k then binPMF (n / 2) (1 / 2 : ℝ) k else 0))
        = ∑ k ∈ Finset.Ico (n / 2 - n / 8 + 1) (n / 2 + 1), binPMF (n / 2) (1 / 2 : ℝ) k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hlow_eq, hhigh_eq]
    have h1 := WitnessOffsetTail.offset_lower_tail n hn
    have h2 := WitnessOffsetTailFull.offset_upper_tail n hn
    linarith

/-- The total real coin-flip mass is `1`: `∑_b (cfd.toPMF b).toReal = 1`. -/
theorem weight_total_eq_one (S : ProbVec n) (cfd : CoinFlipDist n S) :
    (∑ b : BinVec n, (cfd.toPMF b).toReal) = 1 := by
  have hsum_one : (∑ b : BinVec n, cfd.toPMF b) = 1 :=
    (hasSum_fintype (f := (cfd.toPMF ·))).unique (PMF.hasSum_coe_one cfd.toPMF)
  rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ _), hsum_one, ENNReal.toReal_one]

/-- **Part D — final numeric bound.**
`2·√n·exp(-n/256) + 2·exp(-n/256) ≤ (1/4)·exp(-√n/2)` for `n ≥ 10^12`. -/
theorem final_numeric_bound (hn : (10 ^ 12 : ℕ) ≤ n) :
    2 * (Real.sqrt n * Real.exp (-((n : ℝ) / 256)))
        + 2 * Real.exp (-((n : ℝ) / 256))
      ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2)) := by
  set s : ℝ := Real.sqrt n with hs
  have hn_lb : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs_sq : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  -- s ≥ 10^6
  have hs_lb : (10 ^ 6 : ℝ) ≤ s := by
    rw [hs]
    rw [show (10 ^ 6 : ℝ) = Real.sqrt (10 ^ 12) by
      rw [show (10:ℝ)^12 = (10^6)^2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hn_lb
  -- rewrite n = s^2 in the exponents
  rw [← hs_sq]
  -- goal: 2(s·exp(-s²/256)) + 2 exp(-s²/256) ≤ (1/4) exp(-s/2)
  -- factor: LHS = (2s+2)·exp(-s²/256)
  have hLHS : 2 * (s * Real.exp (-(s ^ 2 / 256))) + 2 * Real.exp (-(s ^ 2 / 256))
      = (2 * s + 2) * Real.exp (-(s ^ 2 / 256)) := by ring
  rw [hLHS]
  -- suffices (2s+2)·exp(-s²/256) ≤ (1/4)·exp(-s/2)
  -- ⟺ (2s+2) ≤ (1/4)·exp(s²/256 - s/2)
  rw [show -(s / 2) = (s ^ 2 / 256 - s / 2) + (-(s ^ 2 / 256)) by ring, Real.exp_add]
  rw [show (1 / 4 : ℝ) * (Real.exp (s ^ 2 / 256 - s / 2) * Real.exp (-(s ^ 2 / 256)))
      = ((1 / 4) * Real.exp (s ^ 2 / 256 - s / 2)) * Real.exp (-(s ^ 2 / 256)) by ring]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
  -- now: 2s+2 ≤ (1/4)·exp(s²/256 - s/2)
  set y : ℝ := s ^ 2 / 256 - s / 2 with hy
  have hy_nn : 0 ≤ y := by rw [hy]; nlinarith [hs_lb, hs_nn]
  have hy_lb : s ^ 2 / 512 ≤ y := by rw [hy]; nlinarith [hs_lb, hs_nn]
  -- y³/6 ≤ exp y
  have hcube : y ^ 3 / 6 ≤ Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy_nn 3
    simpa using this
  -- and y³ ≥ (s²/512)³ ; combine to get 2s+2 ≤ (1/4)·exp y
  have hy3 : (s ^ 2 / 512) ^ 3 ≤ y ^ 3 :=
    pow_le_pow_left₀ (by positivity) hy_lb 3
  have hkey : 2 * s + 2 ≤ (1 / 4 : ℝ) * (y ^ 3 / 6) := by
    have hbig : 2 * s + 2 ≤ (1 / 4 : ℝ) * ((s ^ 2 / 512) ^ 3 / 6) := by
      rw [show (1 / 4 : ℝ) * ((s ^ 2 / 512) ^ 3 / 6) = s ^ 6 / (24 * 512 ^ 3) by ring]
      rw [le_div_iff₀ (by norm_num)]
      have hs5 : (10 ^ 6 : ℝ) ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (by norm_num) hs_lb 5
      have hs6_eq : s ^ 6 = s * s ^ 5 := by ring
      nlinarith [hs_lb, hs_nn, hs5, mul_le_mul_of_nonneg_left hs5 hs_nn, hs6_eq]
    have h2 : (1 / 4 : ℝ) * ((s ^ 2 / 512) ^ 3 / 6) ≤ (1 / 4 : ℝ) * (y ^ 3 / 6) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_right hy3 (by norm_num)
    linarith
  calc 2 * s + 2 ≤ (1 / 4 : ℝ) * (y ^ 3 / 6) := hkey
    _ ≤ (1 / 4 : ℝ) * Real.exp y := by
        apply mul_le_mul_of_nonneg_left hcube (by norm_num)

/-- **Master bound (Parts C & D).**  For the witness `S` with
`S.p i ≤ √n·binPMF n (1/2) i`, the Tonelli-reorganized bad-event sum is
`≤ (1/4)·exp(-√n/2)`. -/
theorem master_bound (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hSval : ∀ i : Fin n, S.p i ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val) :
    (∑ b : BinVec n,
        (cfd.toPMF b).toReal *
          (∑' r : ℤ, (if bitPred b r then (offsetWeight n r).toReal else 0)))
      ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2)) := by
  classical
  set w : BinVec n → ℝ := fun b => (cfd.toPMF b).toReal with hw
  have hw_nn : ∀ b, 0 ≤ w b := fun b => ENNReal.toReal_nonneg
  -- inner tsum → finite sum over Icc
  have hinner : ∀ b : BinVec n,
      (∑' r : ℤ, (if bitPred b r then (offsetWeight n r).toReal else 0))
        = ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
            (if bitPred b r then (offsetWeight n r).toReal else 0) := by
    intro b
    apply tsum_eq_sum
    intro r hr
    rw [Finset.mem_Icc] at hr
    push_neg at hr
    have hout : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r := by
      by_contra hc; push_neg at hc; exact absurd (hr hc.1) (not_lt.mpr hc.2)
    by_cases hb : bitPred b r
    · rw [if_pos hb,
        WitnessPrefixSuffixTailSupport.offsetWeight_toReal_zero_of_out_of_range hn8 r hout]
    · rw [if_neg hb]
  simp_rw [hinner]
  -- pull the finite sums together and swap order
  have hswap :
      (∑ b : BinVec n, w b *
          (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
            (if bitPred b r then (offsetWeight n r).toReal else 0)))
        = ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
            (offsetWeight n r).toReal *
              (∑ b : BinVec n, (if bitPred b r then w b else 0)) := by
    -- distribute w b into the inner Icc sum
    have hdist : (∑ b : BinVec n, w b *
          (∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
            (if bitPred b r then (offsetWeight n r).toReal else 0)))
        = ∑ b : BinVec n, ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
            (if bitPred b r then w b * (offsetWeight n r).toReal else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hb : bitPred b r
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb, mul_zero]
    rw [hdist, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : bitPred b r
    · rw [if_pos hb, if_pos hb]; ring
    · rw [if_neg hb, if_neg hb, mul_zero]
  rw [hswap]
  -- Now bound termwise over r ∈ Icc.
  -- Split each r-term: |r| ≤ n/8 (bit tail) vs |r| > n/8 (offset tail).
  have hbit_one : ∀ r : ℤ, (∑ b : BinVec n, (if bitPred b r then w b else 0)) ≤ 1 := by
    intro r
    calc (∑ b : BinVec n, (if bitPred b r then w b else 0))
        ≤ ∑ b : BinVec n, w b :=
          Finset.sum_le_sum (fun b _ => by
            by_cases hb : bitPred b r
            · rw [if_pos hb]
            · rw [if_neg hb]; exact hw_nn b)
      _ = 1 := weight_total_eq_one S cfd
  have hbit_nn : ∀ r : ℤ, 0 ≤ (∑ b : BinVec n, (if bitPred b r then w b else 0)) :=
    fun r => Finset.sum_nonneg (fun b _ => by
      by_cases hb : bitPred b r
      · rw [if_pos hb]; exact hw_nn b
      · rw [if_neg hb])
  -- per-r upper bound on the inner b-sum
  set C : ℝ := 2 * (Real.sqrt n * Real.exp (-((n : ℝ) / 256))) with hC
  have hbit_small : ∀ r : ℤ, (-((n / 8 : ℕ) : ℤ) ≤ r ∧ r ≤ ((n / 8 : ℕ) : ℤ)) →
      (∑ b : BinVec n, (if bitPred b r then w b else 0)) ≤ C := by
    intro r hr
    exact WitnessBitProb.bitPred_prob_le n hn hn8 S cfd hSval r hr
  -- Bound the whole r-sum by splitting Icc by |r| ≤ n/8.
  set IccR : Finset ℤ := Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ) with hIccR
  have hmain :
      (∑ r ∈ IccR, (offsetWeight n r).toReal *
          (∑ b : BinVec n, (if bitPred b r then w b else 0)))
        ≤ C * (∑ r ∈ IccR, (offsetWeight n r).toReal)
          + 2 * Real.exp (-((n : ℝ) / 256)) := by
    -- termwise bound
    have hterm : ∀ r ∈ IccR,
        (offsetWeight n r).toReal *
            (∑ b : BinVec n, (if bitPred b r then w b else 0))
          ≤ C * (offsetWeight n r).toReal
            + (if (r < -((n / 8 : ℕ) : ℤ) ∨ ((n / 8 : ℕ) : ℤ) < r)
               then (offsetWeight n r).toReal else 0) := by
      intro r _
      by_cases hsmall : (r < -((n / 8 : ℕ) : ℤ) ∨ ((n / 8 : ℕ) : ℤ) < r)
      · -- |r| > n/8: use bit-prob ≤ 1
        rw [if_pos hsmall]
        have h1 : (offsetWeight n r).toReal *
              (∑ b : BinVec n, (if bitPred b r then w b else 0))
            ≤ (offsetWeight n r).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hbit_one r) (ow_toReal_nonneg n r)
        have hCnn : 0 ≤ C * (offsetWeight n r).toReal := by
          have : 0 ≤ C := by rw [hC]; positivity
          exact mul_nonneg this (ow_toReal_nonneg n r)
        rw [mul_one] at h1
        linarith
      · -- |r| ≤ n/8: use bit-prob ≤ C
        rw [if_neg hsmall]
        push_neg at hsmall
        have hr8 : -((n / 8 : ℕ) : ℤ) ≤ r ∧ r ≤ ((n / 8 : ℕ) : ℤ) := ⟨hsmall.1, hsmall.2⟩
        have h1 : (offsetWeight n r).toReal *
              (∑ b : BinVec n, (if bitPred b r then w b else 0))
            ≤ (offsetWeight n r).toReal * C :=
          mul_le_mul_of_nonneg_left (hbit_small r hr8) (ow_toReal_nonneg n r)
        rw [mul_comm C] at *
        linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hoff := offset_tail_le hn8 hn
    rw [← hIccR] at hoff
    linarith
  refine le_trans hmain ?_
  -- C·1 + 2exp(-n/256) ≤ (1/4)exp(-√n/2)
  have hoff_one : (∑ r ∈ IccR, (offsetWeight n r).toReal) ≤ 1 := by
    rw [hIccR]; exact offset_total_le_one hn8
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hstep1 : C * (∑ r ∈ IccR, (offsetWeight n r).toReal)
      + 2 * Real.exp (-((n : ℝ) / 256)) ≤ C + 2 * Real.exp (-((n : ℝ) / 256)) := by
    have := mul_le_mul_of_nonneg_left hoff_one hCnn
    rw [mul_one] at this; linarith
  refine le_trans hstep1 ?_
  -- C + 2exp(-n/256) = 2√n exp(-n/256) + 2exp(-n/256) ≤ (1/4)exp(-√n/2)
  rw [hC]
  exact final_numeric_bound hn

end WitnessTailAssembly
