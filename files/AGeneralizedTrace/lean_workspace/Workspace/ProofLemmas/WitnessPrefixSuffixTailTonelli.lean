import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.ProofLemmas.WitnessPrefixSuffixTailSupport

/-!
# WitnessPrefixSuffixTailTonelli — Tonelli reorganization of the bit-only tsum

The bit-only bad-event tsum (from `WitnessPrefixSuffixTailSupport.badEvent_tsum_eq_bitOnly`)
ranges over `BinVec n × ℤ`.  Since `BinVec n` is a `Fintype`, the `tsum` over the product
splits into a *finite* sum over `b : BinVec n` of an inner `tsum` over `r : ℤ`.

This file lands that reorganization sorry-free, factoring the weight
`w b = (cfd.toPMF b).toReal` out of the inner `r`-tsum:

  `∑'_{(b,r)} [bitPred b r] · w b · offsetWeight(r).toReal`
    `= ∑_{b} w b · ∑'_r [bitPred b r] · offsetWeight(r).toReal`.

All lemmas are sorry-free.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess

open scoped Classical

namespace WitnessPrefixSuffixTailTonelli

variable {n : ℕ}

/-- The prefix/suffix-bit predicate for a fixed string `b` and offset `r`. -/
def bitPred (b : BinVec n) (r : ℤ) : Prop :=
  ∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + r ∨
                  (3 * (n / 4 : ℕ) : ℤ) + r ≤ i.val) ∧ b.bit i = true

/-- The bit-only summand, written with the weight `w b` pulled out of the
indicator: `[bitPred b r] · w b · offsetWeight(r).toReal`. -/
theorem bitOnly_summand_factor (w : BinVec n → ℝ) (b : BinVec n) (r : ℤ) :
    (if bitPred b r then (w b * (offsetWeight n r).toReal) else 0)
      = w b * (if bitPred b r then (offsetWeight n r).toReal else 0) := by
  by_cases h : bitPred b r
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The bit-only summand has finite support: it vanishes unless `r` is in the
offset window `[-(n/4 : ℕ), (n/4 : ℕ)]`, because `offsetWeight n r = 0`
outside it (using `n % 8 = 1`). -/
theorem bitOnly_summand_support (hn8 : n % 8 = 1) (w : BinVec n → ℝ)
    (br : BinVec n × ℤ)
    (hsupp : br ∉ (Finset.univ : Finset (BinVec n)) ×ˢ
        (Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ))) :
    (if bitPred br.1 br.2 then (w br.1 * (offsetWeight n br.2).toReal) else 0) = 0 := by
  obtain ⟨b, r⟩ := br
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and,
    not_and, not_le] at hsupp
  -- `r` is out of `[-(n/4), n/4]`.
  have hr : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r := by
    by_contra hcon
    push_neg at hcon
    omega
  have hzero : (offsetWeight n r).toReal = 0 :=
    WitnessPrefixSuffixTailSupport.offsetWeight_toReal_zero_of_out_of_range hn8 r hr
  by_cases h : bitPred b r
  · rw [if_pos h, hzero, mul_zero]
  · rw [if_neg h]

/-- The bit-only summand is summable over `BinVec n × ℤ` (finite support). -/
theorem bitOnly_summable (hn8 : n % 8 = 1) (w : BinVec n → ℝ) :
    Summable (fun br : BinVec n × ℤ =>
      (if bitPred br.1 br.2 then (w br.1 * (offsetWeight n br.2).toReal) else 0)) := by
  apply summable_of_ne_finset_zero
    (s := (Finset.univ : Finset (BinVec n)) ×ˢ
        (Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ)))
  intro br hbr
  exact bitOnly_summand_support hn8 w br hbr

/-- **Tonelli reorganization.**  The bit-only bad-event tsum over
`BinVec n × ℤ` splits into a finite sum over `b : BinVec n` of the weight
`w b` times the inner `r`-tsum. -/
theorem bitOnly_tsum_split (hn8 : n % 8 = 1) (w : BinVec n → ℝ) :
    (∑' (br : BinVec n × ℤ),
        (if bitPred br.1 br.2 then (w br.1 * (offsetWeight n br.2).toReal) else 0))
      = ∑ b : BinVec n,
          w b * (∑' r : ℤ, (if bitPred b r then (offsetWeight n r).toReal else 0)) := by
  have hsum := bitOnly_summable hn8 w
  have hinner : ∀ b : BinVec n, Summable (fun r : ℤ =>
      (if bitPred (b, r).1 (b, r).2 then (w (b, r).1 * (offsetWeight n (b, r).2).toReal) else 0)) := by
    intro b
    apply summable_of_ne_finset_zero
      (s := Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ))
    intro r hr
    apply bitOnly_summand_support hn8 w (b, r)
    simp only [Finset.mem_product, Finset.mem_univ, true_and]
    exact hr
  rw [hsum.tsum_prod' hinner, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro r
  exact bitOnly_summand_factor w b r

end WitnessPrefixSuffixTailTonelli
