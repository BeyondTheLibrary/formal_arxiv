import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess

/-!
# WitnessPrefixSuffixTailSupport — sorry-free intermediate lemmas

Building blocks toward de-axiomatizing `WitnessPrefixSuffixTail` (paper
Lemma 6's bad-event tail bound).  The full statement is a `tsum` over
`BinVec n × ℤ` of an indicator

  `[ r < -n/4  ∨  n/4 < r  ∨  (∃ i, (i < n/4+r ∨ 3n/4+r ≤ i) ∧ b.bit i) ]`

weighted by `(cfd.toPMF b).toReal * (offsetWeight n r).toReal`.

The lemmas here establish the **support reduction**: the first two
disjuncts (`r` out of `[-n/4, n/4]`) are *vacuous against the weight*,
because `offsetWeight n r = 0` whenever `r < -n/4` or `n/4 < r`.  Hence the
bad-event summand is pointwise equal to the summand of the **bit-only**
indicator `(∃ i, (i < n/4+r ∨ 3n/4+r ≤ i) ∧ b.bit i)`.  This collapses the
three-way disjunction to the single prefix/suffix-bit event the paper
actually analyses, and is the first honest step of any proof of the axiom.

All lemmas are sorry-free.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess

namespace WitnessPrefixSuffixTailSupport

variable {n : ℕ}

/-- The offset weight vanishes whenever `r` falls strictly outside the
support window `[-(n/4 : ℕ), (n/4 : ℕ)]`, provided `n % 8 = 1`
(so that `(n/4 : ℕ) + (n/4 : ℕ) = (n/2 : ℕ)`).  This is the fact that makes
the first two disjuncts of the bad event vacuous against the weight. -/
theorem offsetWeight_zero_of_out_of_range (hn8 : n % 8 = 1) (r : ℤ)
    (hr : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r) :
    offsetWeight n r = 0 := by
  unfold offsetWeight
  simp only
  rw [dif_neg]
  rintro ⟨h1, h2⟩
  -- `h1 : 0 ≤ r + (n/4 : ℕ)`, `h2 : r + (n/4 : ℕ) ≤ (n/2 : ℕ)`.
  -- From `n % 8 = 1`: `(n/4 : ℕ) + (n/4 : ℕ) = (n/2 : ℕ)`.
  have hquarter : (n / 4 : ℕ) + (n / 4 : ℕ) = (n / 2 : ℕ) := by omega
  have hq : ((n / 4 : ℕ) : ℤ) + ((n / 4 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hquarter
  rcases hr with hlo | hhi
  · omega
  · omega

/-- Real-valued form: `(offsetWeight n r).toReal = 0` outside the window. -/
theorem offsetWeight_toReal_zero_of_out_of_range (hn8 : n % 8 = 1) (r : ℤ)
    (hr : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r) :
    (offsetWeight n r).toReal = 0 := by
  rw [offsetWeight_zero_of_out_of_range hn8 r hr, ENNReal.toReal_zero]

/-- **Support reduction (pointwise).**  For every `(b, r)`, the bad-event
summand (three-way disjunction) equals the bit-only summand: the two
out-of-range disjuncts never contribute, because they force
`offsetWeight n r = 0`.  This is the key collapse used by any proof of
`WitnessPrefixSuffixTail`. -/
theorem badEvent_summand_eq_bitOnly (hn8 : n % 8 = 1)
    (w : BinVec n → ℝ) (br : BinVec n × ℤ) :
    (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
          (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                          (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                        br.1.bit i = true)) then
        (w br.1 * (offsetWeight n br.2).toReal)
       else 0)
      =
    (if (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                        (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                      br.1.bit i = true) then
        (w br.1 * (offsetWeight n br.2).toReal)
       else 0) := by
  obtain ⟨b, r⟩ := br
  simp only
  by_cases hbit : (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + r ∨
                      (3 * (n / 4 : ℕ) : ℤ) + r ≤ i.val) ∧ b.bit i = true)
  · -- The bit event holds, so both sides take the `then` branch.
    rw [if_pos (Or.inr (Or.inr hbit)), if_pos hbit]
  · -- The bit event fails.  Either `r` is in range (both `else`) or out of
    -- range (weight is `0`, so the `then` value is also `0`).
    rw [if_neg hbit]
    by_cases hr : r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r
    · -- Out of range: LHS takes a `then` branch but the weight is `0`.
      rw [if_pos (by tauto)]
      rw [offsetWeight_toReal_zero_of_out_of_range hn8 r hr, mul_zero]
    · -- In range and no bit: LHS takes the `else` branch.
      rw [if_neg]
      rintro (h | h | h)
      · exact hr (Or.inl h)
      · exact hr (Or.inr h)
      · exact hbit h

/-- **Support reduction (whole `tsum`).**  The bad-event tsum equals the
bit-only tsum.  This rewrites the LHS of `WitnessPrefixSuffixTail` into the
single prefix/suffix-bit event that the paper bounds, with the out-of-range
offset disjuncts eliminated. -/
theorem badEvent_tsum_eq_bitOnly (hn8 : n % 8 = 1) (w : BinVec n → ℝ) :
    (∑' (br : BinVec n × ℤ),
        (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
              (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                              (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                            br.1.bit i = true)) then
            (w br.1 * (offsetWeight n br.2).toReal)
           else 0))
      =
    (∑' (br : BinVec n × ℤ),
        (if (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                            (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                          br.1.bit i = true) then
            (w br.1 * (offsetWeight n br.2).toReal)
           else 0)) := by
  apply tsum_congr
  intro br
  exact badEvent_summand_eq_bitOnly hn8 w br

end WitnessPrefixSuffixTailSupport
