import Mathlib
import Workspace.Types.PartialDeletionProcess

/-!
# The offset PMF sums to one (`offsetWeight` is a probability distribution)

This file lands, **sorry-free**, the single load-bearing scalar fact that gates
the offset-marginalization half of the `hcore` step (d) of
`PartialDominatesBindForm.bind_identity_of_per_b`:

  `∑' r : ℤ, offsetWeight n r = 1`.

`offsetWeight n r = if 0 ≤ r + n/4 ∧ r + n/4 ≤ n/2 then C(n/2, (r+n/4).toNat) ·
(1/2)^(n/2) else 0` is the `Binomial(n/2, 1/2)`-shifted-by-`n/4` PMF.  Summing it
over all integer offsets `r` collapses (since all but finitely many terms vanish)
to `∑_{k=0}^{n/2} C(n/2, k) · (1/2)^(n/2) = 2^(n/2) · (1/2)^(n/2) = 1`, via
`Nat.sum_range_choose`.

**Why this is the key brick.**  In the `hcore` identity, for each fixed *valid*
offset `r` the per-`r` three-segment factored sum (prefix·middle·suffix, via
`channel_sum_factor3` + the kernel-side convolution) equals the SAME
whole-string keep-set sum `∑_m [restrict b m = τ.bits] ∏ wfac` — independently
of where the offset cut falls, because all three segments are deleted at the
same rate `δ`.  Marginalizing over `r` therefore multiplies that constant
whole-string sum by `∑' r, offsetWeight n r`, and *this lemma* is what makes
that factor `1`, reproducing the offset-free RHS of `hcore`.
-/

namespace OffsetWeightSumOne

open Workspace.Types.PartialDeletionProcess

open scoped Classical

/-- The support of `offsetWeight n` as a function of `r : ℤ`: the offset weight
is nonzero only when `r + n/4 ∈ [0, n/2]`, i.e. `r ∈ [-(n/4), n/2 - n/4]`. -/
lemma offsetWeight_eq_zero_of_not_mem {n : ℕ} {r : ℤ}
    (h : ¬ (0 ≤ r + (n / 4 : ℕ) ∧ r + (n / 4 : ℕ) ≤ (n / 2 : ℕ))) :
    offsetWeight n r = 0 := by
  unfold offsetWeight
  simp only
  rw [dif_neg h]

/-- The offset weight, evaluated at `r`, in terms of the shifted index
`k = r + n/4`, when that index is in range. -/
lemma offsetWeight_eq_of_mem {n : ℕ} {r : ℤ}
    (h : 0 ≤ r + (n / 4 : ℕ) ∧ r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) :
    offsetWeight n r
      = (Nat.choose (n / 2) (r + (n / 4 : ℕ)).toNat : ENNReal)
          * (ENNReal.ofReal (1 / 2)) ^ (n / 2) := by
  unfold offsetWeight
  simp only
  rw [dif_pos h]

/-- The integer-shift embedding `k ↦ (k : ℤ) - n/4` from `Fin (n/2 + 1)` onto the
support of `offsetWeight n`. -/
def shiftEmb (n : ℕ) : ℕ ↪ ℤ where
  toFun k := (k : ℤ) - (n / 4 : ℕ)
  inj' := by intro a b hab; simpa using hab

/-- **The offset PMF sums to one.**  `∑' r : ℤ, offsetWeight n r = 1`.

Reindexing the integer sum to its finite support `{r : r + n/4 ∈ [0, n/2]}` via
the shift `k = r + n/4` and applying `Nat.sum_range_choose`
(`∑_{k≤n/2} C(n/2,k) = 2^(n/2)`) gives `2^(n/2) · (1/2)^(n/2) = 1`. -/
theorem offsetWeight_tsum_eq_one (n : ℕ) :
    ∑' r : ℤ, offsetWeight n r = 1 := by
  -- The support is contained in the image of `range (n/2+1)` under the shift.
  rw [tsum_eq_sum (s := (Finset.range (n / 2 + 1)).map (shiftEmb n))]
  · -- On the finite support, reindex by `k` and apply `Nat.sum_range_choose`.
    rw [Finset.sum_map]
    have hterm : ∀ k ∈ Finset.range (n / 2 + 1),
        offsetWeight n ((shiftEmb n) k)
          = (Nat.choose (n / 2) k : ENNReal) * (ENNReal.ofReal (1 / 2)) ^ (n / 2) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk' : k ≤ n / 2 := Nat.lt_succ_iff.mp hk
      have hmem : 0 ≤ ((shiftEmb n) k) + (n / 4 : ℕ) ∧
          ((shiftEmb n) k) + (n / 4 : ℕ) ≤ (n / 2 : ℕ) := by
        constructor
        · simp only [shiftEmb, Function.Embedding.coeFn_mk]
          have : ((k : ℤ) - (n / 4 : ℕ)) + (n / 4 : ℕ) = (k : ℤ) := by ring
          rw [this]; positivity
        · simp only [shiftEmb, Function.Embedding.coeFn_mk]
          have : ((k : ℤ) - (n / 4 : ℕ)) + (n / 4 : ℕ) = (k : ℤ) := by ring
          rw [this]; exact_mod_cast hk'
      rw [offsetWeight_eq_of_mem hmem]
      congr 2
      -- `((shiftEmb n) k + n/4).toNat = k`.
      simp only [shiftEmb, Function.Embedding.coeFn_mk]
      have : ((k : ℤ) - (n / 4 : ℕ)) + (n / 4 : ℕ) = (k : ℤ) := by ring
      rw [this, Int.toNat_natCast]
    rw [Finset.sum_congr rfl hterm]
    -- `∑ k, C(n/2,k) · c = (∑ k, C(n/2,k)) · c = 2^(n/2) · (1/2)^(n/2) = 1`.
    rw [← Finset.sum_mul]
    have hchoose : (∑ k ∈ Finset.range (n / 2 + 1), (Nat.choose (n / 2) k : ENNReal))
        = (2 : ENNReal) ^ (n / 2) := by
      rw [← Nat.cast_sum]
      rw [Nat.sum_range_choose (n / 2)]
      push_cast
      rfl
    rw [hchoose]
    rw [← mul_pow]
    have h2 : (2 : ENNReal) * ENNReal.ofReal (1 / 2) = 1 := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [h2, one_pow]
  · -- Terms outside the support vanish.
    intro r hr
    apply offsetWeight_eq_zero_of_not_mem
    intro hmem
    apply hr
    -- `r` is in the support, so `r = (r + n/4).toNat - n/4` with index in range.
    rw [Finset.mem_map]
    refine ⟨(r + (n / 4 : ℕ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      have := hmem.2
      have h0 := hmem.1
      omega
    · simp only [shiftEmb, Function.Embedding.coeFn_mk]
      have h0 := hmem.1
      rw [Int.toNat_of_nonneg h0]
      ring

end OffsetWeightSumOne
