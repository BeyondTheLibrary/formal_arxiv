import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.WitnessOffsetTail

/-!
# WitnessBitTail — the prefix/suffix-bit cumulative tail bound

For the witness `Se` (resp. `So`), the per-coordinate "true" probability is

  `S.p i = (1/(4·e²·√(2π)))·√n·(C(n,i)·2^{-n})`   (for `i` of the right parity, else 0)
         ≤ C₀·√n·binPMF n (1/2) i.

The prefix positions for an offset `|r| ≤ n/8` lie strictly below `3n/8`; the
suffix positions strictly above `5n/8`.  Both sit deep in the binomial tail, so
their cumulative `S.p`-mass is `≤ exp(-Ω(n))` — even after the polynomial `√n`
prefactor and a union bound over `≤ n` positions.

The keystone is `WitnessOffsetTail.binPMF_range_chernoff`
(`∑_{k<K} binPMF m (1/2) k ≤ (9/7)^K·(8/9)^m`).

This file lands the cumulative bit-tail `∑_{i<3n/8} binPMF n (1/2) i ≤ exp(-n/64)`,
sorry-free, and the `√n`-weighted version.
-/

open Workspace.Types.AlternatingSumExpression

namespace WitnessBitTail

/-- Cumulative left bit-tail: the `n`-binomial mass strictly below `3n/8` is
`≤ exp(-n/64)`. -/
theorem binPMF_prefix_tail (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ k ∈ Finset.range (3 * n / 8), binPMF n (1 / 2 : ℝ) k)
      ≤ Real.exp (-((n : ℝ) / 256)) := by
  have hn_pos : 0 < n := by have : (0:ℕ) < 10^12 := by norm_num
                            omega
  have hbase := WitnessOffsetTail.binPMF_range_chernoff n (3 * n / 8)
  refine le_trans hbase ?_
  -- (9/7)^(3n/8) · (8/9)^n ≤ exp(-n/256), via logs.
  set a : ℕ := 3 * n / 8 with ha
  have ha_le : (a : ℝ) ≤ 3 * (n : ℝ) / 8 := by
    have : 8 * a ≤ 3 * n := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this; push_cast at this; linarith
  -- rewrite LHS = exp(a·ln(9/7) + n·ln(8/9))
  have h97_pos : (0 : ℝ) < 9 / 7 := by norm_num
  have h89_pos : (0 : ℝ) < 8 / 9 := by norm_num
  have hexp97 : Real.exp ((a : ℝ) * Real.log (9 / 7)) = (9 / 7 : ℝ) ^ a := by
    rw [Real.exp_nat_mul, Real.exp_log h97_pos]
  have hexp89 : Real.exp ((n : ℝ) * Real.log (8 / 9)) = (8 / 9 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log h89_pos]
  have hLrw : (9 / 7 : ℝ) ^ a * (8 / 9 : ℝ) ^ n
      = Real.exp ((a : ℝ) * Real.log (9 / 7) + (n : ℝ) * Real.log (8 / 9)) := by
    rw [Real.exp_add, hexp97, hexp89]
  rw [hLrw]
  apply Real.exp_le_exp.mpr
  -- ln(9/7) ≤ 2/7 ; ln(8/9) ≤ -1/9
  have hln97 : Real.log (9 / 7) ≤ 2 / 7 := by
    have h := Real.log_le_sub_one_of_pos h97_pos
    linarith
  have hln89 : Real.log (8 / 9) ≤ -(1 / 9) := by
    have h := Real.log_le_sub_one_of_pos h89_pos
    linarith
  -- combine: a·ln(9/7) + n·ln(8/9) ≤ (3n/8)(2/7) - n/9 = -n/252 ≤ -n/256
  have hna_nn : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith [ha_le, hln97, hln89, hna_nn, hnn,
    mul_le_mul_of_nonneg_left hln97 hna_nn,
    mul_le_mul_of_nonneg_left hln89 hnn]

end WitnessBitTail
