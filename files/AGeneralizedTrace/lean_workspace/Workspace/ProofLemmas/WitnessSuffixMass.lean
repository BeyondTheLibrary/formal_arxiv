import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.CentralBinomialUpperTailWide
import Workspace.ProofLemmas.WitnessBitTail
import Workspace.ProofLemmas.WitnessBitMass
import Workspace.ProofLemmas.WitnessOffsetTail

/-!
# WitnessSuffixMass — the suffix bit-mass tail bound

Mirror of `WitnessBitMass.witness_prefix_mass` for the suffix positions.
The suffix positions for `|r| ≤ n/8` satisfy `i ≥ 3n/4 + r ≥ 5n/8`, i.e.
`i ∈ Ico (5n/8) n`.  By binomial symmetry `binPMF n (1/2) i = binPMF n (1/2) (n-i)`
these map onto the prefix tail `range (3n/8)` (since `5n/8 ≤ i < n` ⟺
`0 < n - i ≤ 3n/8`), so the cumulative `binPMF`-mass is `≤ exp(-n/256)` and the
witness mass `≤ √n·exp(-n/256)`.

All lemmas are sorry-free.
-/

open Workspace.Types.ProbVec
open Workspace.Types.AlternatingSumExpression

namespace WitnessSuffixMass

/-- A cumulative left-tail bound at the suffix-reindexed cutoff
`K = n - 5n/8 + 1`: `∑_{k < K} binPMF n (1/2) k ≤ exp(-n/256)`.  Same Chernoff
argument as `WitnessBitTail.binPMF_prefix_tail`, with the slightly larger cutoff. -/
theorem suffix_range_tail (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ k ∈ Finset.range (n - (5 * n / 8) + 1), binPMF n (1 / 2 : ℝ) k)
      ≤ Real.exp (-((n : ℝ) / 256)) := by
  have hn_pos : 0 < n := by have : (0:ℕ) < 10^12 := by norm_num
                            omega
  have hbase := WitnessOffsetTail.binPMF_range_chernoff n (n - (5 * n / 8) + 1)
  refine le_trans hbase ?_
  set a : ℕ := n - (5 * n / 8) + 1 with ha
  have ha_le : (a : ℝ) ≤ 3 * (n : ℝ) / 8 + 2 := by
    have : 8 * a ≤ 3 * n + 15 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this; push_cast at this; linarith
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
  have hln97 : Real.log (9 / 7) ≤ 2 / 7 := by
    have h := Real.log_le_sub_one_of_pos h97_pos; linarith
  have hln89 : Real.log (8 / 9) ≤ -(1 / 9) := by
    have h := Real.log_le_sub_one_of_pos h89_pos; linarith
  have hna_nn : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn_lb : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [ha_le, hln97, hln89, hna_nn, hnn, hn_lb,
    mul_le_mul_of_nonneg_left hln97 hna_nn,
    mul_le_mul_of_nonneg_left hln89 hnn]

/-- The suffix `binPMF`-tail: the `n`-binomial mass at coordinates
`i ∈ Ico (5n/8) n` (the suffix positions, valid indices only) is `≤ exp(-n/256)`,
via symmetry onto a cumulative left tail. -/
theorem binPMF_suffix_tail (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ i ∈ Finset.Ico (5 * n / 8) n, binPMF n (1 / 2 : ℝ) i)
      ≤ Real.exp (-((n : ℝ) / 256)) := by
  have hmap :
      (∑ i ∈ Finset.Ico (5 * n / 8) n, binPMF n (1 / 2 : ℝ) i)
        = ∑ k ∈ Finset.Ico 1 (n - (5 * n / 8) + 1), binPMF n (1 / 2 : ℝ) k := by
    apply Finset.sum_nbij' (fun i => n - i) (fun k => n - k)
    · intro i hi
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Ico]; omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_Ico]; omega
    · intro i hi
      rw [Finset.mem_Ico] at hi; omega
    · intro k hk
      rw [Finset.mem_Ico] at hk; omega
    · intro i hi
      rw [Finset.mem_Ico] at hi
      rw [CentralBinomialUpperTailWideProof.binPMF_half_symm n i (by omega)]
  rw [hmap]
  -- Ico 1 (n - 5n/8 + 1) ⊆ range (n - 5n/8 + 1); bound that cumulative tail by Chernoff.
  have hsub : Finset.Ico 1 (n - (5 * n / 8) + 1) ⊆ Finset.range (n - (5 * n / 8) + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]; omega
  refine le_trans ?_ (suffix_range_tail n hn)
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro k _ _
  unfold binPMF
  by_cases h : k ≤ n
  · rw [if_pos h]; positivity
  · rw [if_neg h]

/-- Suffix bit-mass: the witness `S.p`-mass summed over the suffix coordinates
`i ∈ Ico (5n/8) n` is `≤ √n · exp(-n/256)`. -/
theorem witness_suffix_mass (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ i ∈ Finset.Ico (5 * n / 8) n,
      (if i % 2 = 0
       then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
            Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
       else 0))
      ≤ Real.sqrt n * Real.exp (-((n : ℝ) / 256)) := by
  have hstep :
      (∑ i ∈ Finset.Ico (5 * n / 8) n,
        (if i % 2 = 0
         then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
              Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
         else 0))
        ≤ ∑ i ∈ Finset.Ico (5 * n / 8) n, Real.sqrt n * binPMF n (1 / 2 : ℝ) i := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ico] at hi
    apply WitnessBitMass.witness_val_le n i
    omega
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left (binPMF_suffix_tail n hn) (Real.sqrt_nonneg _)

end WitnessSuffixMass
