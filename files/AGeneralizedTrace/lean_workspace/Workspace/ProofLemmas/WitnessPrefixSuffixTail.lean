import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.WitnessPrefixSuffixTailSupport
import Workspace.ProofLemmas.WitnessPrefixSuffixTailTonelli
import Workspace.ProofLemmas.WitnessBitMass
import Workspace.ProofLemmas.WitnessTailAssembly

/-!
# WitnessPrefixSuffixTail — Hoeffding-style tail bound for the bad event (Lemma 6)

For the witness construction (`Se`, `So`) and any `cfdE : CoinFlipDist n Se`,
`cfdO : CoinFlipDist n So`, the joint probability that either (a) the offset
`r` falls outside `[-n/4, n/4]` or (b) some bit in the prefix range
`[0, n/4 + r)` or suffix range `[3n/4 + r, n)` is `true`, is bounded by
`(1/4)·exp(-√n / 2)`.

This file de-axiomatizes the lemma sorry-free, assembling:
* support reduction (`WitnessPrefixSuffixTailSupport`: the out-of-range offset
  disjuncts are vacuous against the weight),
* Tonelli reorganization (`WitnessPrefixSuffixTailTonelli`),
* the master tail bound (`WitnessTailAssembly.master_bound`), which splits the
  offset into `|r| ≤ n/8` (binomial bit-tail via `WitnessBitProb`) and
  `|r| > n/8` (offset tail via `WitnessOffsetTailFull`), closed by the numeric
  bound `2√n·exp(-n/256) + 2·exp(-n/256) ≤ (1/4)exp(-√n/2)`.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess Workspace.Types.AlternatingSumExpression
open WitnessPrefixSuffixTailTonelli

/-- Per-witness instance of the bad-event tail bound. -/
theorem witnessPrefixSuffixTail_single
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hSform : ∀ i : Fin n, S.p i =
      (if (i.val) % 2 = 0
       then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
            Real.sqrt n *
            ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
       else 0)) :
    (∑' (br : (BinVec n) × ℤ),
        (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
              (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                              (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                            br.1.bit i = true)) then
            ((cfd.toPMF br.1).toReal *
             (offsetWeight n br.2).toReal)
           else 0))
      ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2)) := by
  classical
  set w : BinVec n → ℝ := fun b => (cfd.toPMF b).toReal with hw
  -- Step 1: support reduction (three-way disjunction → bit-only).
  rw [WitnessPrefixSuffixTailSupport.badEvent_tsum_eq_bitOnly hn8 w]
  -- Fold the explicit `∃ i, …` into `bitPred` (definitionally equal; the only
  -- difference is the `Decidable` instance on the `ite`).
  have hfold : (∑' (br : BinVec n × ℤ),
        (if (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                            (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                          br.1.bit i = true) then
            (w br.1 * (offsetWeight n br.2).toReal)
           else 0))
      = ∑' (br : BinVec n × ℤ),
          (if bitPred br.1 br.2 then w br.1 * (offsetWeight n br.2).toReal else 0) := by
    apply tsum_congr; intro br
    exact if_congr Iff.rfl rfl rfl
  rw [hfold]
  -- Step 2: Tonelli reorganization.
  rw [WitnessPrefixSuffixTailTonelli.bitOnly_tsum_split hn8 w]
  -- Step 3: per-coordinate witness bound.
  have hSval : ∀ i : Fin n, S.p i ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val := by
    intro i
    rw [hSform i]
    exact WitnessBitMass.witness_val_le n i.val (le_of_lt i.isLt)
  -- Step 4: master bound.
  exact WitnessTailAssembly.master_bound hn hn8 S cfd hSval

/-- `So`-variant of the per-witness bound, with parity `% 2 = 1`. -/
theorem witnessPrefixSuffixTailOdd_single
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hSform : ∀ i : Fin n, S.p i =
      (if (i.val) % 2 = 1
       then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
            Real.sqrt n *
            ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
       else 0)) :
    (∑' (br : (BinVec n) × ℤ),
        (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
              (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                              (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                            br.1.bit i = true)) then
            ((cfd.toPMF br.1).toReal *
             (offsetWeight n br.2).toReal)
           else 0))
      ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2)) := by
  classical
  set w : BinVec n → ℝ := fun b => (cfd.toPMF b).toReal with hw
  rw [WitnessPrefixSuffixTailSupport.badEvent_tsum_eq_bitOnly hn8 w]
  have hfold : (∑' (br : BinVec n × ℤ),
        (if (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                            (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                          br.1.bit i = true) then
            (w br.1 * (offsetWeight n br.2).toReal)
           else 0))
      = ∑' (br : BinVec n × ℤ),
          (if bitPred br.1 br.2 then w br.1 * (offsetWeight n br.2).toReal else 0) := by
    apply tsum_congr; intro br
    exact if_congr Iff.rfl rfl rfl
  rw [hfold]
  rw [WitnessPrefixSuffixTailTonelli.bitOnly_tsum_split hn8 w]
  have hSval : ∀ i : Fin n, S.p i ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i.val := by
    intro i
    rw [hSform i]
    by_cases h : i.val % 2 = 1
    · rw [if_pos h]
      have := WitnessBitMass.witness_val_le n i.val (le_of_lt i.isLt)
      -- the even-branch value is the explicit form; for odd parity the even-`if`
      -- in `witness_val_le` is `else 0`, so bound the value directly.
      have hbin : binPMF n (1 / 2 : ℝ) i.val
          = (Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹ := by
        rw [CentralBinomialLowerTailWideProof.binPMF_half_eq n i.val (le_of_lt i.isLt)]
        rw [show (1 / 2 : ℝ) ^ n = (2 ^ n : ℝ)⁻¹ by rw [one_div, inv_pow]]
      rw [hbin]
      have hc := WitnessBitMass.witness_const_le_one
      have hbin_nn : (0 : ℝ) ≤ (Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹ := by positivity
      calc (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
              * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
          ≤ 1 * Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
            apply mul_le_mul_of_nonneg_right _ hbin_nn
            exact mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
        _ = Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by ring
    · rw [if_neg h]
      have : (0 : ℝ) ≤ binPMF n (1 / 2 : ℝ) i.val := by
        unfold binPMF; by_cases hh : i.val ≤ n
        · rw [if_pos hh]; positivity
        · rw [if_neg hh]
      positivity
  exact WitnessTailAssembly.master_bound hn hn8 S cfd hSval

theorem WitnessPrefixSuffixTail :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (Se So : Workspace.Types.ProbVec.ProbVec n),
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∀ i : Fin n, So.p i =
          (if (i.val) % 2 = 1
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        ∀ (cfdE : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
          (cfdO : Workspace.Types.CoinFlipDist.CoinFlipDist n So),
          (∑' (br : (Workspace.Types.BinVec.BinVec n) × ℤ),
            (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
                  (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                                  (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                                br.1.bit i = true)) then
              ((cfdE.toPMF br.1).toReal *
               (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
             else 0))
            ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2))
        ∧
          (∑' (br : (Workspace.Types.BinVec.BinVec n) × ℤ),
            (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
                  (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                                  (3 * (n / 4 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                                br.1.bit i = true)) then
              ((cfdO.toPMF br.1).toReal *
               (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
             else 0))
            ≤ (1 / 4 : ℝ) * Real.exp (-(Real.sqrt n / 2)) := by
  intro n hn hn8 Se So hSe hSo cfdE cfdO
  refine ⟨?_, ?_⟩
  · exact witnessPrefixSuffixTail_single n hn hn8 Se cfdE hSe
  · -- The `So` witness uses parity `% 2 = 1`, but the per-coordinate bound
    -- `witness_val_le` only needs `S.p i ≤ √n·binPMF i`, which holds for either
    -- parity branch (both branches are `≤` the explicit value form).
    apply witnessPrefixSuffixTailOdd_single n hn hn8 So cfdO hSo

