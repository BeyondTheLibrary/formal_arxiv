import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.ProofLemmas.LengthsOnlyDifferenceClosedForm

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

theorem LengthsDiffSignedReorg :
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
        ∀ (δ : Workspace.Types.DelProb.DelProb),
          (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
          ∀ (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
            (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ)
            (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
            (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So),
            ∀ (m : BinVec (n / 2)) (zMinus zPlus : ℕ),
              ((lenE.toPMF (m, zMinus, zPlus)).toReal
                - (lenO.toPMF (m, zMinus, zPlus)).toReal)
                =
              ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
                (offsetWeight n r).toReal *
                  (prefixLengthWeight n δ r zMinus).toReal *
                  (suffixLengthWeight n δ r zPlus).toReal *
                  (∑ b : BinVec n,
                    ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
                      (middleIndicator n b m r).toReal) := by
  intro n hn hn8 Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co m zMinus zPlus
  rw [LengthsOnlyDifferenceClosedForm n hn hn8 Se So hSe hSo δ hδ_lb hδ_ub
        lenE lenO Ce Co m zMinus zPlus]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring
