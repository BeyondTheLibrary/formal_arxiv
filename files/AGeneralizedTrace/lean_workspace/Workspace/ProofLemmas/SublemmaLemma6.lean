import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.TraceDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.Types.TVDistance
import Workspace.Types.PartialDeletionAxioms
import Workspace.ProofLemmas.PartialDeletionReducesToLengths
import Workspace.ProofLemmas.LengthsDifferenceIsAlternatingSum
import Workspace.ProofLemmas.PartialDominatesHCore
import Workspace.ProofLemmas.CoinFlipDistExists

theorem SublemmaLemma6 :
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
          ∀ (tdE : Workspace.Types.TraceDist.TraceDist n Se δ)
            (tdO : Workspace.Types.TraceDist.TraceDist n So δ)
            (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
            (partO : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n So δ)
            (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
            (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
            Workspace.Types.TVDistance.TVDistance tdE.toPMF tdO.toPMF
              ≤ (4 : ℝ) * Workspace.Types.AlternatingSumExpression.altSum n δ.val
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
                + Real.exp (-(n : ℝ) / 512)
                + Real.exp (-((1 : ℝ) / 2 * Real.sqrt n)) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub tdE tdO partE partO lenE lenO
  have h1 := PartialDominatesHCore.partial_dominates_traceDist_of_gate
              tdE tdO partE partO (CoinFlipDistExists Se).some (CoinFlipDistExists So).some (by omega)
  have h2 := PartialDeletionReducesToLengths n hn hmod Se So hSe hSo δ hδ_lb hδ_ub
              partE partO lenE lenO
  have h3 := LengthsDifferenceIsAlternatingSum n hn hmod Se So hSe hSo δ hδ_lb hδ_ub
              lenE lenO
  linarith
