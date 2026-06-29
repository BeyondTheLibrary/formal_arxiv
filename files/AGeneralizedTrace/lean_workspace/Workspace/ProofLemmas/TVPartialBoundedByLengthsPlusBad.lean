import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.TVPartialBoundedFinal

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.PartialDeletionProcess
open TVPartialBoundedHelpers

open scoped Classical

/--
**`TVPartialBoundedByLengthsPlusBad`** — structural good/bad TV decomposition
(paper Lemma 6, deletion.tex 293-295). Now a THEOREM (de-axiomatized): the
abstract types DO expose enough structure (via the composition laws) to give a
direct proof. Route: triangle inequality + good-event collapse identity (on the
good event the partial process equals the lengths-only process up to relabelling,
by `TraceFromZeroIsLengthBinomial`) + bad-event mass bound. See
`TVPartialBoundedFinal.tvPartialBounded` for the proof.

For any pair of probability vectors `Se So : ProbVec n`, any deletion rate `δ`,
any coin-flip distributions, partial-deletion processes and lengths-only
processes, the L¹ distance on the partial-deletion sample space is bounded above
by the L¹ distance on the lengths-only sample space PLUS the joint probability of
the "bad event" under both witness distributions.
-/
theorem TVPartialBoundedByLengthsPlusBad :
    ∀ {n : ℕ} {Se So : Workspace.Types.ProbVec.ProbVec n}
      {δ : Workspace.Types.DelProb.DelProb}
      (cfdE : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
      (cfdO : Workspace.Types.CoinFlipDist.CoinFlipDist n So)
      (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
      (partO : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n So δ)
      (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
      (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
      ((1/2) : ℝ) * ∑' s : (BinVec (n / 2) × Trace n × Trace n),
         |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|
        ≤ ((1/2) : ℝ) * ∑' s : (BinVec (n / 2) × ℕ × ℕ),
             |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
          + (∑' (br : (BinVec n) × ℤ),
              (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
                    (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                                    ((n / 4 + n / 2 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                                  br.1.bit i = true)) then
                ((cfdE.toPMF br.1).toReal *
                 (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
               else 0))
          + (∑' (br : (BinVec n) × ℤ),
              (if (br.2 < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < br.2 ∨
                    (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + br.2 ∨
                                    ((n / 4 + n / 2 : ℕ) : ℤ) + br.2 ≤ i.val) ∧
                                  br.1.bit i = true)) then
                ((cfdO.toPMF br.1).toReal *
                 (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
               else 0)) := by
  intro n Se So δ cfdE cfdO partE partO lenE lenO
  have h := TVPartialBoundedFinal.tvPartialBounded cfdE cfdO partE partO lenE lenO
  -- the only difference is the `Decidable` instance on the bad-event `if`
  -- (`Classical.propDecidable` vs `instDecidableOr`); these are defeq subsingletons.
  convert h using 6
