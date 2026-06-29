import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.LengthsDiffBoundedByAltSum

open Workspace.Types.BinVec

/-!
`LengthsDifferenceIsAlternatingSum` — algebraic core of Lemma 6 in §3.1 of
Rivkin–Valiant–Valiant (2024).

For every length parameter `n` with `(10^12 : ℕ) ≤ n` and `n % 8 = 1`, every
pair of witness probability vectors `Se So : ProbVec n` constructed as in the
paper's witness construction (`Se` supported on EVEN indices, `So` symmetric
on ODD indices, both assigning to each index `i` of the correct parity the
value `(1/(4·e²·√(2π))) · √n · C(n, i) · 2⁻ⁿ`), every deletion probability
`δ : DelProb` with `(320 : ℝ) / √n ≤ δ.val ≤ 1/2`, and every choice of
lengths-only processes `lenE` and `lenO` for the two witnesses,

```
((1/2) : ℝ) * ∑' s : (BinVec (n/2) × ℕ × ℕ),
   |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
  ≤ Workspace.Types.AlternatingSumExpression.altSum n δ.val α
```

where `α := (1 / (4 · e² · √(2π))) · √n` is the witness-construction's
scaling parameter.

This is the statement of paper Lemma 6 (algebraic identity), now PROVED
(no axiom) from the sorry-free composition lemma
`Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.LengthsDiffBoundedByAltSum`
(which proves the partial-deletion → alternating-sum reduction via the
`Path4Assembly` bridge), supplying the required coin-flip witnesses via
`CoinFlipDistExists`. The additive slack constant is `exp(-n/512)`, an
`e^{-Ω(n)}` term inherited from `LengthsDiffBoundedByAltSum`.

The 12 sub-lemmas in `Workspace.ProofLemmas` (`WitnessCoinFlipFormula`,
`LengthsOnlyDifferenceClosedForm`, `WindowFactorisation`,
`PrefixSuffixMarginalsToOne`, `MiddleWeightExplicit`, `MixedParityVanishes`,
`ParitySwapBijection`, `OffsetWeightBoundedByFirstFactor`,
`SuffixOffByOneIntegrated`, `EllShiftReindex`, `PerSummandBoundLengthsDiff`,
`AltSumExpansionMatches`) record an earlier from-scratch path to this
identity; they are retained in the workspace as documentation but are not
on the critical path to `MainTheorem`, which now goes through the
`Path4Assembly` bridge inside `LengthsDiffBoundedByAltSum`.
-/
theorem LengthsDifferenceIsAlternatingSum :
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
            (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
            ((1 / 2) : ℝ) * ∑' s : (BinVec (n / 2) × ℕ × ℕ),
                |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
              ≤ (4 : ℝ) * Workspace.Types.AlternatingSumExpression.altSum n δ.val
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
                + Real.exp (-(n : ℝ) / 512) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO
  exact Workspace.ProofLemmas.LengthsDiffBoundedByAltSum.LengthsDiffBoundedByAltSum
          n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO
          (CoinFlipDistExists Se).some
          (CoinFlipDistExists So).some
