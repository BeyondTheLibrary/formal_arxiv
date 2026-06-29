import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LengthsDiffTsumSignedRSum
import Workspace.ProofLemmas.AltSumExpansionMatches
import Workspace.ProofLemmas.SignedInnerDefs
import Workspace.ProofLemmas.Path4Assembly

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

set_option linter.dupNamespace false

/-!
# LengthsDiffBoundedByAltSum — the composition lemma proving paper Lemma 6
  (`paper_lemma_6_algebraic_identity`, now de-axiomatised)

This file builds the FINAL composition lemma realising the paper's Lemma
`lem:r-func` (`arXiv-2412.00674v1/deletion.tex`, lines 281–305): the
partial-deletion + parity-identity argument that bounds the total-variation
distance between the lengths-only processes of `S_e` and `S_o` by the
closed-form alternating sum `altSum`, up to the paper's `O(1)` multiplicative
slack (here the constant `4`) and `e^{-Ω(n)}` additive slack (here
`exp(-n/512)`), exactly as stated on line 284.

The whole file is now sorry-free: the per-`r` analytic core is proved via the
`Path4Assembly` bridge (`signed_inner_bridge`) and its aggregate bound
`perMaskPert_sum_le`. There is no longer any axiom and no remaining `sorry`.

## What is PROVED sorry-free in this file

The **composition / algebra**:

* `LengthsDiffTsumSignedRSum` (proved, sorry-free) rewrites the TV-tsum
  `∑'_s |lenE − lenO|` as the finite same-parity sum over middle masks `m`
  of the inner `(z₋,z₊)`-tsum of the *absolute value of the signed `r`-sum*
  (signs kept inside the inner `|·|`, before any triangle bound — the form
  the paper's cancellation argument requires).
* `AltSumExpansionMatches` (proved, sorry-free) rewrites `altSum n δ α` as the
  same finite same-parity sum over masks `m` of
  `∑_{z₋,z₊ ∈ range(n/2+1)} |altRSum n δ α σ_m|`, where
  `σ_m = (ell_m).image (·+1)` is the paper's `{1,…,n/2}`-indexed location set.

`LengthsDiffBoundedByAltSum` (the target — the conclusion formerly admitted as
the axiom `paper_lemma_6_algebraic_identity`, now de-axiomatised) is then
proved by rewriting its LHS through `LengthsDiffTsumSignedRSum`, its RHS
through `AltSumExpansionMatches`, and discharging the resulting *purely
analytic* per-`r` estimate via the helper `signed_inner_bounded_by_altRSum`
below.

## The analytic core (`signed_inner_bounded_by_altRSum`)

The genuinely-new mathematical step is the per-`r` discrepancy absorption
of the paper's lines 297–305.  It is now PROVED (sorry-free) by delegating to
`Workspace.ProofLemmas.Path4Assembly.signed_inner_bridge`.  Its precise
content (the "F38 exact remaining have") is:

For each same-parity mask `m`, with `α := (1/(4·e²·√(2π)))·√n`,
`σ_m := ell_m.image (·+1)`,

```
(1/2) · ∑'_{(z₋,z₊) : ℕ×ℕ} | ∑_r offsetWeight(r)·prefixLengthWeight(r,z₋)·
        suffixLengthWeight(r,z₊)·(signed closed form Q/ellFactor at r,m) |
  ≤ 4 · (∑_{z₋,z₊ ∈ range(n/2+1)} | altRSum n δ.val α σ_m |)
     + (per-mask e^{-Ω(n)} tail)
```

aggregating to the target's `exp(-n/512)` over the finitely-many masks.

The FOUR per-`r` discrepancies between `offsetWeight·prefix·suffix·(signed
form)` and `(-1)^|r|·Fterm` that this bound absorbs (documented in
`lean_knowledge.md` F38, and faithful to the paper):

1. **offset rescale** — `offsetWeight n r = bin(n/2,1/2,r+n/4)` versus
   `Fterm`'s first factor `binPMFInt n (1/2) (r+n/2) = bin(n,1/2,r+n/2)`.
   Worst-case ratio `≤ 4/√π < 4` at `r = 0` (`OffsetWeightFterm.
   offsetWeight_le_central_factor`).  This is a PER-`r`, non-constant
   multiplicative factor; it is the part of the paper's argument that goes
   through the Fourier/convolution route (it cannot be applied term-wise
   inside the alternating `∑_r` without destroying the cancellation).
2. **suffix off-by-one** — `suffixLengthWeight` has length `(n/4−r)+1`
   (one more than `Fterm`'s `bin(n/4−r,…)` for `n%8=1`); the discrepancy
   sums to `≤ 2√(1−δ)` per the proved `SuffixOffByOneIntegrated`.
3. **Q-factor** — the window product `Q_p ∈ [0,1]` (`QFactorBounds.
   Q_mem_unitInterval`).
4. **sign / ℓ-reindex** — align the window-parity sign
   `(-1)^(((n/4)+r+ℓ.min)%2)` (from `InnerSumSignedClosedForm`) to
   `(-1)^|r|` while keeping the sign INSIDE `|∑_r|`, and shift `ellFactor`'s
   index by `+1` to match `AltSumExpansionMatches` (`EllShiftReindex`,
   `j ↦ j−1`).  This is the crux: a per-`r`-uniform rescale pulled through
   the absolute alternating sum because the rescale factor is bounded
   uniformly in `r` (`≤ 4`) and the sign aligns.

These four pieces have proved sorry-free *building blocks*
(`OffsetWeightFterm`, `SuffixOffByOneIntegrated`, `QFactorBounds`,
`EllShiftReindex`, `LengthWeightBinPMFIdentity`, `PrefixSuffixZSupport`,
`AltSumExpansionMatches`), and their assembly into the single inequality
above — the paper's genuine analytic core (the Fourier-domain bound of
lines 297–305) — is now proved in `Path4Assembly` and consumed here via
`signed_inner_bounded_by_altRSum`.  No `sorry` and no axiom remain.
-/

namespace Workspace.ProofLemmas.LengthsDiffBoundedByAltSum

/-- The per-mask `e^{-Ω(n)}` tail share: the target's `exp(-n/8)` additive
slack split uniformly across the `2^(n/2)` middle masks.  Used only so the
per-mask bound's tails aggregate *exactly* to `exp(-n/8)`. -/
noncomputable def perMaskTail (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) / 8) / (Fintype.card (Workspace.Types.BinVec.BinVec (n / 2)) : ℝ)

lemma perMaskTail_nonneg (n : ℕ) : 0 ≤ perMaskTail n := by
  unfold perMaskTail
  positivity

/-- The per-mask tail shares sum (over ALL masks, hence in particular over the
same-parity ones via the `if`) to at most `exp(-n/8)`. Sorry-free. -/
lemma perMaskTail_masked_sum_le (n : ℕ) :
    ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
         then perMaskTail n else 0)
      ≤ Real.exp (-(n : ℝ) / 8) := by
  classical
  -- bound each `if … then perMaskTail else 0` by `perMaskTail` (nonneg)
  have hle : ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
         then perMaskTail n else 0)
      ≤ ∑ _m : Workspace.Types.BinVec.BinVec (n / 2), perMaskTail n := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    by_cases h : (∀ j₁ j₂ : Fin (n / 2),
        m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
    · rw [if_pos h]
    · rw [if_neg h]; exact perMaskTail_nonneg n
  refine hle.trans ?_
  rw [Finset.sum_const, Finset.card_univ]
  unfold perMaskTail
  rw [nsmul_eq_mul]
  have hne : Nonempty (Workspace.Types.BinVec.BinVec (n / 2)) :=
    ⟨⟨fun _ => false⟩⟩
  have hcard_pos : 0 < (Fintype.card (Workspace.Types.BinVec.BinVec (n / 2)) : ℝ) := by
    have : 0 < Fintype.card (Workspace.Types.BinVec.BinVec (n / 2)) := Fintype.card_pos
    exact_mod_cast this
  rw [mul_div_assoc']
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hcard_pos), mul_one]

/-- **The analytic core (paper lines 297–305).**

For a same-parity middle mask `m`, the per-mask contribution of the signed
inner sum is bounded by `4 ·` the matching `altRSum` aggregate over the
truncated `(z₋,z₊)`-range, plus the per-mask `e^{-Ω(n)}` perturbation share
`Path4Assembly.perMaskPert n m`.  Summed over masks
(`Path4Assembly.perMaskPert_sum_le`) the tails realise the target's
`exp(-n/512)` additive slack.

This is now PROVED (sorry-free) by delegating to
`Path4Assembly.signed_inner_bridge`.  It absorbs the four per-`r`
discrepancies (offset rescale `≤ 4/√π`, suffix off-by-one, `Q ∈ [0,1]`,
sign/ℓ-reindex) documented above, via the Fourier-domain argument of the
paper. -/
theorem signed_inner_bounded_by_altRSum
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : Workspace.Types.DelProb.DelProb)
    (hδ_lb : (320 : ℝ) / Real.sqrt n ≤ δ.val) (hδ_ub : δ.val ≤ 1 / 2)
    (m : Workspace.Types.BinVec.BinVec (n / 2))
    (hpar : ∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
        (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) :
    ((1 / 2) : ℝ) *
        (∑' p : ℕ × ℕ, |signedInner n δ m p|)
      ≤ (4 : ℝ) *
          (∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |altRSum n δ.val
                ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
                zMinus zPlus (sigmaSet n m)|)
        + Workspace.ProofLemmas.Path4Assembly.perMaskPert n m := by
  exact Workspace.ProofLemmas.Path4Assembly.signed_inner_bridge n hn hmod δ hδ_lb hδ_ub m hpar

/-- **The target composition lemma** — the conclusion formerly admitted as the
axiom `paper_lemma_6_algebraic_identity`, now PROVED here.

The total-variation distance (in `(1/2)·∑'|·|` form) between the lengths-only
processes of the parity-supported witnesses `S_e, S_o` is bounded by
`4 · altSum n δ α + exp(-n/512)`.

PROOF STRUCTURE (sorry-free composition around the analytic core):
* rewrite the LHS `∑'_s |lenE − lenO|` to the finite same-parity mask sum of
  the inner signed `r`-sum tsum via `LengthsDiffTsumSignedRSum`;
* rewrite the RHS `altSum` to the matching same-parity mask sum of the
  truncated `altRSum`-aggregate via `AltSumExpansionMatches`;
* bound the LHS mask-by-mask through `signed_inner_bounded_by_altRSum`,
  collecting the per-mask `4·(altRSum aggregate)` into `4·altSum` and the
  per-mask perturbation tails into `exp(-n/512)`
  (`Path4Assembly.perMaskPert_sum_le`). -/
theorem LengthsDiffBoundedByAltSum :
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
            ((1 / 2) : ℝ) * ∑' s : (Workspace.Types.BinVec.BinVec (n / 2) × ℕ × ℕ),
                |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
              ≤ (4 : ℝ) * Workspace.Types.AlternatingSumExpression.altSum n δ.val
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
                + Real.exp (-(n : ℝ) / 512) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co
  classical
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα
  -- Predicate "mask m has same-parity support".
  set P : Workspace.Types.BinVec.BinVec (n / 2) → Prop := fun m =>
    ∀ j₁ j₂ : Fin (n / 2),
      m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2 with hP
  -- (1) Rewrite the LHS TV-tsum via the proved signed-rsum assembly.
  have hLHS := LengthsDiffTsumSignedRSum.LengthsDiffTsumSignedRSum
    n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co
  -- The RHS of `hLHS` is, after folding into `signedInner`, exactly
  -- `∑ m, if P m then ∑'_p |signedInner n δ m p| else 0`.
  have hLHS' :
      (∑' s : (Workspace.Types.BinVec.BinVec (n / 2) × ℕ × ℕ),
          |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|)
        = ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
            (if P m then ∑' p : ℕ × ℕ, |signedInner n δ m p| else 0) := by
    rw [hLHS]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hpar : P m
    · rw [hP] at hpar
      rw [if_pos hpar, if_pos hpar]
      refine tsum_congr (fun p => ?_)
      rfl
    · rw [hP] at hpar
      rw [if_neg hpar, if_neg hpar]
  -- (2) Rewrite the RHS `altSum` via the proved expansion-matches lemma.
  have hRHS := AltSumExpansionMatches n hn hmod δ.val α
  -- `hRHS : ∑ m, (if P m then ∑_{z₋,z₊} |altRSum … (image (·+1))| else 0) = altSum n δ α`.
  -- The `image (·+1)` is exactly `sigmaSet n m`.
  have hRHS' :
      Workspace.Types.AlternatingSumExpression.altSum n δ.val α
        = ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
            (if P m then
              ∑ zMinus ∈ Finset.range (n / 2 + 1),
                ∑ zPlus ∈ Finset.range (n / 2 + 1),
                  |altRSum n δ.val α zMinus zPlus (sigmaSet n m)|
             else 0) := by
    rw [← hRHS]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hpar : P m
    · rw [hP] at hpar
      rw [if_pos hpar, if_pos hpar]
      rfl
    · rw [hP] at hpar
      rw [if_neg hpar, if_neg hpar]
  -- (3) Assemble the bound mask-by-mask.
  rw [hLHS']
  rw [Finset.mul_sum]
  rw [hRHS']
  rw [Finset.mul_sum]
  -- Goal:
  --   ∑ m, (1/2)·(if P m then ∑'_p |signedInner| else 0)
  --     ≤ ∑ m, 4·(if P m then ∑ |altRSum| else 0) + exp(-n/8)
  -- Bound the LHS sum by the RHS sum + per-mask tails, then absorb the tails.
  have hmain :
      ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
          ((1 / 2 : ℝ) * (if P m then ∑' p : ℕ × ℕ, |signedInner n δ m p| else 0))
        ≤ ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
            ((4 : ℝ) * (if P m then
                ∑ zMinus ∈ Finset.range (n / 2 + 1),
                  ∑ zPlus ∈ Finset.range (n / 2 + 1),
                    |altRSum n δ.val α zMinus zPlus (sigmaSet n m)|
               else 0)
              + (if P m then Workspace.ProofLemmas.Path4Assembly.perMaskPert n m else 0)) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    by_cases hpar : P m
    · rw [if_pos hpar, if_pos hpar, if_pos hpar]
      rw [hP] at hpar
      have hb := signed_inner_bounded_by_altRSum n hn hmod δ hδ_lb hδ_ub m hpar
      rw [hα]
      exact hb
    · rw [if_neg hpar, if_neg hpar, if_neg hpar]
      simp
  refine hmain.trans ?_
  -- Split the RHS sum of (a_m + tail_m) into (∑ a_m) + (∑ tail_m), then absorb.
  rw [Finset.sum_add_distrib]
  have htail := Workspace.ProofLemmas.Path4Assembly.perMaskPert_sum_le n hn hmod δ hδ_lb hδ_ub
  -- The first summand is exactly the goal's RHS first summand;
  -- the tail summand is ≤ exp(-n/512).
  have htail' : ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
          (if P m then Workspace.ProofLemmas.Path4Assembly.perMaskPert n m else 0)
        ≤ Real.exp (-(n : ℝ) / 512) := htail
  linarith [htail']

end Workspace.ProofLemmas.LengthsDiffBoundedByAltSum
