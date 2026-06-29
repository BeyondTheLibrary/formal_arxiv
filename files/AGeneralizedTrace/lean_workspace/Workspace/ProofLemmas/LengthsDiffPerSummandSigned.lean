import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LengthsDiffSignedReorg
import Workspace.ProofLemmas.LengthsDiffSignedClosedForm

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# LengthsDiffPerSummandSigned

Sorry-free *assembly* step toward de-axiomatising paper Lemma 6.  It composes
two already-proved facts:

* `LengthsDiffSignedReorg` :
  `lenE(m,z₋,z₊) − lenO(m,z₋,z₊) = ∑_r W(r) · (∑_b (Ce−Co)·middleIndicator)`,
  where `W(r) = offsetWeight·prefixW·suffixW`.

* `LengthsDiffSignedClosedForm.InnerSumSignedClosedForm` :
  for an index-level same-parity middle vector `m`, the inner marginal sum
  `∑_b (Ce−Co)·middleIndicator` equals the **signed** closed form
  `(−1)^p · (Q_e or Q_o) · ∏_{j∈ell} ellFactor` (nonempty `ell`) or `Q_e − Q_o`
  (empty `ell`).

The result keeps the alternating sign `(−1)^p` and the window-product `Q`
*inside* the `r`-sum — i.e. it does NOT triangle-inequality away the sign.  This
is the form the paper's Lemma-6 cancellation argument actually needs (the
nonneg/triangle form of `PerSummandBoundLengthsDiff` destroys the cancellation
and therefore cannot reach `altSum`, which is a sum of `|alternating r-sum|`).
-/

namespace Workspace.ProofLemmas.LengthsDiffPerSummandSigned

theorem LengthsDiffPerSummandSigned :
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
          ∀ (m : Workspace.Types.BinVec.BinVec (n / 2)),
            (∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
                (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) →
          ∀ (zMinus zPlus : ℕ),
            let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
            let ell : Finset (Fin (n / 2)) :=
              (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
            ((lenE.toPMF (m, zMinus, zPlus)).toReal
              - (lenO.toPMF (m, zMinus, zPlus)).toReal)
              =
            ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
              (offsetWeight n r).toReal *
                (prefixLengthWeight n δ r zMinus).toReal *
                (suffixLengthWeight n δ r zPlus).toReal *
                (let Q_e : ℝ :=
                    ∏ j ∈ (Finset.univ.filter
                             (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
                      (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
                  let Q_o : ℝ :=
                    ∏ j ∈ (Finset.univ.filter
                             (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
                      (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
                  if h : ell.Nonempty then
                      (-1 : ℝ) ^ (((n / 4 : ℤ) + r + ((ell.min' h : Fin (n / 2)) : ℕ)) % 2).toNat *
                        (if ((n / 4 : ℤ) + r + ((ell.min' h : Fin (n / 2)) : ℕ)) % 2 = 0
                         then Q_e else Q_o) *
                        (∏ j ∈ ell, ellFactor n α r (j : ℕ))
                    else Q_e - Q_o) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co m hpar zMinus zPlus
  intro α ell
  rw [LengthsDiffSignedReorg n hn hmod Se So hSe hSo δ hδ_lb hδ_ub
        lenE lenO Ce Co m zMinus zPlus]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hclosed := Workspace.ProofLemmas.LengthsDiffSignedClosedForm.InnerSumSignedClosedForm
    n hn hmod Se So hSe hSo m hpar Ce Co r hr
  simp only at hclosed ⊢
  rw [mul_assoc, mul_assoc, hclosed]
  ring

end Workspace.ProofLemmas.LengthsDiffPerSummandSigned
