import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LengthsDiffTsumSameParity
import Workspace.ProofLemmas.LengthsDiffPerSummandSigned

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# LengthsDiffTsumSignedRSum

Sorry-free *assembly* step toward de-axiomatising paper Lemma 6.  It combines two
already-proved sorry-free lemmas:

* `LengthsDiffTsumSameParity` — rewrites the total-variation tsum as a finite
  same-parity sum over middle masks `m` of the inner `(z₋,z₊)`-tsum of
  `|lenE − lenO|`.

* `LengthsDiffPerSummandSigned` — gives, for a same-parity mask `m`, the per
  `(z₋,z₊)`-summand SIGNED closed form `lenE − lenO = ∑_r W(r)·(signed Q/ellFactor)`.

Composing them rewrites the TV-tsum as the finite same-parity sum over `m` of the
inner `(z₋,z₊)`-tsum of the *absolute value of the signed r-sum*.  The signs are
kept inside the `r`-sum (before the outer `|·|`), exactly the form the paper's
cancellation argument needs.
-/

namespace Workspace.ProofLemmas.LengthsDiffTsumSignedRSum

theorem LengthsDiffTsumSignedRSum :
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
            (∑' s : (BinVec (n / 2) × ℕ × ℕ),
                |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|)
              =
            ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
              (if (∀ j₁ j₂ : Fin (n / 2),
                      m.bit j₁ = true → m.bit j₂ = true →
                      (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
               then ∑' p : ℕ × ℕ,
                      |∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
                         (offsetWeight n r).toReal *
                           (prefixLengthWeight n δ r p.1).toReal *
                           (suffixLengthWeight n δ r p.2).toReal *
                           (let Q_e : ℝ :=
                               ∏ j ∈ (Finset.univ.filter
                                        (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
                                 (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
                             let Q_o : ℝ :=
                               ∏ j ∈ (Finset.univ.filter
                                        (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
                                 (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
                             if h : ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).Nonempty then
                                 (-1 : ℝ) ^ (((n / 4 : ℤ) + r + ((((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).min' h : Fin (n / 2)) : ℕ)) % 2).toNat *
                                   (if ((n / 4 : ℤ) + r + ((((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).min' h : Fin (n / 2)) : ℕ)) % 2 = 0
                                    then Q_e else Q_o) *
                                   (∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)), ellFactor n ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j : ℕ))
                               else Q_e - Q_o)|
               else 0) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co
  classical
  rw [LengthsDiffTsumSameParity.LengthsDiffTsumSameParity
        n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hpar : (∀ j₁ j₂ : Fin (n / 2),
      m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
  · rw [if_pos hpar, if_pos hpar]
    refine tsum_congr (fun p => ?_)
    congr 1
    have h := LengthsDiffPerSummandSigned.LengthsDiffPerSummandSigned
      n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO Ce Co m hpar p.1 p.2
    simp only at h
    exact h
  · rw [if_neg hpar, if_neg hpar]

end Workspace.ProofLemmas.LengthsDiffTsumSignedRSum
