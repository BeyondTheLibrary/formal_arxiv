import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LightAtypicalZTail
import Workspace.ProofLemmas.LightAtypicalZTailTailR
import Workspace.ProofLemmas.LightEnvelopeBound

/-!
# AltRSumLightAtypicalBoundFinal — the 4-step assembly closing §3.1 atypical-z absorption

This file de-axiomatizes `AltRSumLightAtypicalBound` (paper Lemma 11 / §3.1 atypical-z
absorption, line 418).  Both decay halves are already sorry-free:

* `LightAtypicalZTailProof.pieceA_atypR_envelope_bound` / `pieceB_atypR_envelope_bound`
  (F45) — atypical-`r` ranges `rA2`, `rB2`, carrying the inner z-tail decay.
* `LightAtypicalZTailTailRProof.pieceA_tailR_envelope_bound` / `pieceB_tailR_envelope_bound`
  (F51) — tail-`r` ranges `rA1`, `rB1`, carrying `B1`'s central-binomial-tail decay.

The 4 assembly steps:

1. **Triangle + factor** — bound each piece's `∑_z ∑_z |altRSum|` by the factored
   `∑_{r∈rRange} B1 · (∑_z B2/B3) · ∏ ellFactor`.  Piece A is `LightAtypicalZTail`'s
   `altRSum_pieceA_le` + `pieceA_factor_on_subrange`; Piece B is the twins below
   (`altRSum_pieceB_le`, `pieceB_factor_on_subrange`).
2. **r-split** — `rRange = rA1 ∪ rA2` (Piece A) and `rRange = rB2 ∪ rB1` (Piece B);
   apply the four per-range envelope bounds → each piece `≤ 2·e^{-n/128}·envelopeW ℓ`,
   total per-`ℓ` mass `≤ 4·e^{-n/128}·envelopeW ℓ`.
3. **Sum over `P_L`** — `∑_{ℓ∈P_L} 4·e^{-n/128}·envelopeW ℓ
   ≤ 4·e^{-n/128}·(n·e^{-√n/32})` via `LightEnvelopeBound`.
4. **Numeric** — `4·n·e^{-n/128-√n/32} ≤ (1/16)·e^{-√n/4}` for `n ≥ 10^12`.
-/

set_option maxHeartbeats 40000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace AltRSumLightAtypicalBoundFinalProof

/-- Triangle bound for Piece B: `|altRSum|` over the atypical Piece-B z-range
(`z₋` typical, `z₊ < n/16`) is dominated by the factored triple-product sum over the
full `r`-range.  Twin of `LightAtypicalZTailProof.altRSum_pieceA_le`. -/
lemma altRSum_pieceB_le
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.range (n / 16),
          |altRSum n δ α zMinus zPlus ℓ|)
      ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1))) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  apply Finset.sum_le_sum; intro zMinus _
  apply Finset.sum_le_sum; intro zPlus _
  unfold altRSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum; intro r _
  rw [abs_mul]
  have h_pow_abs : |(-1 : ℝ) ^ r.natAbs| = 1 := by
    rcases Nat.even_or_odd r.natAbs with hev | hodd
    · rw [hev.neg_one_pow]; norm_num
    · rw [hodd.neg_one_pow]; norm_num
  rw [h_pow_abs, one_mul]
  unfold Fterm
  have h_b1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
    LightAtypicalZTailProof.binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
  have h_b2_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus :=
    LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
    LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have h_prod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) :=
    LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r ℓ
  rw [abs_of_nonneg]
  apply mul_nonneg; apply mul_nonneg; apply mul_nonneg h_b1_nn h_b2_nn
  · exact h_b3_nn
  · exact h_prod_nn

/-- Factorisation for Piece B over a generic `r`-subrange `rSub`: pull `B1` and
`∏ ellFactor` out, bounding `∑_{z₋} B2 ≤ 1`.  Twin of
`LightAtypicalZTailProof.pieceA_factor_on_subrange`. -/
lemma pieceB_factor_on_subrange
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2)
    (ℓ : Finset ℕ) (rSub : Finset ℤ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.range (n / 16),
          ∑ r ∈ rSub,
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
              (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      ≤ ∑ r ∈ rSub,
          binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zPlus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  calc (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            ∑ r ∈ rSub,
              binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      = ∑ r ∈ rSub,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        rw [show (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  ∑ zPlus ∈ Finset.range (n / 16),
                    ∑ r ∈ rSub,
                      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
              = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  ∑ r ∈ rSub,
                    ∑ zPlus ∈ Finset.range (n / 16),
                      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
            from by
              apply Finset.sum_congr rfl; intro zMinus _; rw [Finset.sum_comm]]
        rw [Finset.sum_comm]
    _ ≤ ∑ r ∈ rSub,
          binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zPlus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        apply Finset.sum_le_sum
        intro r _
        have hB1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
          LightAtypicalZTailProof.binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
        have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) :=
          LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r ℓ
        -- ∑_{z₋ ∈ Ico (n/16) (n/2+1)} B2 ≤ ∑_{z₋ ∈ range (n/2+1)} B2 ≤ 1
        have hB2sum_le : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 := by
          have hsubset : Finset.Ico (n / 16) (n / 2 + 1) ⊆ Finset.range (n / 2 + 1) := by
            intro x hx
            rw [Finset.mem_Ico] at hx
            rw [Finset.mem_range]; omega
          calc (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus)
              ≤ (∑ zMinus ∈ Finset.range (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) (zMinus : ℤ)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
                intro x _ _
                exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
            _ ≤ 1 := LightAtypicalZTailProof.sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
        have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
          apply Finset.sum_nonneg; intro _ _
          exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
        -- expand inner double sum = B1 · (∑_{z₋} B2) · (∑_{z₊} B3) · ∏ ellFactor
        have hexpand :
            (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
              = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
          have hstep : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                        (∑ zPlus ∈ Finset.range (n / 16),
                          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
                      = ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                          ∑ zPlus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
            Finset.sum_mul_sum _ _ _ _
          rw [show binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1))
                = (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
                  ((∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) from by ring]
          rw [hstep, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro zMinus _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro zPlus _
          ring
        rw [hexpand]
        have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
          apply Finset.sum_nonneg; intro _ _
          exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
        -- bound the B2-sum factor by 1
        calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1))
            ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                1 *
                (∑ zPlus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
              gcongr
          _ = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zPlus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by ring

/-- **Step 1+2 (Piece A): per-`ℓ` atypical Piece-A mass `≤ 2·e^{-n/128}·envelopeW ℓ`.**
Triangle + factor (over full `rRange`), r-split `rRange = rA1 ∪ rA2`, then the two F45/F51
envelope bounds. -/
lemma pieceA_le_envelope
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.range (n / 16),
        ∑ zPlus ∈ Finset.range (n / 2 + 1),
          |altRSum n δ α zMinus zPlus ℓ|)
      ≤ 2 * Real.exp (-((n : ℝ) / 128)) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  -- Step 1: triangle + factor
  have h1 := LightAtypicalZTailProof.altRSum_pieceA_le n hn δ hδ_lb hδ_ub ℓ
  have h2 := LightAtypicalZTailProof.pieceA_factor_on_subrange n hn δ hδ_lb hδ_ub ℓ
    (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4))
  simp only at h1 h2
  -- r-split: rRange = rA1 ∪ rA2
  set rA1 : Finset ℤ := Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1) with hrA1_def
  set rA2 : Finset ℤ := Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4) with hrA2_def
  have h_rRange_eq : Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) = rA1 ∪ rA2 := by
    simp only [hrA1_def, hrA2_def]
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint rA1 rA2 := by
    simp only [hrA1_def, hrA2_def]
    apply Finset.disjoint_left.mpr
    intros r hr1 hr2
    rw [Finset.mem_Icc] at hr1 hr2; omega
  -- the factored term as a function of r
  set g : ℤ → ℝ := fun r =>
    binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
      (∑ zMinus ∈ Finset.range (n / 16),
        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
      (∏ j ∈ ℓ, ellFactor n α r (j - 1)) with hg_def
  have h_factor_split :
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g r)
        = (∑ r ∈ rA1, g r) + (∑ r ∈ rA2, g r) := by
    rw [h_rRange_eq, Finset.sum_union h_disj]
  -- the two envelope bounds
  have hA2 := LightAtypicalZTailProof.pieceA_atypR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  have hA1 := LightAtypicalZTailTailRProof.pieceA_tailR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  simp only at hA2 hA1
  -- chain
  set W : ℝ := ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      ∏ j ∈ ℓ, ellFactor n α r (j - 1) with hW_def
  calc (∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |altRSum n δ α zMinus zPlus ℓ|)
      ≤ _ := h1
    _ ≤ (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g r) := h2
    _ = (∑ r ∈ rA1, g r) + (∑ r ∈ rA2, g r) := h_factor_split
    _ ≤ Real.exp (-((n : ℝ) / 128)) * W + Real.exp (-((n : ℝ) / 128)) * W := by
        exact add_le_add hA1 hA2
    _ = 2 * Real.exp (-((n : ℝ) / 128)) * W := by ring

/-- **Step 1+2 (Piece B): per-`ℓ` atypical Piece-B mass `≤ 2·e^{-n/128}·envelopeW ℓ`.** -/
lemma pieceB_le_envelope
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.range (n / 16),
          |altRSum n δ α zMinus zPlus ℓ|)
      ≤ 2 * Real.exp (-((n : ℝ) / 128)) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  have h1 := altRSum_pieceB_le n hn δ hδ_lb hδ_ub ℓ
  have h2 := pieceB_factor_on_subrange n hn δ hδ_lb hδ_ub ℓ
    (Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4))
  simp only at h1 h2
  -- r-split: rRange = rB2 ∪ rB1
  set rB2 : Finset ℤ := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16) with hrB2_def
  set rB1 : Finset ℤ := Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4) with hrB1_def
  have h_rRange_eq : Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) = rB2 ∪ rB1 := by
    simp only [hrB2_def, hrB1_def]
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint rB2 rB1 := by
    simp only [hrB2_def, hrB1_def]
    apply Finset.disjoint_left.mpr
    intros r hr1 hr2
    rw [Finset.mem_Icc] at hr1 hr2; omega
  set g : ℤ → ℝ := fun r =>
    binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
      (∑ zPlus ∈ Finset.range (n / 16),
        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
      (∏ j ∈ ℓ, ellFactor n α r (j - 1)) with hg_def
  have h_factor_split :
      (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g r)
        = (∑ r ∈ rB2, g r) + (∑ r ∈ rB1, g r) := by
    rw [h_rRange_eq, Finset.sum_union h_disj]
  have hB2 := LightAtypicalZTailProof.pieceB_atypR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  have hB1 := LightAtypicalZTailTailRProof.pieceB_tailR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  simp only at hB2 hB1
  set W : ℝ := ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      ∏ j ∈ ℓ, ellFactor n α r (j - 1) with hW_def
  calc (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            |altRSum n δ α zMinus zPlus ℓ|)
      ≤ _ := h1
    _ ≤ (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4), g r) := h2
    _ = (∑ r ∈ rB2, g r) + (∑ r ∈ rB1, g r) := h_factor_split
    _ ≤ Real.exp (-((n : ℝ) / 128)) * W + Real.exp (-((n : ℝ) / 128)) * W := by
        exact add_le_add hB2 hB1
    _ = 2 * Real.exp (-((n : ℝ) / 128)) * W := by ring

/-- **Step 4 (numeric).** `4·n·e^{-n/128-√n/32} ≤ (1/16)·e^{-√n/4}` for `n ≥ 10^12`. -/
lemma numeric_step (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    4 * Real.exp (-((n : ℝ) / 128)) * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32)))
      ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 4)) := by
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < 10 ^ 12 := by norm_num
    exact_mod_cast Nat.lt_of_lt_of_le this hn
  have hsqn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- Rewrite as: 64 · n ≤ exp(n/128 + √n/32 - √n/4) = exp(n/128 - 7√n/32).
  -- It suffices: 64·n ≤ exp(n/128 - 7√n/32). Since √n ≤ n, 7√n/32 ≤ 7n/32 and n/128-7n/32<0,
  -- so use a cleaner bound: bound n ≤ exp(n/256) (huge slack) and 64 ≤ exp(n/256), giving
  -- 64·n ≤ exp(n/128). Then exp(n/128) ≤ exp(n/128 + √n/32 - √n/4) is FALSE (the extra is neg).
  -- So instead prove directly via:  LHS·exp(√n/4) ≤ 1/16, i.e. 64·n·exp(-n/128+√n/32+√n/4-... )
  -- Cleanest: show 64 * n * exp(√n/32) * exp(√n/4) ≤ exp(n/128) — no, √n/32+√n/4 on left.
  -- Move everything to exponents. We prove:
  --   4 * exp(-n/128) * n * exp(-√n/32) ≤ (1/16) exp(-√n/4)
  -- ⇔ 64 * n * exp(-n/128 - √n/32 + √n/4) ≤ 1
  -- ⇔ 64 * n ≤ exp(n/128 + √n/32 - √n/4) = exp(n/128 - 7√n/32).
  -- Since 7√n/32 ≤ 7n/32 (√n≤n) and n/128 - 7n/32 is negative, that exponent is small.
  -- BUT n/128 dominates 7√n/32 for large n: need n/128 - 7√n/32 ≥ ln(64 n).
  -- We prove n/256 ≥ 7√n/32 (i.e. n ≥ 56 √n, i.e. √n ≥ 56) and n/256 ≥ ln(64 n).
  set s : ℝ := Real.sqrt n with hs_def
  have hs_ge : (10 ^ 6 : ℝ) ≤ s := by
    rw [hs_def]
    have h_sq : (10 ^ 6 : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((10 : ℝ) ^ 6) ^ 2 = 10 ^ 12 := by ring
      rw [this]; exact_mod_cast hn
    calc (10 ^ 6 : ℝ) = Real.sqrt ((10 ^ 6) ^ 2) := by
          rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
  have hs_pos : (0 : ℝ) < s := by linarith
  have hn_eq_s2 : (n : ℝ) = s ^ 2 := by
    rw [hs_def, Real.sq_sqrt hn_pos.le]
  -- KEY: 64 * n ≤ exp(n/128 - 7s/32).
  -- exp(n/128 - 7s/32) = exp(s²/128 - 7s/32) ≥ exp(s²/256) (since s²/256 - 7s/32 ≥ 0 for s ≥ 56),
  -- and exp(s²/256) ≥ (s²/256)²/2 = s⁴/131072 ≥ 64 s² (since s ≥ 2897).
  have hkey : (64 : ℝ) * (n : ℝ) ≤ Real.exp ((n : ℝ) / 128 - 7 * s / 32) := by
    have hexp_lb : Real.exp ((s : ℝ) ^ 2 / 256) ≤ Real.exp ((n : ℝ) / 128 - 7 * s / 32) := by
      apply Real.exp_le_exp.mpr
      rw [hn_eq_s2]
      -- s²/256 ≤ s²/128 - 7s/32 ⇔ 7s/32 ≤ s²/256 ⇔ 56 s ≤ s² ⇔ 56 ≤ s
      nlinarith [hs_ge, hs_pos]
    have hquad : ((s : ℝ) ^ 2 / 256) ^ 2 / (Nat.factorial 2 : ℝ)
        ≤ Real.exp ((s : ℝ) ^ 2 / 256) :=
      Real.pow_div_factorial_le_exp ((s : ℝ) ^ 2 / 256) (by positivity) 2
    have hfact : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [hfact] at hquad
    have h64n_le : (64 : ℝ) * (n : ℝ) ≤ ((s : ℝ) ^ 2 / 256) ^ 2 / 2 := by
      rw [hn_eq_s2]
      -- 64 s² ≤ (s²/256)²/2 = s⁴/131072 ⇔ 64 · 131072 ≤ s² ⇔ s² ≥ 8388608
      have hs2 : (8388608 : ℝ) ≤ s ^ 2 := by nlinarith [hs_ge]
      nlinarith [hs2, hs_pos, sq_nonneg s]
    calc (64 : ℝ) * (n : ℝ)
        ≤ ((s : ℝ) ^ 2 / 256) ^ 2 / 2 := h64n_le
      _ ≤ Real.exp ((s : ℝ) ^ 2 / 256) := hquad
      _ ≤ Real.exp ((n : ℝ) / 128 - 7 * s / 32) := hexp_lb
  -- Reduce the goal to hkey.
  have hgoal_iff :
      4 * Real.exp (-((n : ℝ) / 128)) * ((n : ℝ) * Real.exp (-(s / 32)))
        = (1 / 16 * Real.exp (-(s / 4))) *
            (64 * (n : ℝ) * Real.exp (-((n : ℝ) / 128 - 7 * s / 32))) := by
    rw [Real.exp_neg, Real.exp_neg, Real.exp_neg, Real.exp_neg]
    have he1 : (0 : ℝ) < Real.exp ((n : ℝ) / 128) := Real.exp_pos _
    have he2 : (0 : ℝ) < Real.exp (s / 32) := Real.exp_pos _
    have he3 : (0 : ℝ) < Real.exp (s / 4) := Real.exp_pos _
    have he4 : (0 : ℝ) < Real.exp ((n : ℝ) / 128 - 7 * s / 32) := Real.exp_pos _
    rw [show (n : ℝ) / 128 - 7 * s / 32 = (n : ℝ) / 128 + s / 32 - s / 4 by ring]
    rw [Real.exp_sub, Real.exp_add]
    field_simp
    ring
  rw [hgoal_iff]
  -- Now: (1/16 exp(-s/4)) · (64 n exp(-(n/128 - 7s/32))) ≤ (1/16) exp(-s/4).
  -- suffices 64 n exp(-(n/128-7s/32)) ≤ 1, i.e. 64 n ≤ exp(n/128-7s/32) = hkey.
  have hfront_pos : (0 : ℝ) < 1 / 16 * Real.exp (-(s / 4)) := by positivity
  have hsuff : 64 * (n : ℝ) * Real.exp (-((n : ℝ) / 128 - 7 * s / 32)) ≤ 1 := by
    have he4 : (0 : ℝ) < Real.exp ((n : ℝ) / 128 - 7 * s / 32) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one he4]
    linarith [hkey]
  calc (1 / 16 * Real.exp (-(s / 4))) *
          (64 * (n : ℝ) * Real.exp (-((n : ℝ) / 128 - 7 * s / 32)))
      ≤ (1 / 16 * Real.exp (-(s / 4))) * 1 :=
        mul_le_mul_of_nonneg_left hsuff hfront_pos.le
    _ = 1 / 16 * Real.exp (-(s / 4)) := by ring

end AltRSumLightAtypicalBoundFinalProof

open AltRSumLightAtypicalBoundFinalProof in
/-- **§3.1 atypical-z absorption for the light family (paper Lemma 11), de-axiomatized.**

The full 4-step assembly: per-`ℓ` triangle+factor (Step 1) and r-split into the four
F45/F51 envelope bounds (Step 2) give an atypical-z mass `≤ 4·e^{-n/128}·envelopeW ℓ`;
summing over `P_L` and applying `LightEnvelopeBound` (Step 3) gives
`≤ 4·e^{-n/128}·n·e^{-√n/32}`; the numeric bound (Step 4) closes it under
`(1/16)·e^{-√n/4}`. -/
theorem AltRSumLightAtypicalBoundFinal :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), (320 : ℝ) / Real.sqrt n ≤ δ → δ ≤ 1 / 2 →
    let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    let α : ℝ := c' * Real.sqrt n
    let n_h : ℕ := n / 2
    let S_er : ℤ → ℕ → ℝ := fun r j =>
      α * Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
        (r + ((n : ℤ) / 4) + (j : ℤ))
    let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
      ∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ x then S_er r j else (1 - S_er r j))
    let P_L : Finset (Finset ℕ) :=
      ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
        Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
        ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)))
    (∑ ℓ ∈ P_L,
        ((∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          +
         (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)))
      ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 4)) := by
  intro n hn hmod δ hδ_lb hδ_ub
  simp only
  -- Abbreviations matching LightEnvelopeBound's local defs.
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  set α : ℝ := c' * Real.sqrt n with hα_def
  set n_h : ℕ := n / 2 with hn_h_def
  set S_er : ℤ → ℕ → ℝ := fun r j =>
        α * Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ)) with hS_er_def
  set widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j)) with hwidetildeMu_def
  set P_L : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))) with hP_L_def
  have hn_one : (1 : ℕ) ≤ n := by omega
  have hδ_lb' : 320 / Real.sqrt n ≤ δ := hδ_lb
  have hδ_ub' : δ ≤ 1/2 := by linarith
  -- envelopeW (matches LightEnvelopeBound).
  set envelopeW : Finset ℕ → ℝ := fun ℓ =>
        ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ,
            Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1) with henvelopeW_def
  -- Step 1+2: per-ℓ atypical mass ≤ 4·e^{-n/128}·envelopeW ℓ.
  have h_per_ell : ∀ ℓ : Finset ℕ,
      ((∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        +
       (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))
        ≤ 4 * Real.exp (-((n : ℝ) / 128)) * envelopeW ℓ := by
    intro ℓ
    have hA := pieceA_le_envelope n hn hmod δ hδ_lb' hδ_ub' ℓ
    have hB := pieceB_le_envelope n hn hmod δ hδ_lb' hδ_ub' ℓ
    simp only at hA hB
    rw [henvelopeW_def]
    simp only
    have h := add_le_add hA hB
    calc _ ≤ 2 * Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1))
            + 2 * Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1)) := h
      _ = 4 * Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1)) := by ring
  -- Step 3: sum over P_L, apply LightEnvelopeBound.
  have hexp_nn : (0 : ℝ) ≤ 4 * Real.exp (-((n : ℝ) / 128)) := by positivity
  have henv_nn : ∀ ℓ, 0 ≤ envelopeW ℓ := by
    intro ℓ; rw [henvelopeW_def]; simp only
    apply Finset.sum_nonneg; intro r' _
    apply Finset.prod_nonneg; intro j _
    exact (T4L1NormBoundAux.ellFactor_in_unit_interval n hn_one r' (j - 1)).1
  have h_sum_le :
      (∑ ℓ ∈ P_L,
          ((∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            +
           (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)))
        ≤ ∑ ℓ ∈ P_L, 4 * Real.exp (-((n : ℝ) / 128)) * envelopeW ℓ :=
    Finset.sum_le_sum (fun ℓ _ => h_per_ell ℓ)
  have h_factor :
      (∑ ℓ ∈ P_L, 4 * Real.exp (-((n : ℝ) / 128)) * envelopeW ℓ)
        = 4 * Real.exp (-((n : ℝ) / 128)) * (∑ ℓ ∈ P_L, envelopeW ℓ) := by
    rw [Finset.mul_sum]
  have hLEB := LightEnvelopeBound n hn hmod
  simp only at hLEB
  -- hLEB : ∑_{ℓ∈P_L} envelopeW ℓ ≤ n · e^{-√n/32}  (with matching defs)
  have h_env_sum : (∑ ℓ ∈ P_L, envelopeW ℓ) ≤ (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := by
    rw [henvelopeW_def, hP_L_def, hwidetildeMu_def, hS_er_def, hα_def, hc'_def]
    convert hLEB using 2
  -- Chain: ∑ ≤ 4 e^{-n/128} (∑ env) ≤ 4 e^{-n/128} (n e^{-√n/32}) ≤ (1/16) e^{-√n/4}.
  calc _ ≤ ∑ ℓ ∈ P_L, 4 * Real.exp (-((n : ℝ) / 128)) * envelopeW ℓ := h_sum_le
    _ = 4 * Real.exp (-((n : ℝ) / 128)) * (∑ ℓ ∈ P_L, envelopeW ℓ) := h_factor
    _ ≤ 4 * Real.exp (-((n : ℝ) / 128)) * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32))) := by
        exact mul_le_mul_of_nonneg_left h_env_sum hexp_nn
    _ ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 4)) := numeric_step n hn
