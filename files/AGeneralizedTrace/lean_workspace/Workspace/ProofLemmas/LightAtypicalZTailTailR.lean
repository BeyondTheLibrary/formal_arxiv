import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.T4L1NormBound
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.CentralBinomialUpperTailWide
import Workspace.ProofLemmas.LightAtypicalZTail

/-!
# LightAtypicalZTailTailR — the TAIL-`r` half of the light-family atypical-z bound

`LightAtypicalZTail` (F45) closes the ATYPICAL-`r` sub-ranges
`rA2 = Icc (-(n/16)) (n/4)` (Piece A, z₋-tail) and `rB2 = Icc (-(n/4)) (n/16)`
(Piece B, z₊-tail): there the inner z-tail `∑_{z<n/16} B2/B3` is itself
`≤ e^{-n/128}` (`AtypicalZTailBound` / `AtypicalZPlusTailBound`), giving an
envelope-weighted `e^{-n/128} · envelopeW ℓ` bound.

This file closes the COMPLEMENTARY TAIL-`r` sub-ranges
`rA1 = Icc (-(n/4)) (-(n/16) - 1)` (Piece A) and
`rB1 = Icc ((n/16) + 1) (n/4)` (Piece B), where the inner z-tail bound does NOT
apply (`r` is too far from `0`), but where the *central* binomial factor
`B1(r) = binPMFInt n (1/2) (r + n/2)` is itself in its LOWER tail
(`r` far from `0` ⇒ `r + n/2` far from the mode `n/2` ⇒ small).
`CentralBinomialLowerTailWide` / `CentralBinomialUpperTailWide` give
`∑_{rA1} B1 ≤ e^{-n/128}` and `∑_{rB1} B1 ≤ e^{-n/128}`.

## The key envelope-weighting trick (the gap F45 left)

A *flat* bound `∏ ellFactor ≤ 1` on `rA1/rB1` would give a per-`ℓ` mass of
`e^{-n/128}` with no `ℓ`-dependence, which blows up when summed over the light
family `P_L` (size `~ 2^{n/2}`).  To keep the envelope weighting we instead use:

* `∑_{z<n/16} B2(r) ≤ 1`  (z-sum of a sub-PMF), and
* `∏_{j∈ℓ} ellFactor n α r j ≤ envelopeW ℓ`  — a SINGLE term of the nonneg sum
  `envelopeW ℓ = ∑_{r'∈rRange} ∏_{j∈ℓ} ellFactor n α r' j` is `≤` the whole sum.

So per-`r`: `B1(r) · (∑_{z<n/16} B2) · ∏ ellFactor(r) ≤ B1(r) · 1 · envelopeW ℓ`.
Summing over `rA1` and factoring `envelopeW ℓ` out:
`∑_{rA1} B1(r) · (∑ B2) · ∏ ellFactor(r) ≤ envelopeW ℓ · ∑_{rA1} B1 ≤ e^{-n/128} · envelopeW ℓ`.

This is envelope-weighted (carries `envelopeW ℓ`, composing with `LightEnvelopeBound`)
AND carries the `e^{-n/128}` decay from `B1`'s central lower tail — exactly the
piece F45's `e^{-n/128} · envelopeW` shape needs on the tail-`r` window.
-/

set_option maxHeartbeats 32000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace LightAtypicalZTailTailRProof

/-- A single `∏ ellFactor` evaluated at a fixed `r ∈ rRange` is `≤` the envelope
sum `envelopeW ℓ = ∑_{r'∈rRange} ∏ ellFactor(r')` (all terms nonneg). -/
lemma prod_ellFactor_le_envelopeW
    (n : ℕ) (hn : 1 ≤ n) (ℓ : Finset ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4)) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    ∏ j ∈ ℓ, ellFactor n α r (j - 1)
      ≤ ∑ r' ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ, ellFactor n α r' (j - 1) := by
  intro α
  apply Finset.single_le_sum (f := fun r' => ∏ j ∈ ℓ, ellFactor n α r' (j - 1))
  · intro r' _
    exact LightAtypicalZTailProof.prod_ellFactor_nonneg n hn r' ℓ
  · exact hr

/-- **Envelope-weighted Piece-A bound on the TAIL-`r` sub-range `rA1`.**
On `rA1 = Icc (-(n/4)) (-(n/16) - 1)` the central factor `B1` is in its lower
tail (`∑_{rA1} B1 ≤ e^{-n/128}` by `CentralBinomialLowerTailWide`).  Keeping the
envelope factor `∏ ellFactor` (via `∏ ellFactor(r) ≤ envelopeW ℓ`) and bounding
`∑_{z<n/16} B2 ≤ 1`, the factored Piece-A mass on `rA1` is
`≤ e^{-n/128} · envelopeW ℓ`. -/
lemma pieceA_tailR_envelope_bound
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      ≤ Real.exp (-((n : ℝ) / 128)) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  set W : ℝ := ∑ r' ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      ∏ j ∈ ℓ, ellFactor n α r' (j - 1) with hW_def
  have hW_nn : 0 ≤ W := by
    rw [hW_def]; apply Finset.sum_nonneg; intro r' _
    exact LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r' ℓ
  -- subset rA1 ⊆ rRange
  have hsub : Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1)
              ⊆ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    refine ⟨hr.1, ?_⟩
    have h1 : -((n : ℤ) / 16) - 1 ≤ (n : ℤ) / 4 := by omega
    linarith [hr.2]
  -- Per-r: B1·(∑z₋ B2)·∏ellFactor ≤ B1 · W.
  have h_per_r : ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * W := by
    intro r hr
    have hrR : r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := hsub hr
    have hB1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
      LightAtypicalZTailProof.binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
    have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) :=
      LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r ℓ
    have hB2sum_le : (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 :=
      LightAtypicalZTailProof.sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
    have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
      apply Finset.sum_nonneg; intro _ _
      exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have hprod_le_W : (∏ j ∈ ℓ, ellFactor n α r (j - 1)) ≤ W :=
      prod_ellFactor_le_envelopeW n hn_one ℓ r hrR
    -- B1·(∑B2)·∏ ≤ B1·1·W = B1·W
    calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1))
        ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * 1 * W := by
          gcongr
      _ = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * W := by ring
  -- Sum the per-r bound; factor W; then ∑_{rA1} B1 ≤ e^{-n/128}.
  apply le_trans (Finset.sum_le_sum h_per_r)
  rw [← Finset.sum_mul]
  have hB1tail : (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
        binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4))) ≤ Real.exp (-((n : ℝ) / 128)) :=
    CentralBinomialLowerTailWideHalf n hn hmod
  exact mul_le_mul_of_nonneg_right hB1tail hW_nn

/-- **Envelope-weighted Piece-B bound on the TAIL-`r` sub-range `rB1`.**
Symmetric to `pieceA_tailR_envelope_bound`: on `rB1 = Icc ((n/16)+1) (n/4)` the
central factor `B1` is in its UPPER tail (`∑_{rB1} B1 ≤ e^{-n/128}` by
`CentralBinomialUpperTailWide`).  Keeping the envelope factor and bounding
`∑_{z<n/16} B3 ≤ 1`, the factored Piece-B mass on `rB1` is
`≤ e^{-n/128} · envelopeW ℓ`. -/
lemma pieceB_tailR_envelope_bound
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hmod : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      ≤ Real.exp (-((n : ℝ) / 128)) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_one : (1 : ℕ) ≤ n := by omega
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  set W : ℝ := ∑ r' ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
      ∏ j ∈ ℓ, ellFactor n α r' (j - 1) with hW_def
  have hW_nn : 0 ≤ W := by
    rw [hW_def]; apply Finset.sum_nonneg; intro r' _
    exact LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r' ℓ
  have hsub : Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4)
              ⊆ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    refine ⟨?_, hr.2⟩
    have h1 : -((n : ℤ) / 4) ≤ (n : ℤ) / 16 + 1 := by omega
    linarith [hr.1]
  have h_per_r : ∀ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * W := by
    intro r hr
    have hrR : r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := hsub hr
    have hB1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
      LightAtypicalZTailProof.binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
    have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) :=
      LightAtypicalZTailProof.prod_ellFactor_nonneg n hn_one r ℓ
    have hB3sum_le : (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 :=
      LightAtypicalZTailProof.sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
    have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_nonneg; intro _ _
      exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have hprod_le_W : (∏ j ∈ ℓ, ellFactor n α r (j - 1)) ≤ W :=
      prod_ellFactor_le_envelopeW n hn_one ℓ r hrR
    calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1))
        ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * 1 * W := by
          gcongr
      _ = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * W := by ring
  apply le_trans (Finset.sum_le_sum h_per_r)
  rw [← Finset.sum_mul]
  have hB1tail : (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
        binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4))) ≤ Real.exp (-((n : ℝ) / 128)) :=
    CentralBinomialUpperTailWideHalf n hn hmod
  exact mul_le_mul_of_nonneg_right hB1tail hW_nn

end LightAtypicalZTailTailRProof

/-- **TAIL-`r` half of the light-family atypical-z bound (envelope-weighted).**

On the TAIL-`r` sub-ranges — `rA1 = Icc (-(n/4)) (-(n/16) - 1)` (Piece A, z₋-tail)
and `rB1 = Icc ((n/16)+1) (n/4)` (Piece B, z₊-tail) — the per-`ℓ` factored
atypical-z mass, KEEPING the envelope factor `∏_{j∈ℓ} ellFactor n α r j`, is
bounded by `2 · e^{-n/128} · envelopeW ℓ`, where
`envelopeW ℓ = ∑_{r∈rRange} ∏_{j∈ℓ} ellFactor n α r j`.

Here the decay `e^{-n/128}` comes from the central binomial factor `B1`'s LOWER /
UPPER tail (`CentralBinomialLowerTailWide` / `CentralBinomialUpperTailWide`),
NOT from the inner z-tail (which does not apply on these `r`-ranges).  The
envelope weighting is preserved via `∏ ellFactor(r) ≤ envelopeW ℓ` (a single
nonneg term `≤` the whole sum), so this composes with `LightEnvelopeBound`
exactly as the F45 atypical-`r` half does.

Adding this to `LightAtypicalZTail` (the atypical-`r` half, ranges `rA2/rB2`)
covers the FULL `r`-range `Icc (-(n/4)) (n/4)` for both pieces, giving a per-`ℓ`
atypical-z mass `≤ 4 · e^{-n/128} · envelopeW ℓ`. -/
theorem LightAtypicalZTailTailR :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt n ≤ δ → δ ≤ 1/2 →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      ∀ (ℓ : Finset ℕ),
        ((∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1),
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
          +
         (∑ r ∈ Finset.Icc ((n : ℤ) / 16 + 1) ((n : ℤ) / 4),
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1))))
        ≤ 2 * Real.exp (-((n : ℝ) / 128)) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro n hn hn8 δ hδ_lb hδ_ub α ℓ
  have hA := LightAtypicalZTailTailRProof.pieceA_tailR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  have hB := LightAtypicalZTailTailRProof.pieceB_tailR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  simp only at hA hB
  have h := add_le_add hA hB
  have heq : Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, ellFactor n α r (j - 1))
            + Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, ellFactor n α r (j - 1))
          = 2 * Real.exp (-((n : ℝ) / 128)) *
              (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by ring
  rw [heq] at h
  exact h
