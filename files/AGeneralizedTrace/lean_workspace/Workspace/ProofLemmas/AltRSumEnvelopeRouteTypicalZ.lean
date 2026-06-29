import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.LightAtypicalZTail
import Workspace.ProofLemmas.LightAtypicalPerEll
import Workspace.ProofLemmas.T4L1NormBound

/-!
# AltRSumEnvelopeRouteTypicalZ — the honest "envelope route" bound (rare-ℓ half, TYPICAL z ≥ n/16)

This is the FAITHFUL triangle/factor "envelope route" bound used by the paper's §3.1
assembly for the RARE realizations, on the TYPICAL z-grid `z₋, z₊ ∈ Ico (n/16) (n/2+1)`
(i.e. `z ≥ n/16`).  Over this grid we bound

  ∑_{z₋∈G} ∑_{z₊∈G} |altRSum n δ α z₋ z₊ ℓ| ≤ √(2/(πn)) · envelopeW n α ℓ

where `envelopeW n α ℓ = ∑_{r∈Icc(-(n/4))(n/4)} ∏_{j∈ℓ} ellFactor n α r (j-1)`.

There is NO Fourier input and NO e^{-√n} decay here — this is the honest factor bound:
* `B1 = binPMFInt n (1/2) (r+n/2)` is bounded by the central-binomial-mode bound
  `√(2/(πn))` via `LightAtypicalPerEllProof.B1_le_sqrt`.
* each z-marginal sub-sum over `Ico (n/16) (n/2+1)` is `≤ 1` by enlarging to
  `Finset.range (n/2+1)` (a superset) and applying
  `LightAtypicalZTailProof.sum_binPMFInt_range_le_one` (a binomial PMF sub-sum ≤ 1).

The decay for the rare realizations is supplied DOWNSTREAM by `Σ_{rare ℓ} envelopeW ≤ rare-mass`,
NOT by this lemma.  The proof mirrors `AltRSumEnvelopeRouteTypicalProof.altRSum_envelope_route_typical`
verbatim, with the z-grid switched from `Finset.range (n/16)` (z < n/16) to the typical
`Finset.Ico (n/16) (n/2+1)` (z ≥ n/16), and the per-marginal PMF sub-sum `≤ 1` routed through a
subset-of-range step (mirroring `AltRSumLightAtypicalBoundFinal`'s `pieceB_factor_on_subrange`).

**z-grid choice.** `G := Finset.Ico (n/16) (n/2+1)` for BOTH `z₋` and `z₊` — the genuine typical
region matching the paper's typical region and the per-summand consumers.
-/

set_option maxHeartbeats 40000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace AltRSumEnvelopeRouteTypicalZProof


/-- **The honest envelope-route bound over the TYPICAL z-grid (z ≥ n/16, rare-ℓ half).**

For `n ≥ 10^12`, `n % 8 = 1`, `δ ∈ [320/√n, 1/2]`, and any `ℓ`, with
`α = (1/(4·exp 2·√(2π)))·√n`, the typical-z mass of `|altRSum|` is bounded by the
central-binomial factor `√(2/(πn))` times the envelope weight `envelopeW n α ℓ`.

The typical z-grid is `G = Finset.Ico (n/16) (n/2+1)` for both `z₋` and `z₊`. -/
lemma altRSum_envelope_route_typicalZ
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2)
    (ℓ : Finset ℕ) (hℓ_sub : ℓ ⊆ Finset.Icc 1 (n / 2)) (hℓ_par : sameParity ℓ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          |altRSum n δ α zMinus zPlus ℓ|)
      ≤ Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  -- Numeric setup (mirrors AltRSumEnvelopeRouteTypicalProof.altRSum_envelope_route_typical)
  have hn_pos : (0 : ℕ) < n := by omega
  have hn_one : (1 : ℕ) ≤ n := hn_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  set rRange : Finset ℤ := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) with hrRange_def
  set sq : ℝ := Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) with hsq_def
  have hsq_nn : 0 ≤ sq := Real.sqrt_nonneg _
  have hprod_nn : ∀ r, 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := by
    intro r
    apply Finset.prod_nonneg
    intro j _
    exact (T4L1NormBoundAux.ellFactor_in_unit_interval n hn_one r (j - 1)).1
  have hB1_le : ∀ r, binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ sq := fun r =>
    LightAtypicalPerEllProof.B1_le_sqrt n (by omega) r
  have hB1_nn : ∀ r, 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) := fun r =>
    LightAtypicalZTailProof.binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
  -- triangle inequality on the alternating r-sum
  have triangle : ∀ (zMinus zPlus : ℕ),
      |altRSum n δ α zMinus zPlus ℓ|
        ≤ ∑ r ∈ rRange, |Fterm n δ α r zMinus zPlus ℓ| := by
    intro zMinus zPlus
    unfold altRSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro r _
    rw [abs_mul]
    have h_pow_abs : |(-1 : ℝ) ^ r.natAbs| = 1 := by
      rcases Nat.even_or_odd r.natAbs with hev | hodd
      · rw [hev.neg_one_pow]; norm_num
      · rw [hodd.neg_one_pow]; norm_num
    rw [h_pow_abs, one_mul]
  -- |Fterm| = the product of the four nonneg factors
  have Fterm_eq : ∀ (r : ℤ) (zMinus zPlus : ℕ),
      |Fterm n δ α r zMinus zPlus ℓ|
        = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    intro r zMinus zPlus
    unfold Fterm
    have h_b1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) := hB1_nn r
    have h_b2_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus :=
      LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
      LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_prod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := hprod_nn r
    rw [abs_of_nonneg]
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg h_b1_nn h_b2_nn
    exact h_b3_nn
    exact h_prod_nn
  set G : ℤ → ℕ → ℕ → ℝ := fun r zMinus zPlus =>
    binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
    (∏ j ∈ ℓ, ellFactor n α r (j - 1)) with hG_def
  have altRSum_le : ∀ (zMinus zPlus : ℕ),
      |altRSum n δ α zMinus zPlus ℓ| ≤ ∑ r ∈ rRange, G r zMinus zPlus := by
    intro zMinus zPlus
    refine (triangle zMinus zPlus).trans ?_
    apply Finset.sum_le_sum
    intro r _
    rw [Fterm_eq r zMinus zPlus]
  -- Typical bound: z₋, z₊ ∈ Ico (n/16) (n/2+1)
  show (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            |altRSum n δ α zMinus zPlus ℓ|)
        ≤ sq * (∑ r ∈ rRange, ∏ j ∈ ℓ, ellFactor n α r (j - 1))
  have h_step1 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      |altRSum n δ α zMinus zPlus ℓ|)
                ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ r ∈ rRange, G r zMinus zPlus) := by
    apply Finset.sum_le_sum
    intro zMinus _
    apply Finset.sum_le_sum
    intro zPlus _
    exact altRSum_le zMinus zPlus
  refine h_step1.trans ?_
  have h_swap1 : ∀ zMinus, (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                            ∑ r ∈ rRange, G r zMinus zPlus)
                          = ∑ r ∈ rRange, ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                              G r zMinus zPlus := by
    intro zMinus
    exact Finset.sum_comm
  have h_step2 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ r ∈ rRange, G r zMinus zPlus)
              = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ r ∈ rRange,
                      ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1), G r zMinus zPlus) := by
    apply Finset.sum_congr rfl
    intros zMinus _
    exact h_swap1 zMinus
  rw [h_step2, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h_factor : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1), G r zMinus zPlus)
                = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    have hexpand : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1), G r zMinus zPlus)
        = ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_congr rfl; intros zMinus _
      apply Finset.sum_congr rfl; intros zPlus _
      rw [hG_def]; ring
    rw [hexpand]
    have hpull : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
        = (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
            (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros zMinus _
      rw [Finset.mul_sum]
    rw [hpull, ← Finset.sum_mul_sum]
    ring
  rw [h_factor]
  -- KEY DIFFERENCE: the z-marginal sub-sum over Ico (n/16) (n/2+1) is ≤ 1 by enlarging
  -- to Finset.range (n/2+1) (a superset) and applying sum_binPMFInt_range_le_one.
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
    apply Finset.sum_nonneg; intros _ _
    exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_le : (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 := by
    have hsubset : Finset.Ico (n / 16) (n / 2 + 1) ⊆ Finset.range (n / 2 + 1) := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]; omega
    calc (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
        ≤ (∑ zPlus ∈ Finset.range (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) (zPlus : ℤ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _ _
          exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
      _ ≤ 1 := LightAtypicalZTailProof.sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
    apply Finset.sum_nonneg; intros _ _
    exact LightAtypicalZTailProof.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hkey : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
              ≤ sq := by
    calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
        ≤ sq * 1 * 1 := by
          gcongr
          exact hB1_le r
      _ = sq := by ring
  calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ sq * (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        apply mul_le_mul_of_nonneg_right hkey (hprod_nn r)

end AltRSumEnvelopeRouteTypicalZProof
