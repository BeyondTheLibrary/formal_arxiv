import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.AtypicalZTailBound
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.T4L1NormBound

/-!
# LightAtypicalZTail — strengthened per-`ℓ` atypical-z bound carrying the `e^{-n/128}` z-tail

`LightAtypicalPerEll` (F4) bounds the atypical-`z` `L¹` alt-sum only TRIVIALLY
(z-sum `≤ 1`, `B1 ≤ √(2/πn)`), losing the binomial lower-tail `e^{-n/128}` over the
atypical deletion range `z < n/16`.  This file threads `AtypicalZTailBound` /
`AtypicalZPlusTailBound` (the binomial lower-tail over `z < n/16`) through the per-summand
factorization on the ATYPICAL-`r` sub-range (the range where the z-tail bound applies),
while KEEPING the envelope factor `∏_{j∈ℓ} ellFactor n α r (j - 1)` (rather than dropping it via
`|∏ ellFactor| ≤ 1` as `HeavyAtypicalBound` does).

The key sorry-free result is `lightAtypicalZTail_pieceA_atypR` /
`lightAtypicalZTail_pieceB_atypR`: on the atypical-`r` sub-range the per-`ℓ` atypical-z
contribution is bounded by `e^{-n/128} · (envelope factor over that sub-range)`, hence by
`e^{-n/128} · envelopeW ℓ`.  This is the z-tail-carrying, envelope-weighted bound that F4
lacks.  Combined with the central-binomial tail on the complementary `r` sub-range
(`CentralBinomialLowerTailWide` / `CentralBinomialUpperTailWide`) one recovers the full
atypical absorption; the envelope-weighted atypical-`r` half is what composes with
`LightEnvelopeBound`.
-/

set_option maxHeartbeats 32000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace LightAtypicalZTailProof

/- Nonneg of binPMFInt. -/
lemma binPMFInt_nonneg' (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (z : ℤ) :
    0 ≤ binPMFInt m p z := by
  unfold binPMFInt
  split_ifs
  · unfold binPMF
    split_ifs
    · apply mul_nonneg; apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact pow_nonneg hp _
      · exact pow_nonneg (by linarith) _
    · exact le_refl 0
  · exact le_refl 0

lemma binPMF_nonneg' (m z : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMF m p z := by
  unfold binPMF
  split_ifs
  · apply mul_nonneg; apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg hp _
    · exact pow_nonneg (by linarith) _
  · exact le_refl 0

/- Sum of binPMFInt over Finset.range k is ≤ 1. -/
lemma sum_binPMFInt_range_le_one
    (m : ℕ) (p : ℝ) (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (k : ℕ) :
    (∑ z ∈ Finset.range k, binPMFInt m p (z : ℤ)) ≤ 1 := by
  have h_split : (∑ z ∈ Finset.range k, binPMFInt m p (z : ℤ))
                = (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMFInt m p (z : ℤ))
                  + (∑ z ∈ Finset.range k \ Finset.range (m + 1), binPMFInt m p (z : ℤ)) := by
    rw [← Finset.sum_inter_add_sum_diff (Finset.range k) (Finset.range (m + 1))
        (f := fun z => binPMFInt m p (z : ℤ))]
  have h_outside_zero : (∑ z ∈ Finset.range k \ Finset.range (m + 1), binPMFInt m p (z : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hz
    have hz_gt : (z : ℤ) > (m : ℤ) := by
      have : ¬ z < m + 1 := hz.2
      have : m + 1 ≤ z := by omega
      exact_mod_cast (by omega : (m : ℤ) < z)
    unfold binPMFInt
    rw [if_neg (by push_neg; intro _; linarith)]
  rw [h_split, h_outside_zero, add_zero]
  have h_eq : (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMFInt m p (z : ℤ))
            = (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMF m p z) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [Finset.mem_inter, Finset.mem_range] at hz
    unfold binPMFInt
    have h0 : (0 : ℤ) ≤ (z : ℤ) := Int.ofNat_nonneg _
    have h1 : (z : ℤ) ≤ (m : ℤ) := by
      have : z ≤ m := by omega
      exact_mod_cast this
    rw [if_pos ⟨h0, h1⟩]
    simp [Int.toNat_natCast]
  rw [h_eq]
  have h_subset : Finset.range k ∩ Finset.range (m + 1) ⊆ Finset.range (m + 1) :=
    Finset.inter_subset_right
  have h_full_sum : (∑ z ∈ Finset.range (m + 1), binPMF m p z) = 1 := by
    have h1 : (∑ z ∈ Finset.range (m + 1), (m.choose z : ℝ) * p^z * (1-p)^(m-z))
              = (p + (1-p))^m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro z _; ring
    have h2 : (∑ z ∈ Finset.range (m + 1), binPMF m p z)
              = (∑ z ∈ Finset.range (m + 1), (m.choose z : ℝ) * p^z * (1-p)^(m-z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mem_range] at hz
      unfold binPMF
      rw [if_pos (by omega)]
    rw [h2, h1]
    rw [show p + (1 - p) = 1 from by ring]
    exact one_pow m
  calc (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMF m p z)
      ≤ (∑ z ∈ Finset.range (m + 1), binPMF m p z) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
        intros z _ _
        exact binPMF_nonneg' m z p hp_lb hp_ub
    _ = 1 := h_full_sum

/-- `B1(r) = binPMFInt (n/2) (1/2) (r + n/4) ≤ 1` (a fortiori ≤ √(2/(π·(n/2))) ≤ 1).
Requires `1 ≤ n/2`, i.e. `n ≥ 2`. -/
lemma B1_le_one (n : ℕ) (hn : 1 ≤ n / 2) (r : ℤ) :
    binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ 1 := by
  unfold binPMFInt
  set m : ℕ := n / 2 with hm
  split_ifs with hcase
  · unfold binPMF
    split_ifs with hcase2
    · set k : ℤ := r + ((n : ℤ) / 4) with hk
      have hbin := BinomialPmfMaxBound m hn k.toNat
      have hpow : ((1 : ℝ) / 2) ^ k.toNat * (1 - 1 / 2) ^ (m - k.toNat)
          = (2 ^ m : ℝ)⁻¹ := by
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
        rw [show ((1 : ℝ) / 2) ^ k.toNat * (1 / 2) ^ (m - k.toNat)
              = (1 / 2) ^ (k.toNat + (m - k.toNat)) from by rw [← pow_add]]
        rw [Nat.add_sub_of_le hcase2]
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
        rw [inv_pow]
      have hrearr : (m.choose k.toNat : ℝ) * (1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (m - k.toNat)
          = (m.choose k.toNat : ℝ) * ((1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (m - k.toNat)) := by ring
      rw [hrearr, hpow]
      have hsqrt_le_one : Real.sqrt (2 / (Real.pi * m)) ≤ 1 := by
        have hn_pos : (0:ℝ) < m := by exact_mod_cast hn
        rw [Real.sqrt_le_one, div_le_one (by positivity)]
        have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
        have hn1 : (1:ℝ) ≤ m := by exact_mod_cast hn
        nlinarith [hpi, hn1]
      linarith [hbin]
    · norm_num
  · norm_num

/-- Nonneg of the per-`ℓ` product of `ellFactor`s (witness-index-aligned `j-1` form). -/
lemma prod_ellFactor_nonneg (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (ℓ : Finset ℕ) :
    0 ≤ ∏ j ∈ ℓ, ellFactor n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1) := by
  apply Finset.prod_nonneg
  intro j _
  exact (T4L1NormBoundAux.ellFactor_in_unit_interval n hn r (j - 1)).1

/-- The per-`ℓ` envelope-factorisation of the atypical Piece-A `L¹` mass, on a fixed
`r`-subrange `rSub`.  Identical to `LightAtypicalPerEll`'s factorisation but parametrised
over a generic finite `rSub` so we can specialise to the atypical-`r` window. -/
lemma pieceA_factor_on_subrange
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2)
    (ℓ : Finset ℕ) (rSub : Finset ℤ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.range (n / 16),
        ∑ zPlus ∈ Finset.range (n / 2 + 1),
          ∑ r ∈ rSub,
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
              (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      ≤ ∑ r ∈ rSub,
          binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro α
  have hn_pos : (0 : ℕ) < n := by omega
  have hn_one : (1 : ℕ) ≤ n := hn_pos
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  -- Reorder: ∑_{z₋} ∑_{z₊} ∑_r = ∑_r ∑_{z₋} ∑_{z₊}, then factor each summand.
  calc (∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            ∑ r ∈ rSub,
              binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
      = ∑ r ∈ rSub,
          ∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        rw [show (∑ zMinus ∈ Finset.range (n / 16),
                  ∑ zPlus ∈ Finset.range (n / 2 + 1),
                    ∑ r ∈ rSub,
                      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
              = (∑ zMinus ∈ Finset.range (n / 16),
                  ∑ r ∈ rSub,
                    ∑ zPlus ∈ Finset.range (n / 2 + 1),
                      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                        (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
            from by
              apply Finset.sum_congr rfl; intro zMinus _; rw [Finset.sum_comm]]
        rw [Finset.sum_comm]
    _ ≤ ∑ r ∈ rSub,
          binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        apply Finset.sum_le_sum
        intro r _
        -- factor B1 and ∏ellFactor out of the z₋,z₊ double sum, bound ∑_{z₊}B3 ≤ 1
        have hB1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
          binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
        have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := prod_ellFactor_nonneg n hn_one r ℓ
        have hB3sum_le : (∑ zPlus ∈ Finset.range (n / 2 + 1),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 :=
          sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
        have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 2 + 1),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
          apply Finset.sum_nonneg; intro _ _
          exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
        -- inner double sum = B1 * (∑_{z₋} B2) * (∑_{z₊} B3) * ∏ellFactor
        have hexpand :
            (∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
              = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
          have hstep : (∑ zMinus ∈ Finset.range (n / 16),
                          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                        (∑ zPlus ∈ Finset.range (n / 2 + 1),
                          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
                      = ∑ zMinus ∈ Finset.range (n / 16),
                          ∑ zPlus ∈ Finset.range (n / 2 + 1),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
            Finset.sum_mul_sum _ _ _ _
          rw [show binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1))
                = (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
                  ((∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) from by ring]
          rw [hstep, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro zMinus _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro zPlus _
          ring
        rw [hexpand]
        -- now bound the B3-sum factor by 1
        have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
          apply Finset.sum_nonneg; intro _ _
          exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
        have hfront_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
              (∑ zMinus ∈ Finset.range (n / 16),
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := mul_nonneg hB1_nn hB2sum_nn
        calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1))
            ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                1 *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
              gcongr
          _ = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by ring

/-- Triangle bound: `|altRSum|` over the atypical Piece-A z-range is dominated by the
factored triple-product sum over `r`, restricted to any `rSub ⊇ rRange` is unnecessary —
we use the full `rRange`. -/
lemma altRSum_pieceA_le
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ zMinus ∈ Finset.range (n / 16),
        ∑ zPlus ∈ Finset.range (n / 2 + 1),
          |altRSum n δ α zMinus zPlus ℓ|)
      ≤ (∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
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
  -- |altRSum| ≤ ∑_r |Fterm| = ∑_r (B1·B2·B3·∏ellFactor)
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
    binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
  have h_b2_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus :=
    binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
    binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have h_prod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := prod_ellFactor_nonneg n hn_one r ℓ
  rw [abs_of_nonneg]
  apply mul_nonneg; apply mul_nonneg; apply mul_nonneg h_b1_nn h_b2_nn
  · exact h_b3_nn
  · exact h_prod_nn

/-- **Z-tail-carrying, envelope-weighted Piece-A bound on the atypical-`r` sub-range.**
On `rA2 = Icc (-(n/16)) (n/4)` the inner z₋-tail sum `∑_{z₋<n/16} B2(r)` is bounded by
`e^{-n/128}` (the binomial lower tail, `AtypicalZTailBound`), so the factored Piece-A mass
on `rA2` — KEEPING the envelope factor `∏_{j∈ℓ} ellFactor` — is at most
`e^{-n/128} · envelopeW ℓ`.  This is exactly the bound `LightAtypicalPerEll` (F4) was
missing: it carries the `e^{-n/128}` z-tail instead of the trivial `√(2/πn)`. -/
lemma pieceA_atypR_envelope_bound
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ r ∈ Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4),
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
  have hδ_pos : 0 < δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-((n : ℝ) / 128)) := (Real.exp_pos _).le
  -- Subset relation rA2 ⊆ rRange.
  have hsub : Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4)
              ⊆ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    constructor
    · have : -((n : ℤ) / 4) ≤ -((n : ℤ) / 16) := by omega
      linarith [hr.1]
    · exact hr.2
  -- Per-r bound: B1·(∑z₋ B2)·∏ellFactor ≤ e^{-n/128}·∏ellFactor.
  have h_per_r : ∀ r ∈ Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4),
      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ Real.exp (-((n : ℝ) / 128)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr_lb : -((n : ℤ) / 16) ≤ r := hr.1
    have hr_ub : r ≤ (n : ℤ) / 4 := hr.2
    have hB1_le : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ 1 :=
      B1_le_one n (by omega) r
    have hB1_nn : 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) :=
      binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
    have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := prod_ellFactor_nonneg n hn_one r ℓ
    -- z₋-tail bound via AtypicalZTailBound (range r ∈ [-(n/8)+(n/16), n/4] covers [-(n/16), n/4]).
    have h_lb_target : -((n : ℤ) / 8) + ((n : ℤ) / 16) ≤ r := by
      have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    have hB2sum_le : (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ Real.exp (-((n : ℝ) / 128)) :=
      AtypicalZTailBound n hn hn8 δ hδ_pos hδ_ub r h_lb_target hr_ub
    have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
      apply Finset.sum_nonneg; intro _ _
      exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    -- B1·(∑z₋ B2) ≤ 1·e^{-n/128} = e^{-n/128}
    have hfront : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus)
        ≤ Real.exp (-((n : ℝ) / 128)) := by
      calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus)
          ≤ 1 * Real.exp (-((n : ℝ) / 128)) := by
            apply mul_le_mul hB1_le hB2sum_le hB2sum_nn (by norm_num)
        _ = Real.exp (-((n : ℝ) / 128)) := by ring
    exact mul_le_mul_of_nonneg_right hfront hprod_nn
  -- Sum the per-r bound over rA2, then extend the envelope sum to rRange.
  apply le_trans (Finset.sum_le_sum h_per_r)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hexp_nn
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro r _ _; exact prod_ellFactor_nonneg n hn_one r ℓ

/-- **Z-tail-carrying, envelope-weighted Piece-B bound on the atypical-`r` sub-range.**
Symmetric to `pieceA_atypR_envelope_bound`: on `rB2 = Icc (-(n/4)) (n/16)` the inner
z₊-tail sum `∑_{z₊<n/16} B3(r)` is `≤ e^{-n/128}` (`AtypicalZPlusTailBound`), so the
factored Piece-B mass on `rB2` (KEEPING the envelope factor) is `≤ e^{-n/128} · envelopeW ℓ`. -/
lemma pieceB_atypR_envelope_bound
    (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (hn8 : n % 8 = 1)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16),
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
  have hδ_pos : 0 < δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-((n : ℝ) / 128)) := (Real.exp_pos _).le
  have hsub : Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16)
              ⊆ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    refine ⟨hr.1, ?_⟩
    have : (n : ℤ) / 16 ≤ (n : ℤ) / 4 := by omega
    linarith [hr.2]
  have h_per_r : ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16),
      binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
        (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
        (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ Real.exp (-((n : ℝ) / 128)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr_lb : -((n : ℤ) / 4) ≤ r := hr.1
    have hr_ub : r ≤ (n : ℤ) / 16 := hr.2
    have hB1_le : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ 1 :=
      B1_le_one n (by omega) r
    have hprod_nn : 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := prod_ellFactor_nonneg n hn_one r ℓ
    -- z₊-tail bound via AtypicalZPlusTailBound (needs r ≤ (n/8)-(n/16); covers r ≤ n/16).
    have h_ub_target : r ≤ ((n : ℤ) / 8) - ((n : ℤ) / 16) := by
      have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have h_2n16_le_n8 : 2 * ((n : ℤ) / 16) ≤ (n : ℤ) / 8 := by omega
      omega
    have hB3sum_le : (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ Real.exp (-((n : ℝ) / 128)) :=
      AtypicalZPlusTailBound n hn hn8 δ hδ_pos hδ_ub r hr_lb h_ub_target
    have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_nonneg; intro _ _
      exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have hfront : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zPlus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
        ≤ Real.exp (-((n : ℝ) / 128)) := by
      calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
          ≤ 1 * Real.exp (-((n : ℝ) / 128)) := by
            apply mul_le_mul hB1_le hB3sum_le hB3sum_nn (by norm_num)
        _ = Real.exp (-((n : ℝ) / 128)) := by ring
    exact mul_le_mul_of_nonneg_right hfront hprod_nn
  apply le_trans (Finset.sum_le_sum h_per_r)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hexp_nn
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro r _ _; exact prod_ellFactor_nonneg n hn_one r ℓ

end LightAtypicalZTailProof

/-- **Strengthened per-`ℓ` atypical-z bound carrying the `e^{-n/128}` z-tail (envelope-weighted).**

On the ATYPICAL-`r` sub-ranges — `rA2 = Icc (-(n/16)) (n/4)` for the z₋-tail (Piece A) and
`rB2 = Icc (-(n/4)) (n/16)` for the z₊-tail (Piece B) — the per-`ℓ` factored atypical-z mass,
KEEPING the envelope factor `∏_{j∈ℓ} ellFactor n α r (j - 1)`, is bounded by
`2 · e^{-n/128} · envelopeW ℓ`, where `envelopeW ℓ = ∑_r ∏_{j∈ℓ} ellFactor n α r (j - 1)`.

This is exactly the bound `LightAtypicalPerEll` (F4) lacked: it carries the binomial
lower-tail `e^{-n/128}` over the atypical deletion range `z < n/16` (via
`AtypicalZTailBound` / `AtypicalZPlusTailBound`) instead of the trivial `√(2/πn)`, while
retaining the envelope factor needed to compose with `LightEnvelopeBound`.  Because
`e^{-n/128}` is exponential in `n` (dwarfing the target's `e^{-√n/4}`), composing this with
`∑_{ℓ∈P_L} envelopeW ℓ ≤ n·e^{-√n/32}` closes the light-family atypical absorption on the
atypical-`r` window. -/
theorem LightAtypicalZTail :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt n ≤ δ → δ ≤ 1/2 →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      ∀ (ℓ : Finset ℕ),
        ((∑ r ∈ Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4),
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1)))
          +
         (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16),
            binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
            (∏ j ∈ ℓ, ellFactor n α r (j - 1))))
        ≤ 2 * Real.exp (-((n : ℝ) / 128)) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              ∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
  intro n hn hn8 δ hδ_lb hδ_ub α ℓ
  have hA := LightAtypicalZTailProof.pieceA_atypR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
  have hB := LightAtypicalZTailProof.pieceB_atypR_envelope_bound n hn hn8 δ hδ_lb hδ_ub ℓ
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
