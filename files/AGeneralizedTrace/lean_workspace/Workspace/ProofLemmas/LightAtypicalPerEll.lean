import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.T4L1NormBound

/-!
# LightAtypicalPerEll — per-`ℓ` envelope-weighted atypical bound

For any support `ℓ`, the atypical-`z` contribution of `|altRSum|` is bounded
proportionally to the per-`ℓ` envelope
`envelopeW ℓ := ∑_r ∏_{j∈ℓ} ellFactor n α r j`.

The bound is
  (Piece A) + (Piece B) ≤ 2 · √(2/(π·(n/2))) · envelopeW ℓ
with NO "light" hypothesis on `ℓ` — it holds for every `ℓ`.
(The first factor of `Fterm` is now the `Bin(n/2,1/2)` offset weight, so its mode bound is
`√(2/(π·(n/2)))` ≈ √2 larger than the old `√(2/(πn))`.)
-/

set_option maxHeartbeats 32000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace LightAtypicalPerEllProof

/- Nonneg of binPMFInt -/
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

/- Sum over Ico of binPMFInt ≤ 1. -/
lemma sum_binPMFInt_Ico_le_one
    (m : ℕ) (p : ℝ) (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (a b : ℕ) :
    (∑ z ∈ Finset.Ico a b, binPMFInt m p (z : ℤ)) ≤ 1 := by
  by_cases hab : a ≤ b
  · have h_eq : Finset.range b = Finset.Ico 0 a ∪ Finset.Ico a b := by
      ext x
      simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
      omega
    have h_dis : Disjoint (Finset.Ico 0 a) (Finset.Ico a b) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      rw [Finset.mem_Ico] at hx1 hx2; omega
    have h_sum_split : (∑ z ∈ Finset.range b, binPMFInt m p (z : ℤ))
                  = (∑ z ∈ Finset.Ico 0 a, binPMFInt m p (z : ℤ))
                    + (∑ z ∈ Finset.Ico a b, binPMFInt m p (z : ℤ)) := by
      rw [h_eq, Finset.sum_union h_dis]
    have h_first_nn : 0 ≤ (∑ z ∈ Finset.Ico 0 a, binPMFInt m p (z : ℤ)) := by
      apply Finset.sum_nonneg
      intro z _
      exact binPMFInt_nonneg' m p hp_lb hp_ub _
    have h_full := sum_binPMFInt_range_le_one m p hp_lb hp_ub b
    linarith
  · push_neg at hab
    have : Finset.Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    norm_num

/-- `B1(r) = binPMFInt (n/2) (1/2) (r + n/4) ≤ √(2/(π·(n/2)))` for all `r`
(the central-binomial mode bound for `Bin(n/2, 1/2)` — the new first factor of `Fterm`).
Requires `1 ≤ n/2`, i.e. `n ≥ 2`. -/
lemma B1_le_sqrt (n : ℕ) (hn : 1 ≤ n / 2) (r : ℤ) :
    binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) := by
  unfold binPMFInt
  set m : ℕ := n / 2 with hm
  set k : ℤ := r + ((n : ℤ) / 4) with hk
  split_ifs with hcase
  · unfold binPMF
    split_ifs with hcase2
    · have hbin := BinomialPmfMaxBound m hn k.toNat
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
      exact hbin
    · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

/-- `√(2/(πn)) ≤ 1` for `n ≥ 1`. -/
lemma sqrt_two_div_pi_n_le_one (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 / (Real.pi * n)) ≤ 1 := by
  have hn_pos : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_le_one]
  rw [div_le_one (by positivity)]
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [hpi, hn1]

/-- **Piece A bound**, extracted as a standalone lemma so it elaborates on its own. -/
private lemma pieceA_lemma (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    (∑ zMinus ∈ Finset.range (n / 16),
        ∑ zPlus ∈ Finset.range (n / 2 + 1),
          |altRSum n δ
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
            zMinus zPlus ℓ|)
      ≤ Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ,
              ellFactor n
                ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1)) := by
  -- Numeric setup
  have hn_pos : (0 : ℕ) < n := by omega
  have hn_one : (1 : ℕ) ≤ n := hn_pos
  have hn_half : (1 : ℕ) ≤ n / 2 := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα_def
  set rRange : Finset ℤ := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) with hrRange_def
  set sq : ℝ := Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) with hsq_def
  have hsq_nn : 0 ≤ sq := Real.sqrt_nonneg _
  have hprod_nn : ∀ r, 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := by
    intro r
    apply Finset.prod_nonneg
    intro j _
    have h := (T4L1NormBoundAux.ellFactor_in_unit_interval n hn_one r (j - 1))
    simp only at h
    exact h.1
  have hB1_le : ∀ r, binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ sq := fun r =>
    B1_le_sqrt n hn_half r
  have hB1_nn : ∀ r, 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) := fun r =>
    binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
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
      binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
      binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
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
  -- Piece A bound
  show (∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |altRSum n δ α zMinus zPlus ℓ|)
        ≤ sq * (∑ r ∈ rRange, ∏ j ∈ ℓ, ellFactor n α r (j - 1))
  have h_step1 : (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ zPlus ∈ Finset.range (n / 2 + 1),
                      |altRSum n δ α zMinus zPlus ℓ|)
                ≤ (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ zPlus ∈ Finset.range (n / 2 + 1),
                      ∑ r ∈ rRange, G r zMinus zPlus) := by
    apply Finset.sum_le_sum
    intro zMinus _
    apply Finset.sum_le_sum
    intro zPlus _
    exact altRSum_le zMinus zPlus
  refine h_step1.trans ?_
  have h_swap1 : ∀ zMinus, (∑ zPlus ∈ Finset.range (n / 2 + 1),
                            ∑ r ∈ rRange, G r zMinus zPlus)
                          = ∑ r ∈ rRange, ∑ zPlus ∈ Finset.range (n / 2 + 1),
                              G r zMinus zPlus := by
    intro zMinus
    exact Finset.sum_comm
  have h_step2 : (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ zPlus ∈ Finset.range (n / 2 + 1),
                      ∑ r ∈ rRange, G r zMinus zPlus)
              = (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ r ∈ rRange,
                      ∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus) := by
    apply Finset.sum_congr rfl
    intros zMinus _
    exact h_swap1 zMinus
  rw [h_step2, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h_factor : (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus)
                = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    have hexpand : (∑ zMinus ∈ Finset.range (n / 16),
                    ∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus)
        = ∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_congr rfl; intros zMinus _
      apply Finset.sum_congr rfl; intros zPlus _
      rw [hG_def]; ring
    rw [hexpand]
    have hpull : (∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
        = (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
            (∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros zMinus _
      rw [Finset.mul_sum]
    rw [hpull, ← Finset.sum_mul_sum]
    ring
  rw [h_factor]
  have hB2sum_le : (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 :=
    sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
  have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
    apply Finset.sum_nonneg; intros _ _
    exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_le : (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 :=
    sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
    apply Finset.sum_nonneg; intros _ _
    exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hkey : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
              ≤ sq := by
    calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
        ≤ sq * 1 * 1 := by
          gcongr <;> first | exact hB1_le r | exact hB2sum_le | exact hB3sum_le
      _ = sq := by ring
  calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (∑ zPlus ∈ Finset.range (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ sq * (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        apply mul_le_mul_of_nonneg_right hkey (hprod_nn r)

/-- **Piece B bound**, extracted as a standalone lemma so it elaborates on its own. -/
private lemma pieceB_lemma (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n)
    (δ : ℝ) (hδ_lb : 320 / Real.sqrt n ≤ δ) (hδ_ub : δ ≤ 1/2) (ℓ : Finset ℕ) :
    (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.range (n / 16),
          |altRSum n δ
            ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
            zMinus zPlus ℓ|)
      ≤ Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) *
          (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            ∏ j ∈ ℓ,
              ellFactor n
                ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1)) := by
  -- Numeric setup
  have hn_pos : (0 : ℕ) < n := by omega
  have hn_one : (1 : ℕ) ≤ n := hn_pos
  have hn_half : (1 : ℕ) ≤ n / 2 := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα_def
  set rRange : Finset ℤ := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) with hrRange_def
  set sq : ℝ := Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) with hsq_def
  have hsq_nn : 0 ≤ sq := Real.sqrt_nonneg _
  have hprod_nn : ∀ r, 0 ≤ ∏ j ∈ ℓ, ellFactor n α r (j - 1) := by
    intro r
    apply Finset.prod_nonneg
    intro j _
    have h := (T4L1NormBoundAux.ellFactor_in_unit_interval n hn_one r (j - 1))
    simp only at h
    exact h.1
  have hB1_le : ∀ r, binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) ≤ sq := fun r =>
    B1_le_sqrt n hn_half r
  have hB1_nn : ∀ r, 0 ≤ binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) := fun r =>
    binPMFInt_nonneg' (n / 2) (1/2) (by norm_num) (by norm_num) _
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
      binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
      binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
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
  -- Piece B bound
  show (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            |altRSum n δ α zMinus zPlus ℓ|)
        ≤ sq * (∑ r ∈ rRange, ∏ j ∈ ℓ, ellFactor n α r (j - 1))
  have h_step1 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.range (n / 16),
                      |altRSum n δ α zMinus zPlus ℓ|)
                ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.range (n / 16),
                      ∑ r ∈ rRange, G r zMinus zPlus) := by
    apply Finset.sum_le_sum
    intro zMinus _
    apply Finset.sum_le_sum
    intro zPlus _
    exact altRSum_le zMinus zPlus
  refine h_step1.trans ?_
  have h_swap1 : ∀ zMinus, (∑ zPlus ∈ Finset.range (n / 16),
                            ∑ r ∈ rRange, G r zMinus zPlus)
                          = ∑ r ∈ rRange, ∑ zPlus ∈ Finset.range (n / 16),
                              G r zMinus zPlus := by
    intro zMinus
    exact Finset.sum_comm
  have h_step2 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.range (n / 16),
                      ∑ r ∈ rRange, G r zMinus zPlus)
              = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ r ∈ rRange,
                      ∑ zPlus ∈ Finset.range (n / 16), G r zMinus zPlus) := by
    apply Finset.sum_congr rfl
    intros zMinus _
    exact h_swap1 zMinus
  rw [h_step2, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h_factor : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.range (n / 16), G r zMinus zPlus)
                = binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                  (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                  (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
                  (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
    have hexpand : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    ∑ zPlus ∈ Finset.range (n / 16), G r zMinus zPlus)
        = ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_congr rfl; intros zMinus _
      apply Finset.sum_congr rfl; intros zPlus _
      rw [hG_def]; ring
    rw [hexpand]
    have hpull : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
              (binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
        = (binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) * (∏ j ∈ ℓ, ellFactor n α r (j - 1))) *
            (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros zMinus _
      rw [Finset.mul_sum]
    rw [hpull, ← Finset.sum_mul_sum]
    ring
  rw [h_factor]
  have hB2sum_le : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 :=
    sum_binPMFInt_Ico_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _ _
  have hB2sum_nn : 0 ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
    apply Finset.sum_nonneg; intros _ _
    exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_le : (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 :=
    sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
  have hB3sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 16),
                    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
    apply Finset.sum_nonneg; intros _ _
    exact binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  have hkey : binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
              ≤ sq := by
    calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
                (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                (∑ zPlus ∈ Finset.range (n / 16),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)
        ≤ sq * 1 * 1 := by
          gcongr <;> first | exact hB1_le r | exact hB2sum_le | exact hB3sum_le
      _ = sq := by ring
  calc binPMFInt (n / 2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (∑ zPlus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) *
          (∏ j ∈ ℓ, ellFactor n α r (j - 1))
      ≤ sq * (∏ j ∈ ℓ, ellFactor n α r (j - 1)) := by
        apply mul_le_mul_of_nonneg_right hkey (hprod_nn r)

end LightAtypicalPerEllProof

/-- **Per-`ℓ` envelope-weighted atypical bound (light family).**
For any `ℓ`, the atypical-`z` contribution is bounded by
`2 · √(2/(πn)) · envelopeW ℓ` where
`envelopeW ℓ = ∑_r ∏_{j∈ℓ} ellFactor n α r j`. No "light" hypothesis on `ℓ`. -/
theorem LightAtypicalPerEll :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt n ≤ δ → δ ≤ 1/2 →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      ∀ (ℓ : Finset ℕ),
        ((∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          +
         (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))
        ≤ 2 * Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) *
            (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              ∏ j ∈ ℓ,
                Workspace.Types.AlternatingSumExpression.ellFactor n
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j - 1)) := by
  intro n hn hn8 δ hδ_lb hδ_ub α ℓ
  set sq : ℝ := Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) with hsq_def
  have hA := LightAtypicalPerEllProof.pieceA_lemma n hn δ hδ_lb hδ_ub ℓ
  have hB := LightAtypicalPerEllProof.pieceB_lemma n hn δ hδ_lb hδ_ub ℓ
  -- Final assembly: A + B ≤ 2 sq envelope
  have h := add_le_add hA hB
  have heq : sq * (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1))
            + sq * (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1))
          = 2 * sq * (∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
                ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1)) := by ring
  rw [heq] at h
  exact h
