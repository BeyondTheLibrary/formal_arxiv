import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.DeletionLengthMarginal
import Workspace.ProofLemmas.TraceFromZeroIsLengthBinomial
import Workspace.ProofLemmas.DeletionChannelTotalMass
import Workspace.ProofLemmas.MiddleIndicatorSumsToOne
import Workspace.ProofLemmas.LengthsOnlyExists
import Workspace.ProofLemmas.PartialDeletionExists

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

open scoped Classical

namespace TVPartialBoundedHelpers

variable {n : ℕ}

/-- The bad-event predicate used in the statement: offset out of range OR some
prefix/suffix bit of `b` is `true`. -/
def badPred (n : ℕ) (b : BinVec n) (r : ℤ) : Prop :=
  r < -((n / 4 : ℕ) : ℤ) ∨ ((n / 4 : ℕ) : ℤ) < r ∨
    (∃ i : Fin n, ((i.val : ℤ) < (n / 4 : ℕ) + r ∨
                    ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ i.val) ∧
                  b.bit i = true)

/-- ℕ-cast-form in-range bounds. -/
lemma not_bad_inrange_natcast {b : BinVec n} {r : ℤ} (h : ¬ badPred n b r) :
    0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
  unfold badPred at h
  push_neg at h
  obtain ⟨h1, h2, _⟩ := h
  -- h1 : -↑(n/4) ≤ r ; h2 : r ≤ ↑(n/4)
  have hquart : (n / 4 : ℕ) + (n / 4 : ℕ) ≤ (n / 2 : ℕ) := by omega
  have hquartZ : ((n / 4 : ℕ) : ℤ) + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    exact_mod_cast hquart
  refine ⟨by omega, by omega⟩

/-- ℤ-division-form in-range bounds, the form wanted by `DeletionLengthMarginal`,
`DeletionChannelTotalMass`, `MiddleIndicatorSumsToOne`. -/
lemma not_bad_inrange_intdiv {b : BinVec n} {r : ℤ} (h : ¬ badPred n b r) :
    0 ≤ r + (n / 4 : ℤ) ∧ r + (n / 4 : ℤ) ≤ (n / 2 : ℤ) := by
  have hc4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := by push_cast; omega
  have hc2 : ((n / 2 : ℕ) : ℤ) = (n / 2 : ℤ) := by push_cast; omega
  obtain ⟨ha, hb⟩ := not_bad_inrange_natcast h
  rw [hc4] at ha; rw [hc4, hc2] at hb
  exact ⟨ha, hb⟩

/-- On the good event, every prefix-range bit of `b` is `false`. -/
lemma not_bad_prefix_false {b : BinVec n} {r : ℤ} (h : ¬ badPred n b r) :
    ∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r → b.bit i = false := by
  unfold badPred at h
  push_neg at h
  obtain ⟨_, _, h3⟩ := h
  intro i hi
  have := h3 i (Or.inl hi)
  simpa using this

/-- On the good event, every suffix-range bit of `b` is `false`. -/
lemma not_bad_suffix_false {b : BinVec n} {r : ℤ} (h : ¬ badPred n b r) :
    ∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) → b.bit i = false := by
  unfold badPred at h
  push_neg at h
  obtain ⟨_, _, h3⟩ := h
  intro i hi
  have := h3 i (Or.inr hi)
  simpa using this

/-! ## Per-output ENNReal masses, parameterised by a coin-flip distribution. -/

variable {Se : Workspace.Types.ProbVec.ProbVec n} {δ : DelProb}

/-- The full partial mass at output `(m,t₁,t₂)`, equal to `partE.toPMF (m,t₁,t₂)`
by the composition law. -/
noncomputable def partMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    cfd.toPMF b *
      (offsetWeight n r *
        (prefixWeight n b δ r t₁ *
          (suffixWeight n b δ r t₂ * middleIndicator n b m r)))

/-- The good-event restricted partial mass. -/
noncomputable def goodMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    (if ¬ badPred n b r then
      cfd.toPMF b *
        (offsetWeight n r *
          (prefixWeight n b δ r t₁ *
            (suffixWeight n b δ r t₂ * middleIndicator n b m r)))
     else 0)

/-- The bad-event restricted partial mass. -/
noncomputable def badMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    (if badPred n b r then
      cfd.toPMF b *
        (offsetWeight n r *
          (prefixWeight n b δ r t₁ *
            (suffixWeight n b δ r t₂ * middleIndicator n b m r)))
     else 0)

/-- The full lengths mass at output `(m,z₋,z₊)`, equal to `lenE.toPMF (m,z₋,z₊)`. -/
noncomputable def lenMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zMinus zPlus : ℕ) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    cfd.toPMF b *
      (offsetWeight n r *
        (prefixLengthWeight n δ r zMinus *
          (suffixLengthWeight n δ r zPlus * middleIndicator n b m r)))

/-- The good-event restricted lengths mass. -/
noncomputable def goodLenMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zMinus zPlus : ℕ) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    (if ¬ badPred n b r then
      cfd.toPMF b *
        (offsetWeight n r *
          (prefixLengthWeight n δ r zMinus *
            (suffixLengthWeight n δ r zPlus * middleIndicator n b m r)))
     else 0)

/-- The bad-event restricted lengths mass. -/
noncomputable def badLenMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zMinus zPlus : ℕ) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    (if badPred n b r then
      cfd.toPMF b *
        (offsetWeight n r *
          (prefixLengthWeight n δ r zMinus *
            (suffixLengthWeight n δ r zPlus * middleIndicator n b m r)))
     else 0)

/-- The bad-event total mass (= the statement's bad term). -/
noncomputable def badTotal (cfd : CoinFlipDist n Se) : ENNReal :=
  ∑' (b : BinVec n) (r : ℤ),
    (if badPred n b r then cfd.toPMF b * offsetWeight n r else 0)

/-- Split: full partial mass = good + bad (pointwise). -/
lemma partMass_eq_good_add_bad (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) :
    partMass (δ := δ) cfd m t₁ t₂
      = goodMass (δ := δ) cfd m t₁ t₂ + badMass (δ := δ) cfd m t₁ t₂ := by
  unfold partMass goodMass badMass
  rw [← ENNReal.tsum_add]
  apply tsum_congr; intro b
  rw [← ENNReal.tsum_add]
  apply tsum_congr; intro r
  by_cases hbad : badPred n b r
  · simp [hbad]
  · simp [hbad]

/-- Split: full lengths mass = good + bad (pointwise). -/
lemma lenMass_eq_good_add_bad (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zMinus zPlus : ℕ) :
    lenMass (δ := δ) cfd m zMinus zPlus
      = goodLenMass (δ := δ) cfd m zMinus zPlus + badLenMass (δ := δ) cfd m zMinus zPlus := by
  unfold lenMass goodLenMass badLenMass
  rw [← ENNReal.tsum_add]
  apply tsum_congr; intro b
  rw [← ENNReal.tsum_add]
  apply tsum_congr; intro r
  by_cases hbad : badPred n b r
  · simp [hbad]
  · simp [hbad]

/-- `partE.toPMF` equals `partMass` via the composition law. -/
lemma partE_eq_partMass (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    partE.toPMF (m, t₁, t₂) = partMass (δ := δ) cfd m t₁ t₂ := by
  have := partE.composition_law cfd m t₁ t₂
  rw [this]; rfl

/-- `lenE.toPMF` equals `lenMass` via the composition law. -/
lemma lenE_eq_lenMass (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (m : BinVec (n / 2)) (zMinus zPlus : ℕ) :
    lenE.toPMF (m, zMinus, zPlus) = lenMass (δ := δ) cfd m zMinus zPlus := by
  have := lenE.composition_law cfd m zMinus zPlus
  rw [this]; rfl

/-! ## Bad-mass bound (Claim B) and bad-lengths-mass total (= badTotal). -/

/-- Inner triple-sum of the partial weights equals 1 for in-range `r`
(reordered as `(m,t₁,t₂)`). -/
lemma inner_partial_tsum_eq_one (b : BinVec n) (r : ℤ)
    (h : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (∑' (s : BinVec (n / 2) × Trace n × Trace n),
        prefixWeight n b δ r s.2.1 *
          (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r)) = 1 := by
  rw [ENNReal.tsum_prod']
  rw [show (∑' (m : BinVec (n / 2)) (q : Trace n × Trace n),
        prefixWeight n b δ r (m, q).2.1 *
          (suffixWeight n b δ r (m, q).2.2 * middleIndicator n b (m, q).1 r))
      = (∑' (m : BinVec (n / 2)) (t₁ : Trace n) (t₂ : Trace n),
        prefixWeight n b δ r t₁ *
          (suffixWeight n b δ r t₂ * middleIndicator n b m r)) from by
    refine tsum_congr (fun m => ?_)
    rw [ENNReal.tsum_prod']]
  exact PartialDeletionExistsScratch.Fr_eq_one_partial n δ b r h

/-- Inner triple-sum of the lengths weights equals 1 for in-range `r`. -/
lemma inner_lengths_tsum_eq_one (b : BinVec n) (r : ℤ)
    (h : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (∑' (s : BinVec (n / 2) × ℕ × ℕ),
        prefixLengthWeight n δ r s.2.1 *
          (suffixLengthWeight n δ r s.2.2 * middleIndicator n b s.1 r)) = 1 := by
  rw [ENNReal.tsum_prod']
  rw [show (∑' (m : BinVec (n / 2)) (q : ℕ × ℕ),
        prefixLengthWeight n δ r (m, q).2.1 *
          (suffixLengthWeight n δ r (m, q).2.2 * middleIndicator n b (m, q).1 r))
      = (∑' (m : BinVec (n / 2)) (zM : ℕ) (zP : ℕ),
        prefixLengthWeight n δ r zM *
          (suffixLengthWeight n δ r zP * middleIndicator n b m r)) from by
    refine tsum_congr (fun m => ?_)
    rw [ENNReal.tsum_prod']]
  exact LengthsOnlyExistsScratch.Fr_eq_one n δ b r h

/-- Per-`(b,r)` bad summand bound: the inner triple-sum is `≤ 1`, so the
bad term is bounded by `cfd b * offsetWeight r`. -/
lemma bad_summand_le (cfd : CoinFlipDist n Se) (b : BinVec n) (r : ℤ) :
    (if badPred n b r then
      cfd.toPMF b * (offsetWeight n r *
        (∑' (s : BinVec (n / 2) × Trace n × Trace n),
          prefixWeight n b δ r s.2.1 *
            (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r)))
     else 0)
      ≤ (if badPred n b r then cfd.toPMF b * offsetWeight n r else 0) := by
  by_cases hbad : badPred n b r
  · rw [if_pos hbad, if_pos hbad]
    by_cases hrange : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)
    · rw [inner_partial_tsum_eq_one b r hrange, mul_one]
    · -- out of range ⇒ offsetWeight = 0
      have h0 : offsetWeight n r = 0 := by unfold offsetWeight; rw [dif_neg hrange]
      rw [h0]; simp
  · rw [if_neg hbad, if_neg hbad]

/-- Swap the output-sum to the inside of the `(b,r)` sums for `badMass`. -/
lemma sum_badMass_swap (cfd : CoinFlipDist n Se) :
    (∑' (s : BinVec (n / 2) × Trace n × Trace n),
        badMass (δ := δ) cfd s.1 s.2.1 s.2.2)
      = ∑' (b : BinVec n) (r : ℤ),
          (if badPred n b r then
            cfd.toPMF b * (offsetWeight n r *
              (∑' (s : BinVec (n / 2) × Trace n × Trace n),
                prefixWeight n b δ r s.2.1 *
                  (suffixWeight n b δ r s.2.2 * middleIndicator n b s.1 r)))
           else 0) := by
  unfold badMass
  -- LHS: ∑'_s ∑'_b ∑'_r G s b r
  rw [ENNReal.tsum_comm]
  -- now ∑'_b ∑'_s ∑'_r G
  apply tsum_congr; intro b
  rw [ENNReal.tsum_comm]
  -- now ∑'_r ∑'_s G ; want ∑'_r [...] -- but we want ∑'_b ∑'_r, currently ∑'_b ∑'_r ∑'_s
  apply tsum_congr; intro r
  by_cases hbad : badPred n b r
  · simp only [hbad, if_true]
    -- ∑'_s cfd·(offW·(prefW·(suffW·midI))) = cfd·(offW·(∑'_s prefW·(suffW·midI)))
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [ENNReal.tsum_mul_left]
  · simp only [hbad, if_false, tsum_zero]

/-- **Claim B**: the total bad partial mass is `≤ badTotal`. -/
lemma sum_badMass_le_badTotal (cfd : CoinFlipDist n Se) :
    (∑' (s : BinVec (n / 2) × Trace n × Trace n),
        badMass (δ := δ) cfd s.1 s.2.1 s.2.2)
      ≤ badTotal cfd := by
  rw [sum_badMass_swap]
  unfold badTotal
  apply ENNReal.tsum_le_tsum; intro b
  apply ENNReal.tsum_le_tsum; intro r
  exact bad_summand_le cfd b r

/-- Per-`(b,r)` bad summand bound for the LENGTHS process. -/
lemma bad_lengths_summand_le (cfd : CoinFlipDist n Se) (b : BinVec n) (r : ℤ) :
    (if badPred n b r then
      cfd.toPMF b * (offsetWeight n r *
        (∑' (s : BinVec (n / 2) × ℕ × ℕ),
          prefixLengthWeight n δ r s.2.1 *
            (suffixLengthWeight n δ r s.2.2 * middleIndicator n b s.1 r)))
     else 0)
      ≤ (if badPred n b r then cfd.toPMF b * offsetWeight n r else 0) := by
  by_cases hbad : badPred n b r
  · rw [if_pos hbad, if_pos hbad]
    by_cases hrange : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧ r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)
    · rw [inner_lengths_tsum_eq_one b r hrange, mul_one]
    · have h0 : offsetWeight n r = 0 := by unfold offsetWeight; rw [dif_neg hrange]
      rw [h0]; simp
  · rw [if_neg hbad, if_neg hbad]

/-- Swap the output-sum inside the `(b,r)` sums for `badLenMass`. -/
lemma sum_badLenMass_swap (cfd : CoinFlipDist n Se) :
    (∑' (s : BinVec (n / 2) × ℕ × ℕ),
        badLenMass (δ := δ) cfd s.1 s.2.1 s.2.2)
      = ∑' (b : BinVec n) (r : ℤ),
          (if badPred n b r then
            cfd.toPMF b * (offsetWeight n r *
              (∑' (s : BinVec (n / 2) × ℕ × ℕ),
                prefixLengthWeight n δ r s.2.1 *
                  (suffixLengthWeight n δ r s.2.2 * middleIndicator n b s.1 r)))
           else 0) := by
  unfold badLenMass
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro b
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro r
  by_cases hbad : badPred n b r
  · simp only [hbad, if_true]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [ENNReal.tsum_mul_left]
  · simp only [hbad, if_false, tsum_zero]

/-- The total bad lengths mass is `≤ badTotal`. -/
lemma sum_badLenMass_le_badTotal (cfd : CoinFlipDist n Se) :
    (∑' (s : BinVec (n / 2) × ℕ × ℕ),
        badLenMass (δ := δ) cfd s.1 s.2.1 s.2.2)
      ≤ badTotal cfd := by
  rw [sum_badLenMass_swap]
  unfold badTotal
  apply ENNReal.tsum_le_tsum; intro b
  apply ENNReal.tsum_le_tsum; intro r
  exact bad_lengths_summand_le cfd b r

end TVPartialBoundedHelpers
