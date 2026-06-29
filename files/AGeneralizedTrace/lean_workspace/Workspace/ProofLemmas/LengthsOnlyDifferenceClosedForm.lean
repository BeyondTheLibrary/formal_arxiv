import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

theorem LengthsOnlyDifferenceClosedForm :
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
            ∀ (m : BinVec (n / 2)) (zMinus zPlus : ℕ),
              ((lenE.toPMF (m, zMinus, zPlus)).toReal
                - (lenO.toPMF (m, zMinus, zPlus)).toReal)
                =
              ∑ b : BinVec n,
                ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
                  ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
                    (offsetWeight n r).toReal *
                    (prefixLengthWeight n δ r zMinus).toReal *
                    (suffixLengthWeight n δ r zPlus).toReal *
                    (middleIndicator n b m r).toReal := by
  intro n _hn hn8 Se So _ _ δ _ _ lenE lenO Ce Co m zMinus zPlus
  -- offsetWeight is zero outside the integer range Icc(-n/4, n/4)
  have hoff_zero : ∀ (r : ℤ),
      r ∉ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) → offsetWeight n r = 0 := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    push_neg at hr
    have hcast4 : ((n / 4 : ℕ) : ℤ) = (n : ℤ) / 4 := by push_cast; ring
    have hcast2 : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by push_cast; ring
    unfold offsetWeight
    simp only
    rw [dif_neg]
    rintro ⟨h1, h2⟩
    rw [hcast4] at h1 h2
    rw [hcast2] at h2
    -- Use n % 8 = 1 hypothesis to derive contradiction
    -- From n%8=1, n%4=1, hence (n/4)+(n/4) = n/2
    omega
  -- Prove finiteness of each piece
  have hoffsetWeight_ne_top : ∀ r : ℤ, offsetWeight n r ≠ ⊤ := by
    intro r
    unfold offsetWeight
    simp only
    split_ifs
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hprefixLW_ne_top : ∀ r : ℤ, ∀ z : ℕ, prefixLengthWeight n δ r z ≠ ⊤ := by
    intros r z
    unfold prefixLengthWeight
    simp only
    split_ifs
    · unfold binomialPMF
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.natCast_ne_top _
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hsuffixLW_ne_top : ∀ r : ℤ, ∀ z : ℕ, suffixLengthWeight n δ r z ≠ ⊤ := by
    intros r z
    unfold suffixLengthWeight
    simp only
    split_ifs
    · unfold binomialPMF
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.natCast_ne_top _
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hmid_ne_top : ∀ b : BinVec n, ∀ r : ℤ, middleIndicator n b m r ≠ ⊤ := by
    intros b r
    unfold middleIndicator
    split_ifs <;> simp [ENNReal.one_ne_top]
  -- The composition law
  have hcompE := lenE.composition_law Ce m zMinus zPlus
  have hcompO := lenO.composition_law Co m zMinus zPlus
  set LHS_E := lenE.toPMF (m, zMinus, zPlus) with hLHS_E_def
  set LHS_O := lenO.toPMF (m, zMinus, zPlus) with hLHS_O_def
  -- The key zero-outside-Icc fact for the full inner factor
  have hF_zero_out : ∀ (b : BinVec n) (r : ℤ),
      r ∉ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) →
      offsetWeight n r *
        (prefixLengthWeight n δ r zMinus *
          (suffixLengthWeight n δ r zPlus *
            middleIndicator n b m r)) = 0 := by
    intro b r hr
    rw [hoff_zero r hr]
    ring
  -- Helper: ∑'_r [...] = ∑_r∈Icc [...]
  have hsumI_E : ∀ b : BinVec n,
      (∑' r : ℤ,
        Ce.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r)))) =
      ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Ce.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r))) := by
    intro b
    rw [tsum_eq_sum (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))]
    intro r hr
    rw [hF_zero_out b r hr]
    simp
  have hsumI_O : ∀ b : BinVec n,
      (∑' r : ℤ,
        Co.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r)))) =
      ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Co.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r))) := by
    intro b
    rw [tsum_eq_sum (s := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)))]
    intro r hr
    rw [hF_zero_out b r hr]
    simp
  -- LHS_E = ∑ b : BinVec n, ∑ r ∈ Icc, [Ce·offset·prefix·suffix·middle]
  have h_sum_b_r_E : LHS_E = ∑ b : BinVec n,
      ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Ce.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r))) := by
    rw [hcompE, tsum_fintype]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hsumI_E b
  have h_sum_b_r_O : LHS_O = ∑ b : BinVec n,
      ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
        Co.toPMF b *
          (offsetWeight n r *
            (prefixLengthWeight n δ r zMinus *
              (suffixLengthWeight n δ r zPlus *
                middleIndicator n b m r))) := by
    rw [hcompO, tsum_fintype]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hsumI_O b
  -- Each summand is finite
  have h_term_ne_top_E : ∀ b r, Ce.toPMF b *
      (offsetWeight n r *
        (prefixLengthWeight n δ r zMinus *
          (suffixLengthWeight n δ r zPlus *
            middleIndicator n b m r))) ≠ ⊤ := by
    intro b r
    apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    apply ENNReal.mul_ne_top (hoffsetWeight_ne_top r)
    apply ENNReal.mul_ne_top (hprefixLW_ne_top r zMinus)
    exact ENNReal.mul_ne_top (hsuffixLW_ne_top r zPlus) (hmid_ne_top b r)
  have h_term_ne_top_O : ∀ b r, Co.toPMF b *
      (offsetWeight n r *
        (prefixLengthWeight n δ r zMinus *
          (suffixLengthWeight n δ r zPlus *
            middleIndicator n b m r))) ≠ ⊤ := by
    intro b r
    apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    apply ENNReal.mul_ne_top (hoffsetWeight_ne_top r)
    apply ENNReal.mul_ne_top (hprefixLW_ne_top r zMinus)
    exact ENNReal.mul_ne_top (hsuffixLW_ne_top r zPlus) (hmid_ne_top b r)
  -- Compute LHS_E.toReal as a ℝ-finite sum
  have hE_toReal :
      LHS_E.toReal =
        ∑ b : BinVec n, ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          (Ce.toPMF b).toReal *
            (offsetWeight n r).toReal *
            (prefixLengthWeight n δ r zMinus).toReal *
            (suffixLengthWeight n δ r zPlus).toReal *
            (middleIndicator n b m r).toReal := by
    rw [h_sum_b_r_E]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl (fun r _ => ?_)
        repeat rw [ENNReal.toReal_mul]
        ring
      · intro r _; exact h_term_ne_top_E b r
    · intro b _
      rw [ENNReal.sum_ne_top]
      intro r _
      exact h_term_ne_top_E b r
  have hO_toReal :
      LHS_O.toReal =
        ∑ b : BinVec n, ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          (Co.toPMF b).toReal *
            (offsetWeight n r).toReal *
            (prefixLengthWeight n δ r zMinus).toReal *
            (suffixLengthWeight n δ r zPlus).toReal *
            (middleIndicator n b m r).toReal := by
    rw [h_sum_b_r_O]
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl (fun r _ => ?_)
        repeat rw [ENNReal.toReal_mul]
        ring
      · intro r _; exact h_term_ne_top_O b r
    · intro b _
      rw [ENNReal.sum_ne_top]
      intro r _
      exact h_term_ne_top_O b r
  rw [hE_toReal, hO_toReal]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring
