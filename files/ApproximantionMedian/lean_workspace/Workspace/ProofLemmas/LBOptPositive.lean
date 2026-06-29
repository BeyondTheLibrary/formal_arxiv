import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.LqNormZeroIffEqZero

open Workspace.Types.LqNorm Workspace.Types.SocialCost Workspace.ProofLemmas.LBConstruction
open Workspace.ProofLemmas.FqHasUniqueInteriorZero

namespace Workspace.ProofLemmas.LBOptPositive

theorem LBOptPositive (q : ℝ) (hq : 1 < q) (d : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) :
    0 < optSocialCost q (P_LB q d t) ∧
    0 < socialCost q (P_LB q d t) (f_opt d) := by
  have hq1 : (1 : ℝ) ≤ q := le_of_lt hq
  obtain ⟨ha_pos, ha_half⟩ := AStarLessThanOneHalf q hq
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  -- k < d  (from a* < 1/2 and d ≥ 1)
  have hkd : kCount q d < d := by
    unfold kCount
    have harg_nn : (0 : ℝ) ≤ a_star q * (d : ℝ) := by positivity
    rw [Nat.floor_lt harg_nn]
    nlinarith
  -- There is at least one Type-I point (index 0) : numTypeI ≥ 1, hence nCount ≥ 1.
  have htypeI_pos : 0 < numTypeI q d t := by
    unfold numTypeI
    exact Nat.mul_pos hd ht
  -- There is at least one Type-II point : d - 2k ≥ 1 (from k < d/2 ... actually 2k < d).
  have h2k_lt_d : 2 * kCount q d < d := by
    -- kCount = ⌊a* d⌋ ≤ a* d < (1/2) d, so 2 kCount < d
    have hk_lt : (kCount q d : ℝ) < (1 / 2) * (d : ℝ) := by
      have hle : (kCount q d : ℝ) ≤ a_star q * (d : ℝ) := by
        unfold kCount
        exact Nat.floor_le (by positivity)
      nlinarith
    have : ((2 * kCount q d : ℕ) : ℝ) < (d : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have htypeII_pos : 0 < numTypeII q d t := by
    unfold numTypeII
    apply Nat.mul_pos
    · omega
    · exact ht
  have hn_pos : 0 < nCount q d t := by
    unfold nCount; omega
  -- Indices: i₁ = 0 (Type I), i₂ = numTypeI (Type II), coordinate j₀ = kCount.
  have hi1lt : 0 < nCount q d t := hn_pos
  have hi2lt : numTypeI q d t < nCount q d t := by
    unfold nCount; omega
  have hj0lt : kCount q d < d := hkd
  set i1 : Fin (nCount q d t) := ⟨0, hi1lt⟩ with hi1
  set i2 : Fin (nCount q d t) := ⟨numTypeI q d t, hi2lt⟩ with hi2
  set j0 : Fin d := ⟨kCount q d, hj0lt⟩ with hj0
  have hj0val : (j0 : Fin d).val = kCount q d := rfl
  have hi1val : (i1 : Fin (nCount q d t)).val = 0 := rfl
  have hi2val : (i2 : Fin (nCount q d t)).val = numTypeI q d t := rfl
  -- Values at coordinate j0.
  have hval1 : P_LB q d t i1 j0 = 0 := by
    unfold P_LB
    rw [hi1val, hj0val]
    rw [if_pos htypeI_pos]
    -- typeIActiveB q d (0 % d) (kCount q d) = false
    have hact : typeIActiveB q d (0 % d) (kCount q d) = false := by
      unfold typeIActiveB
      rw [decide_eq_false_iff_not]
      simp only [Nat.zero_mod, Nat.sub_zero]
      have hmod : (kCount q d + d) % d = kCount q d := by
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt hkd
      rw [hmod]
      exact lt_irrefl _
    rw [hact]
    simp
  have hval2 : P_LB q d t i2 j0 = 1 := by
    unfold P_LB
    rw [hi2val]
    have hnlt : ¬ numTypeI q d t < numTypeI q d t := lt_irrefl _
    rw [if_neg hnlt]
  -- f_opt at j0 is 1.
  have hf0 : f_opt d j0 = 1 := rfl
  -- i1 ≠ i2 (different .val).
  have hi1ne2 : i1 ≠ i2 := by
    intro h
    have : (i1 : Fin (nCount q d t)).val = (i2 : Fin (nCount q d t)).val := by rw [h]
    rw [hi1val, hi2val] at this
    exact htypeI_pos.ne this
  -- Sum-triangle inequality with negation for lqNorm.
  have htri : ∀ (a b : Fin d → ℝ),
      lqNorm q (fun j => a j - b j) ≤ lqNorm q a + lqNorm q b := by
    intro a b
    have h := Real.Lp_add_le (Finset.univ : Finset (Fin d))
      (fun j => a j) (fun j => -(b j)) hq1
    have hL : (∑ j, |a j + -(b j)| ^ q) = (∑ j, |a j - b j| ^ q) := by
      apply Finset.sum_congr rfl; intro j _
      rw [show a j + -(b j) = a j - b j from by ring]
    have hR : (∑ j, |(-(b j))| ^ q) = (∑ j, |b j| ^ q) := by
      apply Finset.sum_congr rfl; intro j _; rw [abs_neg]
    rw [hL, hR] at h
    unfold lqNorm
    exact h
  -- lqNorm q (P i1 - P i2) > 0, since they differ at j0.
  have hdiffpos : 0 < lqNorm q (fun j => P_LB q d t i1 j - P_LB q d t i2 j) := by
    have hnn : 0 ≤ lqNorm q (fun j => P_LB q d t i1 j - P_LB q d t i2 j) :=
      lqNorm_nonneg hq1 _
    rcases eq_or_lt_of_le hnn with heq | hlt
    · exfalso
      have hz := ((LqNormZeroIffEqZero q hq1 hd
        (fun j => P_LB q d t i1 j - P_LB q d t i2 j)).mp heq.symm)
      have hzj0 : P_LB q d t i1 j0 - P_LB q d t i2 j0 = 0 := by
        have := congrFun hz j0
        simpa using this
      rw [hval1, hval2] at hzj0
      norm_num at hzj0
    · exact hlt
  -- Cost lower bound at any facility g.
  have hcost_lb : ∀ (g : Fin d → ℝ),
      lqNorm q (fun j => P_LB q d t i1 j - P_LB q d t i2 j)
        ≤ socialCost q (P_LB q d t) g := by
    intro g
    have hsub : ({i1, i2} : Finset (Fin (nCount q d t))) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (nCount q d t))),
        i ∉ ({i1, i2} : Finset (Fin (nCount q d t))) →
        0 ≤ lqNorm q (fun j => P_LB q d t i j - g j) :=
      fun i _ _ => lqNorm_nonneg hq1 _
    have hpair : (∑ i ∈ ({i1, i2} : Finset (Fin (nCount q d t))),
        lqNorm q (fun j => P_LB q d t i j - g j))
        = lqNorm q (fun j => P_LB q d t i1 j - g j)
          + lqNorm q (fun j => P_LB q d t i2 j - g j) := by
      rw [Finset.sum_pair hi1ne2]
    have hsum_le : (∑ i ∈ ({i1, i2} : Finset (Fin (nCount q d t))),
        lqNorm q (fun j => P_LB q d t i j - g j))
        ≤ socialCost q (P_LB q d t) g := by
      unfold socialCost
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    -- triangle: lqNorm(P i1 - P i2) ≤ lqNorm(P i1 - g) + lqNorm(P i2 - g)
    have htri' : lqNorm q (fun j => P_LB q d t i1 j - P_LB q d t i2 j)
        ≤ lqNorm q (fun j => P_LB q d t i1 j - g j)
          + lqNorm q (fun j => P_LB q d t i2 j - g j) := by
      have := htri (fun j => P_LB q d t i1 j - g j) (fun j => P_LB q d t i2 j - g j)
      have heqfun : (fun j => (P_LB q d t i1 j - g j) - (P_LB q d t i2 j - g j))
          = (fun j => P_LB q d t i1 j - P_LB q d t i2 j) := by
        funext j; ring
      rw [heqfun] at this
      exact this
    calc lqNorm q (fun j => P_LB q d t i1 j - P_LB q d t i2 j)
        ≤ lqNorm q (fun j => P_LB q d t i1 j - g j)
          + lqNorm q (fun j => P_LB q d t i2 j - g j) := htri'
      _ = (∑ i ∈ ({i1, i2} : Finset (Fin (nCount q d t))),
            lqNorm q (fun j => P_LB q d t i j - g j)) := hpair.symm
      _ ≤ socialCost q (P_LB q d t) g := hsum_le
  refine ⟨?_, ?_⟩
  · -- OPT > 0
    have hbdd : 0 < optSocialCost q (P_LB q d t) := by
      apply lt_of_lt_of_le hdiffpos
      unfold optSocialCost
      exact le_ciInf hcost_lb
    exact hbdd
  · -- socialCost q P (f_opt d) > 0
    have hi1term_pos :
        0 < lqNorm q (fun j => P_LB q d t i1 j - f_opt d j) := by
      have hnn : 0 ≤ lqNorm q (fun j => P_LB q d t i1 j - f_opt d j) :=
        lqNorm_nonneg hq1 _
      rcases eq_or_lt_of_le hnn with heq | hlt
      · exfalso
        have hz := ((LqNormZeroIffEqZero q hq1 hd
          (fun j => P_LB q d t i1 j - f_opt d j)).mp heq.symm)
        have hzj0 : P_LB q d t i1 j0 - f_opt d j0 = 0 := by
          have := congrFun hz j0
          simpa using this
        rw [hval1, hf0] at hzj0
        norm_num at hzj0
      · exact hlt
    have hterm_le :
        lqNorm q (fun j => P_LB q d t i1 j - f_opt d j)
          ≤ socialCost q (P_LB q d t) (f_opt d) := by
      unfold socialCost
      apply Finset.single_le_sum
        (f := fun i => lqNorm q (fun j => P_LB q d t i j - f_opt d j))
      · intro i _; exact lqNorm_nonneg hq1 _
      · exact Finset.mem_univ i1
    exact lt_of_lt_of_le hi1term_pos hterm_le

end Workspace.ProofLemmas.LBOptPositive
