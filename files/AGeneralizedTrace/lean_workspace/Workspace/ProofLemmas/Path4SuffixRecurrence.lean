import Mathlib
import Workspace.Types.AlternatingSumExpression

/-!
# Path4SuffixRecurrence

The binomial PMF Pascal/Bernoulli recurrence (`Bin(M+1) = (1-p)·Bin(M) + p·Bin(M) shifted`),
and its consequence for the matched alternating suffix sum: incrementing the trial count
`M → M+1` costs at most a factor `1` in the absolute suffix sum.
-/

namespace Workspace.ProofLemmas.Path4SuffixRecurrence

open scoped BigOperators

open Workspace.Types.AlternatingSumExpression

/-- The Bernoulli/Pascal recurrence for the binomial PMF:
`Bin(M+1, p) = (1-p)·Bin(M,p) + p·Bin(M,p)·(shift by one)`. -/
theorem binPMF_succ_trials (M : ℕ) (p : ℝ) (z : ℕ) :
    Workspace.Types.AlternatingSumExpression.binPMF (M+1) p z
      = (1 - p) * Workspace.Types.AlternatingSumExpression.binPMF M p z
        + p * (if z = 0 then 0 else Workspace.Types.AlternatingSumExpression.binPMF M p (z-1)) := by
  unfold Workspace.Types.AlternatingSumExpression.binPMF
  -- Case on z = 0
  rcases Nat.eq_zero_or_pos z with hz0 | hzpos
  · subst hz0
    rw [if_pos rfl, mul_zero, add_zero]
    rw [if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    -- (1-p)^(M+1) = (1-p)^M * (1-p)
    rw [pow_succ]
    ring
  · -- z ≥ 1, so z = k + 1
    obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 := ⟨z - 1, by omega⟩
    simp only [if_false, Nat.add_sub_cancel, add_eq_zero,
      one_ne_zero, and_false]
    -- Now case on whether k+1 ≤ M+1, etc.
    by_cases hk1 : k + 1 ≤ M + 1
    · -- z = k+1 ≤ M+1
      rw [if_pos hk1]
      rw [Nat.choose_succ_succ M k, Nat.cast_add]
      -- choose: (M+1).choose (k+1) = M.choose k + M.choose (k+1)
      by_cases hkM : k + 1 ≤ M
      · -- both M.choose (k+1) and M.choose k available
        rw [if_pos hkM, if_pos (Nat.le_of_succ_le hkM)]
        -- exponents: M+1-(k+1) = M-k, and M-(k+1) = (M-k)-1, so (1-p)^(M-(k+1))*(1-p) = (1-p)^(M-k)
        have e1 : M + 1 - (k + 1) = M - k := by omega
        have e2 : M - k = (M - (k + 1)) + 1 := by omega
        rw [e1, e2, pow_succ p k, pow_succ (1 - p) (M - (k + 1)),
          show k.succ = k + 1 from rfl]
        ring
      · -- k+1 > M, so k+1 = M+1, i.e. k = M
        have hkeqM : k = M := by omega
        subst hkeqM
        rw [if_neg (by omega), if_pos (le_refl k), Nat.choose_self,
          Nat.choose_succ_self, Nat.cast_zero, Nat.cast_one]
        have e1 : k + 1 - (k + 1) = 0 := by omega
        have e2 : k - k = 0 := by omega
        rw [e1, e2]
        simp only [pow_zero, pow_succ]
        ring
    · -- k+1 > M+1: all three binPMF are 0
      rw [if_neg hk1, if_neg (by omega), if_neg (by omega)]
      ring

/-- Incrementing the trial count in the matched alternating suffix sum costs at most a
factor `1` in the absolute suffix sum. -/
theorem matched_suffix_shift_abs_sum_le
    (M0 : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (c : ℤ → ℝ) (rs : Finset ℤ) (Mof : ℤ → ℕ) (Z : ℕ) :
    ∑ zPlus ∈ Finset.range (Z+1),
        |∑ r ∈ rs, c r * Workspace.Types.AlternatingSumExpression.binPMF ((Mof r)+1) (1-δ) zPlus|
      ≤ ∑ w ∈ Finset.range (Z+2),
          |∑ r ∈ rs, c r * Workspace.Types.AlternatingSumExpression.binPMF (Mof r) (1-δ) w| := by
  classical
  -- F w := the matched alternating sum with `Mof r` trials at suffix index `w`.
  set F : ℕ → ℝ := fun w => ∑ r ∈ rs, c r * binPMF (Mof r) (1-δ) w with hF
  -- Abbreviate the target right-hand side.
  set S : ℝ := ∑ w ∈ Finset.range (Z+2), |F w| with hS
  -- Key pointwise rewrite: the M+1-trial inner sum equals δ·F(zPlus) + (1-δ)·(shifted F).
  have hp1 : (1 : ℝ) - (1 - δ) = δ := by ring
  have key : ∀ zPlus : ℕ,
      (∑ r ∈ rs, c r * binPMF ((Mof r)+1) (1-δ) zPlus)
        = δ * F zPlus + (1 - δ) * (if zPlus = 0 then 0 else F (zPlus - 1)) := by
    intro zPlus
    by_cases hz : zPlus = 0
    · -- zPlus = 0: shifted term vanishes; recurrence's `if` is 0.
      subst hz
      have hterm : ∀ r ∈ rs,
          c r * binPMF ((Mof r)+1) (1-δ) 0
            = δ * (c r * binPMF (Mof r) (1-δ) 0) := by
        intro r _
        rw [binPMF_succ_trials (Mof r) (1-δ) 0, hp1]
        simp only [if_true, mul_zero, add_zero]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      simp [hF]
    · -- zPlus ≠ 0: full recurrence.
      have hterm : ∀ r ∈ rs,
          c r * binPMF ((Mof r)+1) (1-δ) zPlus
            = δ * (c r * binPMF (Mof r) (1-δ) zPlus)
              + (1 - δ) * (c r * binPMF (Mof r) (1-δ) (zPlus-1)) := by
        intro r _
        rw [binPMF_succ_trials (Mof r) (1-δ) zPlus, hp1]
        simp [hz]; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [hz, if_false, hF]
  -- Pointwise bound after taking absolute values.
  have hpt : ∀ zPlus : ℕ,
      |∑ r ∈ rs, c r * binPMF ((Mof r)+1) (1-δ) zPlus|
        ≤ δ * |F zPlus| + (1 - δ) * (if zPlus = 0 then 0 else |F (zPlus - 1)|) := by
    intro zPlus
    rw [key zPlus]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - δ)]
    by_cases hz : zPlus = 0
    · simp [hz]
    · simp only [hz, if_false, le_refl]
  -- Sum the pointwise bound over zPlus ∈ range(Z+1).
  refine (Finset.sum_le_sum (fun zPlus _ => hpt zPlus)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- First piece: δ * ∑_{range(Z+1)} |F zPlus| ≤ δ * S.
  have hA : ∑ zPlus ∈ Finset.range (Z+1), |F zPlus| ≤ S := by
    rw [hS]
    have hsub : Finset.range (Z + 1) ⊆ Finset.range (Z + 2) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; exact abs_nonneg _
  -- Second piece: ∑_{range(Z+1)} (if zPlus=0 then 0 else |F (zPlus-1)|) ≤ S.
  have hB : ∑ zPlus ∈ Finset.range (Z+1),
      (if zPlus = 0 then 0 else |F (zPlus - 1)|) ≤ S := by
    have hreindex : ∑ zPlus ∈ Finset.range (Z+1),
        (if zPlus = 0 then 0 else |F (zPlus - 1)|)
          = ∑ w ∈ Finset.range Z, |F w| := by
      rw [Finset.sum_range_succ']
      simp
    rw [hreindex, hS]
    have hsub : Finset.range Z ⊆ Finset.range (Z + 2) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; exact abs_nonneg _
  calc δ * (∑ zPlus ∈ Finset.range (Z+1), |F zPlus|)
        + (1 - δ) * (∑ zPlus ∈ Finset.range (Z+1), (if zPlus = 0 then 0 else |F (zPlus - 1)|))
      ≤ δ * S + (1 - δ) * S := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hA hδ0
        · exact mul_le_mul_of_nonneg_left hB (by linarith)
    _ = S := by ring


end Workspace.ProofLemmas.Path4SuffixRecurrence
