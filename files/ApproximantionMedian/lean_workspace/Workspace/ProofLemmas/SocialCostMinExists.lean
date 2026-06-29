import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.LqNormSubReverseTriangle

open scoped BigOperators
open Workspace.Types.SocialCost
open Workspace.Types.LqNorm

namespace SocialCostMinExistsProof

-- Auxiliary lemma: lqNorm bounds individual coordinates.
private lemma _scme_lqNorm_ge_abs_coord {q : ℝ} (hq : 1 ≤ q) {d : ℕ}
    (x : Fin d → ℝ) (j : Fin d) :
    |x j| ≤ lqNorm q x := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_pos : 0 < (1 : ℝ) / q := by positivity
  -- |x j|^q ≤ ∑ k, |x k|^q
  have h_pos : ∀ k, 0 ≤ |x k| ^ q := fun k => Real.rpow_nonneg (abs_nonneg _) q
  have h_le : |x j| ^ q ≤ ∑ k, |x k| ^ q := by
    have := Finset.single_le_sum (f := fun k => |x k| ^ q)
      (s := Finset.univ) (a := j)
      (fun k _ => h_pos k) (Finset.mem_univ j)
    exact this
  -- Take rpow (1/q) of both sides
  have h_lhs_nn : 0 ≤ |x j| ^ q := h_pos j
  have h_rhs_nn : 0 ≤ ∑ k, |x k| ^ q := sum_abs_rpow_nonneg q x
  have h2 : (|x j| ^ q) ^ ((1 : ℝ) / q) ≤ (∑ k, |x k| ^ q) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow h_lhs_nn h_le (le_of_lt h_inv_pos)
  -- Simplify (|x j|^q)^(1/q) = |x j|
  have habs_nn : (0 : ℝ) ≤ |x j| := abs_nonneg _
  have h3 : (|x j| ^ q) ^ ((1 : ℝ) / q) = |x j| := by
    rw [← Real.rpow_mul habs_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
  rw [h3] at h2
  exact h2

-- Continuity of lqNorm
private lemma lqNorm_continuous {q : ℝ} (hq : 1 ≤ q) {d : ℕ} :
    Continuous (fun x : Fin d → ℝ => lqNorm q x) := by
  unfold lqNorm
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h_inv_nn : 0 ≤ (1 : ℝ) / q := by positivity
  have hq_nn : 0 ≤ q := le_of_lt hq_pos
  -- continuous fun x => ∑ j, |x j|^q
  have h_inner : Continuous (fun x : Fin d → ℝ => ∑ j, |x j| ^ q) := by
    apply continuous_finset_sum
    intro j _
    exact (Real.continuous_rpow_const hq_nn).comp ((continuous_apply j).abs)
  -- continuous fun y => y^(1/q) on [0, ∞), well, on all reals when 1/q ≥ 0
  exact (Real.continuous_rpow_const h_inv_nn).comp h_inner

-- Continuity of socialCost
private lemma socialCost_continuous {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) :
    Continuous (fun f : Fin d → ℝ => socialCost q P f) := by
  unfold socialCost
  apply continuous_finset_sum
  intro i _
  -- f ↦ lqNorm q (fun j => P i j - f j) = lqNorm q ∘ (P i - f)
  have h_arg : Continuous (fun f : Fin d → ℝ => fun j => P i j - f j) := by
    apply continuous_pi
    intro j
    exact continuous_const.sub (continuous_apply j)
  exact (lqNorm_continuous hq).comp h_arg

end SocialCostMinExistsProof

open SocialCostMinExistsProof

theorem SocialCostMinExists
    (q : ℝ) (hq : 1 ≤ q) {n d : ℕ} (hd : 1 ≤ d) (P : Fin n → Fin d → ℝ) :
    ∃ f : Fin d → ℝ, socialCost q P f = optSocialCost q P := by
  classical
  -- Case n = 0: socialCost is identically 0
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun _ => 0, ?_⟩
    have h0 : socialCost q P (fun _ => 0) = 0 := socialCost_empty_agents q d P _
    rw [h0]
    -- optSocialCost = ⨅ f, socialCost q P f = ⨅ f, 0 = 0
    unfold optSocialCost
    have hconst : ∀ f : Fin d → ℝ, socialCost q P f = 0 :=
      fun f => socialCost_empty_agents q d P f
    simp only [hconst]
    exact (ciInf_const (α := ℝ)).symm
  -- Case n ≥ 1
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Use that socialCost is continuous and coercive: bounded sublevel set.
    have hcont : Continuous (fun f : Fin d → ℝ => socialCost q P f) :=
      socialCost_continuous hq P
    -- Pick base point f₀ = 0
    set K : ℝ := socialCost q P (fun _ => 0) with hK_def
    -- We show {f | socialCost q P f ≤ K} is bounded.
    -- For any f in this set: lqNorm q (P 0 - f) ≤ K (since other terms ≥ 0),
    -- and |f j - P 0 j| ≤ lqNorm q (P 0 - f), so |f j| ≤ K + |P 0 j|.
    have hbdd : Bornology.IsBounded {f : Fin d → ℝ | socialCost q P f ≤ K} := by
      -- Define R := K + max j |P 0 j|. Use pi_norm_le_iff_of_nonneg.
      -- Use Metric.isBounded_iff_subset_closedBall to wrap up.
      -- Define a uniform bound
      have hPmax : ∀ f : Fin d → ℝ, socialCost q P f ≤ K →
          ∀ j : Fin d, |f j| ≤ K + |P ⟨0, hn_pos⟩ j| := by
        intro f hfK j
        -- socialCost q P f ≥ lqNorm q (fun k => P 0 k - f k)
        have h_term_nn : ∀ i, 0 ≤ lqNorm q (fun k => P i k - f k) := fun i =>
          lqNorm_nonneg hq _
        have h_le : lqNorm q (fun k => P ⟨0, hn_pos⟩ k - f k) ≤ socialCost q P f := by
          unfold socialCost
          exact Finset.single_le_sum (f := fun i => lqNorm q (fun k => P i k - f k))
            (s := Finset.univ) (a := ⟨0, hn_pos⟩)
            (fun i _ => h_term_nn i) (Finset.mem_univ _)
        have h1 : lqNorm q (fun k => P ⟨0, hn_pos⟩ k - f k) ≤ K := le_trans h_le hfK
        -- |P 0 j - f j| ≤ lqNorm q (fun k => P 0 k - f k)
        have h2 : |P ⟨0, hn_pos⟩ j - f j| ≤ lqNorm q (fun k => P ⟨0, hn_pos⟩ k - f k) := by
          have := _scme_lqNorm_ge_abs_coord hq (fun k => P ⟨0, hn_pos⟩ k - f k) j
          simpa using this
        have h3 : |P ⟨0, hn_pos⟩ j - f j| ≤ K := le_trans h2 h1
        -- |f j| ≤ |P 0 j - f j| + |P 0 j|, by reverse triangle inequality
        have h4 : |f j| ≤ |P ⟨0, hn_pos⟩ j - f j| + |P ⟨0, hn_pos⟩ j| := by
          have key : |f j - P ⟨0, hn_pos⟩ j| ≤
              |P ⟨0, hn_pos⟩ j - f j| := by
            rw [abs_sub_comm]
          have triangle : |f j| ≤ |f j - P ⟨0, hn_pos⟩ j| + |P ⟨0, hn_pos⟩ j| := by
            have := abs_sub_abs_le_abs_sub (f j) (P ⟨0, hn_pos⟩ j)
            -- |f j| - |P 0 j| ≤ |f j - P 0 j|, so |f j| ≤ |f j - P 0 j| + |P 0 j|
            linarith [abs_nonneg (P ⟨0, hn_pos⟩ j)]
          linarith
        linarith
      -- Now show boundedness using closedBall
      rw [Metric.isBounded_iff_subset_closedBall (0 : Fin d → ℝ)]
      -- Choose R = K + ∑ j, |P 0 j| (a single uniform bound for all coordinates)
      -- Actually, use R = K + max_j |P 0 j|. But sup of finite set is a Real.
      -- For simplicity, use M := ∑ j, |P 0 j|.
      set M : ℝ := ∑ j, |P ⟨0, hn_pos⟩ j| with hM_def
      refine ⟨K + M, ?_⟩
      intro f hf
      simp only [Set.mem_setOf_eq] at hf
      rw [Metric.mem_closedBall, dist_zero_right]
      -- ‖f‖ ≤ K + M; use pi_norm_le_iff_of_nonneg
      have hKnn : 0 ≤ K := socialCost_nonneg hq P _
      have hMnn : 0 ≤ M := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ K + M)]
      intro j
      have hj := hPmax f hf j
      -- |f j| ≤ K + |P 0 j| ≤ K + M
      have hPj : |P ⟨0, hn_pos⟩ j| ≤ M := by
        exact Finset.single_le_sum (f := fun k => |P ⟨0, hn_pos⟩ k|)
          (s := Finset.univ) (a := j)
          (fun k _ => abs_nonneg _) (Finset.mem_univ _)
      simp only [Real.norm_eq_abs]
      linarith
    -- Apply Continuous.exists_forall_le_of_isBounded
    obtain ⟨f₀, hf₀⟩ := hcont.exists_forall_le_of_isBounded (fun _ => 0) hbdd
    refine ⟨f₀, ?_⟩
    -- Show socialCost q P f₀ = optSocialCost q P
    unfold optSocialCost
    apply le_antisymm
    · -- socialCost q P f₀ ≤ ⨅ f, socialCost q P f
      apply le_ciInf
      intro f
      exact hf₀ f
    · -- ⨅ f, socialCost q P f ≤ socialCost q P f₀
      exact ciInf_le (socialCost_bddBelow hq P) f₀
