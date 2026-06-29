import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem

namespace Workspace.ProofLemmas.RGEvenAugmentReduction

private lemma socialCost_zero_agents {q : ℝ} (d : ℕ)
    (P : Fin 0 → Fin d → ℝ) (f : Fin d → ℝ) :
    socialCost q P f = 0 := by
  unfold socialCost
  exact Fin.sum_univ_zero _

private lemma optSocialCost_zero_agents {q : ℝ} (hq : 1 ≤ q) (d : ℕ)
    (P : Fin 0 → Fin d → ℝ) :
    optSocialCost q P = 0 := by
  apply le_antisymm
  · have := optSocialCost_le_socialCost hq P (fun _ => 0)
    rw [socialCost_zero_agents] at this
    exact this
  · exact optSocialCost_nonneg hq P

theorem RGEvenAugmentReduction
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h_even : ∀ {n d : ℕ}, Even (n + ⌊c * (n : ℝ)⌋₊) →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) → 1 ≤ d →
      ∀ (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P pred (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        (∀ j, pred j ≠ m j) →
        socialCost 2 P m ≤ RG c * optSocialCost 2 P) :
    ∀ {n d : ℕ}, (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) → 1 ≤ d →
    ∀ (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (fstar : Fin d → ℝ),
      socialCost 2 P fstar = optSocialCost 2 P →
    ∀ (m : Fin d → ℝ),
      IsCoordinateMedian m (augment P pred (⌊c * (n : ℝ)⌋₊)) →
      (∀ j, fstar j ≠ m j) →
      (∀ j, pred j ≠ m j) →
      socialCost 2 P m ≤ RG c * optSocialCost 2 P := by
  intro n d hcn hd P pred fstar hfstar m hm hgp hgppred
  classical
  -- Case n = 0: both sides are 0.
  by_cases hn0 : n = 0
  · subst hn0
    have h1 : socialCost 2 P m = 0 := socialCost_zero_agents d P m
    have h2 : optSocialCost 2 P = 0 := optSocialCost_zero_agents (by norm_num) d P
    rw [h1, h2, mul_zero]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Abbreviation for ⌊cn⌋.
  set K : ℕ := ⌊c * (n : ℝ)⌋₊ with hK
  -- Case split on parity of n + K.
  by_cases heven : Even (n + K)
  · exact h_even heven hcn hd P pred fstar hfstar m hm hgp hgppred
  -- Odd case: duplicate P to 2n.
  -- Notation for the floor at 2n.
  have hcn2 : ⌊c * ((n + n : ℕ) : ℝ)⌋₊ = K + K := by
    have hcast : ((n + n : ℕ) : ℝ) = (n : ℝ) + (n : ℝ) := by push_cast; ring
    rw [hcast]
    have : c * ((n : ℝ) + (n : ℝ)) = ((K + K : ℕ) : ℝ) := by
      push_cast
      have : c * (n : ℝ) = (K : ℝ) := hcn.symm
      rw [show c * ((n : ℝ) + (n : ℝ)) = 2 * (c * (n : ℝ)) by ring, this]
      ring
    rw [this, Nat.floor_natCast]
  -- Build the duplicated instance P'.
  let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  let P' : Fin (n + n) → Fin d → ℝ := fun i => Sum.elim P P (e.symm i)
  have hn2_even : Even (n + n + (K + K)) := ⟨n + K, by ring⟩
  have hcn2' : (⌊c * ((n + n : ℕ) : ℝ)⌋₊ : ℝ) = c * ((n + n : ℕ) : ℝ) := by
    rw [hcn2]
    push_cast
    have : c * (n : ℝ) = (K : ℝ) := hcn.symm
    rw [show c * ((n : ℝ) + (n : ℝ)) = 2 * (c * (n : ℝ)) by ring, this]
    ring
  -- socialCost doubling.
  have h_sc : ∀ f : Fin d → ℝ, socialCost 2 P' f = 2 * socialCost 2 P f := by
    intro f
    unfold socialCost
    set F : Fin n → ℝ := fun i => lqNorm 2 (fun j => P i j - f j) with hF
    have h1 : (∑ i : Fin (n + n), lqNorm 2 (fun j => P' i j - f j))
        = ∑ i : Fin n ⊕ Fin n, lqNorm 2 (fun j => Sum.elim P P i j - f j) := by
      rw [← Equiv.sum_comp e (fun i : Fin (n + n) =>
            lqNorm 2 (fun j => P' i j - f j))]
      apply Finset.sum_congr rfl
      intro i _
      simp [P', Equiv.symm_apply_apply]
    rw [h1]
    have h2 : ∀ i : Fin n ⊕ Fin n,
        lqNorm 2 (fun j => Sum.elim P P i j - f j) = Sum.elim F F i := by
      intro i
      cases i with
      | inl a => simp [F, Sum.elim_inl]
      | inr a => simp [F, Sum.elim_inr]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    rw [Fintype.sum_sumElim]
    ring
  -- Median preservation of the augmented instance (now augmenting with `pred`).
  have hm' : IsCoordinateMedian m (augment P' pred (⌊c * ((n + n : ℕ) : ℝ)⌋₊)) := by
    rw [hcn2]
    intro j
    -- For an addCases function, split filter cardinality into the P-block and the
    -- constant-pred block, then count both blocks doubled.
    have count_aug : ∀ (R : ℝ → ℝ → Prop)
        {nn kk : ℕ} (Q : Fin nn → Fin d → ℝ)
        [DecidablePred (fun i : Fin (nn + kk) =>
          R ((augment Q pred kk) i j) (m j))]
        [DecidablePred (fun i : Fin nn => R (Q i j) (m j))],
        (Finset.univ.filter (fun i : Fin (nn + kk) =>
            R ((augment Q pred kk) i j) (m j))).card =
          (Finset.univ.filter (fun i : Fin nn => R (Q i j) (m j))).card
            + (if R (pred j) (m j) then kk else 0) := by
      intro R nn kk Q _ _
      classical
      have hcard1 : (Finset.univ.filter (fun i : Fin (nn + kk) =>
            R ((augment Q pred kk) i j) (m j))).card =
          ∑ i : Fin (nn + kk),
            (if R ((augment Q pred kk) i j) (m j) then (1 : ℕ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            smul_eq_mul, mul_one]
      rw [hcard1]
      let e2 : Fin nn ⊕ Fin kk ≃ Fin (nn + kk) := finSumFinEquiv
      rw [← Equiv.sum_comp e2 (fun i : Fin (nn + kk) =>
            (if R ((augment Q pred kk) i j) (m j) then (1 : ℕ) else 0))]
      have hsplit : ∀ i : Fin nn ⊕ Fin kk,
          (if R ((augment Q pred kk) (e2 i) j) (m j) then (1 : ℕ) else 0) =
          Sum.elim
            (fun a : Fin nn => if R (Q a j) (m j) then (1 : ℕ) else 0)
            (fun _ : Fin kk => if R (pred j) (m j) then (1 : ℕ) else 0) i := by
        intro i
        cases i with
        | inl a =>
          have hrw : (augment Q pred kk) (e2 (Sum.inl a)) = Q a := by
            simp only [augment, e2, finSumFinEquiv_apply_left, Fin.addCases_left]
          simp only [Sum.elim_inl, hrw]
        | inr a =>
          have hrw : (augment Q pred kk) (e2 (Sum.inr a)) = pred := by
            simp only [augment, e2, finSumFinEquiv_apply_right, Fin.addCases_right]
          simp only [Sum.elim_inr, hrw]
      rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
      rw [Fintype.sum_sumElim]
      congr 1
      · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            smul_eq_mul, mul_one]
      · by_cases hR : R (pred j) (m j)
        · simp [hR]
        · simp [hR]
    -- Count on P-block for P' equals twice the count for P.
    have hPblock : ∀ (R : ℝ → ℝ → Prop)
        [DecidablePred (fun i : Fin (n + n) => R (P' i j) (m j))]
        [DecidablePred (fun i : Fin n => R (P i j) (m j))],
        (Finset.univ.filter (fun i : Fin (n + n) => R (P' i j) (m j))).card =
        2 * (Finset.univ.filter (fun i : Fin n => R (P i j) (m j))).card := by
      intro R _ _
      classical
      have hc1 : (Finset.univ.filter (fun i : Fin (n + n) => R (P' i j) (m j))).card =
          ∑ i : Fin (n + n), (if R (P' i j) (m j) then (1 : ℕ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            smul_eq_mul, mul_one]
      have hc2 : (Finset.univ.filter (fun i : Fin n => R (P i j) (m j))).card =
          ∑ i : Fin n, (if R (P i j) (m j) then (1 : ℕ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            smul_eq_mul, mul_one]
      rw [hc1, hc2]
      rw [← Equiv.sum_comp e (fun i : Fin (n + n) =>
            (if R (P' i j) (m j) then (1 : ℕ) else 0))]
      have hF : ∀ i : Fin n ⊕ Fin n,
          (if R (P' (e i) j) (m j) then (1 : ℕ) else 0) =
          Sum.elim
            (fun a : Fin n => if R (P a j) (m j) then (1 : ℕ) else 0)
            (fun a : Fin n => if R (P a j) (m j) then (1 : ℕ) else 0) i := by
        intro i
        cases i with
        | inl a =>
          show (if R (P' (e (Sum.inl a)) j) (m j) then (1 : ℕ) else 0) = _
          have hrw : P' (e (Sum.inl a)) = P a := by
            show Sum.elim P P (e.symm (e (Sum.inl a))) = P a
            rw [e.symm_apply_apply]; rfl
          simp [hrw]
        | inr a =>
          show (if R (P' (e (Sum.inr a)) j) (m j) then (1 : ℕ) else 0) = _
          have hrw : P' (e (Sum.inr a)) = P a := by
            show Sum.elim P P (e.symm (e (Sum.inr a))) = P a
            rw [e.symm_apply_apply]; rfl
          simp [hrw]
      rw [Finset.sum_congr rfl (fun i _ => hF i)]
      rw [Fintype.sum_sumElim]
      ring
    -- Now combine. Get original median bounds.
    obtain ⟨hlt, hgt⟩ := hm j
    -- Rewrite original bounds via count_aug on (P, K).
    have hlt_aug := count_aug (· < ·) P (nn := n) (kk := K)
    have hgt_aug := count_aug (· > ·) P (nn := n) (kk := K)
    -- And the new (P', K+K) counts.
    have hlt_aug' := count_aug (· < ·) P' (nn := n + n) (kk := K + K)
    have hgt_aug' := count_aug (· > ·) P' (nn := n + n) (kk := K + K)
    rw [hPblock (· < ·)] at hlt_aug'
    rw [hPblock (· > ·)] at hgt_aug'
    -- The augmented size is n + n + (K + K) = 2(n+K); half is n+K.
    have hsize : (n + n + (K + K)) / 2 = n + K := by omega
    refine ⟨?_, ?_⟩
    · rw [hlt_aug', hsize]
      rw [hlt_aug] at hlt
      by_cases hR : (pred j) < (m j)
      · simp only [hR, if_true] at hlt ⊢
        have hpar : (n + K) / 2 + (n + K) / 2 ≤ n + K := by omega
        omega
      · simp only [hR, if_false] at hlt ⊢
        have hpar : (n + K) / 2 + (n + K) / 2 ≤ n + K := by omega
        omega
    · rw [hgt_aug', hsize]
      rw [hgt_aug] at hgt
      by_cases hR : (pred j) > (m j)
      · simp only [hR, if_true] at hgt ⊢
        have hpar : (n + K) / 2 + (n + K) / 2 ≤ n + K := by omega
        omega
      · simp only [hR, if_false] at hgt ⊢
        have hpar : (n + K) / 2 + (n + K) / 2 ≤ n + K := by omega
        omega
  -- optSocialCost doubles exactly: optSocialCost 2 P' = 2 * optSocialCost 2 P.
  have h_opt_le : optSocialCost 2 P' ≤ 2 * optSocialCost 2 P := by
    have hhalf : optSocialCost 2 P' / 2 ≤ optSocialCost 2 P := by
      apply le_ciInf
      intro f
      have hle := optSocialCost_le_socialCost (show (1:ℝ) ≤ 2 by norm_num) P' f
      rw [h_sc f] at hle
      linarith
    linarith
  have h_opt_ge : 2 * optSocialCost 2 P ≤ optSocialCost 2 P' := by
    have : ∀ f, 2 * optSocialCost 2 P ≤ socialCost 2 P' f := by
      intro f
      rw [h_sc f]
      have := optSocialCost_le_socialCost (show (1:ℝ) ≤ 2 by norm_num) P f
      linarith
    unfold optSocialCost
    exact le_ciInf (fun f => this f)
  have h_opt_eq : optSocialCost 2 P' = 2 * optSocialCost 2 P := le_antisymm h_opt_le h_opt_ge
  have h_opt : optSocialCost 2 P' ≤ 2 * optSocialCost 2 P := h_opt_le
  -- fstar is optimal for P' as well: socialCost 2 P' fstar = optSocialCost 2 P'.
  have hfstar' : socialCost 2 P' fstar = optSocialCost 2 P' := by
    rw [h_sc fstar, hfstar, h_opt_eq]
  -- Apply h_even to P'.
  have h_main := h_even (by rw [hcn2]; exact hn2_even) hcn2' hd P' pred fstar hfstar' m hm' hgp hgppred
  -- Convert back.
  have h_lhs : socialCost 2 P' m = 2 * socialCost 2 P m := h_sc m
  have hRG_nn : 0 ≤ RG c := by
    unfold RG
    apply div_nonneg (Real.sqrt_nonneg _)
    linarith
  rw [h_lhs] at h_main
  have h_chain : 2 * socialCost 2 P m ≤ RG c * (2 * optSocialCost 2 P) := by
    calc 2 * socialCost 2 P m
        ≤ RG c * optSocialCost 2 P' := h_main
      _ ≤ RG c * (2 * optSocialCost 2 P) := mul_le_mul_of_nonneg_left h_opt hRG_nn
  have h2 : RG c * (2 * optSocialCost 2 P) = 2 * (RG c * optSocialCost 2 P) := by ring
  rw [h2] at h_chain
  linarith

end Workspace.ProofLemmas.RGEvenAugmentReduction
