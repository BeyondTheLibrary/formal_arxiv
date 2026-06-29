import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Workspace.Types.IsPSmall
import Workspace.Definitions.LambdaH
import Workspace.Definitions.ProbDistributions
import Workspace.Lemmas.Lemma_KeyLemma
import Workspace.Lemmas.Lemma_UnionDistribution
import Workspace.Lemmas.Lemma_JointProbBasics

open BigOperators
open Classical

namespace Workspace.Lemmas.ProbGoodEvent

open Workspace.Types.IsPSmall
open Workspace.Definitions.ProbDistributions
open Workspace.Lemmas.KeyLemma
open Workspace.Lemmas.UnionDistribution
open Workspace.Lemmas.JointProbBasics

/-- **`prob_good_event` (Theorem 1.3 deep content, paper Section 3.3).**

For `q = 16p`, if `ℋ` is *not* `p`-small and `λ_H : X → [0,1]` is any family
of weight vectors, then
`1/3 ≤ ProbXp (1 - (1-q)^s) {W : ∃ H ∈ ℋ, 1 - 2^{-s} ≤ ∑_{x ∈ W} λ_H(x)}`.

# Proof structure

Following the paper Section 3.3:

1. **Bad event**: `W = (W_1,…,W_s)` is *bad* iff `∀ H ∈ ℋ`,
   `∑_{x ∈ ⋃W_i ∩ H} λ_H(x) < 1 - 2^{-s}`.

2. **`Lemma_KeyLemma.key_lemma_bound`** gives `Pr_{joint}[bad] ≤ 2/3`
   (the deep content of paper §3.3, now admitted as the single
   `¬IsPSmall ℋ p`-scoped bound axiom `Workspace.Axioms.LemKey.lem_key_bound`
   — the paper's `lem:key` bound).

3. **`Lemma_JointProbBasics.prob_xp_joint_complement`** gives
   `Pr[¬bad] = 1 - Pr[bad] ≥ 1/3` (uses `prob_xp_joint_norm`, which is
   the discrete Bernoulli normalisation identity, fully proven).

4. **"Not bad ⇒ heavy"**: if `W` is not bad, some `H` witnesses
   `1 - 2^{-s} ≤ ∑_{x ∈ ⋃W_i ∩ H} λ_H ≤ ∑_{x ∈ ⋃W_i} λ_H` (since `λ_H ≥ 0`),
   so `⋃W_i` lies in the heavy event.

5. **`Lemma_JointProbBasics.prob_xp_joint_mono`** lifts the pointwise
   inequality `I[¬bad] ≤ I[(⋃W_i) ∈ heavy]` to the joint expectation.

6. **`Lemma_UnionDistribution.union_distribution_eq`** gives
   `Pr_{joint}[(⋃W_i) ∈ A] = ProbXp (1 - (1-q)^s) A` (fully proven).

7. **Conclude**: combine the chain to land in `1/3 ≤ ProbXp (1-(1-q)^s) heavy`.

# Status

The remaining external assumption is exactly the single minimal
`¬IsPSmall ℋ p`-scoped bound axiom `Workspace.Axioms.LemKey.lem_key_bound`
(the paper's §3.3 `lem:key` bound).

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 3.3, eqs. 3.6 and surrounding)
-/
theorem prob_good_event
    {X : Type} [Fintype X] [DecidableEq X]
    (p q : ℝ) (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (hp : 0 < p) (hq : q = 16 * p) (hq_le_one : q ≤ 1)
    (h_not_small : ¬ IsPSmall ℋ p)
    (h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card)
    (h_range : ∀ H hH x, 0 ≤ lambda_vec H hH x ∧ lambda_vec H hH x ≤ 1)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    1 / 3 ≤ ProbXp (1 - (1 - q) ^ s)
      {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
        1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambda_vec H hH x} := by
  -- Density q = 16p ≥ 0.
  have hq_nonneg : (0 : ℝ) ≤ q := by rw [hq]; linarith
  -- Abbreviate the heavy event for clarity.
  set heavyEvent : Set (Finset X) :=
    {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
      1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambda_vec H hH x} with h_heavyEvent_def

  -- ===== Step 2: key lemma bound =====
  have h_key : ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) ≤ 2/3 :=
    KeyLemma.key_lemma_bound p q ℋ s lambda_vec hp hq hq_le_one h_not_small h_H_nonempty h_range
      h_support h_sum_ge_one

  -- ===== Step 3: complement =====
  have h_complement :
      ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (0 : ℝ) else 1) =
      1 - ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) :=
    prob_xp_joint_complement (X := X) q s (IsBad ℋ s lambda_vec) hq_nonneg hq_le_one

  have h_not_bad_ge :
      (1/3 : ℝ) ≤
      ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (0 : ℝ) else 1) := by
    rw [h_complement]; linarith

  -- ===== Step 4 & 5: not bad implies heavy on union; lift via mono =====
  -- Pointwise: I[¬bad](W) ≤ I[(⋃W_i) ∈ heavyEvent](W).
  have h_pointwise : ∀ W : Fin s → Finset X,
      (if IsBad ℋ s lambda_vec W then (0 : ℝ) else 1) ≤
      (if (Finset.univ.biUnion W) ∈ heavyEvent then (1 : ℝ) else 0) := by
    intro W
    by_cases h_bad : IsBad ℋ s lambda_vec W
    · -- Bad: LHS = 0, RHS ≥ 0 (it's an indicator).
      rw [if_pos h_bad]
      split_ifs <;> norm_num
    · -- Not bad: LHS = 1, must show ⋃W_i ∈ heavyEvent so RHS = 1.
      rw [if_neg h_bad]
      have h_in_heavy : (Finset.univ.biUnion W) ∈ heavyEvent := by
        unfold IsBad at h_bad
        push_neg at h_bad
        obtain ⟨H, hH, h_witness⟩ := h_bad
        refine ⟨H, hH, ?_⟩
        have h_subset : (Finset.univ.biUnion W) ∩ H ⊆ Finset.univ.biUnion W :=
          Finset.inter_subset_left
        have h_sum_mono :
            ∑ x ∈ (Finset.univ.biUnion W) ∩ H, lambda_vec H hH x ≤
            ∑ x ∈ Finset.univ.biUnion W, lambda_vec H hH x :=
          Finset.sum_le_sum_of_subset_of_nonneg h_subset
            (fun x _ _ => (h_range H hH x).1)
        linarith
      rw [if_pos h_in_heavy]

  have h_mono :
      ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (0 : ℝ) else 1) ≤
      ProbXpJoint q s
        (fun W => if (Finset.univ.biUnion W) ∈ heavyEvent then (1 : ℝ) else 0) :=
    prob_xp_joint_mono q s _ _ hq_nonneg hq_le_one h_pointwise

  -- ===== Step 6: union distribution =====
  have h_union :
      ProbXpJoint q s
        (fun W => if (Finset.univ.biUnion W) ∈ heavyEvent then (1 : ℝ) else 0)
      = ProbXp (1 - (1 - q) ^ s) heavyEvent := by
    have h := UnionDistribution.union_distribution_eq q s heavyEvent hq_nonneg hq_le_one
    -- The two if-expressions agree pointwise (Decidable on a Prop is a
    -- subsingleton), so the ProbXpJoint values are equal.
    have h_fn_eq :
        (fun W : Fin s → Finset X =>
            if (Finset.univ.biUnion W) ∈ heavyEvent then (1 : ℝ) else 0) =
        (fun W : Fin s → Finset X =>
            @ite ℝ ((Finset.univ.biUnion W) ∈ heavyEvent)
              (Classical.propDecidable _) 1 0) := by
      funext W
      congr 1
    rw [h_fn_eq]
    exact h

  -- ===== Step 7: combine =====
  rw [← h_heavyEvent_def] at *
  linarith [h_not_bad_ge, h_mono, h_union]

end Workspace.Lemmas.ProbGoodEvent
