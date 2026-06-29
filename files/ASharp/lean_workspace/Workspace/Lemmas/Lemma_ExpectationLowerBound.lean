import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Workspace.Definitions.ProbDistributions

open Workspace.Definitions.ProbDistributions
open BigOperators

namespace Workspace.Lemmas.ExpectationLowerBound

/-- If an event has probability at least p and the random variable is at least v on that event,
    then the expectation is at least p * v. This is a standard probability fact.

    The hypothesis `h_Z_nonneg : ∀ W, 0 ≤ Z W` is required: without it the statement is false
    (a large negative `Z` outside `A` can drive the RHS arbitrarily negative). In the intended
    application (`exp_bound`), `Z(W) = ∑_{W' ⊆ W} cov.w W' ≥ 0`, so the hypothesis is satisfied.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem expectation_lower_bound {X : Type} [Fintype X] (A : Set (Finset X)) (p q v : ℝ)
    (Z : Finset X → ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq_le : q ≤ 1)
    (h_Z_nonneg : ∀ W : Finset X, 0 ≤ Z W)
    (h_prob : p ≤ ProbXp q A)
    (h_val : ∀ W ∈ A, v ≤ Z W) :
    p * v ≤ ∑ W : Finset X, Z W * (q ^ W.card * (1 - q) ^ (Fintype.card X - W.card)) := by
  -- The Bernoulli weight is nonneg.
  have h_one_sub_q_nonneg : 0 ≤ 1 - q := by linarith
  have h_w_nonneg : ∀ W : Finset X,
      0 ≤ q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) := by
    intro W
    exact mul_nonneg (pow_nonneg hq _) (pow_nonneg h_one_sub_q_nonneg _)
  -- Abbreviation for weight.
  set w : Finset X → ℝ := fun W => q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) with hw_def
  -- Decidability of A-membership.
  classical
  -- Step 1: RHS ≥ ∑_{W ∈ A} Z W * w W (drop nonneg terms outside A).
  have h_split :
      ∑ W : Finset X, (if W ∈ A then Z W * w W else 0)
        ≤ ∑ W : Finset X, Z W * w W := by
    apply Finset.sum_le_sum
    intro W _
    by_cases hWA : W ∈ A
    · simp [hWA]
    · simp [hWA]
      exact mul_nonneg (h_Z_nonneg W) (h_w_nonneg W)
  -- Step 2: ∑_{W ∈ A} Z W * w W ≥ ∑_{W ∈ A} v * w W (since v ≤ Z on A and w ≥ 0).
  have h_val_sum :
      ∑ W : Finset X, (if W ∈ A then v * w W else 0)
        ≤ ∑ W : Finset X, (if W ∈ A then Z W * w W else 0) := by
    apply Finset.sum_le_sum
    intro W _
    by_cases hWA : W ∈ A
    · simp [hWA]
      exact mul_le_mul_of_nonneg_right (h_val W hWA) (h_w_nonneg W)
    · simp [hWA]
  -- Step 3: ∑_{W ∈ A} v * w W = v * ProbXp q A.
  have h_factor :
      ∑ W : Finset X, (if W ∈ A then v * w W else 0)
        = v * ProbXp q A := by
    unfold ProbXp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    by_cases hWA : W ∈ A
    · simp [hWA, hw_def]
    · simp [hWA]
  -- Step 4: combine the above into v * ProbXp q A ≤ RHS.
  have h_RHS_ge_v_prob :
      v * ProbXp q A ≤ ∑ W : Finset X, Z W * w W := by
    rw [← h_factor]
    exact le_trans h_val_sum h_split
  -- Step 5: case-split on the sign of v.
  rcases lt_or_ge v 0 with hv_neg | hv_nonneg
  · -- v < 0: p * v ≤ 0 ≤ RHS (since Z ≥ 0 and w ≥ 0).
    have h_pv_nonpos : p * v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp (le_of_lt hv_neg)
    have h_RHS_nonneg : 0 ≤ ∑ W : Finset X, Z W * w W := by
      apply Finset.sum_nonneg
      intro W _
      exact mul_nonneg (h_Z_nonneg W) (h_w_nonneg W)
    linarith
  · -- v ≥ 0: chain  p * v ≤ ProbXp q A * v ≤ RHS.
    have h_pv_le : p * v ≤ ProbXp q A * v :=
      mul_le_mul_of_nonneg_right h_prob hv_nonneg
    have h_eq : ProbXp q A * v = v * ProbXp q A := by ring
    calc p * v ≤ ProbXp q A * v := h_pv_le
      _ = v * ProbXp q A := h_eq
      _ ≤ ∑ W : Finset X, Z W * w W := h_RHS_ge_v_prob

end Workspace.Lemmas.ExpectationLowerBound
