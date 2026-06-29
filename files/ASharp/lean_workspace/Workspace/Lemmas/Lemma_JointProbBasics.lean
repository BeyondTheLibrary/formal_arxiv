import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Workspace.Definitions.ProbDistributions

open BigOperators

namespace Workspace.Lemmas.JointProbBasics

open Workspace.Definitions.ProbDistributions

/-- The Bernoulli weight `∏_i q^|W_i|·(1-q)^(|X|-|W_i|)` is non-negative
when `q ∈ [0,1]`. -/
lemma joint_weight_nonneg {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (W : Fin s → Finset X)
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1) :
    0 ≤ ∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card) := by
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg
  · exact pow_nonneg hq_nn _
  · apply pow_nonneg; linarith

/-- Linearity over addition. -/
theorem prob_xp_joint_add {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (φ ψ : (Fin s → Finset X) → ℝ) :
    ProbXpJoint q s (fun W => φ W + ψ W) =
    ProbXpJoint q s φ + ProbXpJoint q s ψ := by
  unfold ProbXpJoint
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro W _; ring

/-- Pointwise monotonicity for `q ∈ [0,1]`. -/
theorem prob_xp_joint_mono {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (φ ψ : (Fin s → Finset X) → ℝ)
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1)
    (h_le : ∀ W, φ W ≤ ψ W) :
    ProbXpJoint q s φ ≤ ProbXpJoint q s ψ := by
  unfold ProbXpJoint
  apply Finset.sum_le_sum
  intro W _
  exact mul_le_mul_of_nonneg_right (h_le W) (joint_weight_nonneg q s W hq_nn hq_le)

/-- Normalisation: the joint distribution sums to 1 over the constant function 1.

Proof:
* Swap `∑ W : Fin s → Finset X, ∏ i, ...` to `∏ i, ∑ S : Finset X, ...` via
  `Finset.sum_prod_piFinset` (after converting `Finset.univ` over functions to
  `Fintype.piFinset` of pointwise `Finset.univ`).
* Each inner sum equals `(q + (1-q))^(card X) = 1` by `Fintype.sum_pow_mul_eq_add_pow`.
* The outer product over `Fin s` of `1`'s is `1`. -/
theorem prob_xp_joint_norm {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (_hq_nn : 0 ≤ q) (_hq_le : q ≤ 1) :
    ProbXpJoint q s (fun _ : Fin s → Finset X => (1 : ℝ)) = 1 := by
  unfold ProbXpJoint
  simp only [one_mul]
  -- Convert `Finset.univ : Finset (Fin s → Finset X)` to a `piFinset`.
  rw [show (Finset.univ : Finset (Fin s → Finset X)) =
        Fintype.piFinset (fun _ : Fin s => (Finset.univ : Finset (Finset X))) from
        Fintype.piFinset_univ.symm]
  -- Swap sum-of-product with product-of-sum.
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset (Finset X))
        (fun (_ : Fin s) (W : Finset X) =>
          q ^ W.card * (1 - q) ^ (Fintype.card X - W.card))]
  -- Each inner sum equals (q + (1-q))^(card X) = 1.
  apply Finset.prod_eq_one
  intro i _
  rw [Fintype.sum_pow_mul_eq_add_pow]
  have h_one : q + (1 - q) = (1 : ℝ) := by ring
  rw [h_one, one_pow]

/-- Complement probability: `Pr[¬A] = 1 - Pr[A]`. -/
theorem prob_xp_joint_complement {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (P : (Fin s → Finset X) → Prop) [DecidablePred P]
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1) :
    ProbXpJoint q s (fun W => if P W then (0 : ℝ) else 1) =
      1 - ProbXpJoint q s (fun W => if P W then (1 : ℝ) else 0) := by
  have h_norm := prob_xp_joint_norm (X := X) q s hq_nn hq_le
  have h_split :
      ProbXpJoint q s (fun W => if P W then (0 : ℝ) else 1) +
        ProbXpJoint q s (fun W => if P W then (1 : ℝ) else 0) =
      ProbXpJoint q s (fun _ : Fin s → Finset X => (1 : ℝ)) := by
    rw [← prob_xp_joint_add (X := X) q s
          (fun W => if P W then (0 : ℝ) else 1)
          (fun W => if P W then (1 : ℝ) else 0)]
    unfold ProbXpJoint
    apply Finset.sum_congr rfl
    intro W _
    simp only []
    have : (if P W then (0 : ℝ) else 1) + (if P W then (1 : ℝ) else 0) = 1 := by
      by_cases h : P W <;> simp [h]
    rw [this]
  linarith [h_split, h_norm]

end Workspace.Lemmas.JointProbBasics
