import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Workspace.Definitions.ProbDistributions

open BigOperators
open Workspace.Definitions.ProbDistributions

namespace Workspace.Lemmas.ProbXpSetMonotone

/-- Set monotonicity of `ProbXp`: if `A ⊆ B` and `0 ≤ q ≤ 1`, then `ProbXp q A ≤ ProbXp q B`.

    Each Bernoulli weight `q^|S| · (1-q)^(|X|-|S|)` is nonnegative when `q ∈ [0,1]`,
    so summing the indicator over a larger set yields a larger value.
-/
theorem prob_xp_set_monotone {X : Type} [Fintype X]
    (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_le : q ≤ 1)
    {A B : Set (Finset X)} (hAB : A ⊆ B) :
    ProbXp q A ≤ ProbXp q B := by
  unfold ProbXp
  apply Finset.sum_le_sum
  intro S _
  by_cases hSA : S ∈ A
  · -- S ∈ A, so S ∈ B; both are q^|S| * (1-q)^(|X|-|S|)
    have hSB : S ∈ B := hAB hSA
    simp [hSA, hSB]
  · -- S ∉ A, LHS is 0
    by_cases hSB : S ∈ B
    · -- S ∈ B, RHS is q^|S| * (1-q)^(|X|-|S|) which is nonneg
      simp [hSA, hSB]
      have h1 : 0 ≤ q ^ S.card := pow_nonneg hq_nonneg _
      have h2 : 0 ≤ (1 - q) ^ (Fintype.card X - S.card) :=
        pow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    · simp [hSA, hSB]

end Workspace.Lemmas.ProbXpSetMonotone
