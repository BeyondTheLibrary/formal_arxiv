import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators
open Real
open Classical

namespace Workspace.Definitions.ProbDistributions

/-- The probability of a property `A ⊆ 2^X` under the product measure `X_p`. -/
noncomputable def ProbXp {X : Type} [Fintype X] (p : ℝ) (A : Set (Finset X)) : ℝ :=
  ∑ S : Finset X, if S ∈ A then p ^ S.card * (1 - p) ^ (Fintype.card X - S.card) else 0

/-- Joint product distribution `X_q^s` evaluated as an expectation:
    `E_{W₁,…,W_s ∼ X_q indep.}[φ W]`. -/
noncomputable def ProbXpJoint {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (φ : (Fin s → Finset X) → ℝ) : ℝ :=
  ∑ W : Fin s → Finset X,
    φ W * ∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card)

end Workspace.Definitions.ProbDistributions
