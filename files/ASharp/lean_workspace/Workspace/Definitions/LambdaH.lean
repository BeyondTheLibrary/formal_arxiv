import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover

open BigOperators

namespace Workspace.Definitions.LambdaH

open Workspace.Types.FractionalCover

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- The weight vector λ_H constructed from the fractional cover w. -/
noncomputable def lambdaH (H : Finset X) (_hH : H ∈ ℋ) (x : X) : ℝ :=

  let num := ∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0
  let den := ∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0
  num / den

end Workspace.Definitions.LambdaH
