import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset
open BigOperators

namespace Workspace.Types.FractionalCover

/--
A fractional cover of a family `ℋ ⊆ 2^X` is a function
`w : Finset X → ℝ` taking values in `[0,1]` such that for every `H ∈ ℋ`,
the sum `∑_{W ⊆ H} w(W)` is at least `1`.

This is the LP-relaxation of the cover used to define Talagrand's
fractional expectation threshold.
-/
structure FractionalCover (X : Type*) [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) where
  /-- The cover function on subsets of `X`. -/
  w        : Finset X → ℝ
  /-- Nonnegativity of `w`. -/
  nonneg   : ∀ W : Finset X, 0 ≤ w W
  /-- Upper bound: `w W ≤ 1` for all `W`. -/
  le_one   : ∀ W : Finset X, w W ≤ 1
  /-- Fractional covering inequality: for every `H ∈ ℋ`,
      `1 ≤ ∑ W ∈ H.powerset, w W`. -/
  is_cover : ∀ H ∈ ℋ, (1 : ℝ) ≤ ∑ W ∈ H.powerset, w W
  /-- The empty set has weight zero. -/
  w_empty  : w ∅ = 0

end Workspace.Types.FractionalCover
