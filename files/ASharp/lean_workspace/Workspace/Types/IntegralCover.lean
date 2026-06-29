import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Workspace.Types.IntegralCover

/--
An *integral cover* of a family `ℋ ⊆ 2^X` is a `{0,1}`-valued function
`g : Finset X → Bool` such that every `H ∈ ℋ` has some subset `W ⊆ H`
with `g W = true`. Equivalently, the subfamily `{W : g W = true}` meets
every `H ∈ ℋ` in at least one of its subsets.

Only the indicator data and the covering condition are recorded here.
The LP cost bound `∑_W (if g W then 1 else 0) * p^|W| ≤ 1/2` is *not*
part of this structure; it is captured separately by an `IsPSmall`
predicate.
-/
structure IntegralCover (X : Type*) [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) where
  /-- The `{0,1}`-valued indicator (encoded as `Bool`) of the chosen subfamily. -/
  g        : Finset X → Bool
  /-- For every `H ∈ ℋ`, some subset `W ⊆ H` is selected by `g`. -/
  is_cover : ∀ H ∈ ℋ, ∃ W : Finset X, W ⊆ H ∧ g W = true

end Workspace.Types.IntegralCover
