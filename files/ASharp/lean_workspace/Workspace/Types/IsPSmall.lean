import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.IntegralCover

open BigOperators

namespace Workspace.Types.IsPSmall

open Workspace.Types.IntegralCover

/--
`IsPSmall ℋ p` asserts that the family `ℋ ⊆ 2^X` is *p-small*: there
exists an integral cover `g : 2^X → {0,1}` of `ℋ` whose LP cost
`∑_{W ∈ 2^X} g(W) · p^{|W|}` is at most `1/2`.

This is the central notion `c_int(ℋ; p) ≤ 1/2` from §1 of the paper.
-/
def IsPSmall {X : Type*} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (p : ℝ) : Prop :=
  ∃ g : IntegralCover X ℋ,
    (∑ W : Finset X, (if g.g W then (1:ℝ) else 0) * p ^ W.card) ≤ 1/2

end Workspace.Types.IsPSmall
