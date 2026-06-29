import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Workspace.Types.IsPSmall

open BigOperators

namespace Workspace.Lemmas.CoverBoundFromNotPSmall

open Workspace.Types.IsPSmall

/-- **Cover bound from "not p-small"** (paper §3.3, the inequality
`∑_{U ∈ 𝒰(W)} p^|U| ≥ 1/2` whenever `𝒰(W)` is a cover of `ℋ`).

Statement (informal): if `ℋ` is *not* `p`-small, then for every cover
`𝒰` of `ℋ` (i.e. every `H ∈ ℋ` has some `U ∈ 𝒰` with `U ⊆ H`), we have
`∑_{U ∈ 𝒰} p^{|U|} ≥ 1/2`.

In the present formalisation, we expose this as a generic fact about
covers `g : Finset X → Bool` of `ℋ`. By definition of `IsPSmall`, the
*negation* says: for every integral cover `g`, the cost
`∑_W (if g W then 1 else 0) * p^|W|` is `> 1/2`. This is what we
package here.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 3.3, "Conclusion" paragraph)
-/
theorem cover_bound_of_not_psmall
    {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (p : ℝ)
    (h_not_small : ¬ IsPSmall ℋ p) :
    ∀ (g : Workspace.Types.IntegralCover.IntegralCover X ℋ),
      1 / 2 < ∑ W : Finset X, (if g.g W then (1 : ℝ) else 0) * p ^ W.card := by
  intro g
  -- IsPSmall ℋ p is: ∃ g, cost g ≤ 1/2.
  -- ¬ IsPSmall ℋ p is: ∀ g, ¬ (cost g ≤ 1/2), i.e. cost g > 1/2.
  unfold IsPSmall at h_not_small
  push_neg at h_not_small
  exact h_not_small g

end Workspace.Lemmas.CoverBoundFromNotPSmall
