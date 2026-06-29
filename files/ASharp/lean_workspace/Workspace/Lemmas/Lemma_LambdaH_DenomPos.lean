import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_DenomEq

open BigOperators

namespace Workspace.Lemmas.LambdaH_DenomPos

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- The denominator of λ_H is positive when H is covered.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_denom_pos (H : Finset X) (hH : H ∈ ℋ) :
    0 < ∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0 := by
  rw [Workspace.Lemmas.LambdaH_DenomEq.lambdaH_denom_eq cov H hH]
  have cover_bound := cov.is_cover H hH
  calc ∑ W ∈ H.powerset, cov.w W
      ≥ 1 := cover_bound
    _ > 0 := by norm_num

end Workspace.Lemmas.LambdaH_DenomPos
