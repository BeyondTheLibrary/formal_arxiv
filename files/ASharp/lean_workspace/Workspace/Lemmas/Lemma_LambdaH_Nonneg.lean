import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_NumNonneg
import Workspace.Lemmas.Lemma_LambdaH_DenomPos

namespace Workspace.Lemmas.LambdaH_Nonneg

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Theorem: λ_H(x) is non-negative.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_nonneg (H : Finset X) (hH : H ∈ ℋ) (x : X) :
    0 ≤ lambdaH cov H hH x := by
  unfold lambdaH
  have num_nonneg := Workspace.Lemmas.LambdaH_NumNonneg.lambdaH_num_nonneg cov H hH x
  have denom_pos := Workspace.Lemmas.LambdaH_DenomPos.lambdaH_denom_pos cov H hH
  exact div_nonneg num_nonneg (le_of_lt denom_pos)

end Workspace.Lemmas.LambdaH_Nonneg
