import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_NumZeroOfNotMem

namespace Workspace.Lemmas.LambdaH_Support

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Theorem: λ_H(x) = 0 when x ∉ H.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_support (H : Finset X) (hH : H ∈ ℋ) (x : X) (hx : x ∉ H) :
    lambdaH cov H hH x = 0 := by
  unfold lambdaH
  have num_zero := Workspace.Lemmas.LambdaH_NumZeroOfNotMem.lambdaH_num_zero_of_not_mem cov H hH x hx
  rw [num_zero]
  exact zero_div _

end Workspace.Lemmas.LambdaH_Support
