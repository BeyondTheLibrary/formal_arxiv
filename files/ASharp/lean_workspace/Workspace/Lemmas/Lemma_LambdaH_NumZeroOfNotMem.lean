import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH

open BigOperators

namespace Workspace.Lemmas.LambdaH_NumZeroOfNotMem

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Helper: the numerator is 0 when x is not in H.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_num_zero_of_not_mem (H : Finset X) (_hH : H ∈ ℋ) (x : X) (hx : x ∉ H) :
    (∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun W hW => ?_
  by_cases h : x ∈ W
  · -- If x ∈ W and W ⊆ H, then x ∈ H, contradiction
    exfalso
    have W_sub_H : W ⊆ H := Finset.mem_powerset.mp hW
    exact hx (W_sub_H h)
  · simp [h]

end Workspace.Lemmas.LambdaH_NumZeroOfNotMem
