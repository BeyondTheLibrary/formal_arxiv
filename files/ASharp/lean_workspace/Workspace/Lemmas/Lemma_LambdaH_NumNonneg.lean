import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH

open BigOperators

namespace Workspace.Lemmas.LambdaH_NumNonneg

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- The numerator of λ_H(x) is non-negative.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_num_nonneg (H : Finset X) (hH : H ∈ ℋ) (x : X) :
    0 ≤ ∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0 := by
  apply Finset.sum_nonneg
  intro W _hW
  split_ifs with h
  · apply div_nonneg (cov.nonneg W)
    exact Nat.cast_nonneg _
  · exact le_refl _

end Workspace.Lemmas.LambdaH_NumNonneg
