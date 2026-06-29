import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH

open BigOperators

namespace Workspace.Lemmas.LambdaH_NumSumEqDenom

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Helper: Sum of numerators over all x equals the denominator.

For each W ⊆ H, the contribution to the sum is:
∑_{x ∈ X} ∑_{W ∋ x} w(W)/|W| = ∑_W (∑_{x ∈ W} w(W)/|W|) = ∑_W w(W).

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_num_sum_eq_denom (H : Finset X) (hH : H ∈ ℋ) :
    (∑ x : X, ∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0)
    = ∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0 := by
  symm
  -- Use Finset.sum_subset: for x ∉ H, the inner sum is 0
  apply Finset.sum_subset (Finset.subset_univ H)
  intro x _ hx
  apply Finset.sum_eq_zero
  intro W hW
  simp only [ite_eq_right_iff]
  intro hxW
  -- x ∈ W and W ⊆ H implies x ∈ H, contradiction
  exact absurd (Finset.mem_powerset.mp hW hxW) hx

end Workspace.Lemmas.LambdaH_NumSumEqDenom
