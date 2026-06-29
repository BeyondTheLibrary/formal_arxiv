import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_NumSumEqDenom
import Workspace.Lemmas.Lemma_LambdaH_DenomEq
import Workspace.Lemmas.Lemma_LambdaH_DenomPos

namespace Workspace.Lemmas.LambdaH_SumOne

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Theorem: ∑_{x ∈ X} λ_H(x) = 1.

Proof strategy:
- Numerator sum: ∑_x ∑_W (if x ∈ W then w(W)/|W| else 0)
- After exchange: ∑_W ∑_{x ∈ W} w(W)/|W| = ∑_W w(W)
- This equals the denominator
- Therefore the ratio is 1

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_sum_one (H : Finset X) (hH : H ∈ ℋ) :
    ∑ x : X, lambdaH cov H hH x = 1 := by
  unfold lambdaH
  -- Factor out the common denominator
  have h_num_sum := Workspace.Lemmas.LambdaH_NumSumEqDenom.lambdaH_num_sum_eq_denom cov H hH
  have h_denom_eq := Workspace.Lemmas.LambdaH_DenomEq.lambdaH_denom_eq cov H hH
  have h_denom_pos := Workspace.Lemmas.LambdaH_DenomPos.lambdaH_denom_pos cov H hH
  have h_denom_ne : (∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0) ≠ 0 :=
    ne_of_gt h_denom_pos
  -- Convert sum of ratios to ratio of sums
  rw [show ∑ x : X, (∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0) /
          (∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0) =
      (∑ x : X, ∑ W ∈ H.powerset, if x ∈ W then cov.w W / (W.card : ℝ) else 0) /
          (∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0) by
    rw [← Finset.sum_div]]
  rw [h_num_sum, h_denom_eq]
  exact div_self (h_denom_eq ▸ (h_denom_pos.ne'))

end Workspace.Lemmas.LambdaH_SumOne
