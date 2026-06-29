import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Lemmas.Lemma_LambdaH_DenomEq
import Workspace.Lemmas.Lemma_LambdaH_DenomPos

open BigOperators

namespace Workspace.Lemmas.LambdaH_LeOne

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Theorem: λ_H(x) ≤ 1 for all x.

Proof strategy: The numerator for x only includes W with x ∈ W, while
the denominator includes all W ⊆ H. So numerator ≤ denominator.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_le_one (H : Finset X) (hH : H ∈ ℋ) (x : X) :
    lambdaH cov H hH x ≤ 1 := by
  unfold lambdaH
  have denom_pos := Workspace.Lemmas.LambdaH_DenomPos.lambdaH_denom_pos cov H hH
  rw [div_le_one denom_pos]
  -- Show numerator ≤ denominator
  -- Rewrite denominator using denom_eq
  rw [Workspace.Lemmas.LambdaH_DenomEq.lambdaH_denom_eq cov H hH]
  -- Each term: (if x ∈ W then w(W)/|W| else 0) ≤ w(W)
  apply Finset.sum_le_sum
  intro W _hW
  split_ifs with h
  · -- x ∈ W: w(W)/|W| ≤ w(W)
    apply div_le_self (cov.nonneg W)
    have hcard : 0 < W.card := Finset.card_pos.mpr ⟨x, h⟩
    exact_mod_cast hcard
  · exact cov.nonneg W

end Workspace.Lemmas.LambdaH_LeOne
