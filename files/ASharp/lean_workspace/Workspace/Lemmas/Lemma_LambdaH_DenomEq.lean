import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH

open BigOperators

namespace Workspace.Lemmas.LambdaH_DenomEq

open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ℋ : Set (Finset X)} (cov : FractionalCover X ℋ)

/-- Helper: rewrite the denominator as ∑_{W ⊆ H} w(W).

Proof strategy: Exchange order of summation, then for each W ⊆ H:
∑_{y ∈ H} (if y ∈ W then w(W)/|W| else 0) = ∑_{y ∈ W} w(W)/|W| = w(W).

The equality ∑_{y ∈ W} w(W)/|W| = w(W) follows from:
- ∑_{y ∈ W} w(W)/|W| = |W| · (w(W)/|W|) = w(W) when |W| > 0
- Both sides are 0 when W = ∅ (by w_empty)

This is mathematically straightforward but requires library work for sum exchange.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
lemma lambdaH_denom_eq (H : Finset X) (hH : H ∈ ℋ) :
    (∑ y ∈ H, ∑ W ∈ H.powerset, if y ∈ W then cov.w W / (W.card : ℝ) else 0)
    = ∑ W ∈ H.powerset, cov.w W := by
  -- Exchange order of summation
  rw [Finset.sum_comm]
  -- Now goal: ∑ W ∈ H.powerset, ∑ y ∈ H, if y ∈ W then w(W)/|W| else 0 = ∑ W ∈ H.powerset, w(W)
  apply Finset.sum_congr rfl
  intro W hW
  rw [Finset.mem_powerset] at hW
  -- Inner sum: ∑ y ∈ H, if y ∈ W then w(W)/|W| else 0
  -- Filter to y ∈ W: = ∑ y ∈ W, w(W)/|W|  (since W ⊆ H)
  rw [← Finset.sum_filter]
  -- {y ∈ H | y ∈ W} = W since W ⊆ H
  have h_filter : H.filter (· ∈ W) = W := by
    ext y; simp only [Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hW h, h⟩⟩
  rw [h_filter]
  -- ∑ y ∈ W, w(W)/|W| = |W| * (w(W)/|W|) = w(W)
  rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos W.card with h | h
  · -- W = ∅ case: |W| = 0, so both sides are 0
    simp [h, Finset.card_eq_zero.mp h |>.symm ▸ cov.w_empty]
  · -- W nonempty: cancel |W|
    have hc : (W.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    rw [mul_comm, div_mul_cancel₀ _ hc]

end Workspace.Lemmas.LambdaH_DenomEq
