import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Workspace.Types.FractionalCover

open BigOperators

namespace Workspace.Lemmas.SumOverSubsetLe

open Workspace.Types.FractionalCover

/-- If Z(W) ≥ ∑_{W' ⊆ H ∩ W} w(W') for all H ∈ ℋ and W, then
    the event {∃ H : ∑_{W' ⊆ H ∩ W} w(W') ≥ 1/2} implies Z(W) ≥ 1/2.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
lemma sum_over_subset_le {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (cov : FractionalCover X ℋ)
    (W : Finset X) (H : Finset X) (hH : H ∈ ℋ) :
    ∑ W' ∈ (H ∩ W).powerset, cov.w W' ≤ ∑ W' ∈ W.powerset, cov.w W' := by
  have h_subset : (H ∩ W).powerset ⊆ W.powerset := by
    intro W' hW'
    simp only [Finset.mem_powerset] at hW' ⊢
    exact hW'.trans Finset.inter_subset_right
  have h_sdiff := Finset.sum_sdiff h_subset (f := cov.w)
  have h_nonneg : 0 ≤ ∑ W' ∈ W.powerset \ (H ∩ W).powerset, cov.w W' :=
    Finset.sum_nonneg (fun W' _ => cov.nonneg W')
  linarith

end Workspace.Lemmas.SumOverSubsetLe
