import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Workspace.Types.FractionalCover
import Workspace.Definitions.ProbDistributions
import Workspace.Lemmas.Lemma_ExpectationLowerBound
import Workspace.Lemmas.Lemma_ExpectationEqSum
import Workspace.Lemmas.Lemma_SumOverSubsetLe

open BigOperators
open Workspace.Types.FractionalCover
open Workspace.Definitions.ProbDistributions

namespace Workspace.Lemmas.ExpBound

/-- exp_bound theorem: expectation lower bound.

    If with probability at least 1/3 (under the product measure X_{q'}) there exists
    H ∈ ℋ with ∑_{W' ⊆ H ∩ W} w(W') ≥ 1/2, then E_{W ~ X_{q'}}[∑_{W' ⊆ W} w(W')] ≥ 1/6.

    By linearity of expectation (`expectation_eq_sum`), the RHS equals
    ∑_W w(W) q'^|W|, giving the stated bound.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem exp_bound {X : Type} [Fintype X] [DecidableEq X]
    (t : ℕ) (ℋ : Set (Finset X)) (cov : FractionalCover X ℋ)
    (q' : ℝ)
    (h_max_w : (1 / 3 : ℝ) ≤ ProbXp q' {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
                1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W'})
    (hq'_pos : 0 ≤ q') (hq'_le_one : q' ≤ 1) :
    (1 / 6 : ℝ) ≤ ∑ W : Finset X, cov.w W * q' ^ W.card := by
  -- Define Z(W) = ∑_{W' ⊆ W} cov.w W'.
  set Z : Finset X → ℝ := fun W => ∑ W' ∈ W.powerset, cov.w W' with hZ_def
  -- Z is nonneg pointwise.
  have hZ_nonneg : ∀ W, 0 ≤ Z W :=
    fun W => Finset.sum_nonneg (fun W' _ => cov.nonneg W')
  -- The "heavy" event A.
  set A : Set (Finset X) := {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
      1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W'} with hA_def
  -- For W ∈ A, Z(W) ≥ 1/2 by `sum_over_subset_le`.
  have hZ_val : ∀ W ∈ A, (1 / 2 : ℝ) ≤ Z W := by
    intro W hW
    obtain ⟨H, hH, h_half⟩ := hW
    have h_subset :=
      Workspace.Lemmas.SumOverSubsetLe.sum_over_subset_le ℋ cov W H hH
    -- h_subset : ∑ W' ∈ (H ∩ W).powerset, cov.w W' ≤ ∑ W' ∈ W.powerset, cov.w W'
    -- h_half   : 1/2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W'
    -- so 1/2 ≤ Z W.
    show (1 / 2 : ℝ) ≤ ∑ W' ∈ W.powerset, cov.w W'
    linarith
  -- Apply expectation_lower_bound with p = 1/3, v = 1/2, q = q'.
  have h_exp :
      (1 / 3 : ℝ) * (1 / 2) ≤
        ∑ W : Finset X, Z W * (q' ^ W.card * (1 - q') ^ (Fintype.card X - W.card)) :=
    Workspace.Lemmas.ExpectationLowerBound.expectation_lower_bound
      A (1 / 3) q' (1 / 2) Z (by norm_num) hq'_pos hq'_le_one
      hZ_nonneg h_max_w hZ_val
  -- Build a coerced cover with empty ℋ to feed `expectation_eq_sum`.
  let cov0 : FractionalCover X (∅ : Set (Finset X)) :=
    { w := cov.w
    , nonneg := cov.nonneg
    , le_one := cov.le_one
    , is_cover := fun H hH => absurd hH (Set.notMem_empty H)
    , w_empty := cov.w_empty }
  -- Linearity of expectation: ∑ cov.w W * q'^|W| = ∑ Z(W) * Bernoulli weight.
  have h_eq :
      (∑ W : Finset X, cov0.w W * q' ^ W.card) =
        ∑ W : Finset X, (∑ W' ∈ W.powerset, cov0.w W') *
          (q' ^ W.card * (1 - q') ^ (Fintype.card X - W.card)) :=
    Workspace.Lemmas.ExpectationEqSum.expectation_eq_sum cov0 q' hq'_pos hq'_le_one
  -- cov0.w = cov.w by construction, so we may rewrite.
  have h_eq' :
      (∑ W : Finset X, cov.w W * q' ^ W.card) =
        ∑ W : Finset X, Z W *
          (q' ^ W.card * (1 - q') ^ (Fintype.card X - W.card)) := h_eq
  -- Combine.
  have h_one_six : (1 / 3 : ℝ) * (1 / 2) = 1 / 6 := by norm_num
  rw [h_eq']
  linarith [h_exp]

end Workspace.Lemmas.ExpBound
