import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Workspace.Types.FractionalCover
import Workspace.Definitions.LambdaH
import Workspace.Definitions.ProbDistributions
import Workspace.Lemmas.Lemma_LambdaH_Support
import Workspace.Lemmas.Lemma_LambdaHToWInequality
import Workspace.Lemmas.Lemma_ProbXpSetMonotone

open BigOperators
open Workspace.Types.FractionalCover
open Workspace.Definitions.LambdaH
open Workspace.Definitions.ProbDistributions

namespace Workspace.Lemmas.MaxWProb

/-- max_w_prob theorem: probability bound conversion from λ_H to w.

    Given a probability lower bound on the heavy-λ event, we transfer it to a
    probability lower bound on the heavy-w event. The transformation goes through
    a deterministic set inclusion (via `lambdaH_to_w_inequality`) and uses
    set monotonicity of `ProbXp`.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem max_w_prob {X : Type} [Fintype X] [DecidableEq X]
    (t : ℕ) (ℋ : Set (Finset X)) (cov : FractionalCover X ℋ)
    (s : ℕ) (q' : ℝ)
    (h_heavy_prob : (1 / 3 : ℝ) ≤ ProbXp q' {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
                    1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambdaH cov H hH x})
    (h_heavy_le : 1 - (2 : ℝ) ^ (-(s : ℝ)) ≥ 1 - 1 / (2 * (t : ℝ)))
    (h_supp : ∀ W : Finset X, t < W.card → cov.w W = 0)
    (hq'_pos : 0 ≤ q') (hq'_le_one : q' ≤ 1)
    (hs : s = Nat.ceil (Real.log (2 * t) / Real.log 2)) :
    (1 / 3 : ℝ) ≤ ProbXp q' {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
                  1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W'} := by
  -- Set A: the heavy-λ event.
  set A : Set (Finset X) := {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
        1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambdaH cov H hH x} with hA_def
  -- Set B: the heavy-w event.
  set B : Set (Finset X) := {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
        1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W'} with hB_def
  -- Step 1: Show A ⊆ B.
  have hAB : A ⊆ B := by
    intro W hW
    -- Extract witness H, hH from membership in A.
    rcases hW with ⟨H, hH, h_lambda_W⟩
    -- Step 1a: Convert ∑ x ∈ W to ∑ x ∈ W ∩ H using support of λ_H.
    have h_sum_eq : ∑ x ∈ W, lambdaH cov H hH x = ∑ x ∈ W ∩ H, lambdaH cov H hH x := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro x hxW hxnotinter
      have hxH : x ∉ H := by
        intro hxH
        exact hxnotinter (Finset.mem_inter.mpr ⟨hxW, hxH⟩)
      exact Workspace.Lemmas.LambdaH_Support.lambdaH_support cov H hH x hxH
    -- Step 1b: Get the heavy-λ bound on W ∩ H.
    have h_lambda_inter : (1 : ℝ) - (2 : ℝ) ^ (-(s : ℝ)) ≤
        ∑ x ∈ W ∩ H, lambdaH cov H hH x := by
      rw [← h_sum_eq]; exact h_lambda_W
    -- Step 1c: Apply lambdaH_to_w_inequality.
    -- The lemma needs the bound with s = Nat.ceil (log(2t)/log 2),
    -- so we rewrite using hs.
    have h_lambda_inter' : (1 : ℝ) -
        (2 : ℝ) ^ (-(Nat.ceil (Real.log (2 * t) / Real.log 2) : ℝ)) ≤
        ∑ x ∈ W ∩ H, lambdaH cov H hH x := by
      rw [← hs]; exact h_lambda_inter
    have h_heavy_le' : (1 : ℝ) -
        (2 : ℝ) ^ (-(Nat.ceil (Real.log (2 * t) / Real.log 2) : ℝ)) ≥
        1 - 1 / (2 * (t : ℝ)) := by
      rw [← hs]; exact h_heavy_le
    have h_w_bound : 1 / 2 ≤ ∑ W' ∈ (H ∩ W).powerset, cov.w W' :=
      Workspace.Lemmas.LambdaHToWInequality.lambdaH_to_w_inequality
        t ℋ cov H hH W h_supp h_lambda_inter' h_heavy_le'
    -- Step 1d: Conclude W ∈ B.
    exact ⟨H, hH, h_w_bound⟩
  -- Step 2: Apply set monotonicity of ProbXp.
  have h_mono : ProbXp q' A ≤ ProbXp q' B :=
    Workspace.Lemmas.ProbXpSetMonotone.prob_xp_set_monotone q' hq'_pos hq'_le_one hAB
  -- Step 3: Combine with hypothesis.
  linarith

end Workspace.Lemmas.MaxWProb
