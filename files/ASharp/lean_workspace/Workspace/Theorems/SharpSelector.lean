import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Workspace.Types.IsPSmall
import Workspace.Definitions.ProbDistributions
import Workspace.Lemmas.Lemma_CSelFact
import Workspace.Lemmas.Lemma_BernoulliIneq
import Workspace.Lemmas.Lemma_ProbXpMonotone
import Workspace.Lemmas.Lemma_ProbGoodEvent

open BigOperators
open Classical

namespace Workspace.Theorems.SharpSelector

open Workspace.Types.IsPSmall

/-- Sharp version of Talagrand's selector process conjecture.
    Theorem 1.3 in @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
    (@../../../arXiv-2412.03540v1.tex, \ref{thm:sharp-selector})

Proof strategy:
The deep probabilistic content of the theorem (towers of minimum fragments,
encoding arguments, etc.) is encapsulated by `Workspace.Lemmas.ProbGoodEvent.prob_good_event`,
which gives a `1/3` lower bound on the probability of the heavy event at density
`1 - (1 - q)^s` with `q = 16p`.

To convert this to the desired conclusion at density `16sp`, we use:
- `bernoulli_ineq`: `1 - (1 - q)^s ≤ s · q = 16sp`
- `prob_xp_monotone`: `ProbXp` is monotone in the density for upward-closed events
- The heavy event is upward-closed because `λ_H ≥ 0`, so adding elements to `W`
  only increases the sum `∑_{x ∈ W} λ_H(x)`.
-/
theorem sharp_selector_theorem :
    ∃ c : ℝ, 0 < c ∧ c ≤ 100 * Real.log 2 ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X]
        (p : ℝ) (s : ℕ) (ℋ : Set (Finset X))
        (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ),
        0 < p → p ≤ 1 → 0 < s →
        16 * (s : ℝ) * p ≤ 1 →
        ¬ IsPSmall ℋ p →
        (∀ H hH, ∀ x, 0 ≤ lambda_vec H hH x ∧ lambda_vec H hH x ≤ 1) →
        (∀ H hH, ∀ x, x ∉ H → lambda_vec H hH x = 0) →
        (∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) →
        1 / 3 ≤ Workspace.Definitions.ProbDistributions.ProbXp (16 * s * p) {W | ∃ (H : Finset X) (hH : H ∈ ℋ), 1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambda_vec H hH x} := by
  refine ⟨1, by norm_num, Workspace.Lemmas.CSelFact.c_sel_fact, ?_⟩
  intro X _ _ p s ℋ lambda_vec hp _ hs_pos h_16sp_le_one h_not_small h_range h_supp h_sum_ge_one
  set q := 16 * p with hq_def
  -- Derive 16 * p ≤ 1 from 16 * s * p ≤ 1 and s ≥ 1.
  have hs_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
  have h_16p_le_one : 16 * p ≤ 1 := by
    have hp_nn : 0 ≤ p := hp.le
    have : 16 * p ≤ 16 * (s : ℝ) * p := by nlinarith
    linarith
  -- Step 1: Apply the (now-proven) deep probabilistic lemma at density 1 - (1 - q)^s.
  --   Lemma 3.7 + cover bound + union distribution → 1/3 ≤ Pr[heavy].
  have hq_le_one_for_good : q ≤ 1 := by rw [hq_def]; exact h_16p_le_one
  -- Derive `1 ≤ H.card` for every `H ∈ ℋ` from the existing hypotheses.
  -- Since `λ_H` is supported on `H` (`h_supp`) with values in `[0, 1]` (`h_range`)
  -- and `1 ≤ ∑ x : X, λ_H(x)` (`h_sum_ge_one`), we get
  --   `1 ≤ ∑ x : X, λ_H(x) = ∑ x ∈ H, λ_H(x) ≤ ∑ x ∈ H, 1 = |H|`.
  have h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card := by
    intro H hH
    have h_sum_restrict : ∑ x ∈ H, lambda_vec H hH x = ∑ x : X, lambda_vec H hH x := by
      rw [← Finset.sum_subset (Finset.subset_univ H)]
      intro x _ hxH
      exact h_supp H hH x hxH
    have h_le_one : ∑ x ∈ H, lambda_vec H hH x ≤ ∑ x ∈ H, (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => (h_range H hH x).2)
    have h_card_eq : ∑ x ∈ H, (1 : ℝ) = (H.card : ℝ) := by
      simp
    have h_ge_one : (1 : ℝ) ≤ (H.card : ℝ) := by
      have h_ge := h_sum_ge_one H hH
      rw [← h_sum_restrict] at h_ge
      linarith [h_le_one, h_card_eq]
    exact_mod_cast h_ge_one
  have h_good := Workspace.Lemmas.ProbGoodEvent.prob_good_event
    p q ℋ s lambda_vec hp hq_def hq_le_one_for_good h_not_small h_H_nonempty h_range h_supp h_sum_ge_one
  -- Step 2: Bernoulli's inequality bounds the density above by 16sp.
  --         Requires 0 ≤ q ≤ 1, i.e. 0 ≤ 16p ≤ 1.
  have hq_nonneg : 0 ≤ q := by rw [hq_def]; linarith
  have hq_le_one : q ≤ 1 := by rw [hq_def]; exact h_16p_le_one
  have h_density_bound : 1 - (1 - q) ^ s ≤ 16 * (s : ℝ) * p := by
    have h_bern := Workspace.Lemmas.BernoulliIneq.bernoulli_ineq q s hq_nonneg hq_le_one
    have h_eq : (s : ℝ) * q = 16 * (s : ℝ) * p := by rw [hq_def]; ring
    linarith
  -- Lower bound for prob_xp_monotone: 0 ≤ 1 - (1-q)^s.
  have h_density_nonneg : (0 : ℝ) ≤ 1 - (1 - q) ^ s := by
    have h_one_sub_q_nn : (0 : ℝ) ≤ 1 - q := by linarith
    have h_one_sub_q_le : 1 - q ≤ 1 := by linarith
    have h_pow_le_one : (1 - q) ^ s ≤ 1 := pow_le_one₀ h_one_sub_q_nn h_one_sub_q_le
    linarith
  -- Step 3: The heavy event is upward-closed (adding elements only grows the sum)
  have h_event_upward :
      ∀ {S1 S2 : Finset X},
        S1 ∈ {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
                  1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambda_vec H hH x} →
        S1 ⊆ S2 →
        S2 ∈ {W | ∃ (H : Finset X) (hH : H ∈ ℋ),
                  1 - (2 : ℝ) ^ (-(s : ℝ)) ≤ ∑ x ∈ W, lambda_vec H hH x} := by
    intro S1 S2 hS1 hsub
    obtain ⟨H, hH, h_bound⟩ := hS1
    refine ⟨H, hH, ?_⟩
    have h_sum_mono : ∑ x ∈ S1, lambda_vec H hH x ≤ ∑ x ∈ S2, lambda_vec H hH x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => (h_range H hH x).1)
    linarith
  -- Step 4: Combine via monotonicity of ProbXp in the density (using the proven theorem)
  exact le_trans h_good
    (Workspace.Lemmas.ProbXpMonotone.prob_xp_monotone
      h_density_nonneg h_density_bound h_16sp_le_one _ h_event_upward)

end Workspace.Theorems.SharpSelector
