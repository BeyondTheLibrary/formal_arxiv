import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.PerturbAtZero_StrictDescent

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem PEqZeroNotLocalMin
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma : Fin d → ℝ) (hsigma_pm : ∀ j, sigma j = 1 ∨ sigma j = -1)
    (hS_pos : ∃ k, sigma k = 1) :
    ¬ ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma j = 1 → 0 ≤ p j) ∧ (sigma j = -1 → p j ≤ 0)) →
          (∀ j, |p j - 0| < ε) →
          g_lambda q lambda f (fun _ : Fin d => (0 : ℝ)) ≤ g_lambda q lambda f p := by
  -- Step 1: convert the sum hypothesis to lqNorm q f = 1
  have hq_le : 1 ≤ q := le_of_lt hq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq_le
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hf_norm : lqNorm q f = 1 := by
    unfold lqNorm
    have h_abs : (∑ j, |f j| ^ q) = (∑ j, (f j) ^ q) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hf_nn j)]
    rw [h_abs, hf_sum, Real.one_rpow]
  -- Step 2: assume the contradiction hypothesis
  rintro ⟨ε, hε_pos, hε_local⟩
  -- Step 3: apply PerturbAtZero_StrictDescent
  obtain ⟨tildep, h_orthant, h_close, h_strict⟩ :=
    PerturbAtZero_StrictDescent hq hlam0 hlam1 hd f hf_nn hf_norm sigma hsigma_pm hS_pos hε_pos
  -- h_strict : lqNorm q (fun k => tildep k - f k) - lambda * lqNorm q tildep
  --             < lqNorm q (fun k => -(f k))
  -- Step 4: apply the local minimum at tildep
  have h_dist : ∀ j, |tildep j - 0| < ε := by
    intro j
    rw [sub_zero]
    exact h_close j
  have h_local := hε_local tildep h_orthant h_dist
  -- h_local : g_lambda q lambda f 0 ≤ g_lambda q lambda f tildep
  -- Step 5: simplify g_lambda at 0
  have h_g0 : g_lambda q lambda f (fun _ : Fin d => (0 : ℝ))
              = lqNorm q (fun k : Fin d => -(f k)) := by
    unfold g_lambda
    have h_zero : lqNorm q (fun _ : Fin d => (0 : ℝ)) = 0 := lqNorm_zero hq_le
    have h_arg : (fun j : Fin d => (fun (_ : Fin d) => (0 : ℝ)) j - f j)
                  = (fun k : Fin d => -(f k)) := by
      funext j; ring
    rw [h_arg, h_zero]
    ring
  -- Step 6: g_lambda at tildep
  have h_gtilde : g_lambda q lambda f tildep
                  = lqNorm q (fun k => tildep k - f k) - lambda * lqNorm q tildep := rfl
  -- Step 7: derive contradiction
  rw [h_g0] at h_local
  rw [h_gtilde] at h_local
  -- h_local : lqNorm q (fun k => -(f k)) ≤ lqNorm q (fun k => tildep k - f k) - lambda * lqNorm q tildep
  -- h_strict : lqNorm q (fun k => tildep k - f k) - lambda * lqNorm q tildep < lqNorm q (fun k => -(f k))
  linarith
