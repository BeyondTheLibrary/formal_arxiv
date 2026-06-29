import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LocalOptimumCharacterization_CaseSNonempty
import Workspace.ProofLemmas.LocalOptimumCharacterization_CaseSEmpty

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

namespace LocalOptimumCharacterizationProof

open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem case_S_nonempty
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma_i j = 1 → 0 ≤ p_star j) ∧
                  (sigma_i j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma_i j = 1 → 0 ≤ p j) ∧
                (sigma_i j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (S : Finset (Fin d))
    (hS_def : S = Finset.univ.filter (fun j : Fin d => sigma_i j = 1))
    (hS_ne : S.Nonempty) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      (∀ j ∈ S, p_star j = f j / (1 - c)) ∧
      (∀ j ∉ S, p_star j = 0) :=
  LocalOptimumCharacterization_CaseSNonempty q hq lambda hlam0 hlam1 hd f hf_nn hf_pos hf_sum
    sigma_i hsigma_pm p_star hp_in hp_loc S hS_def hS_ne

theorem case_S_empty
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma_i j = 1 → 0 ≤ p_star j) ∧
                  (sigma_i j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma_i j = 1 → 0 ≤ p j) ∧
                (sigma_i j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (S : Finset (Fin d))
    (hS_def : S = Finset.univ.filter (fun j : Fin d => sigma_i j = 1))
    (hS_eq : S = ∅) :
    ∃ T : Finset (Fin d), ∃ c' : ℝ, 1 < c' ∧
      (∀ j ∈ T, -(p_star j) = f j / (c' - 1)) ∧
      (∀ j ∉ T, p_star j = 0) ∧
      (∀ j, p_star j ≤ 0) :=
  LocalOptimumCharacterization_CaseSEmpty q hq lambda hlam0 hlam1 hd f hf_nn hf_pos hf_sum
    sigma_i hsigma_pm p_star hp_in hp_loc S hS_def hS_eq

end LocalOptimumCharacterizationProof

open LocalOptimumCharacterizationProof

open Classical in
theorem LocalOptimumCharacterization
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma_i j = 1 → 0 ≤ p_star j) ∧ (sigma_i j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma_i j = 1 → 0 ≤ p j) ∧ (sigma_i j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p) :
    let S := Finset.univ.filter (fun j : Fin d => sigma_i j = 1)
    ( S.Nonempty ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
        (∀ j ∈ S, p_star j = f j / (1 - c)) ∧
        (∀ j ∉ S, p_star j = 0) )
    ∨
    ( S = ∅ ∧ ∃ T : Finset (Fin d), ∃ c' : ℝ, 1 < c' ∧
        (∀ j ∈ T, -(p_star j) = f j / (c' - 1)) ∧
        (∀ j ∉ T, p_star j = 0) ∧
        (∀ j, p_star j ≤ 0) ) := by
  -- Set up the abbreviation `S := {j : σ_j = +1}` introduced by the `let`
  -- in the goal.
  intro S
  -- The proof distinguishes the two cases of paper Lemma 2:
  --   case (i):  S ≠ ∅, with closed form p_j = f_j/(1-c) on S;
  --   case (ii): S = ∅, with closed form -p_j = f_j/(c'-1) on T.
  by_cases hS : S.Nonempty
  · -- **Case (i): S ≠ ∅.** Apply step (a) to get c.
    left
    refine ⟨hS, ?_⟩
    exact case_S_nonempty q hq lambda hlam0 hlam1 hd f hf_nn hf_pos hf_sum
            sigma_i hsigma_pm p_star hp_in hp_loc S rfl hS
  · -- **Case (ii): S = ∅.** Apply step (b) to get T, c'.
    right
    have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨hS_eq, ?_⟩
    exact case_S_empty q hq lambda hlam0 hlam1 hd f hf_nn hf_pos hf_sum
            sigma_i hsigma_pm p_star hp_in hp_loc S rfl hS_eq
