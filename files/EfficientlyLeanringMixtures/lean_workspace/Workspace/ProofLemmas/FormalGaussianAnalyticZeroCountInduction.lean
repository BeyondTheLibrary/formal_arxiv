-- Cited from: Hurwitz's theorem on uniform-on-compacts limits of holomorphic
-- functions (Hurwitz 1889; see Conway, "Functions of One Complex Variable I",
-- 2nd ed., Springer GTM 11, 1978, Theorem VII.2.5), combined with the
-- real-analytic implicit function theorem (Krantz–Parks, "A Primer of Real
-- Analytic Functions", 2nd ed., Birkhäuser 2002, Theorem 6.1.2), and a
-- standard induction on the number of components.
-- Paper label: [Hurwitz + analytic IFT + induction (Conway 1978; Krantz–Parks 2002)]
-- NL statement: Let k ≥ 1 and let a, μ, τ_sq : Fin k → ℝ satisfy (i) τ_sq i ≠ 0
-- for every i, (ii) τ_sq i ≠ τ_sq j whenever i ≠ j, and (iii) a i ≠ 0 for some
-- i. Then the function
--     f(x) = ∑_{i < k} a i · exp(-(x - μ i)^2 / (2 · τ_sq i))
-- has at most 2(k - 1) real zeros.
--
-- This statement is now a THEOREM, proven by composing three prior-work
-- axioms that isolate the three textbook ingredients of the classical
-- argument:
--   * `HurwitzZeroCountLimitPassage` — Hurwitz's theorem on uniform-on-compacts
--     limits of analytic functions (Conway 1978).
--   * `AnalyticIFTZeroBranchTracking` — the real-analytic implicit function
--     theorem applied to the parametrised family (Krantz–Parks 2002).
--   * `GaussianZeroCountInductiveStep` — the textbook inductive step that
--     combines the above two tools to upgrade a (k-1)-zero bound to a
--     k-zero bound for signed Gaussian combinations.
-- The base case (k = 1) is the fact that a single nonzero Gaussian density
-- has no real zeros, which follows from `Real.exp_ne_zero` and a short
-- elementary computation.

import Mathlib
import Workspace.Types.ZeroCount
-- NOTE: the former import `Workspace.PriorWork.HurwitzZeroCountLimitPassage` was
-- removed: that declaration was a re-wrapping of the FALSE multiplicity-free
-- zero-count upper-semicontinuity axiom (see proving_notes.md Issue 7 and the
-- soundness history in `HurwitzAnalyticZeroCountUSC.lean`) and was never used in
-- this file's proof (the inductive step goes solely through
-- `GaussianZeroCountInductiveStep`).  The dead file has been deleted.
import Workspace.ProofLemmas.GaussianZeroCountInductiveStepProof

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount

theorem FormalGaussianAnalyticZeroCountInduction
    (k : ℕ) (hk : 1 ≤ k)
    (a : Fin k → ℝ)
    (μ : Fin k → ℝ)
    (τ_sq : Fin k → ℝ)
    (h_τ_pos : ∀ i : Fin k, 0 < τ_sq i)
    (h_τ_distinct : ∀ i j : Fin k, i ≠ j → τ_sq i ≠ τ_sq j)
    (h_a_nonzero : ∃ i : Fin k, a i ≠ 0) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      (2 * (k - 1)) := by
  -- Induction on `k` starting from `k = 1`.
  induction k, hk using Nat.le_induction with
  | base =>
    -- Base case k = 1: function is `a 0 * exp(-(x - μ 0)^2 / (2 * τ_sq 0))`,
    -- which has no zeros because `Real.exp` is never zero and `a 0 ≠ 0`.
    -- The bound is `2 * (1 - 1) = 0`.
    obtain ⟨i, hi⟩ := h_a_nonzero
    -- The only index in `Fin 1` is `0`, so `a 0 ≠ 0`.
    have ha0 : a 0 ≠ 0 := by
      have hi_eq : i = 0 := Subsingleton.elim i 0
      simpa [hi_eq] using hi
    -- Show the zero set is empty.
    have hzs : zeroSet
        (fun x => (Finset.univ : Finset (Fin 1)).sum
          (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i)))) = ∅ := by
      ext x
      simp only [zeroSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      -- The sum over `Fin 1` reduces to the single term at `0`.
      have hsum : (Finset.univ : Finset (Fin 1)).sum
            (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i)))
          = a 0 * Real.exp (-(x - μ 0)^2 / (2 * τ_sq 0)) := by
        simp [Fin.sum_univ_one]
      rw [hsum]
      exact mul_ne_zero ha0 (Real.exp_ne_zero _)
    -- From empty zero set, zero count is 0 ≤ 0 = 2*(1-1).
    show hasAtMostNZeros _ (2 * (1 - 1))
    unfold hasAtMostNZeros zeroCount
    rw [hzs]
    simp
  | succ k hk_le ih =>
    -- Inductive step: from `1 ≤ k` and the bound for `k`, derive the bound for `k+1`.
    -- We invoke `GaussianZeroCountInductiveStep` at index `k` (so it concludes about `k+1`).
    exact Workspace.ProofLemmas.GaussianZeroCountInductiveStepProof k hk_le ih
      a μ τ_sq h_τ_pos h_τ_distinct h_a_nonzero

end Workspace.ProofLemmas
