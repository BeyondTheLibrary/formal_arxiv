import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormStrictIncrease_OfSingleCoordinateLarger
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (p tildep : Fin d → ℝ) (j0 : Fin d)
    (h_eq_off : ∀ k : Fin d, k ≠ j0 → tildep k = p k)
    (h_strict : |p j0| < |tildep j0|) :
    lqNorm q p < lqNorm q tildep := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hinv_pos : 0 < (1 : ℝ) / q := by
    rw [one_div]; exact inv_pos.mpr hq_pos
  -- Step 1: reduce to comparing the inner sums via strict monotonicity of x ↦ x^(1/q)
  unfold lqNorm
  -- Set up the two sums
  set S₁ : ℝ := ∑ j, |p j| ^ q with hS₁
  set S₂ : ℝ := ∑ j, |tildep j| ^ q with hS₂
  have hS₁_nn : 0 ≤ S₁ :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) q)
  have hS₂_nn : 0 ≤ S₂ :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) q)
  -- Step 2: show S₁ < S₂
  have h_sum_lt : S₁ < S₂ := by
    -- Apply Finset.sum_lt_sum: every term is ≤, and at j0 it is strictly <
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j0, Finset.mem_univ j0, ?_⟩
    · -- term-wise ≤
      by_cases hk : k = j0
      · -- at j0, use strict inequality (which is in particular ≤)
        subst hk
        have h_abs_nn : 0 ≤ |p k| := abs_nonneg _
        exact le_of_lt (Real.rpow_lt_rpow h_abs_nn h_strict hq_pos)
      · -- off j0: equality
        have hk_eq : tildep k = p k := h_eq_off k hk
        rw [hk_eq]
    · -- strict at j0
      have h_abs_nn : 0 ≤ |p j0| := abs_nonneg _
      exact Real.rpow_lt_rpow h_abs_nn h_strict hq_pos
  -- Step 3: apply (·)^(1/q) which is strictly monotonic on [0,∞)
  exact Real.rpow_lt_rpow hS₁_nn h_sum_lt hinv_pos
