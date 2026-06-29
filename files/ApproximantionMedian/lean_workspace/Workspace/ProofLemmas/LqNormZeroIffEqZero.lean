import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormZeroIffEqZero
    (q : ℝ) (hq : 1 ≤ q) {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) :
    lqNorm q x = 0 ↔ x = 0 := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_ne : (1 : ℝ) / q ≠ 0 := by
    rw [one_div]; exact inv_ne_zero hq_ne
  have hsum_nn : 0 ≤ ∑ j, |x j| ^ q := sum_abs_rpow_nonneg q x
  unfold lqNorm
  rw [Real.rpow_eq_zero hsum_nn h_inv_ne]
  constructor
  · intro hsum
    have hzero : ∀ j ∈ Finset.univ, |x j| ^ q = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) q)] at hsum
      exact hsum
    funext j
    have hj : |x j| ^ q = 0 := hzero j (Finset.mem_univ j)
    have habs : |x j| = 0 := by
      have := (Real.rpow_eq_zero (abs_nonneg _) hq_ne).mp hj
      exact this
    have : x j = 0 := abs_eq_zero.mp habs
    simpa using this
  · intro hx
    subst hx
    apply Finset.sum_eq_zero
    intro j _
    simp [Real.zero_rpow hq_ne]
