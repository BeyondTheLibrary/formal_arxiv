import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormBoundaryUpwardExpansion
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (x : Fin d → ℝ) (j : Fin d) (delta : ℝ)
    (hd_nn : 0 ≤ delta) (hxj_zero : x j = 0) :
    lqNorm q (Function.update x j delta)
      = ((lqNorm q x) ^ q + delta ^ q) ^ ((1 : ℝ) / q) := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsum_nn : (0 : ℝ) ≤ ∑ k, |x k| ^ q := sum_abs_rpow_nonneg q x
  -- Step 1: Compute (lqNorm q x)^q = ∑ k, |x k|^q
  have h_pow_lqNorm : (lqNorm q x) ^ q = ∑ k, |x k| ^ q := by
    show ((∑ k, |x k| ^ q) ^ ((1 : ℝ) / q)) ^ q = ∑ k, |x k| ^ q
    rw [← Real.rpow_mul hsum_nn, one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
  -- Step 2: Split the sum over Function.update using Finset.sum_update_of_mem
  have h_update_sum :
      (∑ k, |Function.update x j delta k| ^ q) = delta ^ q + ∑ k ∈ Finset.univ \ {j}, |x k| ^ q := by
    have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
    have h_eq : (fun k => |Function.update x j delta k| ^ q) =
                Function.update (fun k => |x k| ^ q) j (|delta| ^ q) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp [Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
    rw [show (∑ k, |Function.update x j delta k| ^ q) =
            ∑ k, Function.update (fun k => |x k| ^ q) j (|delta| ^ q) k from by rw [h_eq]]
    rw [Finset.sum_update_of_mem hj_mem]
    rw [abs_of_nonneg hd_nn]
  -- Step 3: ∑ k, |x k|^q = ∑ k ∈ univ \ {j}, |x k|^q (since |x j|^q = 0)
  have h_x_sum : (∑ k, |x k| ^ q) = ∑ k ∈ Finset.univ \ {j}, |x k| ^ q := by
    have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
    rw [← Finset.sum_erase_add _ _ hj_mem]
    rw [hxj_zero, abs_zero, Real.zero_rpow hq_ne, add_zero]
    congr 1
    ext k
    simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, and_comm]
  -- Step 4: combine
  have h_main_sum :
      (∑ k, |Function.update x j delta k| ^ q) = (∑ k, |x k| ^ q) + delta ^ q := by
    rw [h_update_sum, h_x_sum, add_comm]
  -- Step 5: Use h_main_sum and h_pow_lqNorm to rewrite the goal
  show ((∑ k, |Function.update x j delta k| ^ q) ^ ((1 : ℝ) / q))
        = ((lqNorm q x) ^ q + delta ^ q) ^ ((1 : ℝ) / q)
  rw [h_main_sum, h_pow_lqNorm]
