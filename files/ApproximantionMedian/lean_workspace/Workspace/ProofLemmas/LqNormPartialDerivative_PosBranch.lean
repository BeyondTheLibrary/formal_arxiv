import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormPartialDerivative_PosBranch
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (x : Fin d → ℝ) (j : Fin d)
    (hx_pos : 0 < x j) (hlq_pos : 0 < lqNorm q x) :
    HasDerivAt (fun t : ℝ => lqNorm q (Function.update x j t))
      ((x j) ^ (q - 1) / (lqNorm q x) ^ (q - 1)) (x j) := by
  -- Setup basic facts about q
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_xj_ne : (x j) ≠ 0 := ne_of_gt hx_pos
  have h_lqq_pos : 0 < lqNorm q x := hlq_pos
  have h_lqq_ne : lqNorm q x ≠ 0 := ne_of_gt h_lqq_pos
  have h_lqq_nonneg : 0 ≤ lqNorm q x := le_of_lt h_lqq_pos
  -- Define the constant part C = ∑_{k≠j} |x k|^q
  set C : ℝ := ∑ k ∈ Finset.univ.erase j, |x k| ^ q with hC_def
  -- The total sum equals C + (x j)^q (using |x j| = x j since x j > 0)
  have h_total_sum : (∑ k, |x k| ^ q) = C + (x j) ^ q := by
    have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
    have h1 : (∑ k, |x k| ^ q) = ∑ k ∈ Finset.univ.erase j, |x k| ^ q + |x j| ^ q := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin d)) (fun k => |x k| ^ q) hj_mem]
    rw [h1, abs_of_pos hx_pos]
  -- (lqNorm q x)^q = total_sum: ((∑|x|^q)^(1/q))^q = ∑|x|^q
  have h_lqNorm_q_eq : (lqNorm q x) ^ q = ∑ k, |x k| ^ q := by
    unfold lqNorm
    rw [← Real.rpow_mul (sum_abs_rpow_nonneg q x), one_div_mul_cancel hq_ne, Real.rpow_one]
  -- Show: in a nbhd of x j, the function equals (C + t^q)^(1/q)
  have h_pos_nhd : ∀ᶠ t in nhds (x j), (0 : ℝ) < t :=
    eventually_gt_nhds hx_pos
  have h_eq_local : ∀ᶠ t in nhds (x j),
      lqNorm q (Function.update x j t) = (C + t ^ q) ^ ((1 : ℝ) / q) := by
    filter_upwards [h_pos_nhd] with t ht_pos
    unfold lqNorm
    congr 1
    have hj_mem : j ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ j
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin d))
          (fun k => |Function.update x j t k| ^ q) hj_mem]
    rw [Function.update_self, abs_of_pos ht_pos]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [Function.update_of_ne hkj]
  -- Compute derivative of t ↦ C + t^q at t = x j
  have h_t_pow_q : HasDerivAt (fun t : ℝ => t ^ q) (q * (x j) ^ (q - 1)) (x j) :=
    Real.hasDerivAt_rpow_const (Or.inl h_xj_ne)
  have h_C_add : HasDerivAt (fun t : ℝ => C + t ^ q) (q * (x j) ^ (q - 1)) (x j) := by
    have := h_t_pow_q.const_add C
    convert this using 1
  -- (C + (x j)^q) = (lqNorm q x)^q > 0
  have h_inner_eq : C + (x j) ^ q = (lqNorm q x) ^ q := by
    rw [← h_total_sum, ← h_lqNorm_q_eq]
  have h_inner_pos : 0 < C + (x j) ^ q := by
    rw [h_inner_eq]
    exact Real.rpow_pos_of_pos h_lqq_pos q
  have h_inner_ne : C + (x j) ^ q ≠ 0 := ne_of_gt h_inner_pos
  -- Use HasDerivAt.rpow_const for the outer composition
  have h_outer : HasDerivAt (fun t : ℝ => (C + t ^ q) ^ ((1 : ℝ) / q))
      (q * (x j) ^ (q - 1) * ((1 : ℝ) / q) * (C + (x j) ^ q) ^ ((1 : ℝ) / q - 1)) (x j) :=
    h_C_add.rpow_const (Or.inl h_inner_ne)
  -- Transfer via eventuallyEq
  have h_eq_local' : (fun t : ℝ => lqNorm q (Function.update x j t)) =ᶠ[nhds (x j)]
      (fun t : ℝ => (C + t ^ q) ^ ((1 : ℝ) / q)) := by
    filter_upwards [h_eq_local] with t ht
    exact ht
  rw [Filter.EventuallyEq.hasDerivAt_iff h_eq_local']
  -- Algebraic manipulation: show the two derivative values are equal
  convert h_outer using 1
  -- Goal: (x j)^(q-1) / (lqNorm q x)^(q-1) = q * (x j)^(q-1) * (1/q) * (C + (x j)^q)^(1/q - 1)
  rw [h_inner_eq]
  -- Now: (x j)^(q-1) / (lqNorm q x)^(q-1) = q * (x j)^(q-1) * (1/q) * ((lqNorm q x)^q)^(1/q - 1)
  -- Step 1: simplify q * (...) * (1/q) = (...)
  have h_q_simp : q * (x j) ^ (q - 1) * ((1 : ℝ) / q) = (x j) ^ (q - 1) := by
    field_simp
  rw [h_q_simp]
  -- Step 2: ((lqNorm q x)^q)^(1/q - 1) = (lqNorm q x)^(q*(1/q - 1)) = (lqNorm q x)^(1 - q)
  have h_pow_simp : ((lqNorm q x) ^ q) ^ ((1 : ℝ) / q - 1) = (lqNorm q x) ^ (1 - q) := by
    rw [← Real.rpow_mul h_lqq_nonneg]
    congr 1
    field_simp
  rw [h_pow_simp]
  -- Step 3: (lqNorm q x)^(1 - q) = ((lqNorm q x)^(q-1))⁻¹
  have h_neg : (lqNorm q x) ^ (1 - q) = ((lqNorm q x) ^ (q - 1))⁻¹ := by
    have : (1 - q) = -(q - 1) := by ring
    rw [this, Real.rpow_neg h_lqq_nonneg]
  rw [h_neg]
  -- Goal: (x j)^(q-1) / (lqNorm q x)^(q-1) = (x j)^(q-1) * ((lqNorm q x)^(q-1))⁻¹
  rw [div_eq_mul_inv]
