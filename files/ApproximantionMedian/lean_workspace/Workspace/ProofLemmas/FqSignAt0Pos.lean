import Mathlib

namespace Workspace.ProofLemmas.FqSignAt0Pos

noncomputable def F_q (q a : ℝ) : ℝ :=
  2 * (1 - 1/q) * a + (1/q) * a ^ ((1 - q) / q) - 2 + 1/q

end Workspace.ProofLemmas.FqSignAt0Pos

open Workspace.ProofLemmas.FqSignAt0Pos

theorem FqSignAt0Pos (q : ℝ) (hq : 1 < q) :
    Filter.Tendsto (fun a => F_q q a) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_inv_pos : (0 : ℝ) < 1 / q := by positivity
  have hexp_neg : (1 - q) / q < 0 := by
    apply div_neg_of_neg_of_pos
    · linarith
    · exact hq_pos
  -- a^((1-q)/q) → +∞ as a → 0+
  have h_rpow : Filter.Tendsto (fun a : ℝ => a ^ ((1 - q) / q))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_rpow_neg_nhdsGT_zero hexp_neg
  -- (1/q) * a^((1-q)/q) → +∞
  have h_rpow_scaled : Filter.Tendsto (fun a : ℝ => (1/q) * a ^ ((1 - q) / q))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    h_rpow.const_mul_atTop' hq_inv_pos
  -- The remaining terms tend to a finite limit
  -- 2*(1 - 1/q)*a + (-2 + 1/q) → -2 + 1/q as a → 0
  have h_nhds_zero : Filter.Tendsto (fun a : ℝ => a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have h_lin : Filter.Tendsto (fun a : ℝ => 2 * (1 - 1/q) * a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * (1 - 1/q) * 0)) :=
    h_nhds_zero.const_mul _
  have h_lin0 : Filter.Tendsto (fun a : ℝ => 2 * (1 - 1/q) * a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : 2 * (1 - 1/q) * (0 : ℝ) = 0 := by ring
    rw [this] at h_lin
    exact h_lin
  have h_other : Filter.Tendsto (fun a : ℝ => 2 * (1 - 1/q) * a + (-2 + 1/q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + (-2 + 1/q))) :=
    h_lin0.add tendsto_const_nhds
  -- Now combine: ((1/q) * a^((1-q)/q)) + (2*(1-1/q)*a + (-2 + 1/q)) → +∞
  have h_sum : Filter.Tendsto
      (fun a : ℝ => (1/q) * a ^ ((1 - q) / q) + (2 * (1 - 1/q) * a + (-2 + 1/q)))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    h_rpow_scaled.atTop_add h_other
  -- Show F_q q a equals our sum
  have heq : (fun a : ℝ => F_q q a) =
      fun a : ℝ => (1/q) * a ^ ((1 - q) / q) + (2 * (1 - 1/q) * a + (-2 + 1/q)) := by
    funext a
    simp only [F_q]
    ring
  rw [heq]
  exact h_sum
