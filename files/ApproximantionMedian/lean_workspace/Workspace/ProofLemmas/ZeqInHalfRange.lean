import Mathlib
import Workspace.ProofLemmas.DeltaStarDef

open Workspace.ProofLemmas.DeltaStarDef

namespace Workspace.ProofLemmas.ZeqInHalfRange

noncomputable def z_func (q : ℝ) : ℝ :=
  (delta_star q) ^ (-(q / (2*q - 1))) /
    ((delta_star q) ^ (-(q / (2*q - 1))) + 1)

theorem ZeqInHalfRange (q : ℝ) (hq : 1 < q) :
    0 < z_func q ∧ z_func q ≤ 1/2 := by
  -- Use DeltaStarDef to get 1 ≤ delta_star q
  have hD : 1 ≤ delta_star q := (Workspace.ProofLemmas.DeltaStarDef.DeltaStarDef q hq).1
  have hDpos : 0 < delta_star q := lt_of_lt_of_le one_pos hD
  -- p = -(q/(2q-1)) is the exponent. Since q > 1, 2q - 1 > 1 > 0, q/(2q-1) > 0, so p < 0.
  set p : ℝ := -(q / (2*q - 1)) with hp_def
  have h2q1 : 0 < 2*q - 1 := by linarith
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hp_neg : p < 0 := by
    rw [hp_def, neg_lt, neg_zero]
    exact div_pos hqpos h2q1
  have hp_nonpos : p ≤ 0 := le_of_lt hp_neg
  -- D^p > 0
  have hDp_pos : 0 < (delta_star q) ^ p := Real.rpow_pos_of_pos hDpos p
  -- D^p ≤ 1 since D ≥ 1 and p ≤ 0
  have hDp_le_one : (delta_star q) ^ p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hD hp_nonpos
  -- denominator > 0
  have hDenom_pos : 0 < (delta_star q) ^ p + 1 := by linarith
  refine ⟨?_, ?_⟩
  · -- 0 < z_func q
    unfold z_func
    show 0 < (delta_star q) ^ p / ((delta_star q) ^ p + 1)
    exact div_pos hDp_pos hDenom_pos
  · -- z_func q ≤ 1/2
    unfold z_func
    show (delta_star q) ^ p / ((delta_star q) ^ p + 1) ≤ 1/2
    rw [div_le_div_iff₀ hDenom_pos (by norm_num : (0:ℝ) < 2)]
    -- Goal: D^p * 2 ≤ 1 * (D^p + 1)
    linarith

end Workspace.ProofLemmas.ZeqInHalfRange
