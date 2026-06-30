import Mathlib
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.RGInteriorRoot

open Workspace.ProofLemmas.RGDefs
open Workspace.ProofLemmas.RGInteriorRoot

namespace Workspace.ProofLemmas.RGDeltaLambda

theorem RGDeltaLambda (c : ℝ) (hc_lo : 0 ≤ c) (hc_hi : c < 1) :
    let a2v : ℝ := a2' c
    let d2sq : ℝ :=
      ((1 - 2 * a2v + c) / (1 - c) + a2v ^ ((1 : ℝ) / 2)) ^ 2 / (1 - a2v)
    (lambda2 c = (1 + d2sq) ^ (-(1 : ℝ) / 2)) ∧
    (lambda2 c =
      (1 - c) *
        (Real.sqrt
          (-4 * Real.sqrt (3 - 2 * c) * c + 6 * Real.sqrt (3 - 2 * c) + 10 * c - 8))⁻¹) ∧
    (1 / lambda2 c = Workspace.RobustnessTheorem.RG c) := by
  intro a2v d2sq
  -- Surd setup: s = √(3-2c)
  have h23 : (0:ℝ) ≤ 3 - 2 * c := by linarith
  set s := Real.sqrt (3 - 2 * c) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 3 - 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt h23]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  -- s > c  (needed for 1 - a > 0):  s² = 3-2c > c² for c ∈ [0,1)
  have hs_gt_c : c < s := by nlinarith [hs_sq, hs_nonneg, sq_nonneg (s - c)]
  -- helper: (y²)^(1/2) = y for y ≥ 0
  have hsqrt_sq : ∀ (y:ℝ), 0 ≤ y → (y ^ 2) ^ ((1:ℝ)/2) = y := by
    intro y hy; rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy]; norm_num
  -- a2' c = (2 - c - s)/2
  have ha2v : a2v = (2 - c - s) / 2 := by
    show a2' c = (2 - c - s) / 2
    rw [a2']
  -- (a2' c)^(1/2) = t2 = (-1 + s)/2
  have ht2_nonneg : (0:ℝ) ≤ (-1 + s) / 2 := by linarith
  have ha2v_eq_sq : a2v = ((-1 + s) / 2) ^ 2 := by
    rw [ha2v]; nlinarith [hs_sq]
  have hasqrt : a2v ^ ((1 : ℝ) / 2) = (-1 + s) / 2 := by
    rw [ha2v_eq_sq, hsqrt_sq _ ht2_nonneg]
  -- positivity facts
  have h1c_pos : (0:ℝ) < 1 - c := by linarith
  have h1ma_pos : (0:ℝ) < 1 - a2v := by rw [ha2v]; linarith
  set R : ℝ := -4 * s * c + 6 * s + 10 * c - 8 with hR_def
  have hR_pos : (0:ℝ) < R := by
    rw [hR_def]; nlinarith [hs_sq, hs_ge1, hs_gt_c, mul_nonneg hs_nonneg hc_lo]
  have hsqrtR_pos : (0:ℝ) < Real.sqrt R := Real.sqrt_pos.mpr hR_pos
  -- KEY identity: 1 + d2sq = R / (1-c)²
  have hkey : 1 + d2sq = R / (1 - c) ^ 2 := by
    show 1 + ((1 - 2 * a2v + c) / (1 - c) + a2v ^ ((1:ℝ)/2)) ^ 2 / (1 - a2v)
        = R / (1 - c) ^ 2
    rw [hasqrt, ha2v, hR_def]
    rw [show (1:ℝ) - (2 - c - s) / 2 = (s + c) / 2 by ring]
    have hsc : s + c ≠ 0 := by nlinarith [hs_gt_c, hc_lo]
    field_simp
    nlinarith [hs_sq]
  -- conjunct 2 (and lambda2 closed form): lambda2 c = (1-c) * (√R)⁻¹
  have hlam : lambda2 c = (1 - c) * (Real.sqrt R)⁻¹ := by
    rw [lambda2, hR_def]
  -- rpow building blocks
  have hden : ((1 - c) ^ 2 : ℝ) ^ (-(1:ℝ) / 2) = (1 - c)⁻¹ := by
    rw [show (1 - c) ^ 2 = (1 - c) ^ (2:ℕ) by norm_num,
        ← Real.rpow_natCast (1 - c) 2, ← Real.rpow_mul (le_of_lt h1c_pos),
        show ((2:ℕ):ℝ) * (-(1:ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hnum : (R : ℝ) ^ (-(1:ℝ) / 2) = (Real.sqrt R)⁻¹ := by
    rw [Real.sqrt_eq_rpow, show (-(1:ℝ) / 2) = -(1 / 2) by ring,
        Real.rpow_neg (le_of_lt hR_pos)]
  -- (1 + d2sq)^(-1/2) = (1-c) * (√R)⁻¹
  have hpow : (1 + d2sq) ^ (-(1:ℝ) / 2) = (1 - c) * (Real.sqrt R)⁻¹ := by
    rw [hkey, Real.div_rpow (le_of_lt hR_pos) (by positivity), hden, hnum]
    rw [div_eq_mul_inv, inv_inv, mul_comm]
  refine ⟨?_, hlam, ?_⟩
  · rw [hlam, hpow]
  · -- 1 / lambda2 c = RG c
    rw [hlam, Workspace.RobustnessTheorem.RG, hR_def]
    rw [one_div, mul_inv, inv_inv, div_eq_mul_inv]
    ring

end Workspace.ProofLemmas.RGDeltaLambda
