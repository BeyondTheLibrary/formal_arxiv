import Mathlib
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.CGABranchComparison
import Workspace.ProofLemmas.CGInteriorRoot

open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.CGABranchComparison
open Workspace.ProofLemmas.CGInteriorRoot

namespace Workspace.ProofLemmas.CGDeltaLambdaLowBranch

theorem CGDeltaLambdaLowBranch (c : ℝ) (hc_lo : 0 ≤ c) (hc_hi : c < 1 / 2) :
    let a1v : ℝ := a1' c
    let d1sq : ℝ :=
      ((1 - 2 * a1v - c) / (1 + c) + a1v ^ ((1 : ℝ) / 2)) ^ 2 / (1 - a1v)
    (lambda1 c = (1 + d1sq) ^ (-(1 : ℝ) / 2)) ∧
    (lambda1 c =
      (c + 1) *
        (Real.sqrt
          (4 * Real.sqrt (2 * c + 3) * c + 6 * Real.sqrt (2 * c + 3) - 10 * c - 8))⁻¹) ∧
    (1 / lambda1 c = Workspace.ConsistencyTheorem.CG c) := by
  intro a1v d1sq
  -- Surd setup: s = √(2c+3) = √(3+2c)
  have h23 : (0:ℝ) ≤ 2 * c + 3 := by linarith
  set s := Real.sqrt (2 * c + 3) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 2 * c + 3 := by rw [hs_def, sq, Real.mul_self_sqrt h23]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsr : Real.sqrt (3 + 2 * c) = s := by
    rw [hs_def]; congr 1; ring
  -- s > c  (needed for 1 - a > 0):  s² = 2c+3 > c² for c ≥ 0
  have hs_gt_c : c < s := by nlinarith [hs_sq, hs_nonneg, sq_nonneg (s - c)]
  -- helper: (y²)^(1/2) = y for y ≥ 0
  have hsqrt_sq : ∀ (y:ℝ), 0 ≤ y → (y ^ 2) ^ ((1:ℝ)/2) = y := by
    intro y hy; rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy]; norm_num
  -- a1' c = (2 + c - s)/2
  have ha1v : a1v = (2 + c - s) / 2 := by
    show a1' c = (2 + c - s) / 2
    rw [a1', hsr]
  -- (a1' c)^(1/2) = t1 = (-1 + s)/2
  have ht1_nonneg : (0:ℝ) ≤ (-1 + s) / 2 := by linarith
  have ha1v_eq_sq : a1v = ((-1 + s) / 2) ^ 2 := by
    rw [ha1v]; nlinarith [hs_sq]
  have hasqrt : a1v ^ ((1 : ℝ) / 2) = (-1 + s) / 2 := by
    rw [ha1v_eq_sq, hsqrt_sq _ ht1_nonneg]
  -- positivity facts
  have hc1_pos : (0:ℝ) < c + 1 := by linarith
  have h1c_pos : (0:ℝ) < 1 + c := by linarith
  have h1ma_pos : (0:ℝ) < 1 - a1v := by rw [ha1v]; linarith
  set R : ℝ := 4 * s * c + 6 * s - 10 * c - 8 with hR_def
  have hR_pos : (0:ℝ) < R := by
    rw [hR_def]; nlinarith [hs_sq, hs_ge1, hs_gt_c, mul_nonneg hs_nonneg hc_lo]
  have hsqrtR_pos : (0:ℝ) < Real.sqrt R := Real.sqrt_pos.mpr hR_pos
  -- KEY identity: 1 + d1sq = R / (c+1)²
  have hkey : 1 + d1sq = R / (c + 1) ^ 2 := by
    show 1 + ((1 - 2 * a1v - c) / (1 + c) + a1v ^ ((1:ℝ)/2)) ^ 2 / (1 - a1v)
        = R / (c + 1) ^ 2
    rw [hasqrt, ha1v, hR_def]
    rw [show (1:ℝ) - (2 + c - s) / 2 = (s - c) / 2 by ring]
    have hsc : s - c ≠ 0 := by nlinarith [hs_gt_c]
    field_simp
    linear_combination (c ^ 4 - 6 * c ^ 2 - 8 * c - 3) * hs_sq
  -- conjunct 2 (and lambda1 closed form): lambda1 c = (c+1) * (√R)⁻¹
  have hlam : lambda1 c = (c + 1) * (Real.sqrt R)⁻¹ := by
    rw [lambda1, if_pos hc_hi, hR_def]
  -- rpow building blocks
  have hden : ((c + 1) ^ 2 : ℝ) ^ (-(1:ℝ) / 2) = (c + 1)⁻¹ := by
    rw [show (c + 1) ^ 2 = (c + 1) ^ (2:ℕ) by norm_num,
        ← Real.rpow_natCast (c + 1) 2, ← Real.rpow_mul (le_of_lt hc1_pos),
        show ((2:ℕ):ℝ) * (-(1:ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hnum : (R : ℝ) ^ (-(1:ℝ) / 2) = (Real.sqrt R)⁻¹ := by
    rw [Real.sqrt_eq_rpow, show (-(1:ℝ) / 2) = -(1 / 2) by ring,
        Real.rpow_neg (le_of_lt hR_pos)]
  -- (1 + d1sq)^(-1/2) = (c+1) * (√R)⁻¹
  have hpow : (1 + d1sq) ^ (-(1:ℝ) / 2) = (c + 1) * (Real.sqrt R)⁻¹ := by
    rw [hkey, Real.div_rpow (le_of_lt hR_pos) (by positivity), hden, hnum]
    rw [div_eq_mul_inv, inv_inv, mul_comm]
  refine ⟨?_, hlam, ?_⟩
  · rw [hlam, hpow]
  · -- 1 / lambda1 c = CG c
    rw [hlam, Workspace.ConsistencyTheorem.CG, if_pos hc_hi, hR_def]
    rw [one_div, mul_inv, inv_inv, div_eq_mul_inv]
    ring

end Workspace.ProofLemmas.CGDeltaLambdaLowBranch
