import Mathlib
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.CGDefs

open Workspace.ProofLemmas.RGDefs
open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.RGOptimalSolutionForA2

set_option maxHeartbeats 4000000

/-- HasDerivAt for `u2delta c delta` at a point `a` with `0 < a < 1`. -/
theorem u2delta_hasDerivAt (c delta a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun x => u2delta c delta x) (u2deriv c delta a) a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_ne : (1 - a) ≠ 0 := ne_of_gt h1ma_pos
  -- derivative of x ↦ x^(1/2)
  have hd_a_pow : HasDerivAt (fun x : ℝ => x ^ ((1:ℝ)/2)) ((1/2) * a ^ ((1:ℝ)/2 - 1)) a := by
    have h := (hasDerivAt_id a).rpow_const (p := (1:ℝ)/2) (Or.inl ha_ne)
    simpa using h
  -- derivative of x ↦ (1-x)^(1/2)
  have hd_inner : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) a := by
    simpa using (hasDerivAt_id a).const_sub 1
  have hd_1ma_pow : HasDerivAt (fun x : ℝ => (1 - x) ^ ((1:ℝ)/2))
      (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) a := by
    have h := hd_inner.rpow_const (p := (1:ℝ)/2) (Or.inl h1ma_ne)
    convert h using 1
    ring
  have hd_d_1ma : HasDerivAt (fun x : ℝ => delta * (1 - x) ^ ((1:ℝ)/2))
      (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1)))) a :=
    hd_1ma_pow.const_mul delta
  have hd_diff : HasDerivAt (fun x : ℝ => delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2))
      (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1)) a :=
    hd_d_1ma.sub hd_a_pow
  have hd_mul : HasDerivAt (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)))
      ((1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1))) a :=
    hd_diff.const_mul (1 - c)
  have hd_sub1 : HasDerivAt (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)) - 1)
      ((1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1))) a :=
    hd_mul.sub_const 1
  have hd_lin : HasDerivAt (fun x : ℝ => 2 * x) (2 : ℝ) a := by
    simpa using (hasDerivAt_id a).const_mul 2
  have hd_total0 : HasDerivAt
      (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)) - 1 + 2 * x)
      ((1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1)) + 2) a :=
    hd_sub1.add hd_lin
  have hd_total : HasDerivAt
      (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)) - 1 + 2 * x - c)
      ((1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1)) + 2) a :=
    hd_total0.sub_const c
  -- Now match against u2delta and u2deriv.
  have hfun : (fun x => u2delta c delta x) =
      (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)) - 1 + 2 * x - c) := by
    funext x; rw [u2delta]
  rw [hfun]
  -- derivative value matches u2deriv
  have hval : (1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1)) + 2
      = u2deriv c delta a := by
    rw [u2deriv]
    have e1 : ((1:ℝ)/2 - 1) = -(1:ℝ)/2 := by norm_num
    rw [e1]
    ring
  rw [hval] at hd_total
  exact hd_total

/-- On `(0, b)` with `b = ((1-c)/4)^2`, the derivative `u2deriv c delta a` is negative
(`a → 0⁺` makes `a^{-1/2} → +∞`). Concretely `a < ((1-c)/4)^2 ⟹ u2deriv < 0`. -/
theorem u2deriv_neg_near_zero (c delta a : ℝ) (hc1 : c < 1) (hdelta : 0 < delta)
    (ha0 : 0 < a) (ha1 : a < 1) (hab : a < ((1 - c) / 4) ^ 2) :
    u2deriv c delta a < 0 := by
  have h1c : (0:ℝ) < 1 - c := by linarith
  have h1ma_pos : 0 < 1 - a := by linarith
  -- a^{-1/2} > 4/(1-c)
  have hasqrt : Real.sqrt a < (1 - c) / 4 := by
    have h4 : (0:ℝ) < (1 - c) / 4 := by positivity
    have := Real.sqrt_lt_sqrt (le_of_lt ha0) hab
    rwa [Real.sqrt_sq (le_of_lt h4)] at this
  have ha_inv_sqrt : a ^ (-(1:ℝ)/2) = (Real.sqrt a)⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt ha0),
        ← Real.sqrt_eq_rpow]
  have h1ma_inv_sqrt : (1 - a) ^ (-(1:ℝ)/2) = (Real.sqrt (1 - a))⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma_pos),
        ← Real.sqrt_eq_rpow]
  have hsqrta_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsqrt1ma_pos : 0 < Real.sqrt (1 - a) := Real.sqrt_pos.mpr h1ma_pos
  -- a^{-1/2} = (√a)⁻¹ > 4/(1-c)
  have h_inv_gt : (4 : ℝ) / (1 - c) < (Real.sqrt a)⁻¹ := by
    have hpos : (0:ℝ) < (1 - c) / 4 := by positivity
    have hinv : ((1 - c) / 4)⁻¹ < (Real.sqrt a)⁻¹ := by gcongr
    rwa [inv_div] at hinv
  -- the δ term is ≤ 0
  have h_delta_term_nonpos : -delta * (1 - a) ^ (-(1:ℝ)/2) ≤ 0 := by
    rw [h1ma_inv_sqrt]
    have : 0 ≤ delta * (Real.sqrt (1 - a))⁻¹ := by positivity
    linarith
  rw [u2deriv, ha_inv_sqrt]
  -- ½(1-c)·(√a)⁻¹ > 2
  have hmain : (2:ℝ) < (1/2) * (1 - c) * (Real.sqrt a)⁻¹ := by
    have h4 : (4 : ℝ) / (1 - c) < (Real.sqrt a)⁻¹ := h_inv_gt
    have := mul_lt_mul_of_pos_left h4 (show (0:ℝ) < (1/2)*(1-c) by positivity)
    rw [show (1/2 * (1-c)) * (4 / (1 - c)) = 2 by field_simp; ring] at this
    linarith
  nlinarith [h_delta_term_nonpos, hmain]

/-- `u2delta c delta` is continuous on `Set.Icc 0 M` whenever `M < 1`. -/
theorem u2delta_continuousOn (c delta M : ℝ) (hM : M < 1) :
    ContinuousOn (fun x => u2delta c delta x) (Set.Icc (0:ℝ) M) := by
  intro x hx
  have hx_le : x ≤ M := hx.2
  have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le hM
  have h1mx_pos : 0 < 1 - x := by linarith
  have hx_nn : 0 ≤ x := hx.1
  have h_inner : ContinuousAt (fun y : ℝ => 1 - y) x :=
    (continuous_const.sub continuous_id).continuousAt
  have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) (1 - x) :=
    Real.continuousAt_rpow_const (1 - x) ((1:ℝ)/2) (Or.inl (ne_of_gt h1mx_pos))
  have h_1mx_pow : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/2)) x :=
    h_outer.comp h_inner
  have h_d_1mx_pow : ContinuousAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2)) x :=
    h_1mx_pow.const_mul delta
  have h_x_pow : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) x :=
    Real.continuousAt_rpow_const x ((1:ℝ)/2) (Or.inr (by norm_num))
  have h_diff : ContinuousAt
      (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2)) x :=
    h_d_1mx_pow.sub h_x_pow
  have h_mul : ContinuousAt
      (fun y : ℝ => (1 - c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) x :=
    h_diff.const_mul (1 - c)
  have h_total : ContinuousAt (fun x => u2delta c delta x) x := by
    have : (fun x => u2delta c delta x) =
        (fun y : ℝ => (1 - c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2)) - 1 + 2 * y - c) := by
      funext y; rw [u2delta]
    rw [this]
    exact (((h_mul.sub continuousAt_const).add
      ((continuous_const.mul continuous_id).continuousAt)).sub continuousAt_const)
  exact h_total.continuousWithinAt

/-- The inflection identity at `z = zCG delta`. (shared with CG; reproved here). -/
theorem zCG_inflection (delta : ℝ) (hdelta : 0 < delta) :
    delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = (zCG delta) ^ (-(3:ℝ)/2) := by
  set D : ℝ := delta ^ (-(2:ℝ)/3) with hD_def
  have hD_pos : 0 < D := Real.rpow_pos_of_pos hdelta _
  have hDp1_pos : 0 < D + 1 := by linarith
  have hDp1_ne : D + 1 ≠ 0 := ne_of_gt hDp1_pos
  have hz : zCG delta = D / (D + 1) := rfl
  have hz_pos : 0 < zCG delta := by
    rw [zCG]
    have hnum : 0 < delta ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hdelta _
    have hden : 0 < delta ^ (-(2 : ℝ) / 3) + 1 := by linarith
    exact div_pos hnum hden
  have h1mz : 1 - zCG delta = 1 / (D + 1) := by
    rw [hz]; field_simp; ring
  have h1mz_pos : 0 < 1 - zCG delta := by rw [h1mz]; positivity
  rw [h1mz, hz]
  rw [Real.div_rpow (le_of_lt hD_pos) (le_of_lt hDp1_pos),
      Real.div_rpow (by norm_num) (le_of_lt hDp1_pos), Real.one_rpow]
  have hD_pow : D ^ (-(3:ℝ)/2) = delta := by
    rw [hD_def, ← Real.rpow_mul (le_of_lt hdelta)]
    rw [show (-(2:ℝ)/3) * (-(3:ℝ)/2) = 1 by ring, Real.rpow_one]
  have hDp1_pow_pos : 0 < (D + 1) ^ (-(3:ℝ)/2) := Real.rpow_pos_of_pos hDp1_pos _
  rw [← hD_pow]
  field_simp

/-- The "bracket" — same as CG's `zBracket`. -/
noncomputable def zBracket (delta z : ℝ) : ℝ :=
  (1/2) * (delta * (1 - z) ^ ((1:ℝ)/2) - z ^ ((1:ℝ)/2)) - (1/2) * z ^ (-(1:ℝ)/2) + 1

theorem zCG_pos (delta : ℝ) (hdelta : 0 < delta) : 0 < zCG delta := by
  rw [zCG]
  have hnum : 0 < delta ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hdelta _
  have hden : 0 < delta ^ (-(2 : ℝ) / 3) + 1 := by linarith
  exact div_pos hnum hden

theorem zCG_lt_one (delta : ℝ) (hdelta : 0 < delta) : zCG delta < 1 := by
  rw [zCG]
  have hnum : 0 < delta ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hdelta _
  have hden : 0 < delta ^ (-(2 : ℝ) / 3) + 1 := by linarith
  rw [div_lt_one hden]; linarith

/-- `zBracket ≥ 0` at the inflection point (same algebra as CG).  Holds for ALL
`delta > 0` (the final reduced form `((s-1)²(s+1/2))/s³ ≥ 0` needs only `s = √z > 0`,
no `z ≤ 1/2` constraint — crucial for the RG single-branch case where the boundary
is `(1+c)/2 ≥ 1/2`). -/
theorem zBracket_nonneg (delta : ℝ) (hdelta : 0 < delta) :
    0 ≤ zBracket delta (zCG delta) := by
  set z : ℝ := zCG delta with hz_def
  have hz0 : 0 < z := zCG_pos delta hdelta
  have hz1 : z < 1 := zCG_lt_one delta hdelta
  have h1mz_pos : 0 < 1 - z := by linarith
  have hinfl : delta * (1 - z) ^ ((1:ℝ)/2) = z ^ (-(3:ℝ)/2) * (1 - z) ^ 2 := by
    have h := zCG_inflection delta hdelta
    rw [← hz_def] at h
    have hpow : (1 - z) ^ (-(3:ℝ)/2) * (1 - z) ^ (2:ℝ) = (1 - z) ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_add h1mz_pos]; norm_num
    have hrw2 : (1 - z) ^ (2:ℝ) = (1 - z) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    calc delta * (1 - z) ^ ((1:ℝ)/2)
        = delta * ((1 - z) ^ (-(3:ℝ)/2) * (1 - z) ^ (2:ℝ)) := by rw [hpow]
      _ = (delta * (1 - z) ^ (-(3:ℝ)/2)) * (1 - z) ^ (2:ℝ) := by ring
      _ = z ^ (-(3:ℝ)/2) * (1 - z) ^ (2:ℝ) := by rw [h]
      _ = z ^ (-(3:ℝ)/2) * (1 - z) ^ 2 := by rw [hrw2]
  have hsqrt_sq : Real.sqrt z ^ 2 = z := Real.sq_sqrt (le_of_lt hz0)
  have hsqrt_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
  have h_half : z ^ ((1:ℝ)/2) = Real.sqrt z := (Real.sqrt_eq_rpow z).symm
  have hzinv : z ^ (-(1:ℝ)/2) = (Real.sqrt z)⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hz0), h_half]
  have hz3inv : z ^ (-(3:ℝ)/2) = (Real.sqrt z ^ 3)⁻¹ := by
    rw [show (-(3:ℝ)/2) = ((1:ℝ)/2) * (-3) by ring, Real.rpow_mul (le_of_lt hz0), h_half,
        Real.rpow_neg (le_of_lt hsqrt_pos), ← Real.rpow_natCast (Real.sqrt z) 3]
    norm_num
  rw [zBracket, hinfl, hzinv, hz3inv, h_half]
  generalize hs : Real.sqrt z = s at hsqrt_pos hsqrt_sq ⊢
  rw [← hsqrt_sq]
  have hs_ne : s ≠ 0 := ne_of_gt hsqrt_pos
  have hbracket_eq :
      (1/2) * ((s ^ 3)⁻¹ * (1 - s ^ 2) ^ 2 - s) - (1/2) * s⁻¹ + 1
        = ((s - 1) ^ 2 * (s + 1/2)) / s ^ 3 := by
    field_simp
    ring
  rw [hbracket_eq]
  positivity

/-- Slope identity at `z`: `u₂'(z)·(1−z) + u₂(z) = (1−c)·bracket(z)`. -/
theorem u2deriv_slope_identity (c delta z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    u2deriv c delta z * (1 - z) + u2delta c delta z = (1 - c) * zBracket delta z := by
  have h1mz_pos : 0 < 1 - z := by linarith
  have hz_rel : z ^ (-(1:ℝ)/2) * z = z ^ ((1:ℝ)/2) := by
    nth_rewrite 2 [← Real.rpow_one z]
    rw [← Real.rpow_add hz0]; norm_num
  have h1mz_rel : (1 - z) ^ (-(1:ℝ)/2) * (1 - z) = (1 - z) ^ ((1:ℝ)/2) := by
    nth_rewrite 2 [← Real.rpow_one (1 - z)]
    rw [← Real.rpow_add h1mz_pos]; norm_num
  rw [u2deriv, u2delta, zBracket]
  have e1 : (1 - z) ^ (-(1:ℝ)/2) * (1 - z) = (1 - z) ^ ((1:ℝ)/2) := h1mz_rel
  have e2 : z ^ (-(1:ℝ)/2) * (1 - z) = z ^ (-(1:ℝ)/2) - z ^ ((1:ℝ)/2) := by
    rw [mul_sub, mul_one, hz_rel]
  linear_combination (-(1/2) * (1 - c) * delta) * e1 - ((1/2) * (1 - c)) * e2

/-- The minimality sign: at a right-endpoint minimum, `u₂'(a₂v) ≤ 0`. -/
theorem u2deriv_nonpos_at_rightmin (c delta M a2v : ℝ)
    (ha2v_pos : 0 < a2v) (ha2v_lt_one : a2v < 1) (ha2v_le_M : a2v ≤ M)
    (hmin : ∀ a ∈ Set.Icc (0 : ℝ) M, u2delta c delta a2v ≤ u2delta c delta a) :
    u2deriv c delta a2v ≤ 0 := by
  have hderiv : HasDerivAt (fun x => u2delta c delta x) (u2deriv c delta a2v) a2v :=
    u2delta_hasDerivAt c delta a2v ha2v_pos ha2v_lt_one
  have htends := hderiv.tendsto_slope_zero_left
  have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Iio 0),
      t⁻¹ • ((fun x => u2delta c delta x) (a2v + t) - (fun x => u2delta c delta x) a2v) ≤ 0 := by
    have hmemIoo : Set.Ioo (-a2v) 0 ∈ nhdsWithin (0:ℝ) (Set.Iio 0) :=
      Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hmemIoo] with t ht
    have ht_neg : t < 0 := ht.2
    have ht_gt : -a2v < t := ht.1
    have hxt_pos : 0 < a2v + t := by linarith
    have hxt_lt_M : a2v + t ≤ M := by linarith
    have hxt_mem : a2v + t ∈ Set.Icc (0:ℝ) M := ⟨le_of_lt hxt_pos, hxt_lt_M⟩
    have hval : u2delta c delta a2v ≤ u2delta c delta (a2v + t) := hmin _ hxt_mem
    have hnum_nonneg : 0 ≤ (fun x => u2delta c delta x) (a2v + t) - (fun x => u2delta c delta x) a2v := by
      simp only; linarith
    have htinv_neg : t⁻¹ < 0 := inv_lt_zero.mpr ht_neg
    rw [smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt htinv_neg) hnum_nonneg
  exact le_of_tendsto htends hev

/-- **RGOptimalSolutionForA2**. -/
theorem RGOptimalSolutionForA2
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (delta : ℝ) (hdelta : 0 < delta)
    (a2v : ℝ)
    (hmem : a2v ∈ Set.Icc (0 : ℝ) (min (zCG delta) ((1 + c) / 2)))
    (hmin : ∀ a ∈ Set.Icc (0 : ℝ) (min (zCG delta) ((1 + c) / 2)),
      u2delta c delta a2v ≤ u2delta c delta a)
    (hzero : u2delta c delta a2v = 0) :
    u2deriv c delta a2v = 0 ∨ a2v = (1 + c) / 2 := by
  set M : ℝ := min (zCG delta) ((1 + c) / 2) with hM_def
  have hzCG_pos : 0 < zCG delta := zCG_pos delta hdelta
  have h1c2_pos : 0 < (1 + c) / 2 := by linarith
  have hM_pos : 0 < M := lt_min hzCG_pos h1c2_pos
  have hM_le_half : M ≤ (1 + c) / 2 := min_le_right _ _
  have hM_le_z : M ≤ zCG delta := min_le_left _ _
  have hM_lt_one : M < 1 := by
    have := zCG_lt_one delta hdelta
    linarith [hM_le_z]
  have ha2v_nn : 0 ≤ a2v := hmem.1
  have ha2v_le_M : a2v ≤ M := hmem.2
  have ha2v_lt_one : a2v < 1 := lt_of_le_of_lt ha2v_le_M hM_lt_one
  by_cases hcase : a2v = (1 + c) / 2
  · exact Or.inr hcase
  · refine Or.inl ?_
    have ha2v_lt_half : a2v < (1 + c) / 2 := lt_of_le_of_ne (le_trans ha2v_le_M hM_le_half) hcase
    -- STEP 1: rule out a2v = 0, i.e. 0 < a2v.
    have ha2v_pos : 0 < a2v := by
      rcases lt_or_eq_of_le ha2v_nn with h | h
      · exact h
      · exfalso
        have ha2v_eq : a2v = 0 := h.symm
        set b : ℝ := ((1 - c) / 4) ^ 2 with hb_def
        have hb_pos : 0 < b := by
          have h1c : (0:ℝ) < 1 - c := by linarith
          positivity
        set a0 : ℝ := min M b / 2 with ha0_def
        have hminMb_pos : 0 < min M b := lt_min hM_pos hb_pos
        have ha0_pos : 0 < a0 := by positivity
        have ha0_lt_M : a0 < M := by
          have : min M b ≤ M := min_le_left _ _
          have h2 : a0 < min M b := by
            rw [ha0_def]; linarith [hminMb_pos]
          linarith
        have ha0_lt_b : a0 < b := by
          have : min M b ≤ b := min_le_right _ _
          have h2 : a0 < min M b := by rw [ha0_def]; linarith [hminMb_pos]
          linarith
        have ha0_lt_one : a0 < 1 := lt_trans ha0_lt_M hM_lt_one
        have hanti : StrictAntiOn (fun x => u2delta c delta x) (Set.Icc (0:ℝ) a0) := by
          apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 a0)
            (u2delta_continuousOn c delta a0 ha0_lt_one)
          · intro x hx
            rw [interior_Icc] at hx
            have hx0 : 0 < x := hx.1
            have hx_lt_a0 : x < a0 := hx.2
            have hx_lt_one : x < 1 := lt_trans hx_lt_a0 ha0_lt_one
            exact (u2delta_hasDerivAt c delta x hx0 hx_lt_one).hasDerivWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            have hx0 : 0 < x := hx.1
            have hx_lt_a0 : x < a0 := hx.2
            have hx_lt_one : x < 1 := lt_trans hx_lt_a0 ha0_lt_one
            have hx_lt_b : x < b := lt_trans hx_lt_a0 ha0_lt_b
            exact u2deriv_neg_near_zero c delta x hc1 hdelta hx0 hx_lt_one hx_lt_b
        have hmem0 : (0:ℝ) ∈ Set.Icc (0:ℝ) a0 := ⟨le_refl _, le_of_lt ha0_pos⟩
        have hmema0 : a0 ∈ Set.Icc (0:ℝ) a0 := ⟨le_of_lt ha0_pos, le_refl _⟩
        have hdecr : (fun x => u2delta c delta x) a0 < (fun x => u2delta c delta x) 0 :=
          hanti hmem0 hmema0 ha0_pos
        simp only at hdecr
        have hu0_eq : u2delta c delta (0:ℝ) = u2delta c delta a2v := by rw [ha2v_eq]
        rw [hu0_eq, hzero] at hdecr
        have ha0_mem : a0 ∈ Set.Icc (0:ℝ) M := ⟨le_of_lt ha0_pos, le_of_lt ha0_lt_M⟩
        have := hmin a0 ha0_mem
        rw [hzero] at this
        linarith
    -- STEP 2: split on interior vs right endpoint.
    rcases lt_or_eq_of_le ha2v_le_M with hlt | heq
    · have ha2v_int : a2v ∈ Set.Ioo (0:ℝ) M := ⟨ha2v_pos, hlt⟩
      have hderiv : HasDerivAt (fun x => u2delta c delta x) (u2deriv c delta a2v) a2v :=
        u2delta_hasDerivAt c delta a2v ha2v_pos ha2v_lt_one
      have hlocmin : IsLocalMin (fun x => u2delta c delta x) a2v := by
        have hnhds : Set.Ioo (0:ℝ) M ∈ nhds a2v := isOpen_Ioo.mem_nhds ha2v_int
        rw [IsLocalMin, IsMinFilter]
        filter_upwards [hnhds] with x hx
        have hx_mem : x ∈ Set.Icc (0:ℝ) M := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
        exact hmin x hx_mem
      exact hlocmin.hasDerivAt_eq_zero hderiv
    · have ha2v_eq_M : a2v = M := heq
      have hM_lt_half : M < (1 + c) / 2 := by rw [← ha2v_eq_M]; exact ha2v_lt_half
      have hz_le_half : zCG delta ≤ (1 + c) / 2 := by
        by_contra hcon
        push_neg at hcon
        have : M = (1 + c) / 2 := by rw [hM_def]; exact min_eq_right (le_of_lt hcon)
        linarith
      have hM_eq_z : M = zCG delta := by rw [hM_def]; exact min_eq_left hz_le_half
      have ha2v_eq_z : a2v = zCG delta := by rw [ha2v_eq_M, hM_eq_z]
      have hle : u2deriv c delta a2v ≤ 0 :=
        u2deriv_nonpos_at_rightmin c delta M a2v ha2v_pos ha2v_lt_one ha2v_le_M hmin
      have hident := u2deriv_slope_identity c delta a2v ha2v_pos ha2v_lt_one
      rw [hzero] at hident
      have hbr : 0 ≤ zBracket delta a2v := by
        rw [ha2v_eq_z]; exact zBracket_nonneg delta hdelta
      have h1c_pos : (0:ℝ) < 1 - c := by linarith
      have h1mz_pos : 0 < 1 - a2v := by linarith [ha2v_lt_one]
      have hge : 0 ≤ u2deriv c delta a2v := by
        have hprod_nonneg : 0 ≤ u2deriv c delta a2v * (1 - a2v) := by
          have : u2deriv c delta a2v * (1 - a2v) = (1 - c) * zBracket delta a2v := by
            linarith [hident]
          rw [this]; positivity
        nlinarith [hprod_nonneg, h1mz_pos]
      linarith

end Workspace.ProofLemmas.RGOptimalSolutionForA2
