import Mathlib
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.CGOptimalSolutionForA1
import Workspace.ProofLemmas.CGRelaxedCoreNonneg
import Workspace.ProofLemmas.RGABranchComparison
import Workspace.ProofLemmas.RGInteriorRoot
import Workspace.ProofLemmas.RGDeltaLambda
import Workspace.ProofLemmas.RGLambda2InUnitInterval

open Workspace.ProofLemmas.RGDefs
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.CGOptimalSolutionForA1
open Workspace.ProofLemmas.CGRelaxedCoreNonneg
open Workspace.ProofLemmas.RGABranchComparison
open Workspace.ProofLemmas.RGInteriorRoot
open Workspace.ProofLemmas.RGDeltaLambda
open Workspace.ProofLemmas.RGLambda2InUnitInterval

namespace Workspace.ProofLemmas.RGRelaxedCoreNonneg

set_option maxHeartbeats 4000000

/-- HasDerivAt for `u2delta c delta` at a point `a` with `0 < a < 1`. -/
private theorem u2delta_hasDerivAt (c delta a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun x => u2delta c delta x) (u2deriv c delta a) a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_ne : (1 - a) ≠ 0 := ne_of_gt h1ma_pos
  have hd_a_pow : HasDerivAt (fun x : ℝ => x ^ ((1:ℝ)/2)) ((1/2) * a ^ ((1:ℝ)/2 - 1)) a := by
    have h := (hasDerivAt_id a).rpow_const (p := (1:ℝ)/2) (Or.inl ha_ne)
    simpa using h
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
  have hfun : (fun x => u2delta c delta x) =
      (fun x : ℝ => (1 - c) * (delta * (1 - x) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2)) - 1 + 2 * x - c) := by
    funext x; rw [u2delta]
  rw [hfun]
  have hval : (1 - c) * (delta * (-1 * ((1/2) * (1 - a) ^ ((1:ℝ)/2 - 1))) - (1/2) * a ^ ((1:ℝ)/2 - 1)) + 2
      = u2deriv c delta a := by
    rw [u2deriv]
    have e1 : ((1:ℝ)/2 - 1) = -(1:ℝ)/2 := by norm_num
    rw [e1]
    ring
  rw [hval] at hd_total
  exact hd_total

/-- `u2delta c delta` is continuous on `Set.Icc 0 M` whenever `M < 1`. -/
private theorem u2delta_continuousOn (c delta M : ℝ) (hM : M < 1) :
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

/-- Second derivative of `u2delta c delta` at an interior point `0 < a < 1`:
`u₂''(a) = ((1-c)/4)·(a^{-3/2} − δ·(1−a)^{-3/2})`. -/
private theorem u2delta_secondDeriv (c delta a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun y => u2deriv c delta y)
      ((1 - c) / 4 * (a ^ (-(3:ℝ)/2) - delta * (1 - a) ^ (-(3:ℝ)/2))) a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_ne : (1 - a) ≠ 0 := ne_of_gt h1ma_pos
  set p1 : ℝ := -(1:ℝ)/2 with hp1_def
  set p2 : ℝ := -(3:ℝ)/2 with hp2_def
  have hexp : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; norm_num
  have hd_a : HasDerivAt (fun y : ℝ => y ^ p1) (p1 * a ^ p2) a := by
    have h := (hasDerivAt_id a).rpow_const (p := p1) (Or.inl ha_ne)
    rw [hexp] at h; simpa using h
  have hd_inner : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) a := by
    simpa using (hasDerivAt_id a).const_sub 1
  have hd_1ma : HasDerivAt (fun y : ℝ => (1 - y) ^ p1) (-1 * p1 * (1 - a) ^ p2) a := by
    have h := hd_inner.rpow_const (p := p1) (Or.inl h1ma_ne)
    rw [hexp] at h; exact h
  have hfun : (fun y => u2deriv c delta y) =
      (fun y : ℝ => (1/2) * (1 - c) * (-delta * (1 - y) ^ p1 - y ^ p1) + 2) := by
    funext y; rw [u2deriv]
  rw [hfun]
  have hd_d1ma : HasDerivAt (fun y : ℝ => -delta * (1 - y) ^ p1)
      (-delta * (-1 * p1 * (1 - a) ^ p2)) a := hd_1ma.const_mul (-delta)
  have hd_sub : HasDerivAt (fun y : ℝ => -delta * (1 - y) ^ p1 - y ^ p1)
      (-delta * (-1 * p1 * (1 - a) ^ p2) - p1 * a ^ p2) a := hd_d1ma.sub hd_a
  have hd_mul : HasDerivAt (fun y : ℝ => (1/2) * (1 - c) * (-delta * (1 - y) ^ p1 - y ^ p1))
      ((1/2) * (1 - c) * (-delta * (-1 * p1 * (1 - a) ^ p2) - p1 * a ^ p2)) a :=
    hd_sub.const_mul ((1/2) * (1 - c))
  have hd_total := hd_mul.add_const (2 : ℝ)
  convert hd_total using 1
  rw [hp1_def, hp2_def]; ring

/-- `u2delta c δ` is convex on `[0, zCG δ]` (for `δ > 0`, `c ≤ 1`). -/
private theorem u2delta_convexOn_left (c delta : ℝ) (hc1 : c ≤ 1) (hdelta : 0 < delta) :
    ConvexOn ℝ (Set.Icc (0:ℝ) (zCG delta)) (fun y => u2delta c delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have hcont : ContinuousOn (fun y => u2delta c delta y) (Set.Icc (0:ℝ) (zCG delta)) :=
    u2delta_continuousOn c delta (zCG delta) hz_lt_one
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 (zCG delta)) hcont
  · rw [interior_Icc]
    intro y hy
    exact (u2delta_hasDerivAt c delta y hy.1
      (lt_trans hy.2 hz_lt_one)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => u2delta c delta y) =ᶠ[nhds y] fun z => u2deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u2delta_hasDerivAt c delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2 : DifferentiableAt ℝ (fun y => u2deriv c delta y) y :=
      (u2delta_secondDeriv c delta y hy0 hy1).differentiableAt
    exact (hd2.congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => u2delta c delta y) =ᶠ[nhds y] fun z => u2deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u2delta_hasDerivAt c delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2_eq : deriv (deriv (fun y => u2delta c delta y)) y =
        deriv (fun y => u2deriv c delta y) y := hloc.deriv_eq
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hd2_eq, (u2delta_secondDeriv c delta y hy0 hy1).deriv]
    have hpsi_z : (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection delta hdelta; linarith
    have hpsi_anti := u1psi_strictAnti delta hdelta
    have hy_in : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hy0, hy1⟩
    have hz_in : zCG delta ∈ Set.Ioo (0:ℝ) 1 := ⟨hz_pos, hz_lt_one⟩
    have hpsi_y_nonneg : 0 ≤ y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) := by
      rcases eq_or_lt_of_le (le_of_lt hy.2) with heq | hlt
      · have : y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) =
            (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) := by rw [heq]
        rw [this, hpsi_z]
      · have := hpsi_anti hy_in hz_in hlt
        simp only at this
        linarith [hpsi_z]
    have h1c : 0 ≤ (1 - c) / 4 := by linarith
    have : 0 ≤ (1 - c) / 4 * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) :=
      mul_nonneg h1c hpsi_y_nonneg
    simpa using this

/-- `u2delta c δ` is concave on `[zCG δ, 1]` (for `δ > 0`, `c ≤ 1`). -/
private theorem u2delta_concaveOn_right (c delta : ℝ) (hc1 : c ≤ 1) (hdelta : 0 < delta) :
    ConcaveOn ℝ (Set.Icc (zCG delta) 1) (fun y => u2delta c delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have hcont : ContinuousOn (fun y => u2delta c delta y) (Set.Icc (zCG delta) 1) := by
    intro x hx
    have hx_ge : zCG delta ≤ x := hx.1
    have hx_le : x ≤ 1 := hx.2
    have hx_pos : 0 < x := lt_of_lt_of_le hz_pos hx_ge
    have h_inner : ContinuousAt (fun y : ℝ => 1 - y) x :=
      (continuous_const.sub continuous_id).continuousAt
    have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) (1 - x) := by
      rcases eq_or_lt_of_le hx_le with hxone | hxlt
      · rw [hxone]; simpa using
          Real.continuousAt_rpow_const (0:ℝ) ((1:ℝ)/2) (Or.inr (by norm_num))
      · exact Real.continuousAt_rpow_const (1 - x) ((1:ℝ)/2) (Or.inl (by linarith))
    have h_1mx_pow : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/2)) x := h_outer.comp h_inner
    have h_d_1mx : ContinuousAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2)) x :=
      h_1mx_pow.const_mul delta
    have h_x_pow : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) x :=
      Real.continuousAt_rpow_const x ((1:ℝ)/2) (Or.inr (by norm_num))
    have h_diff : ContinuousAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2)) x :=
      h_d_1mx.sub h_x_pow
    have h_mul : ContinuousAt
        (fun y : ℝ => (1 - c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) x :=
      h_diff.const_mul (1 - c)
    have h_total : ContinuousAt (fun y => u2delta c delta y) x := by
      have : (fun y => u2delta c delta y) =
          (fun y : ℝ => (1 - c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2)) - 1 + 2 * y - c) := by
        funext y; rw [u2delta]
      rw [this]
      exact (((h_mul.sub continuousAt_const).add
        ((continuous_const.mul continuous_id).continuousAt)).sub continuousAt_const)
    exact h_total.continuousWithinAt
  apply concaveOn_of_deriv2_nonpos (convex_Icc (zCG delta) 1) hcont
  · rw [interior_Icc]
    intro y hy
    exact (u2delta_hasDerivAt c delta y (lt_trans hz_pos hy.1) hy.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => u2delta c delta y) =ᶠ[nhds y] fun z => u2deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u2delta_hasDerivAt c delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2 : DifferentiableAt ℝ (fun y => u2deriv c delta y) y :=
      (u2delta_secondDeriv c delta y hy0 hy.2).differentiableAt
    exact (hd2.congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hy1 : y < 1 := hy.2
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => u2delta c delta y) =ᶠ[nhds y] fun z => u2deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u2delta_hasDerivAt c delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2_eq : deriv (deriv (fun y => u2delta c delta y)) y =
        deriv (fun y => u2deriv c delta y) y := hloc.deriv_eq
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hd2_eq, (u2delta_secondDeriv c delta y hy0 hy1).deriv]
    have hpsi_z : (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection delta hdelta; linarith
    have hpsi_anti := u1psi_strictAnti delta hdelta
    have hy_in : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hy0, hy1⟩
    have hz_in : zCG delta ∈ Set.Ioo (0:ℝ) 1 := ⟨hz_pos, hz_lt_one⟩
    have hpsi_y_nonpos : y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) ≤ 0 := by
      have := hpsi_anti hz_in hy_in hy.1
      simp only at this
      linarith [hpsi_z]
    have h1c : 0 ≤ (1 - c) / 4 := by linarith
    have : (1 - c) / 4 * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1c hpsi_y_nonpos
    simpa using this

/-- `u2delta c δ 1 = -2c` (the right-endpoint value). Wait — for robustness `u2delta c δ 1`
needs care.  `u2delta c δ 1 = (1-c)(δ·0 - 1) - 1 + 2 - c = -(1-c) + 1 - c = 0`. -/
private theorem u2delta_at_one (c delta : ℝ) : u2delta c delta 1 = 0 := by
  unfold u2delta
  rw [show (1:ℝ) - 1 = 0 by ring, Real.zero_rpow (by norm_num), Real.one_rpow]
  ring

/-- **Nonnegativity engine** (robustness c→−c image). -/
private theorem u2delta_nonneg_engine (c delta a2v : ℝ) (hc1 : c ≤ 1) (hdelta : 0 < delta)
    (ha2v_pos : 0 < a2v) (ha2v_le_z : a2v ≤ zCG delta)
    (hu_zero : u2delta c delta a2v = 0)
    (hderiv_zero : u2deriv c delta a2v = 0) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u2delta c delta y := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have ha2v_lt_one : a2v < 1 := lt_of_le_of_lt ha2v_le_z hz_lt_one
  set f : ℝ → ℝ := fun y => u2delta c delta y with hf_def
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) (zCG delta)) f := u2delta_convexOn_left c delta hc1 hdelta
  have hconc : ConcaveOn ℝ (Set.Icc (zCG delta) 1) f := u2delta_concaveOn_right c delta hc1 hdelta
  have ha2v_mem : a2v ∈ Set.Icc (0:ℝ) (zCG delta) := ⟨le_of_lt ha2v_pos, ha2v_le_z⟩
  have hderiv_a2 : HasDerivAt f (u2deriv c delta a2v) a2v :=
    u2delta_hasDerivAt c delta a2v ha2v_pos ha2v_lt_one
  rw [hderiv_zero] at hderiv_a2
  have hleft : ∀ y ∈ Set.Icc (0:ℝ) (zCG delta), 0 ≤ f y := by
    intro y hy
    have hfa2 : f a2v = 0 := hu_zero
    rcases lt_trichotomy y a2v with hlt | heq | hgt
    · have hsl := hconv.slope_le_of_hasDerivAt hy ha2v_mem hlt hderiv_a2
      rw [slope_def_field] at hsl
      have hpos : 0 < a2v - y := by linarith
      have : f a2v - f y ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have : 0 < (f a2v - f y) / (a2v - y) := div_pos hcon hpos
        linarith
      linarith [hfa2]
    · rw [heq, hfa2]
    · have hsl := hconv.le_slope_of_hasDerivAt ha2v_mem hy hgt hderiv_a2
      rw [slope_def_field] at hsl
      have hpos : 0 < y - a2v := by linarith
      have : 0 ≤ f y - f a2v := by
        by_contra hcon
        push_neg at hcon
        have : (f y - f a2v) / (y - a2v) < 0 := div_neg_of_neg_of_pos hcon hpos
        linarith
      linarith [hfa2]
  have hz_mem_left : zCG delta ∈ Set.Icc (0:ℝ) (zCG delta) := ⟨le_of_lt hz_pos, le_refl _⟩
  have hfz_nonneg : 0 ≤ f (zCG delta) := hleft _ hz_mem_left
  have hf_one : f 1 = 0 := u2delta_at_one c delta
  have hright : ∀ y ∈ Set.Icc (zCG delta) 1, 0 ≤ f y := by
    intro y hy
    have hz_mem : zCG delta ∈ Set.Icc (zCG delta) 1 := ⟨le_refl _, le_of_lt hz_lt_one⟩
    have hone_mem : (1:ℝ) ∈ Set.Icc (zCG delta) 1 := ⟨le_of_lt hz_lt_one, le_refl _⟩
    have hy_seg : y ∈ segment ℝ (zCG delta) 1 := by
      rw [segment_eq_Icc (le_of_lt hz_lt_one)]; exact hy
    have hchord := hconc.ge_on_segment hz_mem hone_mem hy_seg
    have hmin_nn : 0 ≤ min (f (zCG delta)) (f 1) := by
      rw [hf_one]; exact le_min hfz_nonneg (le_refl 0)
    exact le_trans hmin_nn hchord
  intro y hy0 hy1
  rcases le_or_gt y (zCG delta) with hyz | hyz
  · exact hleft y ⟨hy0, hyz⟩
  · exact hright y ⟨le_of_lt hyz, hy1⟩

/-- `0 < delta2 c` for `c ∈ [0,1)` (since `0 < λ₂ < 1`). -/
private theorem delta2_pos (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) : 0 < delta2 c := by
  obtain ⟨hl0, hl1, _⟩ := RGLambda2InUnitInterval c hc0 hc1
  unfold delta2 delta_of_lambda
  have h1 : (1:ℝ) < lambda2 c ^ (-((2:ℝ)/(2-1))) := by
    rw [show (-((2:ℝ)/(2-1))) = (-2:ℝ) by norm_num,
      show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg hl0.le,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [one_lt_inv_iff₀]
    refine ⟨by positivity, ?_⟩
    nlinarith [hl0, hl1, sq_nonneg (lambda2 c)]
  apply Real.rpow_pos_of_pos; linarith

/-- **Single-branch pointwise nonnegativity**: `u2 c y ≥ 0` for `y ∈ [0,1]`,
for ALL `c ∈ [0,1)` (the `c→−c` LOW-branch image; no high branch). -/
private theorem rg_hu2_nonneg (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u2 c y := by
  have hd2pos : 0 < delta2 c := delta2_pos c hc0 hc1
  -- surd s = √(3-2c)
  have h3 : (0:ℝ) ≤ 3 - 2 * c := by linarith
  set s := Real.sqrt (3 - 2 * c) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 3 - 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt h3]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  -- strict: since c < 1, 3-2c > 1, so s > 1.
  have hs_gt1 : 1 < s := by
    have h1 : (1:ℝ) < 3 - 2 * c := by linarith
    nlinarith [hs_sq, hs_nn, hs_ge1]
  -- s > c needs care: s² = 3-2c, c≥0; (s-c) sign? At c→1: s²=1, s=1 > c<1. Generally s>c.
  have hs_gt_c : c < s := by nlinarith [hs_sq, hs_nn, sq_nonneg (s - c)]
  -- a₂' and its square roots
  have ha2v : a2' c = (2 - c - s) / 2 := by rw [a2', hs_def]
  have ht_nn : (0:ℝ) ≤ (s - 1) / 2 := by linarith
  have ha2v_sq : a2' c = ((s - 1) / 2) ^ 2 := by rw [ha2v]; nlinarith [hs_sq]
  have ha2v_pos : 0 < a2' c := by
    rw [ha2v_sq]; have : (0:ℝ) < (s-1)/2 ∨ (s-1)/2 = 0 := by
      rcases eq_or_lt_of_le hs_ge1 with h | h
      · right; rw [← h]; ring
      · left; linarith
    rcases this with h | h
    · positivity
    · exfalso; have : s = 1 := by linarith
      rw [this] at hs_sq; nlinarith [hc0]
  have hsqrt_a2v : (a2' c) ^ ((1:ℝ)/2) = (s - 1) / 2 := by
    rw [ha2v_sq, ← Real.rpow_natCast ((s-1)/2) 2, ← Real.rpow_mul ht_nn]
    norm_num
  have h1ma2v : 1 - a2' c = (s + c) / 2 := by rw [ha2v]; ring
  have h1ma2v_pos : 0 < 1 - a2' c := by rw [h1ma2v]; linarith
  have h1mc_pos : (0:ℝ) < 1 - c := by linarith
  -- δ₂ explicit: δ₂² = N²/(1-a₂'), and δ₂·√(1-a₂') = N with N ≥ 0.
  obtain ⟨hlam_eq, _, _⟩ := RGDeltaLambda c hc0 hc1
  obtain ⟨hl0, hl1, _⟩ := RGLambda2InUnitInterval c hc0 hc1
  set δ := delta2 c with hδ_def
  set rt : ℝ := (1 - a2' c) ^ ((1:ℝ)/2) with hrt_def
  have hrt_sq : rt ^ 2 = 1 - a2' c := by
    rw [hrt_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt h1ma2v_pos)]; norm_num
  have hrt_pos : 0 < rt := by rw [hrt_def]; exact Real.rpow_pos_of_pos h1ma2v_pos _
  -- N (numerator), in surd form.  N = (1-2a₂'+c)/(1-c) + √a₂'.
  set N : ℝ := (1 - 2 * a2' c + c) / (1 - c) + (a2' c) ^ ((1:ℝ)/2) with hN_def
  have hN_s : N = (s - 1 + 2 * c) / (1 - c) + (s - 1) / 2 := by
    rw [hN_def, hsqrt_a2v, ha2v]; congr 1; field_simp; ring
  have hN_nn : 0 ≤ N := by
    rw [hN_s]; rw [div_add_div _ _ (ne_of_gt h1mc_pos) (by norm_num : (2:ℝ) ≠ 0)]
    apply div_nonneg _ (by positivity)
    nlinarith [hs_ge1, hs_gt_c, hc0, hs_sq, sq_nonneg (s - 1)]
  -- δ² = lambda2^{-2} - 1.
  have hbase_nn : (0:ℝ) ≤ lambda2 c ^ (-((2:ℝ)/(2-1))) - 1 := by
    rw [show (-((2:ℝ)/(2-1))) = -(2:ℝ) by norm_num, Real.rpow_neg hl0.le,
      show (2:ℝ)=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      le_sub_iff_add_le, zero_add, one_le_inv_iff₀]
    exact ⟨by positivity, by nlinarith [hl0, hl1, sq_nonneg (lambda2 c)]⟩
  have hδ_sq : δ ^ 2 = lambda2 c ^ (-((2:ℝ)/(2-1))) - 1 := by
    rw [hδ_def]; unfold delta2 delta_of_lambda
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hbase_nn]; norm_num
  have hlaminv : lambda2 c ^ (-((2:ℝ)/(2-1))) = 1 + N ^ 2 / (1 - a2' c) := by
    rw [hlam_eq, ← Real.rpow_mul (by positivity)]
    rw [show (-(1:ℝ)/2) * (-((2:ℝ)/(2-1))) = 1 by norm_num, Real.rpow_one]
  have hδ_d2sq : δ ^ 2 * (1 - a2' c) = N ^ 2 := by
    rw [hδ_sq, hlaminv, hN_def]; field_simp; ring
  -- δ·rt = N
  have hδrt : δ * rt = N := by
    have hsq : (δ * rt) ^ 2 = N ^ 2 := by
      rw [mul_pow, hrt_sq]; exact hδ_d2sq
    have hδrt_nn : 0 ≤ δ * rt := by positivity
    nlinarith [hsq, hN_nn, hδrt_nn, sq_nonneg (δ * rt - N)]
  -- u₂(a₂') = 0.
  have hu_zero : u2 c (a2' c) = 0 := by
    show u2delta c δ (a2' c) = 0
    unfold u2delta
    rw [show (1 - a2' c) ^ ((1:ℝ)/2) = rt from rfl, hsqrt_a2v]
    have : δ * rt = (1 - 2 * a2' c + c) / (1 - c) + (s - 1) / 2 := by
      rw [hδrt, hN_def, hsqrt_a2v]
    rw [this, ha2v]; field_simp; ring
  -- FOC: u2deriv c δ (a₂') = 0.
  have hsqrt_a2v_pos : 0 < (a2' c) ^ ((1:ℝ)/2) := by rw [hsqrt_a2v]; linarith [hs_gt1]
  have hderiv_zero : u2deriv c δ (a2' c) = 0 := by
    unfold u2deriv
    have e1 : (1 - a2' c) ^ (-(1:ℝ)/2) = rt⁻¹ := by
      rw [hrt_def, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma2v_pos)]
    have e2 : (a2' c) ^ (-(1:ℝ)/2) = ((a2' c) ^ ((1:ℝ)/2))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt ha2v_pos)]
    rw [e1, e2, hsqrt_a2v]
    have hs1 : s - 1 > 0 := by linarith
    have hsc : s + c > 0 := by linarith
    have hδrt_inv : δ * rt⁻¹ = N / (1 - a2' c) := by
      rw [eq_div_iff (ne_of_gt h1ma2v_pos), ← hrt_sq]
      have : δ * rt⁻¹ * rt ^ 2 = (δ * rt) * (rt⁻¹ * rt) := by ring
      rw [this, hδrt, inv_mul_cancel₀ (ne_of_gt hrt_pos), mul_one]
    have hbracket : -δ * rt⁻¹ - ((s - 1) / 2)⁻¹ = -(N / (1 - a2' c)) - ((s - 1) / 2)⁻¹ := by
      linear_combination -hδrt_inv
    have hgoal : (1 / 2) * (1 - c) * (-δ * rt⁻¹ - ((s - 1) / 2)⁻¹) + 2 = 0 := by
      rw [hbracket, hN_s, h1ma2v]
      have hsc' : (s + c) / 2 ≠ 0 := ne_of_gt (by linarith)
      have hs1' : (s - 1) / 2 ≠ 0 := ne_of_gt (by linarith)
      field_simp
      nlinarith [hs_sq, hs1, hsc, h1mc_pos]
    exact hgoal
  -- a₂' ≤ zCG δ.
  have hz_pos : 0 < zCG δ := zCG_pos δ hd2pos
  have hz_lt_one : zCG δ < 1 := zCG_lt_one δ hd2pos
  have ha2v_lt_one : a2' c < 1 := by linarith [h1ma2v_pos]
  have ht_pos : 0 < (s - 1) / 2 := by
    rcases eq_or_lt_of_le hs_ge1 with h | h
    · exfalso; have : s = 1 := h.symm; rw [this] at hs_sq; nlinarith [hc0]
    · linarith
  have hpsi_a2_pos : 0 < (a2' c) ^ (-(3:ℝ)/2) - δ * (1 - a2' c) ^ (-(3:ℝ)/2) := by
    have e_a3 : (a2' c) ^ (-(3:ℝ)/2) = (((s - 1) / 2) ^ 3)⁻¹ := by
      rw [ha2v_sq, ← Real.rpow_natCast (((s-1)/2)) 2, ← Real.rpow_mul ht_nn,
        show ((2:ℕ):ℝ) * (-(3:ℝ)/2) = -((3:ℕ):ℝ) by norm_num,
        Real.rpow_neg ht_nn, Real.rpow_natCast]
    have e_1ma3 : (1 - a2' c) ^ (-(3:ℝ)/2) = (rt ^ 3)⁻¹ := by
      have hrt3 : rt ^ 3 = (1 - a2' c) ^ ((3:ℝ)/2) := by
        rw [hrt_def, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (le_of_lt h1ma2v_pos)]
        norm_num
      rw [hrt3, show (-(3:ℝ)/2) = -((3:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma2v_pos)]
    rw [e_a3, e_1ma3]
    have hδ_rt3 : δ * (rt ^ 3)⁻¹ = N / (1 - a2' c) ^ 2 := by
      rw [eq_div_iff (by positivity)]
      have hrtne : rt ≠ 0 := ne_of_gt hrt_pos
      have hkey : (rt ^ 3)⁻¹ * (1 - a2' c) ^ 2 = rt := by
        rw [← hrt_sq]
        field_simp
      calc δ * (rt ^ 3)⁻¹ * (1 - a2' c) ^ 2
          = δ * ((rt ^ 3)⁻¹ * (1 - a2' c) ^ 2) := by ring
        _ = δ * rt := by rw [hkey]
        _ = N := hδrt
    rw [hδ_rt3]
    rw [h1ma2v, hN_s]
    have hs1 : 0 < s - 1 := by linarith
    have hsc : 0 < s + c := by linarith
    rw [inv_eq_one_div, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [div_add_div _ _ (ne_of_gt h1mc_pos) (by norm_num : (2:ℝ) ≠ 0),
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hs_sq, hs1, hsc, h1mc_pos, hs_nn, sq_nonneg (s - 1), mul_pos hs1 hsc,
      mul_nonneg hs_nn (sq_nonneg (s - 1)), mul_pos (mul_pos hs1 hsc) h1mc_pos]
  have ha2v_le_z : a2' c ≤ zCG δ := by
    by_contra hcon
    push_neg at hcon
    have hz_in : zCG δ ∈ Set.Ioo (0:ℝ) 1 := ⟨hz_pos, hz_lt_one⟩
    have ha_in : a2' c ∈ Set.Ioo (0:ℝ) 1 := ⟨ha2v_pos, ha2v_lt_one⟩
    have hpsi_z : (zCG δ) ^ (-(3:ℝ)/2) - δ * (1 - zCG δ) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection δ hd2pos; linarith
    have := u1psi_strictAnti δ hd2pos hz_in ha_in hcon
    simp only at this
    linarith [hpsi_a2_pos, hpsi_z]
  -- Apply the engine.
  have hkey := u2delta_nonneg_engine c δ (a2' c) (le_of_lt hc1) hd2pos ha2v_pos ha2v_le_z hu_zero hderiv_zero
  intro y hy0 hy1
  show 0 ≤ u2delta c δ y
  exact hkey y hy0 hy1

theorem RGRelaxedCoreNonneg
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n : ℕ}
    (x : Fin n → ℝ)
    (hx_nn : ∀ i, 0 ≤ x i) (hx_le_one : ∀ i, x i ≤ 1)
    (hx_sum : (∑ i, x i) = (1 + c) / 2 * (n : ℝ)) :
    0 ≤ (∑ i, h_q 2 (lambda2 c) (delta2 c) (x i)) := by
  have hc_pos : (0 : ℝ) < 1 - c := by linarith
  have hlam_pos : 0 < lambda2 c := (RGLambda2InUnitInterval c hc0 hc1).1
  have hcoef_nn : 0 ≤ lambda2 c / (1 - c) := by positivity
  -- SINGLE branch: `u₂ ≥ 0` global support line `ℓ(x) = λ₂/(1-c)·(1 − 2x + c)`.
  have hu2_nonneg : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u2 c y :=
    rg_hu2_nonneg c hc0 hc1
  have key : ∀ y : ℝ,
      h_q 2 (lambda2 c) (delta2 c) y = lambda2 c / (1 - c) * (u2 c y + 1 - 2 * y + c) := by
    intro y; unfold h_q u2; field_simp; ring
  have h_pointwise : ∀ i,
      lambda2 c / (1 - c) * (1 - 2 * x i + c) ≤ h_q 2 (lambda2 c) (delta2 c) (x i) := by
    intro i
    rw [key (x i)]
    have hu := hu2_nonneg (x i) (hx_nn i) (hx_le_one i)
    have hmul := mul_le_mul_of_nonneg_left
      (show (1 - 2 * x i + c) ≤ (u2 c (x i) + 1 - 2 * (x i) + c) by linarith) hcoef_nn
    linarith [hmul]
  have hsum_lb :
      (∑ i, lambda2 c / (1 - c) * (1 - 2 * x i + c))
        ≤ (∑ i, h_q 2 (lambda2 c) (delta2 c) (x i)) :=
    Finset.sum_le_sum (fun i _ => h_pointwise i)
  have hsum_eq : (∑ i, lambda2 c / (1 - c) * (1 - 2 * x i + c)) = 0 := by
    rw [← Finset.mul_sum]
    have hinner : (∑ i, (1 - 2 * x i + c)) = (n : ℝ) - 2 * (∑ i, x i) + c * n := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
      simp [mul_comm]
    rw [hinner, hx_sum]; ring
  rw [hsum_eq] at hsum_lb
  exact hsum_lb

end Workspace.ProofLemmas.RGRelaxedCoreNonneg
