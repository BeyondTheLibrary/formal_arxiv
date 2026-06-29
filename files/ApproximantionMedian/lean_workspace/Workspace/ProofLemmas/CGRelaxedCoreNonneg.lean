import Mathlib
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.CGABranchComparison
import Workspace.ProofLemmas.CGInteriorRoot
import Workspace.ProofLemmas.CGDeltaLambdaLowBranch
import Workspace.ProofLemmas.CGDeltaLambdaHighBranch
import Workspace.ProofLemmas.CGOptimalSolutionForA1
import Workspace.ProofLemmas.CGLambda1InUnitInterval

open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.CGABranchComparison
open Workspace.ProofLemmas.CGInteriorRoot
open Workspace.ProofLemmas.CGDeltaLambdaLowBranch
open Workspace.ProofLemmas.CGDeltaLambdaHighBranch
open Workspace.ProofLemmas.CGOptimalSolutionForA1
open Workspace.ProofLemmas.CGLambda1InUnitInterval

namespace Workspace.ProofLemmas.CGRelaxedCoreNonneg

set_option maxHeartbeats 4000000

/-- Second derivative of `u1delta c delta` at an interior point `0 < a < 1`:
`u₁''(a) = ((1+c)/4)·(a^{-3/2} − δ·(1−a)^{-3/2})`.  (No `δ ≥ 1` needed.) -/
theorem u1delta_secondDeriv (c delta a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun y => u1deriv c delta y)
      ((1 + c) / 4 * (a ^ (-(3:ℝ)/2) - delta * (1 - a) ^ (-(3:ℝ)/2))) a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_ne : (1 - a) ≠ 0 := ne_of_gt h1ma_pos
  -- exponents
  set p1 : ℝ := -(1:ℝ)/2 with hp1_def
  set p2 : ℝ := -(3:ℝ)/2 with hp2_def
  have hexp : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; norm_num
  -- d/da a^p1 = p1 * a^p2
  have hd_a : HasDerivAt (fun y : ℝ => y ^ p1) (p1 * a ^ p2) a := by
    have h := (hasDerivAt_id a).rpow_const (p := p1) (Or.inl ha_ne)
    rw [hexp] at h; simpa using h
  -- d/da (1-a)^p1 = p1 * (1-a)^p2 * (-1)
  have hd_inner : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) a := by
    simpa using (hasDerivAt_id a).const_sub 1
  have hd_1ma : HasDerivAt (fun y : ℝ => (1 - y) ^ p1) (-1 * p1 * (1 - a) ^ p2) a := by
    have h := hd_inner.rpow_const (p := p1) (Or.inl h1ma_ne)
    rw [hexp] at h; exact h
  -- u1deriv c delta y = (1/2)*(1+c)*(-delta*(1-y)^p1 - y^p1) + 2
  have hfun : (fun y => u1deriv c delta y) =
      (fun y : ℝ => (1/2) * (1 + c) * (-delta * (1 - y) ^ p1 - y ^ p1) + 2) := by
    funext y; rw [u1deriv]
  rw [hfun]
  -- assemble
  have hd_d1ma : HasDerivAt (fun y : ℝ => -delta * (1 - y) ^ p1)
      (-delta * (-1 * p1 * (1 - a) ^ p2)) a := hd_1ma.const_mul (-delta)
  have hd_sub : HasDerivAt (fun y : ℝ => -delta * (1 - y) ^ p1 - y ^ p1)
      (-delta * (-1 * p1 * (1 - a) ^ p2) - p1 * a ^ p2) a := hd_d1ma.sub hd_a
  have hd_mul : HasDerivAt (fun y : ℝ => (1/2) * (1 + c) * (-delta * (1 - y) ^ p1 - y ^ p1))
      ((1/2) * (1 + c) * (-delta * (-1 * p1 * (1 - a) ^ p2) - p1 * a ^ p2)) a :=
    hd_sub.const_mul ((1/2) * (1 + c))
  have hd_total := hd_mul.add_const (2 : ℝ)
  convert hd_total using 1
  rw [hp1_def, hp2_def]; ring

/-- `ψ(a) = a^{-3/2} − δ·(1−a)^{-3/2}` is strictly antitone on `(0,1)` for `δ > 0`. -/
theorem u1psi_strictAnti (delta : ℝ) (hdelta : 0 < delta) :
    StrictAntiOn (fun a => a ^ (-(3:ℝ)/2) - delta * (1 - a) ^ (-(3:ℝ)/2)) (Set.Ioo (0:ℝ) 1) := by
  intro xx hxx yy hyy hxy
  have hx_pos : 0 < xx := hxx.1
  have hy_pos : 0 < yy := hyy.1
  have h1my_pos : 0 < 1 - yy := by linarith [hyy.2]
  have hp_neg : (-(3:ℝ)/2) < 0 := by norm_num
  have hxp : yy ^ (-(3:ℝ)/2) < xx ^ (-(3:ℝ)/2) :=
    Real.rpow_lt_rpow_of_neg hx_pos hxy hp_neg
  have h1mxy : 1 - yy < 1 - xx := by linarith
  have h1m_p : (1 - xx) ^ (-(3:ℝ)/2) < (1 - yy) ^ (-(3:ℝ)/2) :=
    Real.rpow_lt_rpow_of_neg h1my_pos h1mxy hp_neg
  have hd_mul : delta * (1 - xx) ^ (-(3:ℝ)/2) < delta * (1 - yy) ^ (-(3:ℝ)/2) :=
    mul_lt_mul_of_pos_left h1m_p hdelta
  simp only
  linarith

/-- `u1delta c δ` is convex on `[0, zCG δ]` (for `δ > 0`). -/
theorem u1delta_convexOn_left (c delta : ℝ) (hc0 : 0 ≤ c) (hdelta : 0 < delta) :
    ConvexOn ℝ (Set.Icc (0:ℝ) (zCG delta)) (fun y => u1delta c delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have hcont : ContinuousOn (fun y => u1delta c delta y) (Set.Icc (0:ℝ) (zCG delta)) :=
    u1delta_continuousOn c delta (zCG delta) hz_lt_one
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 (zCG delta)) hcont
  · rw [interior_Icc]
    intro y hy
    exact (u1delta_hasDerivAt c delta y hy.1
      (lt_trans hy.2 hz_lt_one)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hopen : IsOpen (Set.Ioo (0:ℝ) (zCG delta)) := isOpen_Ioo
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := hopen.mem_nhds hy
    have hloc : deriv (fun y => u1delta c delta y) =ᶠ[nhds y] fun z => u1deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u1delta_hasDerivAt c delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2 : DifferentiableAt ℝ (fun y => u1deriv c delta y) y :=
      (u1delta_secondDeriv c delta y hy0 hy1).differentiableAt
    exact (hd2.congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hopen : IsOpen (Set.Ioo (0:ℝ) (zCG delta)) := isOpen_Ioo
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := hopen.mem_nhds hy
    have hloc : deriv (fun y => u1delta c delta y) =ᶠ[nhds y] fun z => u1deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u1delta_hasDerivAt c delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2_eq : deriv (deriv (fun y => u1delta c delta y)) y =
        deriv (fun y => u1deriv c delta y) y := hloc.deriv_eq
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hd2_eq, (u1delta_secondDeriv c delta y hy0 hy1).deriv]
    -- second derivative ≥ 0 on (0,z): ψ(y) ≥ 0 since y ≤ z and ψ antitone, ψ(z)=0.
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
    have h1c : 0 ≤ (1 + c) / 4 := by positivity
    have : 0 ≤ (1 + c) / 4 * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) :=
      mul_nonneg h1c hpsi_y_nonneg
    simpa using this

/-- `u1delta c δ` is concave on `[zCG δ, 1]` (for `δ > 0`). -/
theorem u1delta_concaveOn_right (c delta : ℝ) (hc0 : 0 ≤ c) (hdelta : 0 < delta) :
    ConcaveOn ℝ (Set.Icc (zCG delta) 1) (fun y => u1delta c delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  -- continuity on [z,1]: u1delta_continuousOn needs upper bound < 1, so handle endpoint 1 directly.
  have hcont : ContinuousOn (fun y => u1delta c delta y) (Set.Icc (zCG delta) 1) := by
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
        (fun y : ℝ => (1 + c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) x :=
      h_diff.const_mul (1 + c)
    have h_total : ContinuousAt (fun y => u1delta c delta y) x := by
      have : (fun y => u1delta c delta y) =
          (fun y : ℝ => (1 + c) * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2)) - 1 + 2 * y + c) := by
        funext y; rw [u1delta]
      rw [this]
      exact (((h_mul.sub continuousAt_const).add
        ((continuous_const.mul continuous_id).continuousAt)).add continuousAt_const)
    exact h_total.continuousWithinAt
  apply concaveOn_of_deriv2_nonpos (convex_Icc (zCG delta) 1) hcont
  · rw [interior_Icc]
    intro y hy
    exact (u1delta_hasDerivAt c delta y (lt_trans hz_pos hy.1) hy.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hopen : IsOpen (Set.Ioo (zCG delta) 1) := isOpen_Ioo
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := hopen.mem_nhds hy
    have hloc : deriv (fun y => u1delta c delta y) =ᶠ[nhds y] fun z => u1deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u1delta_hasDerivAt c delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2 : DifferentiableAt ℝ (fun y => u1deriv c delta y) y :=
      (u1delta_secondDeriv c delta y hy0 hy.2).differentiableAt
    exact (hd2.congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hy1 : y < 1 := hy.2
    have hopen : IsOpen (Set.Ioo (zCG delta) 1) := isOpen_Ioo
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := hopen.mem_nhds hy
    have hloc : deriv (fun y => u1delta c delta y) =ᶠ[nhds y] fun z => u1deriv c delta z := by
      filter_upwards [hnhds] with z hz
      exact (u1delta_hasDerivAt c delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2_eq : deriv (deriv (fun y => u1delta c delta y)) y =
        deriv (fun y => u1deriv c delta y) y := hloc.deriv_eq
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hd2_eq, (u1delta_secondDeriv c delta y hy0 hy1).deriv]
    -- second derivative ≤ 0 on (z,1): ψ(y) ≤ 0 since y > z and ψ antitone, ψ(z)=0.
    have hpsi_z : (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection delta hdelta; linarith
    have hpsi_anti := u1psi_strictAnti delta hdelta
    have hy_in : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hy0, hy1⟩
    have hz_in : zCG delta ∈ Set.Ioo (0:ℝ) 1 := ⟨hz_pos, hz_lt_one⟩
    have hpsi_y_nonpos : y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) ≤ 0 := by
      have := hpsi_anti hz_in hy_in hy.1
      simp only at this
      linarith [hpsi_z]
    have h1c : 0 ≤ (1 + c) / 4 := by positivity
    have : (1 + c) / 4 * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1c hpsi_y_nonpos
    simpa using this

/-- `u1delta c δ 1 = 0` (the right-endpoint zero). -/
theorem u1delta_at_one (c delta : ℝ) : u1delta c delta 1 = 0 := by
  unfold u1delta
  rw [show (1:ℝ) - 1 = 0 by ring, Real.zero_rpow (by norm_num), Real.one_rpow]
  ring

/-- **Nonnegativity engine.**  If `δ > 0` and `a₁ ∈ (0, zCG δ]` is an interior critical
zero of `u1delta c δ` (`u₁(a₁) = 0` and `u₁'(a₁) = 0`), then `u1delta c δ y ≥ 0` for all
`y ∈ [0,1]`.  (Convex on `[0,z]` with a stationary zero ⇒ `u₁ ≥ 0` there; concave on
`[z,1]` with `u₁(z) ≥ 0`, `u₁(1) = 0` ⇒ chord ⇒ `u₁ ≥ 0` there.) -/
theorem u1delta_nonneg_engine (c delta a1v : ℝ) (hc0 : 0 ≤ c) (hdelta : 0 < delta)
    (ha1v_pos : 0 < a1v) (ha1v_le_z : a1v ≤ zCG delta)
    (hu_zero : u1delta c delta a1v = 0)
    (hderiv_zero : u1deriv c delta a1v = 0) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u1delta c delta y := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have ha1v_lt_one : a1v < 1 := lt_of_le_of_lt ha1v_le_z hz_lt_one
  set f : ℝ → ℝ := fun y => u1delta c delta y with hf_def
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) (zCG delta)) f := u1delta_convexOn_left c delta hc0 hdelta
  have hconc : ConcaveOn ℝ (Set.Icc (zCG delta) 1) f := u1delta_concaveOn_right c delta hc0 hdelta
  have ha1v_mem : a1v ∈ Set.Icc (0:ℝ) (zCG delta) := ⟨le_of_lt ha1v_pos, ha1v_le_z⟩
  have hderiv_a1 : HasDerivAt f (u1deriv c delta a1v) a1v :=
    u1delta_hasDerivAt c delta a1v ha1v_pos ha1v_lt_one
  rw [hderiv_zero] at hderiv_a1
  -- STEP A: f ≥ 0 = f(a₁) on [0,z] (tangent below convex, slope 0).
  have hleft : ∀ y ∈ Set.Icc (0:ℝ) (zCG delta), 0 ≤ f y := by
    intro y hy
    have hfa1 : f a1v = 0 := hu_zero
    rcases lt_trichotomy y a1v with hlt | heq | hgt
    · -- y < a1v: slope f y a1v ≤ f'(a1v) = 0  ⟹ (f a1v - f y)/(a1v-y) ≤ 0 ⟹ f y ≥ f a1v
      have hsl := hconv.slope_le_of_hasDerivAt hy ha1v_mem hlt hderiv_a1
      rw [slope_def_field] at hsl
      have hpos : 0 < a1v - y := by linarith
      have : f a1v - f y ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have : 0 < (f a1v - f y) / (a1v - y) := div_pos hcon hpos
        linarith
      linarith [hfa1]
    · rw [heq, hfa1]
    · -- a1v < y: f'(a1v) = 0 ≤ slope f a1v y = (f y - f a1v)/(y-a1v) ⟹ f y ≥ f a1v
      have hsl := hconv.le_slope_of_hasDerivAt ha1v_mem hy hgt hderiv_a1
      rw [slope_def_field] at hsl
      have hpos : 0 < y - a1v := by linarith
      have : 0 ≤ f y - f a1v := by
        by_contra hcon
        push_neg at hcon
        have : (f y - f a1v) / (y - a1v) < 0 := div_neg_of_neg_of_pos hcon hpos
        linarith
      linarith [hfa1]
  -- u₁(z) ≥ 0.
  have hz_mem_left : zCG delta ∈ Set.Icc (0:ℝ) (zCG delta) := ⟨le_of_lt hz_pos, le_refl _⟩
  have hfz_nonneg : 0 ≤ f (zCG delta) := hleft _ hz_mem_left
  have hf_one : f 1 = 0 := u1delta_at_one c delta
  -- STEP B: f ≥ 0 on [z,1] via concavity chord.
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
  -- Combine.
  intro y hy0 hy1
  rcases le_or_gt y (zCG delta) with hyz | hyz
  · exact hleft y ⟨hy0, hyz⟩
  · exact hright y ⟨le_of_lt hyz, hy1⟩

/-- `0 < delta1 c` for `c ∈ [0,1)` (since `0 < λ₁ < 1`). -/
theorem delta1_pos (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) : 0 < delta1 c := by
  obtain ⟨hl0, hl1, _⟩ := CGLambda1InUnitInterval c hc0 hc1
  unfold delta1 delta_of_lambda
  have h1 : (1:ℝ) < lambda1 c ^ (-((2:ℝ)/(2-1))) := by
    rw [show (-((2:ℝ)/(2-1))) = (-2:ℝ) by norm_num,
      show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg hl0.le,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [one_lt_inv_iff₀]
    refine ⟨by positivity, ?_⟩
    nlinarith [hl0, hl1, sq_nonneg (lambda1 c)]
  apply Real.rpow_pos_of_pos; linarith

/-- **Low-branch pointwise nonnegativity** (`c < 1/2`): `u1 c y ≥ 0` for `y ∈ [0,1]`.
The interior critical point `a₁' = a1' c` is a stationary zero of `u₁` in the convex
region `(0, zCG δ₁]`, so the nonnegativity engine applies. -/
theorem low_branch_hu1_nonneg (c : ℝ) (hc0 : 0 ≤ c) (hc_hi : c < 1 / 2) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u1 c y := by
  have hc1 : c < 1 := by linarith
  have hd1pos : 0 < delta1 c := delta1_pos c hc0 hc1
  -- surd s = √(3+2c)
  have h3 : (0:ℝ) ≤ 3 + 2 * c := by linarith
  set s := Real.sqrt (3 + 2 * c) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 3 + 2 * c := by rw [hs_def, sq, Real.mul_self_sqrt h3]
  have hs_ge1 : 1 ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hs_gt_c : c < s := by nlinarith [hs_sq, hs_nn, sq_nonneg (s - c)]
  -- a₁' and its square roots
  have ha1v : a1' c = (2 + c - s) / 2 := by rw [a1', hs_def]
  have ht_nn : (0:ℝ) ≤ (s - 1) / 2 := by linarith
  have ha1v_sq : a1' c = ((s - 1) / 2) ^ 2 := by rw [ha1v]; nlinarith [hs_sq]
  have ha1v_pos : 0 < a1' c := by
    rw [ha1v_sq]; have : (0:ℝ) < (s-1)/2 ∨ (s-1)/2 = 0 := by
      rcases eq_or_lt_of_le hs_ge1 with h | h
      · right; rw [← h]; ring
      · left; linarith
    rcases this with h | h
    · positivity
    · -- s = 1 ⟹ c such that 3+2c=1 ⟹ c=-1, impossible since c≥0
      exfalso; have : s = 1 := by linarith
      rw [this] at hs_sq; nlinarith [hc0]
  have hsqrt_a1v : (a1' c) ^ ((1:ℝ)/2) = (s - 1) / 2 := by
    rw [ha1v_sq, ← Real.rpow_natCast ((s-1)/2) 2, ← Real.rpow_mul ht_nn]
    norm_num
  have h1ma1v : 1 - a1' c = (s - c) / 2 := by rw [ha1v]; ring
  have h1ma1v_pos : 0 < 1 - a1' c := by rw [h1ma1v]; linarith
  have hc1pos : (0:ℝ) < 1 + c := by linarith
  have ha1v_lt_half : a1' c < (1 - c) / 2 := by
    have := (CGABranchComparison_iff c hc0).mpr (le_of_lt hc_hi)
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · -- a₁' = (1-c)/2 would force c = 1/2, contradiction
      exfalso
      have : a1' c = (1 - c) / 2 := h
      rw [ha1v] at this; have hsc : s = 1 + 2 * c := by linarith
      rw [hsc] at hs_sq; nlinarith [hc_hi, hc0]
  -- δ₁ explicit: δ₁² = d1sq, and δ₁·√(1-a₁') = N with N ≥ 0.
  obtain ⟨hlam_eq, _, _⟩ := CGDeltaLambdaLowBranch c hc0 hc_hi
  obtain ⟨hl0, hl1, _⟩ := CGLambda1InUnitInterval c hc0 hc1
  -- abbreviations matching the surd forms
  set δ := delta1 c with hδ_def
  set rt : ℝ := (1 - a1' c) ^ ((1:ℝ)/2) with hrt_def
  have hrt_sq : rt ^ 2 = 1 - a1' c := by
    rw [hrt_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt h1ma1v_pos)]; norm_num
  have hrt_pos : 0 < rt := by rw [hrt_def]; exact Real.rpow_pos_of_pos h1ma1v_pos _
  -- N (numerator), in surd form.
  set N : ℝ := (1 - 2 * a1' c - c) / (1 + c) + (a1' c) ^ ((1:ℝ)/2) with hN_def
  have hN_s : N = (s - 1 - 2 * c) / (1 + c) + (s - 1) / 2 := by
    rw [hN_def, hsqrt_a1v, ha1v]; congr 1; field_simp; ring
  have hN_nn : 0 ≤ N := by
    rw [hN_s]; rw [div_add_div _ _ (ne_of_gt hc1pos) (by norm_num : (2:ℝ) ≠ 0)]
    apply div_nonneg _ (by positivity)
    nlinarith [hs_ge1, hs_gt_c, hc0, hs_sq, sq_nonneg (s - 3)]
  -- δ² = d1sq = N²/(1-a₁')
  have hbase_nn : (0:ℝ) ≤ lambda1 c ^ (-((2:ℝ)/(2-1))) - 1 := by
    rw [show (-((2:ℝ)/(2-1))) = -(2:ℝ) by norm_num, Real.rpow_neg hl0.le,
      show (2:ℝ)=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      le_sub_iff_add_le, zero_add, one_le_inv_iff₀]
    exact ⟨by positivity, by nlinarith [hl0, hl1, sq_nonneg (lambda1 c)]⟩
  have hδ_sq : δ ^ 2 = lambda1 c ^ (-((2:ℝ)/(2-1))) - 1 := by
    rw [hδ_def]; unfold delta1 delta_of_lambda
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hbase_nn]; norm_num
  have hlaminv : lambda1 c ^ (-((2:ℝ)/(2-1))) = 1 + N ^ 2 / (1 - a1' c) := by
    rw [hlam_eq, ← Real.rpow_mul (by positivity)]
    rw [show (-(1:ℝ)/2) * (-((2:ℝ)/(2-1))) = 1 by norm_num, Real.rpow_one]
  have hδ_d1sq : δ ^ 2 * (1 - a1' c) = N ^ 2 := by
    rw [hδ_sq, hlaminv, hN_def]; field_simp; ring
  -- δ·rt = N (both nonneg, squares equal)
  have hδrt : δ * rt = N := by
    have hsq : (δ * rt) ^ 2 = N ^ 2 := by
      rw [mul_pow, hrt_sq]; exact hδ_d1sq
    have hδrt_nn : 0 ≤ δ * rt := by positivity
    nlinarith [hsq, hN_nn, hδrt_nn, sq_nonneg (δ * rt - N)]
  -- u₁(a₁') = 0.
  have hu_zero : u1 c (a1' c) = 0 := by
    show u1delta c δ (a1' c) = 0
    unfold u1delta
    rw [show (1 - a1' c) ^ ((1:ℝ)/2) = rt from rfl, hsqrt_a1v]
    have : δ * rt = (1 - 2 * a1' c - c) / (1 + c) + (s - 1) / 2 := by
      rw [hδrt, hN_def, hsqrt_a1v]
    rw [this, ha1v]; field_simp; ring
  -- FOC: u1deriv c δ (a₁') = 0.
  have hsqrt_a1v_pos : 0 < (a1' c) ^ ((1:ℝ)/2) := by rw [hsqrt_a1v]; linarith
  have hderiv_zero : u1deriv c δ (a1' c) = 0 := by
    unfold u1deriv
    have e1 : (1 - a1' c) ^ (-(1:ℝ)/2) = rt⁻¹ := by
      rw [hrt_def, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma1v_pos)]
    have e2 : (a1' c) ^ (-(1:ℝ)/2) = ((a1' c) ^ ((1:ℝ)/2))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt ha1v_pos)]
    rw [e1, e2, hsqrt_a1v]
    -- want: ½(1+c)(-δ·rt⁻¹ - ((s-1)/2)⁻¹) + 2 = 0.
    -- Rewrite rt⁻¹ via δ·rt = N and rt² = 1-a₁': δ·rt⁻¹ = N/(1-a₁').
    have hs1 : s - 1 > 0 := by linarith
    have hsc : s - c > 0 := by linarith
    have hδrt_inv : δ * rt⁻¹ = N / (1 - a1' c) := by
      rw [eq_div_iff (ne_of_gt h1ma1v_pos), ← hrt_sq]
      have : δ * rt⁻¹ * rt ^ 2 = (δ * rt) * (rt⁻¹ * rt) := by ring
      rw [this, hδrt, inv_mul_cancel₀ (ne_of_gt hrt_pos), mul_one]
    have hbracket : -δ * rt⁻¹ - ((s - 1) / 2)⁻¹ = -(N / (1 - a1' c)) - ((s - 1) / 2)⁻¹ := by
      linear_combination -hδrt_inv
    have hgoal : (1 / 2) * (1 + c) * (-δ * rt⁻¹ - ((s - 1) / 2)⁻¹) + 2 = 0 := by
      rw [hbracket, hN_s, h1ma1v]
      have hsc' : (s - c) / 2 ≠ 0 := ne_of_gt (by linarith)
      have hs1' : (s - 1) / 2 ≠ 0 := ne_of_gt (by linarith)
      field_simp
      nlinarith [hs_sq, hs1, hsc, hc1pos]
    exact hgoal
  -- a₁' ≤ zCG δ : show u₁''(a₁') > 0 ⟹ ψ(a₁')>0=ψ(z) ⟹ a₁'<z.
  have hz_pos : 0 < zCG δ := zCG_pos δ hd1pos
  have hz_lt_one : zCG δ < 1 := zCG_lt_one δ hd1pos
  have ha1v_lt_one : a1' c < 1 := by linarith [ha1v_lt_half, hc0]
  have ht_pos : 0 < (s - 1) / 2 := by
    rcases eq_or_lt_of_le hs_ge1 with h | h
    · exfalso; have : s = 1 := h.symm; rw [this] at hs_sq; nlinarith [hc0]
    · linarith
  have hpsi_a1_pos : 0 < (a1' c) ^ (-(3:ℝ)/2) - δ * (1 - a1' c) ^ (-(3:ℝ)/2) := by
    -- a₁'^{-3/2} = ((s-1)/2)^{-3} = (((s-1)/2)^3)⁻¹
    have e_a3 : (a1' c) ^ (-(3:ℝ)/2) = (((s - 1) / 2) ^ 3)⁻¹ := by
      rw [ha1v_sq, ← Real.rpow_natCast (((s-1)/2)) 2, ← Real.rpow_mul ht_nn,
        show ((2:ℕ):ℝ) * (-(3:ℝ)/2) = -((3:ℕ):ℝ) by norm_num,
        Real.rpow_neg ht_nn, Real.rpow_natCast]
    -- (1-a₁')^{-3/2} = (rt^3)⁻¹  where rt = (1-a₁')^{1/2}
    have e_1ma3 : (1 - a1' c) ^ (-(3:ℝ)/2) = (rt ^ 3)⁻¹ := by
      have hrt3 : rt ^ 3 = (1 - a1' c) ^ ((3:ℝ)/2) := by
        rw [hrt_def, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (le_of_lt h1ma1v_pos)]
        norm_num
      rw [hrt3, show (-(3:ℝ)/2) = -((3:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma1v_pos)]
    rw [e_a3, e_1ma3]
    -- δ·(rt³)⁻¹ = N/(1-a₁')² . Use δ·rt = N, rt² = 1-a₁'.
    have hδ_rt3 : δ * (rt ^ 3)⁻¹ = N / (1 - a1' c) ^ 2 := by
      rw [eq_div_iff (by positivity)]
      have hrtne : rt ≠ 0 := ne_of_gt hrt_pos
      have hkey : (rt ^ 3)⁻¹ * (1 - a1' c) ^ 2 = rt := by
        rw [← hrt_sq]
        field_simp
      calc δ * (rt ^ 3)⁻¹ * (1 - a1' c) ^ 2
          = δ * ((rt ^ 3)⁻¹ * (1 - a1' c) ^ 2) := by ring
        _ = δ * rt := by rw [hkey]
        _ = N := hδrt
    rw [hδ_rt3]
    -- goal: 0 < (((s-1)/2)^3)⁻¹ - N/(1-a₁')²
    rw [h1ma1v, hN_s]
    have hs1 : 0 < s - 1 := by linarith
    have hsc : 0 < s - c := by linarith
    rw [inv_eq_one_div, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [div_add_div _ _ (ne_of_gt hc1pos) (by norm_num : (2:ℝ) ≠ 0),
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hs_sq, hs1, hsc, hc1pos, hs_nn, sq_nonneg (s - 3), mul_pos hs1 hsc,
      mul_nonneg hs_nn (sq_nonneg (s - 3)), mul_pos (mul_pos hs1 hsc) hc1pos]
  have ha1v_le_z : a1' c ≤ zCG δ := by
    by_contra hcon
    push_neg at hcon
    have hz_in : zCG δ ∈ Set.Ioo (0:ℝ) 1 := ⟨hz_pos, hz_lt_one⟩
    have ha_in : a1' c ∈ Set.Ioo (0:ℝ) 1 := ⟨ha1v_pos, ha1v_lt_one⟩
    have hpsi_z : (zCG δ) ^ (-(3:ℝ)/2) - δ * (1 - zCG δ) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection δ hd1pos; linarith
    have := u1psi_strictAnti δ hd1pos hz_in ha_in hcon
    simp only at this
    linarith [hpsi_a1_pos, hpsi_z]
  -- Apply the engine.
  have hkey := u1delta_nonneg_engine c δ (a1' c) hc0 hd1pos ha1v_pos ha1v_le_z hu_zero hderiv_zero
  intro y hy0 hy1
  show 0 ≤ u1delta c δ y
  exact hkey y hy0 hy1

/- Helper lemmas for `CGRelaxedCoreNonneg` (the main statement is documented at
its declaration below). -/

/-- The calibrating identity `h = λ₁/(1+c)·(u₁ + 1 − 2x − c)`. -/
theorem h_eq_u1_affine (c : ℝ) (hc0 : 0 ≤ c) (y : ℝ) :
    h_q 2 (lambda1 c) (delta1 c) y
      = lambda1 c / (1 + c) * (u1 c y + 1 - 2 * y - c) := by
  have : (1 : ℝ) + c ≠ 0 := by positivity
  unfold h_q u1; field_simp; ring

/-- First derivative of `h_q 2 λ δ` at an interior point. -/
theorem h_firstDeriv (lam delta a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun y => h_q 2 lam delta y)
      (lam * (-delta * (1/2) * (1 - a) ^ (-(1:ℝ)/2) - (1/2) * a ^ (-(1:ℝ)/2))) a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_ne : (1 - a) ≠ 0 := ne_of_gt h1ma_pos
  have hexp : (1:ℝ)/2 - 1 = -(1:ℝ)/2 := by norm_num
  have hd_a : HasDerivAt (fun y : ℝ => y ^ ((1:ℝ)/2)) ((1/2) * a ^ (-(1:ℝ)/2)) a := by
    have h := (hasDerivAt_id a).rpow_const (p := (1:ℝ)/2) (Or.inl ha_ne)
    rw [hexp] at h; simpa using h
  have hd_inner : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) a := by
    simpa using (hasDerivAt_id a).const_sub 1
  have hd_1ma : HasDerivAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/2)) (-1 * ((1/2) * (1 - a) ^ (-(1:ℝ)/2))) a := by
    have h := hd_inner.rpow_const (p := (1:ℝ)/2) (Or.inl h1ma_ne)
    rw [hexp] at h; convert h using 1; ring
  have hd_d1ma : HasDerivAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2))
      (delta * (-1 * ((1/2) * (1 - a) ^ (-(1:ℝ)/2)))) a := hd_1ma.const_mul delta
  have hd_diff : HasDerivAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))
      (delta * (-1 * ((1/2) * (1 - a) ^ (-(1:ℝ)/2))) - (1/2) * a ^ (-(1:ℝ)/2)) a := hd_d1ma.sub hd_a
  have hd_mul : HasDerivAt (fun y => h_q 2 lam delta y)
      (lam * (delta * (-1 * ((1/2) * (1 - a) ^ (-(1:ℝ)/2))) - (1/2) * a ^ (-(1:ℝ)/2))) a := by
    have : (fun y => h_q 2 lam delta y) = (fun y : ℝ => lam * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) := by
      funext y; rfl
    rw [this]; exact hd_diff.const_mul lam
  convert hd_mul using 1; ring

/-- The derivative of `h`'s first-derivative function: the second derivative of `h`,
`h''(y) = lam·(1/4)·(y^{-3/2} − δ·(1−y)^{-3/2})`.  Returns the matching `HasDerivAt`. -/
theorem h_secondDeriv_aux (lam delta y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    True ∧ HasDerivAt
      (fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2)))
      (lam * (1/4) * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2))) y := by
  refine ⟨trivial, ?_⟩
  have hy_ne : y ≠ 0 := ne_of_gt hy0
  have h1my_pos : 0 < 1 - y := by linarith
  have h1my_ne : (1 - y) ≠ 0 := ne_of_gt h1my_pos
  set p1 : ℝ := -(1:ℝ)/2 with hp1_def
  set p2 : ℝ := -(3:ℝ)/2 with hp2_def
  have hexp : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; norm_num
  have hd_y : HasDerivAt (fun z : ℝ => z ^ p1) (p1 * y ^ p2) y := by
    have h := (hasDerivAt_id y).rpow_const (p := p1) (Or.inl hy_ne)
    rw [hexp] at h; simpa using h
  have hd_inner : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have hd_1my : HasDerivAt (fun z : ℝ => (1 - z) ^ p1) (-1 * p1 * (1 - y) ^ p2) y := by
    have h := hd_inner.rpow_const (p := p1) (Or.inl h1my_ne)
    rw [hexp] at h; exact h
  have hd_d1my : HasDerivAt (fun z : ℝ => -delta * (1/2) * (1 - z) ^ p1)
      (-delta * (1/2) * (-1 * p1 * (1 - y) ^ p2)) y := hd_1my.const_mul (-delta * (1/2))
  have hd_y2 : HasDerivAt (fun z : ℝ => (1/2) * z ^ p1) ((1/2) * (p1 * y ^ p2)) y := hd_y.const_mul (1/2)
  have hd_sub : HasDerivAt (fun z : ℝ => -delta * (1/2) * (1 - z) ^ p1 - (1/2) * z ^ p1)
      (-delta * (1/2) * (-1 * p1 * (1 - y) ^ p2) - (1/2) * (p1 * y ^ p2)) y := hd_d1my.sub hd_y2
  have hd_mul := hd_sub.const_mul lam
  convert hd_mul using 1
  rw [hp1_def, hp2_def]; ring

/-- `h_q 2 λ δ` is convex on `[0, zCG δ]` (`δ > 0`, `0 ≤ lam`). -/
theorem h_convexOn_left_gen (lam delta : ℝ) (hlam : 0 ≤ lam) (hdelta : 0 < delta) :
    ConvexOn ℝ (Set.Icc (0:ℝ) (zCG delta)) (fun y => h_q 2 lam delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have hcont : ContinuousOn (fun y => h_q 2 lam delta y) (Set.Icc (0:ℝ) (zCG delta)) := by
    intro x hx
    have hx_le : x ≤ zCG delta := hx.2
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le hz_lt_one
    have h1mx_pos : 0 < 1 - x := by linarith
    have h_inner : ContinuousAt (fun y : ℝ => 1 - y) x := (continuous_const.sub continuous_id).continuousAt
    have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) (1 - x) :=
      Real.continuousAt_rpow_const (1 - x) ((1:ℝ)/2) (Or.inl (ne_of_gt h1mx_pos))
    have h1 : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/2)) x := h_outer.comp h_inner
    have h2 : ContinuousAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2)) x := h1.const_mul delta
    have h3 : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) x :=
      Real.continuousAt_rpow_const x ((1:ℝ)/2) (Or.inr (by norm_num))
    have h4 : ContinuousAt (fun y => h_q 2 lam delta y) x := by
      have : (fun y => h_q 2 lam delta y) = (fun y : ℝ => lam * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) := by
        funext y; rfl
      rw [this]; exact (h2.sub h3).const_mul lam
    exact h4.continuousWithinAt
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 (zCG delta)) hcont
  · rw [interior_Icc]; intro y hy
    exact (h_firstDeriv lam delta y hy.1 (lt_trans hy.2 hz_lt_one)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => h_q 2 lam delta y) =ᶠ[nhds y]
        fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2)) := by
      filter_upwards [hnhds] with z hz
      exact (h_firstDeriv lam delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2 : DifferentiableAt ℝ
        (fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2))) y := by
      have hy_ne : y ≠ 0 := ne_of_gt hy0
      have h1my_ne : (1 - y) ≠ 0 := by linarith
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sub
      · apply DifferentiableAt.const_mul
        exact (((differentiable_const (1:ℝ)).differentiableAt.sub differentiableAt_id).rpow_const
          (Or.inl h1my_ne))
      · exact (DifferentiableAt.rpow_const differentiableAt_id (Or.inl hy_ne)).const_mul _
    exact (hd2.congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := lt_trans hy.2 hz_lt_one
    have hnhds : Set.Ioo (0:ℝ) (zCG delta) ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => h_q 2 lam delta y) =ᶠ[nhds y]
        fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2)) := by
      filter_upwards [hnhds] with z hz
      exact (h_firstDeriv lam delta z hz.1 (lt_trans hz.2 hz_lt_one)).deriv
    have hd2 := h_secondDeriv_aux lam delta y hy0 hy1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hloc.deriv_eq, hd2.2.deriv]
    have hpsi_z : (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection delta hdelta; linarith
    have hpsi_anti := u1psi_strictAnti delta hdelta
    have hpsi_nonneg : 0 ≤ y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) := by
      rcases eq_or_lt_of_le (le_of_lt hy.2) with heq | hlt
      · have : y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) =
            (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) := by rw [heq]
        rw [this, hpsi_z]
      · have := hpsi_anti ⟨hy0, hy1⟩ ⟨hz_pos, hz_lt_one⟩ hlt
        simp only at this; linarith [hpsi_z]
    have : 0 ≤ lam * (1/4) * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) := by
      apply mul_nonneg (by positivity) hpsi_nonneg
    simpa using this

/-- `h_q 2 λ δ` is concave on `[zCG δ, 1]` (`δ > 0`, `0 ≤ lam`). -/
theorem h_concaveOn_right_gen (lam delta : ℝ) (hlam : 0 ≤ lam) (hdelta : 0 < delta) :
    ConcaveOn ℝ (Set.Icc (zCG delta) 1) (fun y => h_q 2 lam delta y) := by
  have hz_pos : 0 < zCG delta := zCG_pos delta hdelta
  have hz_lt_one : zCG delta < 1 := zCG_lt_one delta hdelta
  have hcont : ContinuousOn (fun y => h_q 2 lam delta y) (Set.Icc (zCG delta) 1) := by
    intro x hx
    have hx_ge : zCG delta ≤ x := hx.1
    have hx_le : x ≤ 1 := hx.2
    have hx_pos : 0 < x := lt_of_lt_of_le hz_pos hx_ge
    have h_inner : ContinuousAt (fun y : ℝ => 1 - y) x := (continuous_const.sub continuous_id).continuousAt
    have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) (1 - x) := by
      rcases eq_or_lt_of_le hx_le with hxone | hxlt
      · rw [hxone]; simpa using Real.continuousAt_rpow_const (0:ℝ) ((1:ℝ)/2) (Or.inr (by norm_num))
      · exact Real.continuousAt_rpow_const (1 - x) ((1:ℝ)/2) (Or.inl (by linarith))
    have h1 : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/2)) x := h_outer.comp h_inner
    have h2 : ContinuousAt (fun y : ℝ => delta * (1 - y) ^ ((1:ℝ)/2)) x := h1.const_mul delta
    have h3 : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) x :=
      Real.continuousAt_rpow_const x ((1:ℝ)/2) (Or.inr (by norm_num))
    have h4 : ContinuousAt (fun y => h_q 2 lam delta y) x := by
      have : (fun y => h_q 2 lam delta y) = (fun y : ℝ => lam * (delta * (1 - y) ^ ((1:ℝ)/2) - y ^ ((1:ℝ)/2))) := by
        funext y; rfl
      rw [this]; exact (h2.sub h3).const_mul lam
    exact h4.continuousWithinAt
  apply concaveOn_of_deriv2_nonpos (convex_Icc (zCG delta) 1) hcont
  · rw [interior_Icc]; intro y hy
    exact (h_firstDeriv lam delta y (lt_trans hz_pos hy.1) hy.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => h_q 2 lam delta y) =ᶠ[nhds y]
        fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2)) := by
      filter_upwards [hnhds] with z hz
      exact (h_firstDeriv lam delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2 := h_secondDeriv_aux lam delta y hy0 hy.2
    exact ((hd2.2.differentiableAt).congr_of_eventuallyEq hloc).differentiableWithinAt
  · rw [interior_Icc]; intro y hy
    have hy0 : 0 < y := lt_trans hz_pos hy.1
    have hy1 : y < 1 := hy.2
    have hnhds : Set.Ioo (zCG delta) 1 ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have hloc : deriv (fun y => h_q 2 lam delta y) =ᶠ[nhds y]
        fun z => lam * (-delta * (1/2) * (1 - z) ^ (-(1:ℝ)/2) - (1/2) * z ^ (-(1:ℝ)/2)) := by
      filter_upwards [hnhds] with z hz
      exact (h_firstDeriv lam delta z (lt_trans hz_pos hz.1) hz.2).deriv
    have hd2 := h_secondDeriv_aux lam delta y hy0 hy1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hloc.deriv_eq, hd2.2.deriv]
    have hpsi_z : (zCG delta) ^ (-(3:ℝ)/2) - delta * (1 - zCG delta) ^ (-(3:ℝ)/2) = 0 := by
      have h := zCG_inflection delta hdelta; linarith
    have hpsi_anti := u1psi_strictAnti delta hdelta
    have hpsi_nonpos : y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2) ≤ 0 := by
      have := hpsi_anti ⟨hz_pos, hz_lt_one⟩ ⟨hy0, hy1⟩ hy.1
      simp only at this; linarith [hpsi_z]
    have : lam * (1/4) * (y ^ (-(3:ℝ)/2) - delta * (1 - y) ^ (-(3:ℝ)/2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hpsi_nonpos
    simpa using this

/-- **Tangent-below bound for a convex-then-concave function.**  If `f` is convex on
`[0,z]` and concave on `[z,1]`, `a ∈ (0,z]`, and `f` has derivative `D` at `a`, then for
all `y ∈ [0,1]`, `f y ≥ f a + D·(y − a)` — the global tangent at `a` lies below `f`.
(Convexity gives it on `[0,z]`; on `[z,1]` the tangent line is `≤` the chord from
`(z,f z)` to `(1,f 1)` since it is `≤ f` at both endpoints, and the chord is `≤ f` by
concavity.) -/
theorem tangent_below_convex_concave (f : ℝ → ℝ) (z D a : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1) (ha0 : 0 < a) (ha_le_z : a ≤ z)
    (hconv : ConvexOn ℝ (Set.Icc (0:ℝ) z) f) (hconc : ConcaveOn ℝ (Set.Icc z 1) f)
    (hderiv : HasDerivAt f D a)
    (htan_one : f a + D * (1 - a) ≤ f 1) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → f a + D * (y - a) ≤ f y := by
  have ha_mem : a ∈ Set.Icc (0:ℝ) z := ⟨le_of_lt ha0, ha_le_z⟩
  -- tangent below convex on [0,z]
  have hleft : ∀ y ∈ Set.Icc (0:ℝ) z, f a + D * (y - a) ≤ f y := by
    intro y hy
    rcases lt_trichotomy y a with hlt | heq | hgt
    · have hsl := hconv.slope_le_of_hasDerivAt hy ha_mem hlt hderiv
      rw [slope_def_field] at hsl
      have hpos : 0 < a - y := by linarith
      have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
      -- hmul : f a - f y ≤ D * (a - y)
      nlinarith [hmul]
    · rw [heq]; simp
    · have hsl := hconv.le_slope_of_hasDerivAt ha_mem hy hgt hderiv
      rw [slope_def_field] at hsl
      have hpos : 0 < y - a := by linarith
      have : D * (y - a) ≤ f y - f a := by
        have := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
        linarith
      linarith
  -- value at z
  have hz_mem : z ∈ Set.Icc (0:ℝ) z := ⟨le_of_lt hz0, le_refl _⟩
  have htan_z : f a + D * (z - a) ≤ f z := hleft z hz_mem
  -- right side via chord
  have hright : ∀ y ∈ Set.Icc z 1, f a + D * (y - a) ≤ f y := by
    intro y hy
    have hz_in : z ∈ Set.Icc z 1 := ⟨le_refl _, le_of_lt hz1⟩
    have hone_in : (1:ℝ) ∈ Set.Icc z 1 := ⟨le_of_lt hz1, le_refl _⟩
    -- tangent value at 1 ≤ f 1: need it. Use convex extension? Instead bound directly.
    -- Parametrize y = (1-t)·z + t·1 with t = (y - z)/(1 - z).
    rcases eq_or_lt_of_le hy.1 with hyz | hyz
    · rw [← hyz]; exact htan_z
    · set t : ℝ := (y - z) / (1 - z) with ht_def
      have h1mz_pos : 0 < 1 - z := by linarith
      have ht0 : 0 < t := by rw [ht_def]; exact div_pos (by linarith) h1mz_pos
      have ht1 : t ≤ 1 := by rw [ht_def, div_le_one h1mz_pos]; linarith [hy.2]
      have hcombo : y = (1 - t) * z + t * 1 := by
        rw [ht_def]; field_simp; ring
      -- concavity: f y ≥ (1-t) f z + t f 1
      have hy_seg : y ∈ segment ℝ z 1 := by
        rw [segment_eq_Icc (le_of_lt hz1)]; exact hy
      -- Use the explicit combination form.
      have hconc_app := hconc.2 hz_in hone_in (by linarith : (0:ℝ) ≤ 1 - t)
        (le_of_lt ht0) (by ring)
      simp only [smul_eq_mul] at hconc_app
      have hzpt : (1 - t) * z + t * 1 = y := hcombo.symm
      rw [hzpt] at hconc_app
      -- tangent at 1: f a + D(1-a) ≤ f 1 ?  Get from convex tangent extended is NOT available.
      -- Instead bound the tangent line by the chord of the TANGENT itself (it's linear):
      -- f a + D(y-a) = (1-t)(f a + D(z-a)) + t(f a + D(1-a)).
      have htan_lin : f a + D * (y - a) =
          (1 - t) * (f a + D * (z - a)) + t * (f a + D * (1 - a)) := by
        rw [hcombo]; ring
      -- f y ≥ (1-t) f z + t f 1 ≥ (1-t)(tangent z) + t(tangent 1) = tangent y.
      have h1mt_nn : (0:ℝ) ≤ 1 - t := by linarith
      have hbound1 : (1 - t) * (f a + D * (z - a)) ≤ (1 - t) * f z :=
        mul_le_mul_of_nonneg_left htan_z h1mt_nn
      have hbound2 : t * (f a + D * (1 - a)) ≤ t * f 1 :=
        mul_le_mul_of_nonneg_left htan_one (le_of_lt ht0)
      rw [htan_lin]
      calc (1 - t) * (f a + D * (z - a)) + t * (f a + D * (1 - a))
          ≤ (1 - t) * f z + t * f 1 := by linarith [hbound1, hbound2]
        _ ≤ f y := by linarith [hconc_app]
  intro y hy0 hy1
  rcases le_or_gt y z with hyz | hyz
  · exact hleft y ⟨hy0, hyz⟩
  · exact hright y ⟨le_of_lt hyz, hy1⟩

/-- **High-branch pointwise bound** (`1/2 ≤ c < 1`).  There is a slope `D` such that the
affine line `ℓ(y) = D·(y − (1−c)/2)` through `((1−c)/2, 0)` lies below `h` on `[0,1]`.
(`h((1−c)/2) = 0`; the tangent at the constraint boundary `(1−c)/2 ≤ z` under-estimates
`h` everywhere, by convexity on `[0,z]` and the concavity chord on `[z,1]`.) -/
theorem high_branch_pointwise (c : ℝ) (hc_lo : 1 / 2 ≤ c) (hc1 : c < 1) :
    ∃ D : ℝ, ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
      D * (y - (1 - c) / 2) ≤ h_q 2 (lambda1 c) (delta1 c) y := by
  have hc0 : 0 ≤ c := by linarith
  have hd1pos : 0 < delta1 c := delta1_pos c hc0 hc1
  obtain ⟨hl0, hl1, _⟩ := CGLambda1InUnitInterval c hc0 hc1
  -- high-branch closed forms
  obtain ⟨hd1sq, _, hlam_val, _⟩ := CGDeltaLambdaHighBranch c hc_lo hc1
  -- δ₁ = √((1-c)/(1+c)), λ₁ = √((c+1)/2).
  have h1mc : (0:ℝ) < 1 - c := by linarith
  have h1pc : (0:ℝ) < 1 + c := by linarith
  set a1v : ℝ := (1 - c) / 2 with ha1v_def
  have ha1v_pos : 0 < a1v := by rw [ha1v_def]; linarith
  have ha1v_lt_one : a1v < 1 := by rw [ha1v_def]; linarith
  have h1ma1v : 1 - a1v = (1 + c) / 2 := by rw [ha1v_def]; ring
  have h1ma1v_pos : 0 < 1 - a1v := by rw [h1ma1v]; linarith
  -- δ₁ explicit value: δ₁² = (1-c)/(1+c), δ₁ = √((1-c)/(1+c)).
  have hδ1_sq : delta1 c ^ 2 = (1 - c) / (1 + c) := by
    -- delta1 c = (lambda1 c^{-2} - 1)^{1/2}; lambda1 c = √((c+1)/2).
    have hbase : lambda1 c ^ (-((2:ℝ)/(2-1))) - 1 = (1 - c) / (1 + c) := by
      rw [hlam_val, show (-((2:ℝ)/(2-1))) = -(2:ℝ) by norm_num,
        show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (Real.sqrt_nonneg _),
        Real.rpow_natCast, Real.sq_sqrt (by positivity)]
      rw [inv_div]; field_simp; ring
    have hbn : (0:ℝ) ≤ lambda1 c ^ (-((2:ℝ)/(2-1))) - 1 := by rw [hbase]; positivity
    have hstep : delta1 c ^ 2 = lambda1 c ^ (-((2:ℝ)/(2-1))) - 1 := by
      unfold delta1 delta_of_lambda
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hbn]; norm_num
    rw [hstep, hbase]
  have hδ1_val : delta1 c = Real.sqrt ((1 - c) / (1 + c)) := by
    have : delta1 c = Real.sqrt (delta1 c ^ 2) := by rw [Real.sqrt_sq (le_of_lt hd1pos)]
    rw [this, hδ1_sq]
  -- √a1v = √((1-c)/2), √(1-a1v) = √((1+c)/2).
  have hsqrt_a1v : a1v ^ ((1:ℝ)/2) = Real.sqrt a1v := (Real.sqrt_eq_rpow a1v).symm
  have hsqrt_1ma1v : (1 - a1v) ^ ((1:ℝ)/2) = Real.sqrt (1 - a1v) := (Real.sqrt_eq_rpow _).symm
  -- KEY: δ₁·√(1-a1v) = √a1v, the calibration making h(a1v)=0.
  have hcalib : delta1 c * (1 - a1v) ^ ((1:ℝ)/2) = a1v ^ ((1:ℝ)/2) := by
    rw [hδ1_val, hsqrt_1ma1v, hsqrt_a1v, h1ma1v, ha1v_def,
      ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  -- h(a1v) = 0.
  have hh_a1v : h_q 2 (lambda1 c) (delta1 c) a1v = 0 := by
    unfold h_q
    rw [show (1:ℝ)/(2:ℝ) = (1:ℝ)/2 from rfl, hcalib]; ring
  -- a1v ≤ zCG δ₁.  (Use ψ(a1v) ≥ 0 ⟹ a1v ≤ z, since ψ antitone and ψ(z)=0.)
  have ha1v_le_z : a1v ≤ zCG (delta1 c) := by
    -- z = D₀/(D₀+1) with D₀ = δ₁^{-2/3}.  a1v ≤ z ⟺ a1v/(1-a1v) ≤ D₀, and
    -- a1v/(1-a1v) = (1-c)/(1+c) = δ₁², while D₀ = δ₁^{-2/3} ≥ δ₁² since δ₁ ≤ 1.
    set D0 : ℝ := delta1 c ^ (-(2:ℝ)/3) with hD0_def
    have hD0_pos : 0 < D0 := Real.rpow_pos_of_pos hd1pos _
    have hz_eq : zCG (delta1 c) = D0 / (D0 + 1) := rfl
    have hδ1_le_one : delta1 c ≤ 1 := by
      rw [hδ1_val, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      have : (1 - c) / (1 + c) ≤ 1 := by rw [div_le_one h1pc]; linarith
      linarith
    -- δ₁² ≤ D0 = δ₁^{-2/3}: δ₁^{2} ≤ δ₁^{-2/3} ⟺ δ₁^{8/3} ≤ 1 (δ₁ ≤ 1, exp > 0).
    have hδ1sq_le_D0 : delta1 c ^ 2 ≤ D0 := by
      rw [hD0_def, ← Real.rpow_natCast (delta1 c) 2, show ((2:ℕ):ℝ) = (2:ℝ) by norm_num]
      rcases eq_or_lt_of_le hδ1_le_one with heq | hlt
      · rw [heq]; norm_num
      · apply Real.rpow_le_rpow_of_exponent_ge hd1pos (le_of_lt hlt); norm_num
    -- δ₁² = (1-c)/(1+c), so (1-c)/(1+c) ≤ D0.
    have hratio_le : (1 - c) / (1 + c) ≤ D0 := by rw [← hδ1_sq]; exact hδ1sq_le_D0
    rw [hz_eq, ha1v_def, le_div_iff₀ (by linarith)]
    -- goal: (1-c)/2 * (D0+1) ≤ D0.  From (1-c) ≤ D0(1+c).
    have hkey : (1 - c) ≤ D0 * (1 + c) := by
      rw [div_le_iff₀ h1pc] at hratio_le; linarith
    nlinarith [hkey, hD0_pos, h1pc, h1mc]
  -- the derivative D = h'(a1v) and the tangent bound.
  refine ⟨lambda1 c * (-delta1 c * (1/2) * (1 - a1v) ^ (-(1:ℝ)/2) - (1/2) * a1v ^ (-(1:ℝ)/2)), ?_⟩
  set D : ℝ := lambda1 c * (-delta1 c * (1/2) * (1 - a1v) ^ (-(1:ℝ)/2) - (1/2) * a1v ^ (-(1:ℝ)/2)) with hD_def
  have hderiv : HasDerivAt (fun y => h_q 2 (lambda1 c) (delta1 c) y) D a1v :=
    h_firstDeriv (lambda1 c) (delta1 c) a1v ha1v_pos ha1v_lt_one
  have hconv := h_convexOn_left_gen (lambda1 c) (delta1 c) (le_of_lt hl0) hd1pos
  have hconc := h_concaveOn_right_gen (lambda1 c) (delta1 c) (le_of_lt hl0) hd1pos
  have hz_pos : 0 < zCG (delta1 c) := zCG_pos _ hd1pos
  have hz_lt_one : zCG (delta1 c) < 1 := zCG_lt_one _ hd1pos
  -- htan_one : h(a1v) + D·(1-a1v) ≤ h(1).
  have hh_one : h_q 2 (lambda1 c) (delta1 c) 1 = -lambda1 c := by
    unfold h_q; rw [show (1:ℝ) - 1 = 0 by ring, Real.zero_rpow (by norm_num), Real.one_rpow]; ring
  have htan_one : h_q 2 (lambda1 c) (delta1 c) a1v + D * (1 - a1v) ≤ h_q 2 (lambda1 c) (delta1 c) 1 := by
    rw [hh_a1v, hh_one, zero_add]
    -- D·(1-a1v) = -λ₁/(2√a1v) ≤ -λ₁ (since √a1v ≤ 1/2 ⟺ a1v ≤ 1/4 ⟺ c ≥ 1/2).
    set sa : ℝ := Real.sqrt a1v with hsa_def
    have hsa_pos : 0 < sa := Real.sqrt_pos.mpr ha1v_pos
    have hsa_sq : sa ^ 2 = a1v := Real.sq_sqrt (le_of_lt ha1v_pos)
    have e_a_neg : a1v ^ (-(1:ℝ)/2) = sa⁻¹ := by
      rw [hsa_def, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt ha1v_pos),
        ← Real.sqrt_eq_rpow]
    have e_1ma_neg : (1 - a1v) ^ (-(1:ℝ)/2) = (Real.sqrt (1 - a1v))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt h1ma1v_pos),
        ← Real.sqrt_eq_rpow]
    -- δ₁·(1-a1v)^{-1/2}·(1-a1v) = δ₁·(1-a1v)^{1/2} = a1v^{1/2} = sa (hcalib).
    set sb : ℝ := Real.sqrt (1 - a1v) with hsb_def
    have hsb_pos : 0 < sb := Real.sqrt_pos.mpr h1ma1v_pos
    have hsb_sq : sb ^ 2 = 1 - a1v := Real.sq_sqrt (le_of_lt h1ma1v_pos)
    have hsb_ne : sb ≠ 0 := ne_of_gt hsb_pos
    have hδ_term : delta1 c * sb⁻¹ * (1 - a1v) = sa := by
      have h1 : sb⁻¹ * (1 - a1v) = sb := by
        rw [← hsb_sq, sq, ← mul_assoc, inv_mul_cancel₀ hsb_ne, one_mul]
      have hc2 := hcalib
      rw [hsqrt_1ma1v, hsqrt_a1v] at hc2
      rw [mul_assoc, h1]; exact hc2
    have hsainv_1ma : sa⁻¹ * (1 - a1v) = sa⁻¹ - sa := by
      rw [← hsa_sq]; field_simp
    -- D·(1-a1v) = λ₁·(-δ₁·(1/2)·sb⁻¹ - (1/2)·sa⁻¹)·(1-a1v) = -λ₁/(2 sa).
    have hDval : D * (1 - a1v) = -lambda1 c / (2 * sa) := by
      rw [hD_def, e_a_neg, e_1ma_neg]
      have hbracket : (-delta1 c * (1/2) * sb⁻¹ - 1/2 * sa⁻¹) * (1 - a1v)
          = -(1/2) * sa⁻¹ := by
        have hexpand : (-delta1 c * (1/2) * sb⁻¹ - 1/2 * sa⁻¹) * (1 - a1v)
            = -(1/2) * (delta1 c * sb⁻¹ * (1 - a1v)) - (1/2) * (sa⁻¹ * (1 - a1v)) := by ring
        rw [hexpand, hδ_term, hsainv_1ma]; ring
      have hstep : lambda1 c * (-delta1 c * (1/2) * sb⁻¹ - 1/2 * sa⁻¹) * (1 - a1v)
          = lambda1 c * ((-delta1 c * (1/2) * sb⁻¹ - 1/2 * sa⁻¹) * (1 - a1v)) := by ring
      rw [hstep, hbracket]
      have hsane : sa ≠ 0 := ne_of_gt hsa_pos
      field_simp
    rw [hDval]
    -- -λ₁/(2 sa) ≤ -λ₁ ⟺ 2 sa ≤ 1 (λ₁ > 0).
    have hsa_le : sa ≤ 1 / 2 := by
      rw [hsa_def, show (1:ℝ)/2 = Real.sqrt (1/4) by rw [show (1:ℝ)/4 = (1/2)^2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      rw [ha1v_def]; linarith [hc_lo]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsa_le, hsa_pos, hl0]
  have hbound := tangent_below_convex_concave (fun y => h_q 2 (lambda1 c) (delta1 c) y)
    (zCG (delta1 c)) D a1v hz_pos hz_lt_one ha1v_pos ha1v_le_z hconv hconc hderiv htan_one
  intro y hy0 hy1
  have hb := hbound y hy0 hy1
  simp only [] at hb
  rw [hh_a1v, zero_add] at hb
  exact hb

theorem CGRelaxedCoreNonneg
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n : ℕ}
    (x : Fin n → ℝ)
    (hx_nn : ∀ i, 0 ≤ x i) (hx_le_one : ∀ i, x i ≤ 1)
    (hx_sum : (∑ i, x i) = (1 - c) / 2 * (n : ℝ)) :
    0 ≤ (∑ i, h_q 2 (lambda1 c) (delta1 c) (x i)) := by
  -- ## Two-branch supporting-line certificate.
  --
  -- The per-point objective is `h(x) = h_q 2 λ₁ δ₁ x`.  In BOTH branches we exhibit
  -- an affine support line `ℓ` with `ℓ(xᵢ) ≤ h(xᵢ)` pointwise on `[0,1]` and
  -- `∑ᵢ ℓ(xᵢ) = 0` under the constraint `∑ xᵢ = (1−c)/2·n`; summing gives the result.
  --
  -- * `c < 1/2` (LOW branch): the global supporting line is the tangent at the
  --   interior critical point `a₁' = a1' c`, equivalently `ℓ(x) = λ₁/(1+c)·(1−2x−c)`,
  --   and `h ≥ ℓ ⟺ u₁ ≥ 0` on `[0,1]` (`low_branch_hu1_nonneg`).
  -- * `1/2 ≤ c` (HIGH branch): `u₁ ≥ 0` FAILS pointwise; instead the support line is
  --   the tangent to `h` at the constraint boundary `(1−c)/2 ≤ z`, `ℓ(x)=D·(x−(1−c)/2)`
  --   (`high_branch_pointwise`), with `∑ℓ(xᵢ)=D·0=0`.
  have hc_pos : (0 : ℝ) < 1 + c := by linarith
  have hlam_pos : 0 < lambda1 c := (CGLambda1InUnitInterval c hc0 hc1).1
  have hcoef_nn : 0 ≤ lambda1 c / (1 + c) := by positivity
  by_cases hcase : c < 1 / 2
  · -- LOW branch: `u₁ ≥ 0` global support.
    have hu1_nonneg : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 ≤ u1 c y :=
      low_branch_hu1_nonneg c hc0 hcase
    have key : ∀ y : ℝ,
        h_q 2 (lambda1 c) (delta1 c) y = lambda1 c / (1 + c) * (u1 c y + 1 - 2 * y - c) := by
      intro y; unfold h_q u1; field_simp; ring
    have h_pointwise : ∀ i,
        lambda1 c / (1 + c) * (1 - 2 * x i - c) ≤ h_q 2 (lambda1 c) (delta1 c) (x i) := by
      intro i
      rw [key (x i)]
      have hu := hu1_nonneg (x i) (hx_nn i) (hx_le_one i)
      have hmul := mul_le_mul_of_nonneg_left
        (show (1 - 2 * x i - c) ≤ (u1 c (x i) + 1 - 2 * (x i) - c) by linarith) hcoef_nn
      linarith [hmul]
    have hsum_lb :
        (∑ i, lambda1 c / (1 + c) * (1 - 2 * x i - c))
          ≤ (∑ i, h_q 2 (lambda1 c) (delta1 c) (x i)) :=
      Finset.sum_le_sum (fun i _ => h_pointwise i)
    have hsum_eq : (∑ i, lambda1 c / (1 + c) * (1 - 2 * x i - c)) = 0 := by
      rw [← Finset.mul_sum]
      have hinner : (∑ i, (1 - 2 * x i - c)) = (n : ℝ) - 2 * (∑ i, x i) - c * n := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
        simp [mul_comm]
      rw [hinner, hx_sum]; ring
    rw [hsum_eq] at hsum_lb
    exact hsum_lb
  · -- HIGH branch: boundary-tangent support `ℓ(x) = D·(x − (1−c)/2)`.
    push_neg at hcase
    obtain ⟨D, hD_bound⟩ := high_branch_pointwise c hcase hc1
    have h_pointwise : ∀ i,
        D * (x i - (1 - c) / 2) ≤ h_q 2 (lambda1 c) (delta1 c) (x i) :=
      fun i => hD_bound (x i) (hx_nn i) (hx_le_one i)
    have hsum_lb :
        (∑ i, D * (x i - (1 - c) / 2)) ≤ (∑ i, h_q 2 (lambda1 c) (delta1 c) (x i)) :=
      Finset.sum_le_sum (fun i _ => h_pointwise i)
    have hsum_eq : (∑ i, D * (x i - (1 - c) / 2)) = 0 := by
      rw [← Finset.mul_sum]
      have hinner : (∑ i, (x i - (1 - c) / 2)) = (∑ i, x i) - (1 - c) / 2 * n := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      rw [hinner, hx_sum]; ring
    rw [hsum_eq] at hsum_lb
    exact hsum_lb

end Workspace.ProofLemmas.CGRelaxedCoreNonneg
