import Mathlib
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.UStarMinAttained
import Workspace.ProofLemmas.ZeqInHalfRange

open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.LambdaStarDef
open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.ZeqInHalfRange

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.RelaxedCoreDual

/-- Bridge identity `delta_of_lambda q (lambda_star q) = delta_star q` (pure rpow algebra
from the definitions; self-contained so this file does not need to import the
duplication/limit assembly). -/
theorem deltaOfLambda_lambdaStar_eq (q : ℝ) (hq : 1 < q) :
    delta_of_lambda q (lambda_star q) = delta_star q := by
  have hq1 : q ≠ 1 := ne_of_gt hq
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_pos : 0 < q - 1 := by linarith
  have hqm1_ne : q - 1 ≠ 0 := ne_of_gt hqm1_pos
  have hDS_ge_one : 1 ≤ delta_star q := (DeltaStarDef q hq).1
  have hDS_pos : 0 < delta_star q := lt_of_lt_of_le one_pos hDS_ge_one
  have hDS_nn : 0 ≤ delta_star q := le_of_lt hDS_pos
  set r : ℝ := q / (q - 1) with hr_def
  have hr_pos : 0 < r := div_pos hq_pos hqm1_pos
  set e : ℝ := (q - 1) / q with he_def
  have he_pos : 0 < e := div_pos hqm1_pos hq_pos
  have hDSr_pos : 0 < (delta_star q) ^ r := Real.rpow_pos_of_pos hDS_pos r
  have hDSr_nn : 0 ≤ (delta_star q) ^ r := le_of_lt hDSr_pos
  set B : ℝ := 1 + (delta_star q) ^ r with hB_def
  have hB_pos : 0 < B := by rw [hB_def]; linarith
  have hB_nn : 0 ≤ B := le_of_lt hB_pos
  have hlam_unfold : lambda_star q = B ^ (-e) := by
    unfold lambda_star
    rw [if_neg hq1, if_pos hq]
  have her : e * r = 1 := by rw [he_def, hr_def]; field_simp
  have h_pow_pow : (B ^ (-e)) ^ (-r) = B := by
    rw [← Real.rpow_mul hB_nn]
    have : (-e) * (-r) = 1 := by rw [neg_mul_neg, her]
    rw [this, Real.rpow_one]
  unfold delta_of_lambda
  rw [hlam_unfold]
  rw [← hr_def, ← he_def, h_pow_pow]
  have hB_sub : B - 1 = (delta_star q) ^ r := by rw [hB_def]; ring
  rw [hB_sub, ← Real.rpow_mul hDS_nn, mul_comm r e, her, Real.rpow_one]

/-- The supporting-line / dual potential `u(a) = δ*·(1-a)^{1/q} - a^{1/q} - 1 + 2a`. -/
noncomputable def u_dual (q a : ℝ) : ℝ :=
  delta_star q * (1 - a) ^ ((1 : ℝ) / q) - a ^ ((1 : ℝ) / q) - 1 + 2 * a

/-- On `[0, z_func q]`, `u(a) ≥ 0` is exactly `UStarMinAttained`. -/
theorem u_dual_nonneg_left (q : ℝ) (hq : 1 < q) (a : ℝ) (ha0 : 0 ≤ a)
    (ha_le_z : a ≤ z_func q) : 0 ≤ u_dual q a := by
  have hU := UStarMinAttained q hq
  exact hU.2.2 a ha0 ha_le_z

/-- `u(1) = 0`. -/
theorem u_dual_at_one (q : ℝ) (hq : 1 < q) : u_dual q 1 = 0 := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : (1 : ℝ) / q ≠ 0 := by positivity
  show delta_star q * (1 - 1) ^ ((1 : ℝ) / q) - (1 : ℝ) ^ ((1 : ℝ) / q) - 1 + 2 * 1 = 0
  rw [show (1 : ℝ) - 1 = 0 by ring, Real.zero_rpow hq_ne, Real.one_rpow]
  ring

/-- KEY LEMMA: `u(a) ≥ 0` for all `a ∈ [0,1]` at `q > 1`. -/
theorem u_dual_nonneg (q : ℝ) (hq : 1 < q) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ u_dual q a := by
  -- Basic facts
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hDS_ge_one : 1 ≤ delta_star q := (DeltaStarDef q hq).1
  have hDS_pos : 0 < delta_star q := lt_of_lt_of_le one_pos hDS_ge_one
  have hZ := ZeqInHalfRange q hq
  obtain ⟨hZ_pos, hZ_le_half⟩ := hZ
  have hZ_lt_one : z_func q < 1 := by linarith
  -- Split at z_func q.
  rcases le_or_gt a (z_func q) with ha_le_z | ha_gt_z
  · exact u_dual_nonneg_left q hq a ha0 ha_le_z
  -- Now z_func q < a ≤ 1.  Use concavity on [z_func q, 1].
  -- Exponents.
  set p1 : ℝ := (1 - q) / q with hp1_def
  have hp1_neg : p1 < 0 := by
    rw [hp1_def]; apply div_neg_of_neg_of_pos _ hq_pos; linarith
  set p2 : ℝ := (1 - 2*q) / q with hp2_def
  have hp2_neg : p2 < 0 := by
    rw [hp2_def]; apply div_neg_of_neg_of_pos _ hq_pos; linarith
  -- ψ(x) = x^p2 - δ* (1-x)^p2, strictly antitone on (0,1); ψ(z_func q) = 0.
  set psi : ℝ → ℝ := fun x => x ^ p2 - delta_star q * (1 - x) ^ p2 with hpsi_def
  have hpsi_anti : StrictAntiOn psi (Set.Ioo (0:ℝ) 1) := by
    intro xx hxx yy hyy hxy
    have hx_pos : 0 < xx := hxx.1
    have hy_pos : 0 < yy := hyy.1
    have h1my_pos : 0 < 1 - yy := by linarith [hyy.2]
    have hxp2 : yy ^ p2 < xx ^ p2 :=
      Real.rpow_lt_rpow_of_neg hx_pos hxy hp2_neg
    have h1mxy : 1 - yy < 1 - xx := by linarith
    have h1m_p2 : (1 - xx) ^ p2 < (1 - yy) ^ p2 :=
      Real.rpow_lt_rpow_of_neg h1my_pos h1mxy hp2_neg
    have hd_mul : delta_star q * (1 - xx) ^ p2 < delta_star q * (1 - yy) ^ p2 :=
      mul_lt_mul_of_pos_left h1m_p2 hDS_pos
    show yy ^ p2 - delta_star q * (1 - yy) ^ p2 < xx ^ p2 - delta_star q * (1 - xx) ^ p2
    linarith
  -- ψ(z_func q) = 0  (replicated from UStarMinAttained.hpsi_zfunc).
  have h2qm1_pos : (0 : ℝ) < 2 * q - 1 := by linarith
  have h2qm1_ne : (2 * q - 1) ≠ 0 := ne_of_gt h2qm1_pos
  have hpsi_zfunc : psi (z_func q) = 0 := by
    set D : ℝ := (delta_star q) ^ (-(q / (2*q - 1))) with hD_def
    have hD_pos : 0 < D := Real.rpow_pos_of_pos hDS_pos _
    have hDenom_pos : 0 < D + 1 := by linarith
    have hDenom_ne : D + 1 ≠ 0 := ne_of_gt hDenom_pos
    have hz_form : z_func q = D / (D + 1) := rfl
    have hone_minus_z : 1 - z_func q = 1 / (D + 1) := by
      rw [hz_form, eq_div_iff hDenom_ne]; field_simp; ring
    have hp_p2 : -(q / (2*q - 1)) * p2 = 1 := by
      rw [hp2_def]
      have hne : (2*q - 1) * q ≠ 0 := mul_ne_zero h2qm1_ne hq_ne
      have hstep : -(q / (2*q - 1)) * ((1 - 2*q) / q) =
             (-q * (1 - 2*q)) / ((2*q - 1) * q) := by
        rw [neg_mul, div_mul_div_comm]; ring
      rw [hstep, div_eq_iff hne]; ring
    have h_z_p2 : (z_func q) ^ p2 = D ^ p2 / (D + 1) ^ p2 := by
      rw [hz_form]; exact Real.div_rpow (le_of_lt hD_pos) (le_of_lt hDenom_pos) p2
    have h_1mz_p2 : (1 - z_func q) ^ p2 = 1 / (D + 1) ^ p2 := by
      rw [hone_minus_z, Real.div_rpow (by norm_num) (le_of_lt hDenom_pos), Real.one_rpow]
    have hD_p2 : D ^ p2 = delta_star q := by
      rw [hD_def, ← Real.rpow_mul (le_of_lt hDS_pos), hp_p2, Real.rpow_one]
    show (z_func q) ^ p2 - delta_star q * (1 - z_func q) ^ p2 = 0
    rw [h_z_p2, h_1mz_p2, hD_p2]
    have hDpow_ne : (D + 1) ^ p2 ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hDenom_pos p2)
    field_simp; ring
  -- Define u as a function for derivative work.
  set u : ℝ → ℝ := fun a => u_dual q a with hu_eq
  have hu_def : ∀ a, u a =
      delta_star q * (1 - a) ^ ((1 : ℝ) / q) - a ^ ((1 : ℝ) / q) - 1 + 2 * a := by
    intro a; rfl
  -- First derivative of u on (0,1).
  have h_deriv : ∀ y, 0 < y → y < 1 →
      HasDerivAt u (-(delta_star q) / q * (1 - y) ^ p1 - (1/q) * y ^ p1 + 2) y := by
    intro y hy hy1
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h1my_pos : 0 < 1 - y := by linarith
    have h1my_ne : 1 - y ≠ 0 := ne_of_gt h1my_pos
    have hd_y_pow : HasDerivAt (fun z : ℝ => z ^ ((1:ℝ)/q)) ((1/q) * y ^ p1) y := by
      have h := Real.hasDerivAt_rpow_const (p := (1:ℝ)/q) (x := y) (Or.inl hy_ne)
      have heq : ((1:ℝ)/q) - 1 = p1 := by rw [hp1_def]; field_simp
      rw [heq] at h; exact h
    have hd_inner : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hd_1my_pow : HasDerivAt (fun z : ℝ => (1 - z) ^ ((1:ℝ)/q))
        ((1/q) * (1 - y) ^ p1 * (-1)) y := by
      have h := Real.hasDerivAt_rpow_const (p := (1:ℝ)/q) (x := 1 - y) (Or.inl h1my_ne)
      have heq : ((1:ℝ)/q) - 1 = p1 := by rw [hp1_def]; field_simp
      rw [heq] at h; exact h.comp y hd_inner
    have hd_d_1my : HasDerivAt (fun z : ℝ => delta_star q * (1 - z) ^ ((1:ℝ)/q))
        (delta_star q * ((1/q) * (1 - y) ^ p1 * (-1))) y :=
      hd_1my_pow.const_mul (delta_star q)
    have hd_diff : HasDerivAt
        (fun z : ℝ => delta_star q * (1 - z) ^ ((1:ℝ)/q) - z ^ ((1:ℝ)/q))
        (delta_star q * ((1/q) * (1 - y) ^ p1 * (-1)) - (1/q) * y ^ p1) y :=
      hd_d_1my.sub hd_y_pow
    have hd_diff_const : HasDerivAt
        (fun z : ℝ => delta_star q * (1 - z) ^ ((1:ℝ)/q) - z ^ ((1:ℝ)/q) - 1)
        (delta_star q * ((1/q) * (1 - y) ^ p1 * (-1)) - (1/q) * y ^ p1) y :=
      hd_diff.sub_const 1
    have hd_lin : HasDerivAt (fun z : ℝ => 2 * z) (2 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_mul 2
    have hd_total :
        HasDerivAt u
          (delta_star q * ((1/q) * (1 - y) ^ p1 * (-1)) - (1/q) * y ^ p1 + 2) y := by
      simp only [hu_eq]
      exact hd_diff_const.add hd_lin
    have heq_d :
        delta_star q * ((1/q) * (1 - y) ^ p1 * (-1)) - (1/q) * y ^ p1 + 2 =
        -(delta_star q) / q * (1 - y) ^ p1 - (1/q) * y ^ p1 + 2 := by field_simp
    rw [heq_d] at hd_total; exact hd_total
  -- Second derivative of u on (0,1).
  have h_deriv2 : ∀ y, 0 < y → y < 1 →
      HasDerivAt (fun y => -(delta_star q) / q * (1 - y) ^ p1 - (1/q) * y ^ p1 + 2)
        ((p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2)) y := by
    intro y hy hy1
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h1my_pos : 0 < 1 - y := by linarith
    have h1my_ne : 1 - y ≠ 0 := ne_of_gt h1my_pos
    have hd_y_p1 : HasDerivAt (fun z : ℝ => z ^ p1) (p1 * y ^ p2) y := by
      have h := Real.hasDerivAt_rpow_const (p := p1) (x := y) (Or.inl hy_ne)
      have heq : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; field_simp; ring
      rw [heq] at h; exact h
    have hd_inner : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hd_1my_p1 : HasDerivAt (fun z : ℝ => (1 - z) ^ p1) (p1 * (1 - y) ^ p2 * (-1)) y := by
      have h := Real.hasDerivAt_rpow_const (p := p1) (x := 1 - y) (Or.inl h1my_ne)
      have heq : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; field_simp; ring
      rw [heq] at h; exact h.comp y hd_inner
    have hd_part1 : HasDerivAt (fun z : ℝ => -(delta_star q) / q * (1 - z) ^ p1)
        (-(delta_star q) / q * (p1 * (1 - y) ^ p2 * (-1))) y :=
      hd_1my_p1.const_mul (-(delta_star q) / q)
    have hd_part2 : HasDerivAt (fun z : ℝ => (1/q) * z ^ p1) ((1/q) * (p1 * y ^ p2)) y :=
      hd_y_p1.const_mul (1/q)
    have hd_sub : HasDerivAt
        (fun z : ℝ => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1)
        (-(delta_star q) / q * (p1 * (1 - y) ^ p2 * (-1)) - (1/q) * (p1 * y ^ p2)) y :=
      hd_part1.sub hd_part2
    have hd_total := hd_sub.add_const (2 : ℝ)
    have heq_simp :
        -(delta_star q) / q * (p1 * (1 - y) ^ p2 * (-1)) - (1/q) * (p1 * y ^ p2) =
        (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) := by field_simp
    rw [heq_simp] at hd_total; exact hd_total
  -- u'' ≤ 0 on (z_func q, 1).
  have h_uSecond_np : ∀ y, z_func q < y → y < 1 →
      (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) ≤ 0 := by
    intro y hy_gt_z hy_lt_one
    have hy_pos : 0 < y := lt_trans hZ_pos hy_gt_z
    -- ψ(y) < ψ(z_func q) = 0  (ψ antitone, y > z)
    have hpsi_y_neg : y ^ p2 - delta_star q * (1 - y) ^ p2 < 0 := by
      have hy_in : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hy_pos, hy_lt_one⟩
      have hz_in : z_func q ∈ Set.Ioo (0:ℝ) 1 := ⟨hZ_pos, hZ_lt_one⟩
      have h_anti := hpsi_anti hz_in hy_in hy_gt_z
      have hpsi_y_val : psi y = y ^ p2 - delta_star q * (1 - y) ^ p2 := rfl
      rw [hpsi_zfunc, hpsi_y_val] at h_anti
      exact h_anti
    have hp1_q_neg : p1 / q < 0 := div_neg_of_neg_of_pos hp1_neg hq_pos
    have hbracket_pos : 0 < delta_star q * (1 - y) ^ p2 - y ^ p2 := by linarith
    have h_neg : (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) < 0 :=
      mul_neg_of_neg_of_pos hp1_q_neg hbracket_pos
    linarith
  -- Continuity of u on [z_func q, 1].
  have hq_inv_pos : (0 : ℝ) < 1 / q := by positivity
  have h_cont : ContinuousOn u (Set.Icc (z_func q) 1) := by
    intro xx hx
    have hx_ge_z : z_func q ≤ xx := hx.1
    have hx_le_one : xx ≤ 1 := hx.2
    have hx_pos : 0 < xx := lt_of_lt_of_le hZ_pos hx_ge_z
    have h_inner : ContinuousAt (fun y : ℝ => 1 - y) xx :=
      (continuous_const.sub continuous_id).continuousAt
    have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/q)) (1 - xx) := by
      rcases eq_or_lt_of_le hx_le_one with hxone | hxlt
      · -- xx = 1, 1 - xx = 0; use exponent positivity branch
        rw [hxone] at *
        simpa using Real.continuousAt_rpow_const (0:ℝ) ((1:ℝ)/q) (Or.inr (le_of_lt hq_inv_pos))
      · have h1mx_pos : 0 < 1 - xx := by linarith
        exact Real.continuousAt_rpow_const (1 - xx) ((1:ℝ)/q) (Or.inl (ne_of_gt h1mx_pos))
    have h_1mx_pow : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/q)) xx :=
      h_outer.comp h_inner
    have h_d_1mx_pow : ContinuousAt (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q)) xx :=
      h_1mx_pow.const_mul (delta_star q)
    have h_x_pow : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/q)) xx :=
      Real.continuousAt_rpow_const xx ((1:ℝ)/q) (Or.inr (le_of_lt hq_inv_pos))
    have h_diff : ContinuousAt
        (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q) - y ^ ((1:ℝ)/q)) xx :=
      h_d_1mx_pow.sub h_x_pow
    have h_diff_const : ContinuousAt
        (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q) - y ^ ((1:ℝ)/q) - 1) xx :=
      h_diff.sub continuousAt_const
    have h_lin : ContinuousAt (fun y : ℝ => 2 * y) xx :=
      (continuous_const.mul continuous_id).continuousAt
    have h_total : ContinuousAt u xx := by
      simp only [hu_eq]; exact h_diff_const.add h_lin
    exact h_total.continuousWithinAt
  -- ConcaveOn u on [z_func q, 1].
  have hConvexIcc : Convex ℝ (Set.Icc (z_func q) 1) := convex_Icc (z_func q) 1
  have h_int : interior (Set.Icc (z_func q) 1) = Set.Ioo (z_func q) 1 := interior_Icc
  have hConc_u : ConcaveOn ℝ (Set.Icc (z_func q) 1) u := by
    apply concaveOn_of_deriv2_nonpos hConvexIcc h_cont
    · rw [h_int]
      intro y hy
      have hy_pos : 0 < y := lt_trans hZ_pos hy.1
      exact (h_deriv y hy_pos hy.2).differentiableAt.differentiableWithinAt
    · rw [h_int]
      intro y hy
      have hy_pos : 0 < y := lt_trans hZ_pos hy.1
      have hopen : IsOpen (Set.Ioo (z_func q) 1) := isOpen_Ioo
      have hnhds : Set.Ioo (z_func q) 1 ∈ nhds y := hopen.mem_nhds hy
      have hloc : deriv u =ᶠ[nhds y]
          fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2 := by
        filter_upwards [hnhds] with z hz
        exact (h_deriv z (lt_trans hZ_pos hz.1) hz.2).deriv
      have hd2 : DifferentiableAt ℝ
          (fun z : ℝ => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2) y :=
        (h_deriv2 y hy_pos hy.2).differentiableAt
      have hd_local : DifferentiableAt ℝ (deriv u) y :=
        hd2.congr_of_eventuallyEq hloc
      exact hd_local.differentiableWithinAt
    · rw [h_int]
      intro y hy
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      have hy_pos : 0 < y := lt_trans hZ_pos hy.1
      have hopen : IsOpen (Set.Ioo (z_func q) 1) := isOpen_Ioo
      have hnhds : Set.Ioo (z_func q) 1 ∈ nhds y := hopen.mem_nhds hy
      have hloc : deriv u =ᶠ[nhds y]
          fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2 := by
        filter_upwards [hnhds] with z hz
        exact (h_deriv z (lt_trans hZ_pos hz.1) hz.2).deriv
      have hd2_eq : deriv (deriv u) y =
          deriv (fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2) y :=
        hloc.deriv_eq
      rw [hd2_eq, (h_deriv2 y hy_pos hy.2).deriv]
      exact h_uSecond_np y hy.1 hy.2
  -- Apply ConcaveOn.ge_on_segment with endpoints z_func q and 1.
  have hz_mem : z_func q ∈ Set.Icc (z_func q) 1 := ⟨le_refl _, le_of_lt hZ_lt_one⟩
  have hone_mem : (1:ℝ) ∈ Set.Icc (z_func q) 1 := ⟨le_of_lt hZ_lt_one, le_refl _⟩
  have ha_mem_seg : a ∈ segment ℝ (z_func q) 1 := by
    rw [segment_eq_Icc (le_of_lt hZ_lt_one)]
    exact ⟨le_of_lt ha_gt_z, ha1⟩
  have hchord := hConc_u.ge_on_segment hz_mem hone_mem ha_mem_seg
  -- u(z_func q) ≥ 0  and  u(1) = 0, so min ≥ 0.
  have hu_z_nn : 0 ≤ u (z_func q) :=
    u_dual_nonneg_left q hq (z_func q) (le_of_lt hZ_pos) (le_refl _)
  have hu_one : u 1 = 0 := u_dual_at_one q hq
  have hmin_nn : 0 ≤ min (u (z_func q)) (u 1) := by
    rw [hu_one]; exact le_min hu_z_nn (le_refl 0)
  -- u a = u_dual q a.
  show 0 ≤ u_dual q a
  have : u a = u_dual q a := rfl
  rw [← this]
  exact le_trans hmin_nn hchord

/-- MAIN: dual-certificate proof of the relaxed core inequality. -/
theorem relaxedFeasibleSumNonneg_dual
    (q : ℝ) (hq : 1 < q)
    {n : ℕ} (hn_pos : 0 < n) (hn_even : Even n)
    (lambda : ℝ) (hlam_eq : lambda = lambda_star q)
    (delta : ℝ) (hdelta_eq : delta = delta_of_lambda q lambda)
    (x : Fin n → ℝ)
    (hx_nn : ∀ i, 0 ≤ x i) (hx_le_one : ∀ i, x i ≤ 1)
    (hx_sum : (∑ i, x i) = (n : ℝ) / 2) :
    0 ≤ (∑ i, h_q q lambda delta (x i)) := by
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hlam_pos : 0 < lambda := by rw [hlam_eq]; exact (LambdaStarDef.1 q hq_le).1
  -- Bridge: delta = delta_star q.
  have hdelta_star : delta = delta_star q := by
    rw [hdelta_eq, hlam_eq]
    exact deltaOfLambda_lambdaStar_eq q hq
  -- Pointwise lower bound: h_q q lambda delta (x i) ≥ lambda * (1 - 2 * x i).
  have h_pointwise : ∀ i, lambda * (1 - 2 * x i) ≤ h_q q lambda delta (x i) := by
    intro i
    have hu_nn : 0 ≤ u_dual q (x i) := u_dual_nonneg q hq (x i) (hx_nn i) (hx_le_one i)
    -- h_q = lambda * (u_dual q (x i) + 1 - 2 * x i)
    have h_rewrite : h_q q lambda delta (x i) = lambda * (u_dual q (x i) + 1 - 2 * (x i)) := by
      show lambda * (delta * (1 - x i) ^ ((1:ℝ)/q) - (x i) ^ ((1:ℝ)/q))
        = lambda * ((delta_star q * (1 - x i) ^ ((1:ℝ)/q) - (x i) ^ ((1:ℝ)/q) - 1 + 2 * (x i)) + 1 - 2 * (x i))
      rw [hdelta_star]; ring
    rw [h_rewrite]
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (1 - 2 * x i) ≤ (u_dual q (x i) + 1 - 2 * (x i))) (le_of_lt hlam_pos)
    linarith [hmul]
  -- Sum the pointwise bound.
  have hsum_lb : (∑ i, lambda * (1 - 2 * x i)) ≤ (∑ i, h_q q lambda delta (x i)) :=
    Finset.sum_le_sum (fun i _ => h_pointwise i)
  -- ∑ lambda*(1 - 2 x i) = lambda * (n - 2 * ∑ x i) = lambda * (n - n) = 0.
  have hsum_eq : (∑ i, lambda * (1 - 2 * x i)) = 0 := by
    rw [← Finset.mul_sum]
    have hinner : (∑ i, (1 - 2 * x i)) = (n : ℝ) - 2 * (∑ i, x i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Finset.mul_sum]
      simp
    rw [hinner, hx_sum]
    ring
  rw [hsum_eq] at hsum_lb
  exact hsum_lb

end Workspace.ProofLemmas.RelaxedCoreDual
