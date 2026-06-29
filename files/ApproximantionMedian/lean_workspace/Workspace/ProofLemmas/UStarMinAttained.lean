import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.ZeqInHalfRange
import Workspace.ProofLemmas.AStarLessThanOneHalf

open Workspace.ProofLemmas.FqSignAt0Pos
open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.ZeqInHalfRange

set_option maxHeartbeats 4000000

theorem UStarMinAttained (q : ℝ) (hq : 1 < q) :
    let u_star (a : ℝ) : ℝ :=
      delta_star q * (1 - a) ^ ((1 : ℝ) / q) - a ^ ((1 : ℝ) / q) - 1 + 2 * a
    (0 ≤ a_star q ∧ a_star q ≤ z_func q) ∧
      u_star (a_star q) = 0 ∧
      (∀ a, 0 ≤ a → a ≤ z_func q → 0 ≤ u_star a) := by
  -- Basic facts.
  have hAStar := AStarLessThanOneHalf q hq
  obtain ⟨hAS_pos, hAS_lt_half⟩ := hAStar
  have hAS_lt_one : a_star q < 1 := by linarith
  have hAS_one_minus_pos : 0 < 1 - a_star q := by linarith
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_inv_pos : (0 : ℝ) < 1 / q := by positivity
  have hq_inv_le_one : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one hq_pos]; linarith
  have h2qm1_pos : (0 : ℝ) < 2 * q - 1 := by linarith
  have h2qm1_ne : (2 * q - 1) ≠ 0 := ne_of_gt h2qm1_pos
  have hDS := DeltaStarDef q hq
  obtain ⟨hDS_ge_one, hDenom_pos⟩ := hDS
  have hDS_pos : 0 < delta_star q := lt_of_lt_of_le one_pos hDS_ge_one
  have hZ := ZeqInHalfRange q hq
  obtain ⟨hZ_pos, hZ_le_half⟩ := hZ
  have hZ_lt_one : z_func q < 1 := by linarith
  -- Key identity: delta_star definition.
  have h_delta_eq : delta_star q =
      ((a_star q) ^ ((1 : ℝ) / q) + 1 - 2 * (a_star q)) /
      (1 - (a_star q)) ^ ((1 : ℝ) / q) := rfl
  have hU_at_AStar :
      delta_star q * (1 - a_star q) ^ ((1 : ℝ) / q) =
      (a_star q) ^ ((1 : ℝ) / q) + 1 - 2 * (a_star q) := by
    rw [h_delta_eq]
    field_simp
  -- Now define u_star via let-intro.
  intro u_star
  show (0 ≤ a_star q ∧ a_star q ≤ z_func q) ∧
      u_star (a_star q) = 0 ∧
      (∀ a, 0 ≤ a → a ≤ z_func q → 0 ≤ u_star a)
  have hu_def : ∀ a, u_star a =
      delta_star q * (1 - a) ^ ((1 : ℝ) / q) - a ^ ((1 : ℝ) / q) - 1 + 2 * a := by
    intro a; rfl
  -- Part 2: u_star(a_star q) = 0.
  have hUStar_AStar_eq_zero : u_star (a_star q) = 0 := by
    rw [hu_def]
    linarith [hU_at_AStar]

  -- F_q(a_star q) = 0.
  have hFqAstar : F_q q (a_star q) = 0 := by
    have h := (FqHasUniqueInteriorZero q hq).2
    exact h.2.2

  -- Set up exponents.
  set p1 : ℝ := (1 - q) / q with hp1_def
  have hp1_neg : p1 < 0 := by
    rw [hp1_def]
    apply div_neg_of_neg_of_pos _ hq_pos
    linarith
  set p2 : ℝ := (1 - 2*q) / q with hp2_def
  have hp2_neg : p2 < 0 := by
    rw [hp2_def]
    apply div_neg_of_neg_of_pos _ hq_pos
    linarith
  have hp1_one_over_q : p1 = (1:ℝ)/q - 1 := by
    rw [hp1_def]; field_simp
  have hp2_eq_p1m1 : p2 = p1 - 1 := by
    rw [hp2_def, hp1_def]
    field_simp
    ring

  -- (a_star q)^p1 = 2q - 1 - 2(q-1) a_star.
  have hAStar_p1_eq : (a_star q) ^ p1 = 2*q - 1 - 2*(q-1)*(a_star q) := by
    have hFq_def : F_q q (a_star q) =
        2 * (1 - 1/q) * (a_star q) + (1/q) * (a_star q) ^ ((1 - q) / q) - 2 + 1/q := rfl
    rw [hFq_def] at hFqAstar
    have hkey : (1/q) * (a_star q) ^ ((1 - q) / q) =
        2 - 1/q - 2*(1 - 1/q)*(a_star q) := by linarith
    have h_mul_q : q * ((1/q) * (a_star q) ^ ((1 - q) / q)) =
        q * (2 - 1/q - 2*(1 - 1/q)*(a_star q)) := by
      rw [hkey]
    have hq_inv_eq : q * (1/q) = 1 := by field_simp
    have h_lhs : q * ((1/q) * (a_star q) ^ ((1 - q) / q)) = (a_star q) ^ ((1 - q) / q) := by
      rw [← mul_assoc, hq_inv_eq, one_mul]
    have h_rhs : q * (2 - 1/q - 2*(1 - 1/q)*(a_star q)) =
        2*q - 1 - 2*(q-1)*(a_star q) := by
      field_simp
    rw [h_lhs] at h_mul_q
    rw [h_mul_q, h_rhs]

  -- (a*)^(1/q) = (2q-1)*a* - 2(q-1)*a*^2.
  have hAStar_one_over_q : (a_star q) ^ ((1 : ℝ) / q) =
      (2*q - 1) * (a_star q) - 2*(q-1) * (a_star q)^2 := by
    have hid : (a_star q) ^ p1 * (a_star q) = (a_star q) ^ ((1 : ℝ) / q) := by
      have hsum : p1 + 1 = (1 : ℝ) / q := by
        rw [hp1_def]; field_simp; ring
      have hadd := Real.rpow_add hAS_pos p1 1
      rw [Real.rpow_one] at hadd
      rw [← hadd, hsum]
    rw [← hid, hAStar_p1_eq]
    ring

  -- (8b): delta_star * (1-a*)^p1 + (a*)^p1 = 2q.
  have h8b : delta_star q * (1 - a_star q) ^ p1 + (a_star q) ^ p1 = 2 * q := by
    have hid_1ma : (1 - a_star q) ^ p1 * (1 - a_star q) = (1 - a_star q) ^ ((1 : ℝ) / q) := by
      have hsum : p1 + 1 = (1 : ℝ) / q := by
        rw [hp1_def]; field_simp; ring
      have hadd := Real.rpow_add hAS_one_minus_pos p1 1
      rw [Real.rpow_one] at hadd
      rw [← hadd, hsum]
    have h1ma_ne : (1 - a_star q) ≠ 0 := ne_of_gt hAS_one_minus_pos
    have hpow_p1_pos : 0 < (1 - a_star q) ^ p1 := Real.rpow_pos_of_pos hAS_one_minus_pos p1
    have step1 : delta_star q * (1 - a_star q) ^ p1 * (1 - a_star q) =
        (a_star q) ^ ((1 : ℝ) / q) + 1 - 2 * (a_star q) := by
      rw [mul_assoc, hid_1ma, hU_at_AStar]
    have step2 : delta_star q * (1 - a_star q) ^ p1 =
        ((a_star q) ^ ((1 : ℝ) / q) + 1 - 2 * (a_star q)) / (1 - a_star q) := by
      rw [eq_div_iff h1ma_ne]
      exact step1
    rw [step2, hAStar_one_over_q, hAStar_p1_eq]
    field_simp
    ring

  -- ψ(x) = x^p2 - delta_star * (1-x)^p2.
  set psi : ℝ → ℝ := fun x => x ^ p2 - delta_star q * (1 - x) ^ p2 with hpsi_def

  -- ψ strictly antitone on (0, 1).
  have hpsi_anti : StrictAntiOn psi (Set.Ioo (0:ℝ) 1) := by
    intro x hx y hy hxy
    have hx_pos : 0 < x := hx.1
    have hy_pos : 0 < y := hy.1
    have h1my_pos : 0 < 1 - y := by linarith [hy.2]
    have hxp2 : y ^ p2 < x ^ p2 :=
      Real.rpow_lt_rpow_of_exponent_neg hx_pos hxy hp2_neg
    have h1mxy : 1 - y < 1 - x := by linarith
    have h1m_p2 : (1 - x) ^ p2 < (1 - y) ^ p2 :=
      Real.rpow_lt_rpow_of_exponent_neg h1my_pos h1mxy hp2_neg
    have hd_mul : delta_star q * (1 - x) ^ p2 < delta_star q * (1 - y) ^ p2 :=
      mul_lt_mul_of_pos_left h1m_p2 hDS_pos
    show psi y < psi x
    rw [hpsi_def]
    show y ^ p2 - delta_star q * (1 - y) ^ p2 < x ^ p2 - delta_star q * (1 - x) ^ p2
    linarith

  -- ψ(z_func) = 0.
  have hpsi_zfunc : psi (z_func q) = 0 := by
    set D : ℝ := (delta_star q) ^ (-(q / (2*q - 1))) with hD_def
    have hD_pos : 0 < D := Real.rpow_pos_of_pos hDS_pos _
    have hDenom_pos2 : 0 < D + 1 := by linarith
    have hDenom_ne : D + 1 ≠ 0 := ne_of_gt hDenom_pos2
    have hz_form : z_func q = D / (D + 1) := rfl
    have hone_minus_z : 1 - z_func q = 1 / (D + 1) := by
      rw [hz_form, eq_div_iff hDenom_ne]
      field_simp
      ring
    have hone_minus_z_pos : 0 < 1 - z_func q := by
      rw [hone_minus_z]; positivity
    have hp_p2 : -(q / (2*q - 1)) * p2 = 1 := by
      rw [hp2_def]
      have hne : (2*q - 1) * q ≠ 0 := mul_ne_zero h2qm1_ne hq_ne
      have hstep : -(q / (2*q - 1)) * ((1 - 2*q) / q) =
             (-q * (1 - 2*q)) / ((2*q - 1) * q) := by
        rw [neg_mul, div_mul_div_comm]
        congr 1
        ring
      rw [hstep, div_eq_iff hne]
      ring
    have h_z_p2 : (z_func q) ^ p2 = D ^ p2 / (D + 1) ^ p2 := by
      rw [hz_form]
      exact Real.div_rpow (le_of_lt hD_pos) (le_of_lt hDenom_pos2) p2
    have h_1mz_p2 : (1 - z_func q) ^ p2 = 1 / (D + 1) ^ p2 := by
      rw [hone_minus_z]
      rw [Real.div_rpow (by norm_num) (le_of_lt hDenom_pos2), Real.one_rpow]
    have hD_p2 : D ^ p2 = delta_star q := by
      rw [hD_def]
      rw [← Real.rpow_mul (le_of_lt hDS_pos), hp_p2, Real.rpow_one]
    show (z_func q) ^ p2 - delta_star q * (1 - z_func q) ^ p2 = 0
    rw [h_z_p2, h_1mz_p2, hD_p2]
    have hDpow_ne : (D + 1) ^ p2 ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hDenom_pos2 p2)
    field_simp
    ring

  -- ψ(a_star) > 0.
  have hAStar_p2 : (a_star q) ^ p2 = (a_star q) ^ p1 / (a_star q) := by
    rw [hp2_eq_p1m1]
    rw [show p1 - 1 = p1 + (-1) by ring]
    rw [Real.rpow_add hAS_pos]
    rw [Real.rpow_neg_one]
    rw [div_eq_mul_inv]
  have h1mAStar_p2 : (1 - a_star q) ^ p2 = (1 - a_star q) ^ p1 / (1 - a_star q) := by
    rw [hp2_eq_p1m1]
    rw [show p1 - 1 = p1 + (-1) by ring]
    rw [Real.rpow_add hAS_one_minus_pos]
    rw [Real.rpow_neg_one]
    rw [div_eq_mul_inv]
  have hprod_pos : 0 < (a_star q) * (1 - a_star q) := mul_pos hAS_pos hAS_one_minus_pos
  have hpsi_AStar_eq :
      psi (a_star q) =
      (2*q - 1) * (1 - 2 * (a_star q)) / ((a_star q) * (1 - a_star q)) := by
    show (a_star q) ^ p2 - delta_star q * (1 - a_star q) ^ p2 =
        (2*q - 1) * (1 - 2 * (a_star q)) / ((a_star q) * (1 - a_star q))
    rw [hAStar_p2, h1mAStar_p2]
    rw [mul_div_assoc']
    have h8b' : delta_star q * (1 - a_star q) ^ p1 = 2 * q - (a_star q) ^ p1 := by
      linarith [h8b]
    rw [h8b']
    rw [hAStar_p1_eq]
    field_simp
    ring
  have hpsi_AStar_pos : 0 < psi (a_star q) := by
    rw [hpsi_AStar_eq]
    apply div_pos
    · apply mul_pos
      · linarith
      · linarith
    · exact hprod_pos

  -- Hence a_star q < z_func q.
  have hAStar_lt_zfunc : a_star q < z_func q := by
    by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [← heq] at hpsi_AStar_pos
      rw [hpsi_zfunc] at hpsi_AStar_pos
      linarith
    · have hzfunc_in : z_func q ∈ Set.Ioo (0:ℝ) 1 := ⟨hZ_pos, hZ_lt_one⟩
      have hAStar_in : a_star q ∈ Set.Ioo (0:ℝ) 1 := ⟨hAS_pos, hAS_lt_one⟩
      have := hpsi_anti hzfunc_in hAStar_in hlt
      rw [hpsi_zfunc] at this
      linarith

  have hAStar_le_zfunc : a_star q ≤ z_func q := le_of_lt hAStar_lt_zfunc

  refine ⟨⟨le_of_lt hAS_pos, hAStar_le_zfunc⟩, hUStar_AStar_eq_zero, ?_⟩

  -- Part 3: ∀ a ∈ [0, z_func q], 0 ≤ u_star a.

  intro a ha_nn ha_le_z

  -- Define u : ℝ → ℝ explicitly.
  set u : ℝ → ℝ := fun a =>
    delta_star q * (1 - a) ^ ((1 : ℝ) / q) - a ^ ((1 : ℝ) / q) - 1 + 2 * a with hu_eq

  have hu_eq_ustar : ∀ x, u x = u_star x := by
    intro x
    show delta_star q * (1 - x) ^ ((1 : ℝ) / q) - x ^ ((1 : ℝ) / q) - 1 + 2 * x = u_star x
    rw [hu_def]

  -- ContinuousOn u on [0, z_func q].
  have h_cont : ContinuousOn u (Set.Icc (0:ℝ) (z_func q)) := by
    intro x hx
    have hx_le_z : x ≤ z_func q := hx.2
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le_z hZ_lt_one
    have h1mx_pos : 0 < 1 - x := by linarith
    have hx_nn : 0 ≤ x := hx.1
    have h_inner : ContinuousAt (fun y : ℝ => 1 - y) x :=
      (continuous_const.sub continuous_id).continuousAt
    have h_outer : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/q)) (1 - x) :=
      Real.continuousAt_rpow_const (1 - x) ((1:ℝ)/q) (Or.inl (ne_of_gt h1mx_pos))
    have h_1mx_pow : ContinuousAt (fun y : ℝ => (1 - y) ^ ((1:ℝ)/q)) x :=
      h_outer.comp h_inner
    have h_d_1mx_pow : ContinuousAt (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q)) x :=
      h_1mx_pow.const_mul (delta_star q)
    have h_x_pow : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/q)) x :=
      Real.continuousAt_rpow_const x ((1:ℝ)/q) (Or.inr (le_of_lt hq_inv_pos))
    have h_diff : ContinuousAt
        (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q) - y ^ ((1:ℝ)/q)) x :=
      h_d_1mx_pow.sub h_x_pow
    have h_diff_const : ContinuousAt
        (fun y : ℝ => delta_star q * (1 - y) ^ ((1:ℝ)/q) - y ^ ((1:ℝ)/q) - 1) x :=
      h_diff.sub continuousAt_const
    have h_lin : ContinuousAt (fun y : ℝ => 2 * y) x :=
      (continuous_const.mul continuous_id).continuousAt
    have h_total : ContinuousAt u x := by
      simp only [hu_eq]
      exact h_diff_const.add h_lin
    exact h_total.continuousWithinAt

  -- Derivative of u on (0, 1).
  have h_deriv : ∀ y, 0 < y → y < 1 →
      HasDerivAt u (-(delta_star q) / q * (1 - y) ^ p1 - (1/q) * y ^ p1 + 2) y := by
    intro y hy hy1
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h1my_pos : 0 < 1 - y := by linarith
    have h1my_ne : 1 - y ≠ 0 := ne_of_gt h1my_pos
    have hd_y_pow : HasDerivAt (fun z : ℝ => z ^ ((1:ℝ)/q)) ((1/q) * y ^ p1) y := by
      have h := Real.hasDerivAt_rpow_const (p := (1:ℝ)/q) (x := y) (Or.inl hy_ne)
      have heq : ((1:ℝ)/q) - 1 = p1 := by
        rw [hp1_def]; field_simp
      rw [heq] at h
      exact h
    have hd_inner : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hd_1my_pow : HasDerivAt (fun z : ℝ => (1 - z) ^ ((1:ℝ)/q))
        ((1/q) * (1 - y) ^ p1 * (-1)) y := by
      have h := Real.hasDerivAt_rpow_const (p := (1:ℝ)/q) (x := 1 - y) (Or.inl h1my_ne)
      have heq : ((1:ℝ)/q) - 1 = p1 := by
        rw [hp1_def]; field_simp
      rw [heq] at h
      exact h.comp y hd_inner
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
        -(delta_star q) / q * (1 - y) ^ p1 - (1/q) * y ^ p1 + 2 := by
      field_simp
    rw [heq_d] at hd_total
    exact hd_total

  -- u'(a_star q) = 0.
  have h_uPrime_AStar :
      -(delta_star q) / q * (1 - a_star q) ^ p1 - (1/q) * (a_star q) ^ p1 + 2 = 0 := by
    have h := h8b
    have heq : -(delta_star q) / q * (1 - a_star q) ^ p1 - (1/q) * (a_star q) ^ p1 + 2 =
        -(1/q) * (delta_star q * (1 - a_star q) ^ p1 + (a_star q) ^ p1) + 2 := by
      field_simp
      ring
    rw [heq, h]
    field_simp
    ring

  have h_uPrime_AStar_zero : HasDerivAt u 0 (a_star q) := by
    have h := h_deriv (a_star q) hAS_pos hAS_lt_one
    rw [h_uPrime_AStar] at h
    exact h

  -- Second derivative of u on (0, 1).
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
      rw [heq] at h
      exact h
    have hd_inner : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hd_1my_p1 : HasDerivAt (fun z : ℝ => (1 - z) ^ p1) (p1 * (1 - y) ^ p2 * (-1)) y := by
      have h := Real.hasDerivAt_rpow_const (p := p1) (x := 1 - y) (Or.inl h1my_ne)
      have heq : p1 - 1 = p2 := by rw [hp1_def, hp2_def]; field_simp; ring
      rw [heq] at h
      exact h.comp y hd_inner
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
        (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) := by
      field_simp
    rw [heq_simp] at hd_total
    exact hd_total

  -- u'' ≥ 0 on (0, z_func q).
  have h_uSecond_nn : ∀ y, 0 < y → y < z_func q →
      0 ≤ (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) := by
    intro y hy_pos hy_lt_z
    have hy_lt_one : y < 1 := lt_trans hy_lt_z hZ_lt_one
    have hpsi_y_pos : 0 < y ^ p2 - delta_star q * (1 - y) ^ p2 := by
      have hy_in : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hy_pos, hy_lt_one⟩
      have hz_in : z_func q ∈ Set.Ioo (0:ℝ) 1 := ⟨hZ_pos, hZ_lt_one⟩
      have h_anti := hpsi_anti hy_in hz_in hy_lt_z
      -- h_anti : psi (z_func q) < psi y, i.e. fun-eval form
      have hpsi_y_val : psi y = y ^ p2 - delta_star q * (1 - y) ^ p2 := rfl
      have hpsi_z_val : psi (z_func q) =
          (z_func q) ^ p2 - delta_star q * (1 - z_func q) ^ p2 := rfl
      have h_anti' : psi (z_func q) < psi y := h_anti
      rw [hpsi_zfunc, hpsi_y_val] at h_anti'
      exact h_anti'
    have hp1_q_neg : p1 / q < 0 := div_neg_of_neg_of_pos hp1_neg hq_pos
    have hbracket_neg : delta_star q * (1 - y) ^ p2 - y ^ p2 < 0 := by linarith
    have h_pos : 0 < (p1/q) * (delta_star q * (1 - y) ^ p2 - y ^ p2) :=
      mul_pos_of_neg_of_neg hp1_q_neg hbracket_neg
    linarith

  -- ConvexOn u on [0, z_func q].
  have hConvexIcc : Convex ℝ (Set.Icc (0:ℝ) (z_func q)) := convex_Icc 0 (z_func q)
  have h_int : interior (Set.Icc (0:ℝ) (z_func q)) = Set.Ioo 0 (z_func q) := interior_Icc
  have hConv_u : ConvexOn ℝ (Set.Icc (0:ℝ) (z_func q)) u := by
    apply convexOn_of_deriv2_nonneg hConvexIcc h_cont
    · rw [h_int]
      intro y hy
      have hy_pos : 0 < y := hy.1
      have hy_lt_z : y < z_func q := hy.2
      have hy_lt_one : y < 1 := lt_trans hy_lt_z hZ_lt_one
      exact (h_deriv y hy_pos hy_lt_one).differentiableAt.differentiableWithinAt
    · rw [h_int]
      intro y hy
      have hy_pos : 0 < y := hy.1
      have hy_lt_z : y < z_func q := hy.2
      have hy_lt_one : y < 1 := lt_trans hy_lt_z hZ_lt_one
      have hopen : IsOpen (Set.Ioo (0:ℝ) (z_func q)) := isOpen_Ioo
      have hnhds : Set.Ioo (0:ℝ) (z_func q) ∈ nhds y := hopen.mem_nhds hy
      have hloc : deriv u =ᶠ[nhds y]
          fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2 := by
        filter_upwards [hnhds] with z hz
        exact (h_deriv z hz.1 (lt_trans hz.2 hZ_lt_one)).deriv
      have hd2 : DifferentiableAt ℝ
          (fun z : ℝ => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2) y :=
        (h_deriv2 y hy_pos hy_lt_one).differentiableAt
      have hd_local : DifferentiableAt ℝ (deriv u) y :=
        hd2.congr_of_eventuallyEq hloc
      exact hd_local.differentiableWithinAt
    · rw [h_int]
      intro y hy
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      have hy_pos : 0 < y := hy.1
      have hy_lt_z : y < z_func q := hy.2
      have hy_lt_one : y < 1 := lt_trans hy_lt_z hZ_lt_one
      have hopen : IsOpen (Set.Ioo (0:ℝ) (z_func q)) := isOpen_Ioo
      have hnhds : Set.Ioo (0:ℝ) (z_func q) ∈ nhds y := hopen.mem_nhds hy
      have hloc : deriv u =ᶠ[nhds y]
          fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2 := by
        filter_upwards [hnhds] with z hz
        exact (h_deriv z hz.1 (lt_trans hz.2 hZ_lt_one)).deriv
      have hd2_eq : deriv (deriv u) y =
          deriv (fun z => -(delta_star q) / q * (1 - z) ^ p1 - (1/q) * z ^ p1 + 2) y :=
        hloc.deriv_eq
      rw [hd2_eq, (h_deriv2 y hy_pos hy_lt_one).deriv]
      exact h_uSecond_nn y hy_pos hy_lt_z

  -- a_star q is in interior of [0, z_func q].
  have hAS_in_Ioo : a_star q ∈ Set.Ioo (0:ℝ) (z_func q) := ⟨hAS_pos, hAStar_lt_zfunc⟩
  have hAS_in_int : a_star q ∈ interior (Set.Icc (0:ℝ) (z_func q)) := by
    rw [h_int]; exact hAS_in_Ioo

  -- derivWithin u (Ioi a_star q) (a_star q) = 0.
  have h_derivWithin : derivWithin u (Set.Ioi (a_star q)) (a_star q) = 0 := by
    have h := h_uPrime_AStar_zero.hasDerivWithinAt
        (s := Set.Ioi (a_star q))
    exact h.derivWithin (uniqueDiffWithinAt_Ioi (a_star q))

  -- Apply ConvexOn.isMinOn_of_rightDeriv_eq_zero.
  have h_isMinOn : IsMinOn u (Set.Icc (0:ℝ) (z_func q)) (a_star q) :=
    hConv_u.isMinOn_of_rightDeriv_eq_zero hAS_in_int h_derivWithin

  -- Apply at a.
  have ha_in_Icc : a ∈ Set.Icc (0:ℝ) (z_func q) := ⟨ha_nn, ha_le_z⟩
  have h_min_raw := h_isMinOn ha_in_Icc
  -- h_min_raw : u (a_star q) ≤ u a (in setOf form)
  have h_min : u (a_star q) ≤ u a := h_min_raw
  have hu_AStar_zero : u (a_star q) = 0 := by
    rw [hu_eq_ustar]; exact hUStar_AStar_eq_zero
  rw [hu_AStar_zero] at h_min
  -- h_min : 0 ≤ u a.
  have hua_eq : u a = u_star a := hu_eq_ustar a
  linarith
