import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos

open Workspace.ProofLemmas.FqSignAt0Pos

theorem FqStrictConvex (q : ℝ) (hq : 1 < q) :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun a => F_q q a) := by
  set p : ℝ := (1 - q) / q with hp_def
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_inv_pos : 0 < 1 / q := by positivity
  have hp_neg : p < 0 := by
    have h1 : 1 - q < 0 := by linarith
    exact div_neg_of_neg_of_pos h1 hq_pos
  have hp_minus_one_neg : p - 1 < 0 := by linarith
  have hpp1_pos : 0 < p * (p - 1) := mul_pos_of_neg_of_neg hp_neg hp_minus_one_neg
  -- Define helper: linear coefficient.
  set c1 : ℝ := 2 * (1 - 1 / q) with hc1_def
  set c2 : ℝ := 1 / q with hc2_def
  set c3 : ℝ := -2 + 1 / q with hc3_def
  -- Rewrite F_q q a = c1 * a + c2 * a^p + c3 (for any a).
  have hFq_eq : ∀ a : ℝ, F_q q a = c1 * a + c2 * a ^ p + c3 := by
    intro a
    simp [F_q, c1, c2, c3, p]
    ring
  -- Continuity on Ioi 0.
  have hCont : ContinuousOn (fun a => F_q q a) (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.congr ?_ (fun a _ => hFq_eq a)
    refine ((continuousOn_const.mul continuousOn_id).add ?_).add continuousOn_const
    refine continuousOn_const.mul ?_
    intro a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    exact (Real.continuousAt_rpow_const a p (Or.inl ha_ne)).continuousWithinAt
  -- First derivative on Ioi 0: F_q' a = c1 + c2 * p * a^(p-1).
  have hFq_deriv : ∀ a ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun a => F_q q a) (c1 + c2 * (p * a ^ (p - 1))) a := by
    intro a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hd_lin : HasDerivAt (fun y : ℝ => c1 * y) c1 a := by
      simpa using (hasDerivAt_id a).const_mul c1
    have hd_rpow : HasDerivAt (fun y : ℝ => y ^ p) (p * a ^ (p - 1)) a :=
      Real.hasDerivAt_rpow_const (Or.inl ha_ne)
    have hd_smul : HasDerivAt (fun y : ℝ => c2 * y ^ p) (c2 * (p * a ^ (p - 1))) a :=
      hd_rpow.const_mul c2
    have hd_sum : HasDerivAt (fun y : ℝ => c1 * y + c2 * y ^ p)
        (c1 + c2 * (p * a ^ (p - 1))) a := hd_lin.add hd_smul
    have hd_const : HasDerivAt (fun y : ℝ => c1 * y + c2 * y ^ p + c3)
        (c1 + c2 * (p * a ^ (p - 1))) a := hd_sum.add_const c3
    -- congr to F_q
    have hcongr : (fun y : ℝ => F_q q y) = (fun y => c1 * y + c2 * y ^ p + c3) := by
      funext y
      exact hFq_eq y
    rw [hcongr]
    exact hd_const
  -- Now apply strictConvexOn_of_deriv2_pos.
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0) hCont
  intro a ha
  rw [interior_Ioi] at ha
  have ha_pos : 0 < a := ha
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  -- Show deriv (deriv F_q) a > 0.
  -- Step 1: deriv F_q is eventually equal to a ↦ c1 + c2 * (p * a^(p-1)) on Ioi 0.
  have hIoi_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hnhds : Set.Ioi (0 : ℝ) ∈ nhds a := hIoi_open.mem_nhds ha_pos
  -- deriv F_q =ᶠ[𝓝 a] fun y => c1 + c2 * (p * y^(p-1))
  have hderiv_eq : deriv (fun a => F_q q a)
      =ᶠ[nhds a] (fun y => c1 + c2 * (p * y ^ (p - 1))) := by
    filter_upwards [hnhds] with y hy
    exact (hFq_deriv y hy).deriv
  -- Therefore deriv (deriv F_q) a = deriv (fun y => c1 + c2 * (p * y^(p-1))) a
  have hd2_eq : deriv (deriv (fun a => F_q q a)) a =
      deriv (fun y => c1 + c2 * (p * y ^ (p - 1))) a :=
    hderiv_eq.deriv_eq
  show 0 < deriv^[2] (fun a => F_q q a) a
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [hd2_eq]
  -- Now compute deriv (fun y => c1 + c2 * (p * y^(p-1))) a.
  have hd_inner : HasDerivAt (fun y : ℝ => y ^ (p - 1))
      ((p - 1) * a ^ (p - 1 - 1)) a :=
    Real.hasDerivAt_rpow_const (Or.inl ha_ne)
  have hd_mul1 : HasDerivAt (fun y : ℝ => p * y ^ (p - 1))
      (p * ((p - 1) * a ^ (p - 1 - 1))) a := hd_inner.const_mul p
  have hd_mul2 : HasDerivAt (fun y : ℝ => c2 * (p * y ^ (p - 1)))
      (c2 * (p * ((p - 1) * a ^ (p - 1 - 1)))) a := hd_mul1.const_mul c2
  have hd_total : HasDerivAt (fun y : ℝ => c1 + c2 * (p * y ^ (p - 1)))
      (c2 * (p * ((p - 1) * a ^ (p - 1 - 1)))) a := hd_mul2.const_add c1
  rw [hd_total.deriv]
  -- c2 * (p * ((p-1) * a^(p-2))) > 0
  have ha_rpow_pos : 0 < a ^ (p - 1 - 1) := Real.rpow_pos_of_pos ha_pos _
  have : 0 < c2 * (p * ((p - 1) * a ^ (p - 1 - 1))) := by
    apply mul_pos hq_inv_pos
    rw [show p * ((p - 1) * a ^ (p - 1 - 1)) = (p * (p - 1)) * a ^ (p - 1 - 1) by ring]
    exact mul_pos hpp1_pos ha_rpow_pos
  exact this
