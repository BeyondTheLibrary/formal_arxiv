import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.AStarLessThanOneHalf

open Workspace.ProofLemmas.FqSignAt0Pos
open Workspace.ProofLemmas.FqHasUniqueInteriorZero

namespace Workspace.ProofLemmas.DeltaStarDef

noncomputable def delta_star (q : ℝ) : ℝ :=
  ((a_star q) ^ ((1 : ℝ) / q) + 1 - 2 * (a_star q)) /
  (1 - (a_star q)) ^ ((1 : ℝ) / q)

/-- Auxiliary: for `r ∈ (0, 1]` and `x ∈ [0, 1/2]`,
    `(1-x)^r ≤ x^r + 1 - 2x`. -/
private lemma aux_chord_inequality (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ 1)
    (x : ℝ) (hx_nn : 0 ≤ x) (hx_le : x ≤ 1/2) :
    (1 - x) ^ r ≤ x ^ r + 1 - 2 * x := by
  rcases eq_or_lt_of_le hr_le with hr_eq | hr_lt
  · -- r = 1
    rw [hr_eq]
    rw [Real.rpow_one, Real.rpow_one]
    linarith
  · -- r < 1
    rcases eq_or_lt_of_le hx_nn with hx_zero | hx_pos
    · -- x = 0
      rw [← hx_zero]
      simp [Real.zero_rpow (ne_of_gt hr_pos)]
    · rcases eq_or_lt_of_le hx_le with hx_eq_half | hx_lt_half
      · -- x = 1/2
        rw [hx_eq_half]
        have : (1 - (1/2 : ℝ)) = 1/2 := by norm_num
        rw [this]
        linarith
      · -- 0 < x < 1/2
        set H : ℝ → ℝ := fun x => (1 - x) ^ r - x ^ r - 1 + 2 * x with hH_def
        suffices hH_le : H x ≤ 0 by
          have : H x = (1 - x) ^ r - x ^ r - 1 + 2 * x := rfl
          linarith
        have hH0 : H 0 = 0 := by
          simp [hH_def, Real.zero_rpow (ne_of_gt hr_pos), Real.one_rpow]
        have hH_half : H (1/2 : ℝ) = 0 := by
          show (1 - (1/2 : ℝ)) ^ r - ((1/2 : ℝ)) ^ r - 1 + 2 * (1/2 : ℝ) = 0
          have h12 : (1 - (1/2 : ℝ)) = 1/2 := by norm_num
          rw [h12]
          ring
        -- Continuity of H on [0, 1/2].
        have hCont : ContinuousOn H (Set.Icc (0 : ℝ) (1/2)) := by
          have h1 : ContinuousOn (fun x : ℝ => (1 - x) ^ r) (Set.Icc (0 : ℝ) (1/2)) := by
            intro x hx
            have hx_le : x ≤ 1/2 := hx.2
            have h1x_pos : 0 < 1 - x := by linarith
            have h_inner : ContinuousAt (fun x : ℝ => 1 - x) x :=
              (continuous_const.sub continuous_id).continuousAt
            have h_outer : ContinuousAt (fun y : ℝ => y ^ r) (1 - x) :=
              Real.continuousAt_rpow_const (1 - x) r (Or.inl (ne_of_gt h1x_pos))
            exact (h_outer.comp h_inner).continuousWithinAt
          have h2 : ContinuousOn (fun x : ℝ => x ^ r) (Set.Icc (0 : ℝ) (1/2)) := by
            intro x hx
            have : ContinuousAt (fun x : ℝ => x ^ r) x :=
              Real.continuousAt_rpow_const x r (Or.inr (le_of_lt hr_pos))
            exact this.continuousWithinAt
          have h3 : ContinuousOn (fun x : ℝ => (1 - x) ^ r - x ^ r) (Set.Icc (0 : ℝ) (1/2)) :=
            h1.sub h2
          have h4 : ContinuousOn (fun x : ℝ => (1 - x) ^ r - x ^ r - 1) (Set.Icc (0 : ℝ) (1/2)) :=
            h3.sub continuousOn_const
          have h5 : ContinuousOn H (Set.Icc (0 : ℝ) (1/2)) := by
            simp only [hH_def]
            exact h4.add (continuousOn_const.mul continuousOn_id)
          exact h5
        have hConv_Icc : Convex ℝ (Set.Icc (0 : ℝ) (1/2)) := convex_Icc 0 (1/2)
        have h_int : interior (Set.Icc (0 : ℝ) (1/2)) = Set.Ioo 0 (1/2) := interior_Icc
        -- First derivative formula on (0, 1/2).
        have hH_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) (1/2),
            HasDerivAt H (-r * (1 - y) ^ (r - 1) - r * y ^ (r - 1) + 2) y := by
          intro y hy
          have hy_pos : 0 < y := hy.1
          have hy_ne : y ≠ 0 := ne_of_gt hy_pos
          have h1y_pos : 0 < 1 - y := by linarith [hy.2]
          have h1y_ne : 1 - y ≠ 0 := ne_of_gt h1y_pos
          have hd_inner_neg : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) y := by
            simpa using (hasDerivAt_id y).const_sub 1
          have hd_rpow_y : HasDerivAt (fun y : ℝ => y ^ r) (r * y ^ (r - 1)) y :=
            Real.hasDerivAt_rpow_const (Or.inl hy_ne)
          have hd_rpow_one_minus :
              HasDerivAt (fun y : ℝ => (1 - y) ^ r)
                ((r * (1 - y) ^ (r - 1)) * (-1)) y := by
            have hd := Real.hasDerivAt_rpow_const (p := r) (x := 1 - y) (Or.inl h1y_ne)
            exact hd.comp y hd_inner_neg
          have hd_sub :
              HasDerivAt (fun y : ℝ => (1 - y) ^ r - y ^ r)
                ((r * (1 - y) ^ (r - 1)) * (-1) - r * y ^ (r - 1)) y :=
            hd_rpow_one_minus.sub hd_rpow_y
          have hd_sub_const :
              HasDerivAt (fun y : ℝ => (1 - y) ^ r - y ^ r - 1)
                ((r * (1 - y) ^ (r - 1)) * (-1) - r * y ^ (r - 1)) y :=
            hd_sub.sub_const 1
          have hd_lin : HasDerivAt (fun y : ℝ => 2 * y) (2 : ℝ) y := by
            simpa using (hasDerivAt_id y).const_mul 2
          have hd_total :
              HasDerivAt H
                ((r * (1 - y) ^ (r - 1)) * (-1) - r * y ^ (r - 1) + 2) y := by
            simp only [hH_def]
            exact hd_sub_const.add hd_lin
          have heq :
              (r * (1 - y) ^ (r - 1)) * (-1) - r * y ^ (r - 1) + 2 =
                -r * (1 - y) ^ (r - 1) - r * y ^ (r - 1) + 2 := by ring
          rw [heq] at hd_total
          exact hd_total
        -- Second derivative formula.
        have hH_deriv2 : ∀ y ∈ Set.Ioo (0 : ℝ) (1/2),
            HasDerivAt
              (fun y : ℝ => -r * (1 - y) ^ (r - 1) - r * y ^ (r - 1) + 2)
              (r * (r - 1) * (1 - y) ^ (r - 2) - r * (r - 1) * y ^ (r - 2)) y := by
          intro y hy
          have hy_pos : 0 < y := hy.1
          have hy_ne : y ≠ 0 := ne_of_gt hy_pos
          have h1y_pos : 0 < 1 - y := by linarith [hy.2]
          have h1y_ne : 1 - y ≠ 0 := ne_of_gt h1y_pos
          have hd_inner_neg : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) y := by
            simpa using (hasDerivAt_id y).const_sub 1
          have hd_rpow_inner :
              HasDerivAt (fun y : ℝ => y ^ (r - 1)) ((r - 1) * y ^ (r - 1 - 1)) y :=
            Real.hasDerivAt_rpow_const (Or.inl hy_ne)
          have hd_rpow_one_minus_inner :
              HasDerivAt (fun y : ℝ => (1 - y) ^ (r - 1))
                (((r - 1) * (1 - y) ^ (r - 1 - 1)) * (-1)) y := by
            have hd := Real.hasDerivAt_rpow_const (p := r - 1) (x := 1 - y) (Or.inl h1y_ne)
            exact hd.comp y hd_inner_neg
          have hd_part1 :
              HasDerivAt (fun y : ℝ => -r * (1 - y) ^ (r - 1))
                (-r * (((r - 1) * (1 - y) ^ (r - 1 - 1)) * (-1))) y :=
            hd_rpow_one_minus_inner.const_mul (-r)
          have hd_part2 :
              HasDerivAt (fun y : ℝ => r * y ^ (r - 1))
                (r * ((r - 1) * y ^ (r - 1 - 1))) y :=
            hd_rpow_inner.const_mul r
          have hd_sub :
              HasDerivAt
                (fun y : ℝ => -r * (1 - y) ^ (r - 1) - r * y ^ (r - 1))
                (-r * (((r - 1) * (1 - y) ^ (r - 1 - 1)) * (-1)) -
                  r * ((r - 1) * y ^ (r - 1 - 1))) y :=
            hd_part1.sub hd_part2
          have hd_total := hd_sub.add_const (2 : ℝ)
          have heq :
              -r * (((r - 1) * (1 - y) ^ (r - 1 - 1)) * (-1)) -
                  r * ((r - 1) * y ^ (r - 1 - 1)) =
                r * (r - 1) * (1 - y) ^ (r - 2) - r * (r - 1) * y ^ (r - 2) := by
            have h1 : r - 1 - 1 = r - 2 := by ring
            rw [h1]
            ring
          rw [heq] at hd_total
          exact hd_total
        -- Convexity via second derivative ≥ 0.
        have hConv_H : ConvexOn ℝ (Set.Icc (0 : ℝ) (1/2)) H := by
          apply convexOn_of_deriv2_nonneg hConv_Icc hCont
          · rw [h_int]
            intro y hy
            exact (hH_deriv y hy).differentiableAt.differentiableWithinAt
          · rw [h_int]
            intro y hy
            have hopen : IsOpen (Set.Ioo (0 : ℝ) (1/2)) := isOpen_Ioo
            have hnhds : Set.Ioo (0 : ℝ) (1/2) ∈ nhds y := hopen.mem_nhds hy
            have hloc :
                deriv H =ᶠ[nhds y]
                  fun z => -r * (1 - z) ^ (r - 1) - r * z ^ (r - 1) + 2 := by
              filter_upwards [hnhds] with z hz
              exact (hH_deriv z hz).deriv
            have hd2 :
                DifferentiableAt ℝ
                  (fun z : ℝ => -r * (1 - z) ^ (r - 1) - r * z ^ (r - 1) + 2) y :=
              (hH_deriv2 y hy).differentiableAt
            have hd_local : DifferentiableAt ℝ (deriv H) y :=
              hd2.congr_of_eventuallyEq hloc
            exact hd_local.differentiableWithinAt
          · rw [h_int]
            intro y hy
            simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
            have hopen : IsOpen (Set.Ioo (0 : ℝ) (1/2)) := isOpen_Ioo
            have hnhds : Set.Ioo (0 : ℝ) (1/2) ∈ nhds y := hopen.mem_nhds hy
            have hloc :
                deriv H =ᶠ[nhds y]
                  fun z => -r * (1 - z) ^ (r - 1) - r * z ^ (r - 1) + 2 := by
              filter_upwards [hnhds] with z hz
              exact (hH_deriv z hz).deriv
            have hd2_eq : deriv (deriv H) y =
                deriv (fun z => -r * (1 - z) ^ (r - 1) - r * z ^ (r - 1) + 2) y :=
              hloc.deriv_eq
            rw [hd2_eq, (hH_deriv2 y hy).deriv]
            -- Show: 0 ≤ r * (r - 1) * (1 - y) ^ (r - 2) - r * (r - 1) * y ^ (r - 2)
            have hy_pos : 0 < y := hy.1
            have hy_lt : y < 1/2 := hy.2
            have h1y_pos : 0 < 1 - y := by linarith
            have h1y_gt_y : y < 1 - y := by linarith
            have hr_minus_one_neg : r - 1 < 0 := by linarith
            have hr_minus_two_neg : r - 2 < 0 := by linarith
            have h_rpow_lt : (1 - y) ^ (r - 2) < y ^ (r - 2) :=
              Real.rpow_lt_rpow_of_exponent_neg hy_pos h1y_gt_y hr_minus_two_neg
            have hr_rm1_neg : r * (r - 1) < 0 :=
              mul_neg_of_pos_of_neg hr_pos hr_minus_one_neg
            -- r * (r - 1) * ((1 - y)^(r-2) - y^(r-2)) ≥ 0
            -- = (negative) * (negative) ≥ 0
            have h_diff_neg : (1 - y) ^ (r - 2) - y ^ (r - 2) < 0 := by linarith
            have : 0 ≤ r * (r - 1) * ((1 - y) ^ (r - 2) - y ^ (r - 2)) := by
              have := mul_pos_of_neg_of_neg hr_rm1_neg h_diff_neg
              linarith
            linarith
        -- Apply convexity using ConvexOn.le_max_of_mem_Icc.
        have hx_in : x ∈ Set.Icc (0 : ℝ) (1/2) := ⟨le_of_lt hx_pos, le_of_lt hx_lt_half⟩
        have h0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := ⟨le_refl _, by norm_num⟩
        have hhalf_in : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := ⟨by norm_num, le_refl _⟩
        have hbound : H x ≤ max (H 0) (H (1/2 : ℝ)) :=
          hConv_H.le_max_of_mem_Icc h0_in hhalf_in hx_in
        rw [hH0, hH_half] at hbound
        simpa using hbound

theorem DeltaStarDef (q : ℝ) (hq : 1 < q) :
    1 ≤ delta_star q ∧ 0 < (1 - a_star q) ^ ((1 : ℝ) / q) := by
  have h_astar := AStarLessThanOneHalf q hq
  obtain ⟨ha_pos, ha_lt_half⟩ := h_astar
  have ha_lt_one : a_star q < 1 := by linarith
  have h1_minus_pos : 0 < 1 - a_star q := by linarith
  have hq_pos : (0 : ℝ) < q := by linarith
  have hr_pos : (0 : ℝ) < (1 : ℝ) / q := by positivity
  have hr_le : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one hq_pos]; linarith
  have h_denom_pos : 0 < (1 - a_star q) ^ ((1 : ℝ) / q) :=
    Real.rpow_pos_of_pos h1_minus_pos _
  refine ⟨?_, h_denom_pos⟩
  unfold delta_star
  rw [le_div_iff₀ h_denom_pos]
  rw [one_mul]
  have hkey := aux_chord_inequality ((1 : ℝ) / q) hr_pos hr_le (a_star q)
    (le_of_lt ha_pos) (le_of_lt ha_lt_half)
  linarith

end Workspace.ProofLemmas.DeltaStarDef
