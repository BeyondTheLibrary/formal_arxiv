import Mathlib
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.FqAtCOverQ_eventually_pos
import Workspace.ProofLemmas.FqAtCOverQ_eventually_neg
import Workspace.ProofLemmas.FqStrictConvex

open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.FqSignAt0Pos
open Filter Topology

theorem AStarAsymptotic :
    Filter.Tendsto (fun q => q * a_star q) Filter.atTop (nhds (1/2 : ℝ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Pick ε' = min ε (1/4) > 0; ε' ≤ ε and ε' < 1/2.
  set ε' : ℝ := min ε (1/4) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_lt_half : ε' < 1/2 := by
    have h1 : ε' ≤ 1/4 := min_le_right _ _
    linarith
  -- Define c_lo and c_hi.
  set c_lo : ℝ := 1/2 - ε' with hc_lo_def
  set c_hi : ℝ := 1/2 + ε' with hc_hi_def
  have hc_lo_pos : 0 < c_lo := by simp only [hc_lo_def]; linarith
  have hc_lo_lt_half : c_lo < 1/2 := by simp only [hc_lo_def]; linarith
  have hc_hi_gt_half : 1/2 < c_hi := by simp only [hc_hi_def]; linarith
  have hc_lo_lt_hi : c_lo < c_hi := by simp only [hc_lo_def, hc_hi_def]; linarith
  -- Eventually F_q q (c_lo/q) > 0.
  have h_pos : ∀ᶠ q : ℝ in atTop, 0 < F_q q (c_lo/q) :=
    FqAtCOverQ_eventually_pos c_lo hc_lo_pos hc_lo_lt_half
  -- Eventually F_q q (c_hi/q) < 0.
  have h_neg : ∀ᶠ q : ℝ in atTop, F_q q (c_hi/q) < 0 :=
    FqAtCOverQ_eventually_neg c_hi hc_hi_gt_half
  -- Eventually q > 1.
  have h_q_gt_one : ∀ᶠ q : ℝ in atTop, 1 < q := eventually_gt_atTop 1
  -- Eventually q > c_hi (so c_hi/q < 1).
  have h_q_gt_c_hi : ∀ᶠ q : ℝ in atTop, c_hi < q := eventually_gt_atTop c_hi
  -- Combine all eventuallys.
  filter_upwards [h_pos, h_neg, h_q_gt_one, h_q_gt_c_hi] with q hFpos hFneg hq hq_gt_chi
  -- Basic positivity facts.
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_clo_div_pos : 0 < c_lo / q := div_pos hc_lo_pos hq_pos
  have h_chi_div_pos : 0 < c_hi / q := div_pos (by linarith : (0:ℝ) < c_hi) hq_pos
  have h_div_lt : c_lo / q < c_hi / q := by
    apply div_lt_div_of_pos_right hc_lo_lt_hi hq_pos
  have h_chi_div_lt_one : c_hi / q < 1 := by
    rw [div_lt_one hq_pos]
    exact hq_gt_chi
  -- Continuity of F_q on Ioi 0 (use FqStrictConvex's underlying argument).
  -- Easier: use the same continuity argument as in FqHasUniqueInteriorZero.
  set p : ℝ := (1 - q) / q with hp_def
  have hCont : ContinuousOn (fun a => F_q q a) (Set.Ioi (0 : ℝ)) := by
    have heq : ∀ a : ℝ, F_q q a =
        (2 * (1 - 1/q)) * a + (1/q) * a ^ p + (-2 + 1/q) := by
      intro a
      simp only [F_q, p]
      ring
    refine ContinuousOn.congr ?_ (fun a _ => heq a)
    refine ((continuousOn_const.mul continuousOn_id).add ?_).add continuousOn_const
    refine continuousOn_const.mul ?_
    intro a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    exact (Real.continuousAt_rpow_const a p (Or.inl ha_ne)).continuousWithinAt
  -- Continuity on the closed interval [c_lo/q, c_hi/q].
  have hCont_Icc : ContinuousOn (fun a => F_q q a) (Set.Icc (c_lo/q) (c_hi/q)) := by
    apply hCont.mono
    intro x hx
    exact lt_of_lt_of_le h_clo_div_pos hx.1
  -- Apply IVT: 0 ∈ Ioo (F_q q (c_hi/q)) (F_q q (c_lo/q)) ⊆ F_q '' Ioo (c_lo/q) (c_hi/q).
  have h_zero_in : (0:ℝ) ∈ Set.Ioo (F_q q (c_hi/q)) (F_q q (c_lo/q)) :=
    ⟨hFneg, hFpos⟩
  have h_image : Set.Ioo (F_q q (c_hi/q)) (F_q q (c_lo/q)) ⊆
      (fun a => F_q q a) '' Set.Ioo (c_lo/q) (c_hi/q) :=
    intermediate_value_Ioo' (le_of_lt h_div_lt) hCont_Icc
  obtain ⟨α, hα_mem, hα_val⟩ := h_image h_zero_in
  have hα_pos : 0 < α := lt_trans h_clo_div_pos hα_mem.1
  have hα_lt_one : α < 1 := lt_trans hα_mem.2 h_chi_div_lt_one
  -- α satisfies IsAStar q α (which unfolds to 0 < α ∧ α < 1 ∧ F_q q α = 0).
  -- By uniqueness, α = a_star q.
  obtain ⟨hUnique, hStar⟩ := FqHasUniqueInteriorZero q hq
  obtain ⟨hStar1, hStar2, hStar3⟩ := hStar
  have hα_eq : α = a_star q :=
    hUnique.unique
      (show 0 < α ∧ α < 1 ∧ F_q q α = 0 from ⟨hα_pos, hα_lt_one, hα_val⟩)
      (show 0 < a_star q ∧ a_star q < 1 ∧ F_q q (a_star q) = 0 from
        ⟨hStar1, hStar2, hStar3⟩)
  -- Therefore a_star q ∈ (c_lo/q, c_hi/q).
  rw [hα_eq] at hα_mem
  obtain ⟨h_a_gt, h_a_lt⟩ := hα_mem
  -- Multiply by q to get c_lo < q * a_star q < c_hi.
  have h_q_a_gt : c_lo < q * a_star q := by
    rw [div_lt_iff₀ hq_pos] at h_a_gt
    linarith
  have h_q_a_lt : q * a_star q < c_hi := by
    rw [lt_div_iff₀ hq_pos] at h_a_lt
    linarith
  -- |q * a_star q - 1/2| ≤ ε' ≤ ε.
  have h_diff_lo : -ε' < q * a_star q - 1/2 := by
    simp only [hc_lo_def] at h_q_a_gt; linarith
  have h_diff_hi : q * a_star q - 1/2 < ε' := by
    simp only [hc_hi_def] at h_q_a_lt; linarith
  have h_abs : |q * a_star q - 1/2| < ε' := by
    rw [abs_lt]
    exact ⟨h_diff_lo, h_diff_hi⟩
  -- Finish: dist (q * a_star q) (1/2) = |q * a_star q - 1/2| ≤ ε' ≤ ε.
  rw [Real.dist_eq]
  linarith
