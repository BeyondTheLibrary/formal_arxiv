import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqDerivMonotone
import Workspace.ProofLemmas.FqStrictConvex

open Workspace.ProofLemmas.FqSignAt0Pos
open Classical

namespace Workspace.ProofLemmas.FqHasUniqueInteriorZero

/-- The defining property: a is in the open interval (0, 1) and F_q q a = 0. -/
private def IsAStar (q a : ℝ) : Prop := 0 < a ∧ a < 1 ∧ F_q q a = 0

/-- The unique interior zero of F_q in (0, 1), defined for q > 1 by Classical.choose
    of the existence statement. For q ≤ 1, defined as 0 by default (irrelevant). -/
noncomputable def a_star (q : ℝ) : ℝ :=
  if h : ∃ a, IsAStar q a then Classical.choose h else 0

end Workspace.ProofLemmas.FqHasUniqueInteriorZero

open Workspace.ProofLemmas.FqHasUniqueInteriorZero

theorem FqHasUniqueInteriorZero (q : ℝ) (hq : 1 < q) :
    (∃! a : ℝ, IsAStar q a) ∧ IsAStar q (a_star q) := by
  classical
  -- Basic facts.
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_pow_pos : (0 : ℝ) < q^2 := by positivity
  set p : ℝ := (1 - q) / q with hp_def
  have hp_neg : p < 0 := by
    apply div_neg_of_neg_of_pos
    · linarith
    · exact hq_pos
  -- F_q(1) = 0 by direct algebra.
  have hFq_one : F_q q 1 = 0 := by
    simp only [F_q, Real.one_rpow]
    field_simp
    ring
  -- Strict convexity.
  have hStrictConv : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun a => F_q q a) :=
    FqStrictConvex q hq
  -- Continuity of F_q on Ioi 0.
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
  -- HasDerivAt for F_q at any positive point.
  have hFq_deriv : ∀ a : ℝ, 0 < a →
      HasDerivAt (fun a => F_q q a) (2 * (1 - 1/q) + (1/q) * (p * a ^ (p - 1))) a := by
    intro a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hd_lin : HasDerivAt (fun y : ℝ => (2 * (1 - 1/q)) * y) (2 * (1 - 1/q)) a := by
      simpa using (hasDerivAt_id a).const_mul (2 * (1 - 1/q))
    have hd_rpow : HasDerivAt (fun y : ℝ => y ^ p) (p * a ^ (p - 1)) a :=
      Real.hasDerivAt_rpow_const (Or.inl ha_ne)
    have hd_smul : HasDerivAt (fun y : ℝ => (1/q) * y ^ p) ((1/q) * (p * a ^ (p - 1))) a :=
      hd_rpow.const_mul (1/q)
    have hd_sum : HasDerivAt
        (fun y : ℝ => (2 * (1 - 1/q)) * y + (1/q) * y ^ p)
        (2 * (1 - 1/q) + (1/q) * (p * a ^ (p - 1))) a := hd_lin.add hd_smul
    have hd_total : HasDerivAt
        (fun y : ℝ => (2 * (1 - 1/q)) * y + (1/q) * y ^ p + (-2 + 1/q))
        (2 * (1 - 1/q) + (1/q) * (p * a ^ (p - 1))) a := hd_sum.add_const (-2 + 1/q)
    have hcongr : (fun y : ℝ => F_q q y) =
        (fun y => (2 * (1 - 1/q)) * y + (1/q) * y ^ p + (-2 + 1/q)) := by
      funext y; simp only [F_q, p]; ring
    rw [hcongr]; exact hd_total
  -- Compute the derivative value at 1.
  set L : ℝ := 2 * (1 - 1/q) + (1/q) * (p * (1 : ℝ) ^ (p - 1)) with hL_def
  have hL_eq : L = (2*q - 1) * (q - 1) / q^2 := by
    simp only [hL_def, p, Real.one_rpow, mul_one]
    field_simp
    ring
  have hL_pos : 0 < L := by
    rw [hL_eq]
    apply div_pos
    · apply mul_pos
      · linarith
      · linarith
    · exact hq_pow_pos
  have hFq_deriv_one : HasDerivAt (fun a => F_q q a) L 1 := hFq_deriv 1 zero_lt_one
  -- Step 1: Find a < 1 (close to 1, in (0,1)) with F_q a < 0.
  -- Use the slope characterization of HasDerivAt at 1.
  have htendsto_slope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ * (F_q q (1 + t) - F_q q 1))
      (nhdsWithin (0:ℝ) {0}ᶜ) (nhds L) := by
    have h := hFq_deriv_one
    rw [hasDerivAt_iff_tendsto_slope_zero] at h
    simpa [smul_eq_mul] using h
  have htendsto_slope' : Filter.Tendsto
      (fun t : ℝ => t⁻¹ * F_q q (1 + t))
      (nhdsWithin (0:ℝ) {0}ᶜ) (nhds L) := by
    have heq : (fun t : ℝ => t⁻¹ * (F_q q (1 + t) - F_q q 1)) =
        (fun t => t⁻¹ * F_q q (1 + t)) := by
      funext t; rw [hFq_one]; ring
    rw [heq] at htendsto_slope
    exact htendsto_slope
  -- Restrict to nhdsWithin 0 (Iio 0).
  have hsub : nhdsWithin (0:ℝ) (Set.Iio 0) ≤ nhdsWithin (0:ℝ) {0}ᶜ :=
    nhdsWithin_mono _ (fun x hx => ne_of_lt hx)
  have htendsto_left : Filter.Tendsto
      (fun t : ℝ => t⁻¹ * F_q q (1 + t))
      (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds L) :=
    htendsto_slope'.mono_left hsub
  -- Eventually the slope > L/2 > 0.
  have hL_half : 0 < L/2 := by linarith
  have hL_half_lt : L/2 < L := by linarith
  have h_evt_slope : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0),
      L/2 < t⁻¹ * F_q q (1 + t) :=
    htendsto_left.eventually (eventually_gt_nhds hL_half_lt)
  -- Eventually -1/2 < t (so 1 + t > 1/2 > 0).
  have h_evt_t_gt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0), -(1/2 : ℝ) < t := by
    have hneg : (-(1/2:ℝ)) < 0 := by norm_num
    have hev := (eventually_gt_nhds hneg : ∀ᶠ x in nhds (0:ℝ), -(1/2:ℝ) < x)
    exact hev.filter_mono nhdsWithin_le_nhds
  -- Membership: in nhdsWithin 0 (Iio 0), every t satisfies t < 0.
  have h_evt_t_lt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0), t < 0 := by
    rw [Filter.eventually_iff]
    exact self_mem_nhdsWithin
  -- NeBot for the filter.
  haveI hNeBot : (nhdsWithin (0:ℝ) (Set.Iio 0)).NeBot := nhdsLT_neBot 0
  -- Combine the three eventuallys, then extract a witness.
  obtain ⟨t, ht_slope, ht_lt, ht_gt⟩ : ∃ t,
      (L/2 < t⁻¹ * F_q q (1 + t)) ∧ (t < 0) ∧ (-(1/2 : ℝ) < t) := by
    have h_combined : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0),
        (L/2 < t⁻¹ * F_q q (1 + t)) ∧ (t < 0) ∧ (-(1/2 : ℝ) < t) :=
      h_evt_slope.and (h_evt_t_lt.and h_evt_t_gt)
    exact h_combined.exists
  -- Now construct a := 1 + t.
  have ha_pos : 0 < 1 + t := by linarith
  have ha_lt_one : 1 + t < 1 := by linarith
  -- F_q q (1 + t) < 0 from the slope info.
  have h_slope_pos : 0 < t⁻¹ * F_q q (1 + t) := lt_trans hL_half ht_slope
  have ht_inv_neg : t⁻¹ < 0 := inv_lt_zero.mpr ht_lt
  have hFq_neg : F_q q (1 + t) < 0 := by
    by_contra h
    push_neg at h
    have : t⁻¹ * F_q q (1 + t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht_inv_neg) h
    linarith
  set a₁ : ℝ := 1 + t with ha₁_def
  -- Step 2: Find s ∈ (0, a₁) with F_q s > 0.
  -- From FqSignAt0Pos: F_q tends to +∞ at 0+.
  have hTopAtZero : Filter.Tendsto (fun a => F_q q a) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    FqSignAt0Pos q hq
  -- ∃ s ∈ (0, a₁), F_q s > 0.
  have h_evt_top : ∀ᶠ a in nhdsWithin (0:ℝ) (Set.Ioi 0), 1 < F_q q a :=
    hTopAtZero.eventually (Filter.eventually_gt_atTop 1)
  have h_evt_lt_a : ∀ᶠ a in nhdsWithin (0:ℝ) (Set.Ioi 0), a < a₁ := by
    have hev : ∀ᶠ x in nhds (0:ℝ), x < a₁ := eventually_lt_nhds ha_pos
    exact hev.filter_mono nhdsWithin_le_nhds
  have h_evt_a_pos : ∀ᶠ a in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < a := by
    rw [Filter.eventually_iff]
    exact self_mem_nhdsWithin
  haveI hNeBotR : (nhdsWithin (0:ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  obtain ⟨s, hs_top, hs_lt, hs_pos⟩ : ∃ s,
      (1 < F_q q s) ∧ (s < a₁) ∧ (0 < s) := by
    have h := h_evt_top.and (h_evt_lt_a.and h_evt_a_pos)
    exact h.exists
  -- Step 3: Apply IVT to get a zero of F_q in (s, a₁).
  -- Use `intermediate_value_Ioo'`: a ≤ b, ContinuousOn f [a, b], Ioo (f b) (f a) ⊆ f '' Ioo a b.
  -- We have f(s) > 0 > f(a₁), so 0 ∈ Ioo (f a₁) (f s). Need ContinuousOn on [s, a₁].
  have hCont_on_Icc : ContinuousOn (fun a => F_q q a) (Set.Icc s a₁) := by
    apply hCont.mono
    intro x hx
    exact lt_of_lt_of_le hs_pos hx.1
  have hsub_lt : s ≤ a₁ := le_of_lt hs_lt
  have hzero_in : (0:ℝ) ∈ Set.Ioo (F_q q a₁) (F_q q s) := by
    refine ⟨hFq_neg, ?_⟩
    linarith
  have h_image : Set.Ioo (F_q q a₁) (F_q q s) ⊆ (fun a => F_q q a) '' Set.Ioo s a₁ :=
    intermediate_value_Ioo' hsub_lt hCont_on_Icc
  obtain ⟨c, hc_mem, hc_val⟩ := h_image hzero_in
  have hc_pos : 0 < c := lt_trans hs_pos hc_mem.1
  have hc_lt : c < 1 := lt_trans hc_mem.2 ha_lt_one
  -- So `c` is in (0, 1) with F_q q c = 0. Hence IsAStar q c.
  have hIsAStar_c : IsAStar q c := ⟨hc_pos, hc_lt, hc_val⟩
  -- Step 4: Uniqueness: at most one a satisfies IsAStar q a.
  have h_unique : ∀ a b : ℝ, IsAStar q a → IsAStar q b → a = b := by
    intro a b ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · -- a < b < 1, all zeros.
      have ha_pos := ha.1
      have ha_lt := ha.2.1
      have ha_zero := ha.2.2
      have hb_pos := hb.1
      have hb_lt := hb.2.1
      have hb_zero := hb.2.2
      have ha_in_Ioi : a ∈ Set.Ioi (0:ℝ) := ha_pos
      have hone_in_Ioi : (1:ℝ) ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr zero_lt_one
      have h_a_ne_one : a ≠ 1 := ne_of_lt (lt_trans hab hb_lt)
      have hb_in_seg : b ∈ openSegment ℝ a 1 := by
        rw [openSegment_eq_Ioo (lt_trans hab hb_lt)]
        exact ⟨hab, hb_lt⟩
      have h_lt_max : F_q q b < max (F_q q a) (F_q q 1) :=
        hStrictConv.lt_on_openSegment ha_in_Ioi hone_in_Ioi h_a_ne_one hb_in_seg
      rw [ha_zero, hFq_one, max_self] at h_lt_max
      linarith
    · -- b < a < 1, all zeros.
      have ha_pos := ha.1
      have ha_lt := ha.2.1
      have ha_zero := ha.2.2
      have hb_pos := hb.1
      have hb_lt := hb.2.1
      have hb_zero := hb.2.2
      have hb_in_Ioi : b ∈ Set.Ioi (0:ℝ) := hb_pos
      have hone_in_Ioi : (1:ℝ) ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr zero_lt_one
      have h_b_ne_one : b ≠ 1 := ne_of_lt (lt_trans hab ha_lt)
      have ha_in_seg : a ∈ openSegment ℝ b 1 := by
        rw [openSegment_eq_Ioo (lt_trans hab ha_lt)]
        exact ⟨hab, ha_lt⟩
      have h_lt_max : F_q q a < max (F_q q b) (F_q q 1) :=
        hStrictConv.lt_on_openSegment hb_in_Ioi hone_in_Ioi h_b_ne_one ha_in_seg
      rw [hb_zero, hFq_one, max_self] at h_lt_max
      linarith
  -- Step 5: Build ∃! a, IsAStar q a from existence + uniqueness.
  have h_exists_unique : ∃! a, IsAStar q a := by
    refine ⟨c, hIsAStar_c, ?_⟩
    intro y hy
    exact h_unique y c hy hIsAStar_c
  refine ⟨h_exists_unique, ?_⟩
  -- Step 6: IsAStar q (a_star q).
  have h_exists : ∃ a, IsAStar q a := h_exists_unique.exists
  unfold a_star
  rw [dif_pos h_exists]
  exact Classical.choose_spec h_exists
