import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqStrictConvex

open Workspace.ProofLemmas.FqSignAt0Pos

theorem FqDerivMonotone (q : ℝ) (hq : 1 < q) :
    StrictMonoOn (deriv (fun a => F_q q a)) (Set.Ioi (0 : ℝ)) ∧
      Filter.Tendsto (deriv (fun a => F_q q a)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot ∧
      Filter.Tendsto (deriv (fun a => F_q q a)) Filter.atTop (nhds (2 * (1 - 1/q))) := by
  set p : ℝ := (1 - q) / q with hp_def
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_inv_pos : 0 < 1 / q := by positivity
  have hp_neg : p < 0 := by
    have h1 : 1 - q < 0 := by linarith
    exact div_neg_of_neg_of_pos h1 hq_pos
  have hp_minus_one_neg : p - 1 < 0 := by linarith
  set c1 : ℝ := 2 * (1 - 1 / q) with hc1_def
  set c2 : ℝ := 1 / q with hc2_def
  set c3 : ℝ := -2 + 1 / q with hc3_def
  -- Rewrite F_q q a = c1 * a + c2 * a^p + c3.
  have hFq_eq : ∀ a : ℝ, F_q q a = c1 * a + c2 * a ^ p + c3 := by
    intro a
    simp [F_q, c1, c2, c3, p]
    ring
  -- Pointwise derivative on Ioi 0.
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
    have hcongr : (fun y : ℝ => F_q q y) = (fun y => c1 * y + c2 * y ^ p + c3) := by
      funext y
      exact hFq_eq y
    rw [hcongr]
    exact hd_const
  -- DifferentiableAt for each a ∈ Ioi 0.
  have hDiff : ∀ a ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun a => F_q q a) a := by
    intro a ha
    exact (hFq_deriv a ha).differentiableAt
  -- The derivative formula: deriv F_q a = c1 + c2 * (p * a^(p-1)) for a ∈ Ioi 0.
  have hDerivEq : ∀ a ∈ Set.Ioi (0 : ℝ),
      deriv (fun a => F_q q a) a = c1 + c2 * (p * a ^ (p - 1)) := by
    intro a ha
    exact (hFq_deriv a ha).deriv
  refine ⟨?_, ?_, ?_⟩
  · -- StrictMonoOn (deriv F_q) (Ioi 0): use FqStrictConvex.
    have hConv : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun a => F_q q a) :=
      FqStrictConvex q hq
    exact hConv.strictMonoOn_deriv hDiff
  · -- Tendsto deriv F_q at 0+ to atBot.
    -- deriv F_q =ᶠ[nhdsWithin 0 (Ioi 0)] (fun a => c1 + (c2 * p) * a^(p-1))
    have hK_neg : c2 * p < 0 := by
      have : c2 > 0 := hq_inv_pos
      exact mul_neg_of_pos_of_neg this hp_neg
    -- Eventually equal on nhdsWithin 0 (Ioi 0).
    have hEv : (fun a => deriv (fun a => F_q q a) a) =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        (fun a => c1 + (c2 * p) * a ^ (p - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha_pos : (0:ℝ) < a := ha
      rw [hDerivEq a ha_pos]
      ring
    -- (fun a => a^(p-1)) tends to atTop on nhdsWithin 0 (Ioi 0).
    have hTendsRpow : Filter.Tendsto (fun a : ℝ => a ^ (p - 1))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
      tendsto_rpow_neg_nhdsGT_zero hp_minus_one_neg
    -- (fun a => a^(p-1) * (c2 * p)) tends to atBot.
    have hTendsMul : Filter.Tendsto (fun a : ℝ => a ^ (p - 1) * (c2 * p))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
      hTendsRpow.atTop_mul_const_of_neg hK_neg
    -- Convert (fun a => a^(p-1) * (c2 * p)) ↦ (fun a => (c2 * p) * a^(p-1)).
    have hTendsMul' : Filter.Tendsto (fun a : ℝ => (c2 * p) * a ^ (p - 1))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot := by
      convert hTendsMul using 1
      funext a
      ring
    -- Add c1 on the left → atBot.
    have hTendsAdd : Filter.Tendsto (fun a : ℝ => c1 + (c2 * p) * a ^ (p - 1))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
      Filter.tendsto_atBot_add_const_left _ c1 hTendsMul'
    -- Use EventuallyEq.
    exact hTendsAdd.congr' hEv.symm
  · -- Tendsto deriv F_q at atTop to nhds (2 * (1 - 1/q)) = nhds c1.
    have hEv : (fun a => deriv (fun a => F_q q a) a) =ᶠ[(Filter.atTop : Filter ℝ)]
        (fun a => c1 + (c2 * p) * a ^ (p - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha_pos
      rw [hDerivEq a ha_pos]
      ring
    -- (fun a => a^(p-1)) → 0 at atTop.
    have hTendsRpow : Filter.Tendsto (fun a : ℝ => a ^ (p - 1))
        Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun a : ℝ => a ^ (-(1 - p))) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      convert this using 1
      funext a
      congr 1
      ring
    -- (c2 * p) * a^(p-1) → 0.
    have hTendsConstMul : Filter.Tendsto (fun a : ℝ => (c2 * p) * a ^ (p - 1))
        Filter.atTop (nhds ((c2 * p) * 0)) :=
      hTendsRpow.const_mul (c2 * p)
    have hTendsConstMul0 : Filter.Tendsto (fun a : ℝ => (c2 * p) * a ^ (p - 1))
        Filter.atTop (nhds 0) := by
      simpa using hTendsConstMul
    -- c1 + (c2 * p) * a^(p-1) → c1 + 0 = c1.
    have hTendsAdd : Filter.Tendsto (fun a : ℝ => c1 + (c2 * p) * a ^ (p - 1))
        Filter.atTop (nhds (c1 + 0)) :=
      hTendsConstMul0.const_add c1
    have hTendsAdd' : Filter.Tendsto (fun a : ℝ => c1 + (c2 * p) * a ^ (p - 1))
        Filter.atTop (nhds c1) := by simpa using hTendsAdd
    -- The goal target is `nhds (2 * (1 - 1/q))` = `nhds c1` (set substituted).
    exact hTendsAdd'.congr' hEv.symm
