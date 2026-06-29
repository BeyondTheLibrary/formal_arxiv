import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos

open Workspace.ProofLemmas.FqSignAt0Pos
open Filter Topology

theorem FqAtCOverQ_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun q : ℝ => F_q q (c/q)) Filter.atTop (nhds (1/c - 2)) := by
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- 1/q → 0
  have h_inv : Tendsto (fun q : ℝ => q⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h_one_div_q : Tendsto (fun q : ℝ => 1/q) atTop (nhds 0) := by
    simpa [one_div] using h_inv
  -- c/q → 0
  have h_c_div_q : Tendsto (fun q : ℝ => c/q) atTop (nhds 0) := by
    have : (0 : ℝ) = c * 0 := by ring
    rw [this]
    have hcq : Tendsto (fun q : ℝ => c * (1/q)) atTop (nhds (c * 0)) :=
      h_one_div_q.const_mul c
    convert hcq using 1
    funext q
    ring
  -- q^(1/q) → 1 (Mathlib's tendsto_rpow_div)
  have h_q_pow : Tendsto (fun q : ℝ => q ^ (1/q)) atTop (nhds 1) := tendsto_rpow_div
  -- c^(1/q) → 1 via continuity of (fun y => c^y) at 0
  have h_c_pow : Tendsto (fun q : ℝ => c ^ (1/q)) atTop (nhds 1) := by
    have hcont : Continuous (fun y : ℝ => c ^ y) := Real.continuous_const_rpow hc_ne
    have : Tendsto (fun y : ℝ => c ^ y) (nhds 0) (nhds (c ^ (0 : ℝ))) :=
      hcont.tendsto 0
    have hcomp : Tendsto (fun q : ℝ => c ^ (1/q)) atTop (nhds (c ^ (0 : ℝ))) :=
      this.comp h_one_div_q
    simpa using hcomp
  -- (c/q)^(1/q) → 1, eventually rewriting via div_rpow
  have h_pos : ∀ᶠ q : ℝ in atTop, 0 < q := eventually_gt_atTop 0
  have h_cq_pow : Tendsto (fun q : ℝ => (c/q) ^ (1/q)) atTop (nhds 1) := by
    have h_div : Tendsto (fun q : ℝ => c ^ (1/q) / q ^ (1/q)) atTop (nhds (1/1)) :=
      h_c_pow.div h_q_pow one_ne_zero
    have heq : (fun q : ℝ => (c/q) ^ (1/q)) =ᶠ[atTop]
        (fun q : ℝ => c ^ (1/q) / q ^ (1/q)) := by
      filter_upwards [h_pos] with q hq
      have hcle : (0:ℝ) ≤ c := le_of_lt hc
      have hqle : (0:ℝ) ≤ q := le_of_lt hq
      exact Real.div_rpow hcle hqle (1/q)
    have : Tendsto (fun q : ℝ => (c/q) ^ (1/q)) atTop (nhds (1/1)) :=
      Tendsto.congr' heq.symm h_div
    simpa using this
  -- (1/q) * (c/q)^((1-q)/q) → 1/c, using rewrite via Real.rpow_sub
  -- (c/q)^((1-q)/q) = (c/q)^(1/q - 1) = (c/q)^(1/q) / (c/q)
  -- So (1/q) * (c/q)^((1-q)/q) = (1/q) * (c/q)^(1/q) / (c/q) = (c/q)^(1/q) / c
  have h_main_term : Tendsto (fun q : ℝ => (1/q) * (c/q) ^ ((1-q)/q)) atTop (nhds (1/c)) := by
    have h_target : Tendsto (fun q : ℝ => (c/q) ^ (1/q) / c) atTop (nhds (1/c)) := by
      have : Tendsto (fun q : ℝ => (c/q) ^ (1/q) / c) atTop (nhds (1/c)) := by
        have h := h_cq_pow.div_const c
        simpa using h
      exact this
    -- show eventually equal
    have h_pos_c : ∀ᶠ q : ℝ in atTop, c < q := eventually_gt_atTop c
    have heq : (fun q : ℝ => (1/q) * (c/q) ^ ((1-q)/q)) =ᶠ[atTop]
        (fun q : ℝ => (c/q) ^ (1/q) / c) := by
      filter_upwards [h_pos, h_pos_c] with q hq hcq_lt
      have hq_pos : 0 < q := hq
      have hcq_pos : 0 < c/q := div_pos hc hq_pos
      have hexp : (1 - q) / q = 1/q - 1 := by
        field_simp
      rw [hexp]
      rw [Real.rpow_sub hcq_pos]
      rw [Real.rpow_one]
      -- Now goal: (1/q) * ((c/q)^(1/q) / (c/q)) = (c/q)^(1/q) / c
      field_simp
    exact Tendsto.congr' heq.symm h_target
  -- 2 * (1 - 1/q) * (c/q) → 0
  have h_lin : Tendsto (fun q : ℝ => 2 * (1 - 1/q) * (c/q)) atTop (nhds 0) := by
    have h1 : Tendsto (fun q : ℝ => 1 - 1/q) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub h_one_div_q
    have h1' : Tendsto (fun q : ℝ => 1 - 1/q) atTop (nhds 1) := by simpa using h1
    have h2 : Tendsto (fun q : ℝ => 2 * (1 - 1/q)) atTop (nhds (2 * 1)) :=
      h1'.const_mul 2
    have h2' : Tendsto (fun q : ℝ => 2 * (1 - 1/q)) atTop (nhds 2) := by simpa using h2
    have h3 : Tendsto (fun q : ℝ => 2 * (1 - 1/q) * (c/q)) atTop (nhds (2 * 0)) :=
      h2'.mul h_c_div_q
    simpa using h3
  -- 1/q → 0 already
  -- Constant -2
  -- Combine: 2*(1-1/q)*(c/q) + (1/q) * (c/q)^((1-q)/q) - 2 + 1/q
  have h_sum : Tendsto (fun q : ℝ =>
        2 * (1 - 1/q) * (c/q) + (1/q) * (c/q) ^ ((1-q)/q) - 2 + 1/q)
      atTop (nhds (0 + (1/c) - 2 + 0)) := by
    refine ((h_lin.add h_main_term).sub_const 2).add h_one_div_q
  have h_sum' : Tendsto (fun q : ℝ =>
        2 * (1 - 1/q) * (c/q) + (1/q) * (c/q) ^ ((1-q)/q) - 2 + 1/q)
      atTop (nhds (1/c - 2)) := by
    have : (0 : ℝ) + (1/c) - 2 + 0 = 1/c - 2 := by ring
    rw [this] at h_sum
    exact h_sum
  -- Now identify F_q q (c/q) with the sum
  have heq : (fun q : ℝ => F_q q (c/q)) =
      (fun q : ℝ => 2 * (1 - 1/q) * (c/q) + (1/q) * (c/q) ^ ((1-q)/q) - 2 + 1/q) := by
    funext q
    simp only [F_q]
  rw [heq]
  exact h_sum'
