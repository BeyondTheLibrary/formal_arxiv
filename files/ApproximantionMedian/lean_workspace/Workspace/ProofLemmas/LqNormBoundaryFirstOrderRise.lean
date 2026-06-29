import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.LqNormBoundaryUpwardExpansion

open Workspace.Types.LqNorm

theorem LqNormBoundaryFirstOrderRise
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (x : Fin d → ℝ) (j : Fin d)
    (hxj_zero : x j = 0) (hlq_pos : 0 < lqNorm q x) :
    ∃ delta0 > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ delta ∈ Set.Ioo (0 : ℝ) delta0,
        lqNorm q (Function.update x j delta)
          ≤ lqNorm q x + C * delta ^ q := by
  -- Set up the basic constants and positivity facts.
  set M : ℝ := lqNorm q x with hM_def
  have hM_pos : 0 < M := hlq_pos
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_nn : 0 ≤ q := le_of_lt hq_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hinvq_pos : 0 < 1 / q := by positivity
  have hinvq_le_one : 1 / q ≤ 1 := by
    rw [div_le_one hq_pos]; exact le_of_lt hq
  have hinvq_nn : 0 ≤ 1 / q := le_of_lt hinvq_pos
  -- M^q > 0 and M^(q-1) > 0
  have hMq_pos : 0 < M ^ q := Real.rpow_pos_of_pos hM_pos q
  have hMq_nn : 0 ≤ M ^ q := le_of_lt hMq_pos
  have hMq_ne : M ^ q ≠ 0 := ne_of_gt hMq_pos
  have hMqm1_pos : 0 < M ^ (q - 1) := Real.rpow_pos_of_pos hM_pos (q - 1)
  have hMqm1_ne : M ^ (q - 1) ≠ 0 := ne_of_gt hMqm1_pos
  -- Useful identity: (M^q)^(1/q) = M
  have hMq_invq : (M ^ q) ^ ((1 : ℝ) / q) = M := by
    rw [← Real.rpow_mul hM_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
  -- Useful: M^q = M^(q-1) * M
  have hMq_split : M ^ q = M ^ (q - 1) * M := by
    have : M ^ (q - 1) * M ^ (1 : ℝ) = M ^ ((q - 1) + 1) :=
      (Real.rpow_add hM_pos _ _).symm
    rw [Real.rpow_one] at this
    rw [this]
    ring_nf
  -- Choose C = 1 / (q * M^(q-1))
  refine ⟨1, by norm_num, 1 / (q * M ^ (q - 1)), ?_, ?_⟩
  · -- C > 0
    apply div_pos zero_lt_one
    exact mul_pos hq_pos hMqm1_pos
  · -- The main inequality, for all δ ∈ (0, 1)
    intro delta hdelta
    obtain ⟨hdelta_pos, hdelta_lt⟩ := hdelta
    have hdelta_nn : 0 ≤ delta := le_of_lt hdelta_pos
    have hdq_pos : 0 < delta ^ q := Real.rpow_pos_of_pos hdelta_pos q
    have hdq_nn : 0 ≤ delta ^ q := le_of_lt hdq_pos
    -- Use UpwardExpansion to rewrite the LHS.
    have hexp : lqNorm q (Function.update x j delta)
                  = (M ^ q + delta ^ q) ^ ((1 : ℝ) / q) :=
      LqNormBoundaryUpwardExpansion hq hd x j delta hdelta_nn hxj_zero
    rw [hexp]
    -- Factor (M^q + δ^q) = M^q * (1 + δ^q / M^q)
    have hfactor : M ^ q + delta ^ q = M ^ q * (1 + delta ^ q / M ^ q) := by
      field_simp
    rw [hfactor]
    -- (M^q * (1 + δ^q/M^q))^(1/q) = (M^q)^(1/q) * (1 + δ^q/M^q)^(1/q)
    have hsdef : delta ^ q / M ^ q ≥ 0 := div_nonneg hdq_nn hMq_nn
    have h1pos : (0 : ℝ) ≤ 1 + delta ^ q / M ^ q := by linarith
    rw [Real.mul_rpow hMq_nn h1pos]
    rw [hMq_invq]
    -- Apply Bernoulli-type bound: (1 + s)^(1/q) ≤ 1 + (1/q)*s for s ≥ -1
    set s : ℝ := delta ^ q / M ^ q with hs_def
    have hs_ge : -1 ≤ s := by
      have : (0 : ℝ) ≤ s := hsdef
      linarith
    have hbern : (1 + s) ^ ((1 : ℝ) / q) ≤ 1 + (1 / q) * s :=
      rpow_one_add_le_one_add_mul_self hs_ge hinvq_nn hinvq_le_one
    have hbound : M * (1 + s) ^ ((1 : ℝ) / q) ≤ M * (1 + (1 / q) * s) :=
      mul_le_mul_of_nonneg_left hbern hM_nn
    refine le_trans hbound ?_
    -- Now show M * (1 + (1/q) * s) ≤ M + (1/(q*M^(q-1))) * δ^q
    -- Actually equality holds.
    have hgoal : M * (1 + (1 / q) * s) = M + (1 / (q * M ^ (q - 1))) * delta ^ q := by
      show M * (1 + (1 / q) * (delta ^ q / M ^ q))
            = M + (1 / (q * M ^ (q - 1))) * delta ^ q
      rw [hMq_split]
      field_simp
    linarith
