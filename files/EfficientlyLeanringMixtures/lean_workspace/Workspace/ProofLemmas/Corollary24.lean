import Mathlib
import Workspace.Types.GaussianPDF

namespace Workspace.ProofLemmas

/--
Helper: for every real `t`, `t * Real.exp (-t) ≤ 1`.

Proof: from `t ≤ t + 1 ≤ Real.exp t` (and `Real.exp t > 0`).
Multiply both sides by `Real.exp (-t) > 0`.
-/
private lemma aux_t_mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  have h1 : t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have hexp_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt hexp_pos)
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  linarith

theorem Corollary24 :
    ∀ r : ℝ, 0 < r →
      ∀ (G : Workspace.Types.GaussianPDF.GaussianPDF), G.mean = 0 →
        ∀ y : ℝ, r ≤ |y| →
          G.density y ≤ 1 / (r * Real.sqrt (2 * Real.pi)) := by
  intro r hr G hG_mean y hry
  have hσ2_pos : 0 < G.varSq := G.varSq_pos
  set σ := Real.sqrt G.varSq with hσ_def
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hσ2_pos
  have hσ_sq : σ * σ = G.varSq := Real.mul_self_sqrt (le_of_lt hσ2_pos)
  have hσ_sq' : σ ^ 2 = G.varSq := by rw [sq]; exact hσ_sq
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hy_pos : 0 < |y| := lt_of_lt_of_le hr hry
  -- Sqrt of the product.
  have hsqrt_prod : Real.sqrt (2 * Real.pi * G.varSq) = Real.sqrt (2 * Real.pi) * σ := by
    rw [Real.sqrt_mul (le_of_lt h2pi_pos)]
  -- Unfold the density.
  have hdensity : G.density y =
      Real.exp (-y^2 / (2 * G.varSq)) / (Real.sqrt (2 * Real.pi) * σ) := by
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq, hG_mean, sub_zero,
        hsqrt_prod]
    ring
  rw [hdensity]
  -- Step 1: `1/(|y|√(2π)) ≤ 1/(r√(2π))` since |y| ≥ r > 0.
  have step1 : 1 / (|y| * Real.sqrt (2 * Real.pi)) ≤ 1 / (r * Real.sqrt (2 * Real.pi)) := by
    apply one_div_le_one_div_of_le (mul_pos hr hsqrt_2pi_pos)
    exact mul_le_mul_of_nonneg_right hry (le_of_lt hsqrt_2pi_pos)
  -- Step 2: `exp(-y²/(2G.varSq))/(√(2π)·σ) ≤ 1/(|y|·√(2π))`.
  have step2 :
      Real.exp (-y^2 / (2 * G.varSq)) / (Real.sqrt (2 * Real.pi) * σ)
        ≤ 1 / (|y| * Real.sqrt (2 * Real.pi)) := by
    rw [div_le_div_iff₀ (mul_pos hsqrt_2pi_pos hσ_pos)
          (mul_pos hy_pos hsqrt_2pi_pos)]
    -- Goal: exp(...) * (|y| * √(2π)) ≤ 1 * (√(2π) * σ)
    have key : |y| * Real.exp (-y^2 / (2 * G.varSq)) ≤ σ := by
      have hy_abs_sq : |y|^2 = y^2 := sq_abs y
      have hexp_nonneg : 0 ≤ Real.exp (-y^2 / (2 * G.varSq)) := le_of_lt (Real.exp_pos _)
      have hLHS_nonneg : 0 ≤ |y| * Real.exp (-y^2 / (2 * G.varSq)) :=
        mul_nonneg (le_of_lt hy_pos) hexp_nonneg
      -- Use `aux_t_mul_exp_neg_le_one` with t = y²/G.varSq.
      have ht_le_one : (y^2 / G.varSq) * Real.exp (-(y^2/G.varSq)) ≤ 1 :=
        aux_t_mul_exp_neg_le_one (y^2/G.varSq)
      -- Squared: (|y|·exp(...))² = y²·exp(-y²/G.varSq).
      have sq_ineq : (|y| * Real.exp (-y^2 / (2 * G.varSq)))^2 ≤ σ^2 := by
        rw [mul_pow, hy_abs_sq, hσ_sq']
        have hexp_sq : (Real.exp (-y^2 / (2 * G.varSq)))^2 = Real.exp (-y^2 / G.varSq) := by
          rw [sq, ← Real.exp_add]
          congr 1
          have h2pos : (2 : ℝ) * G.varSq ≠ 0 := by positivity
          have hg : G.varSq ≠ 0 := ne_of_gt hσ2_pos
          field_simp
          ring
        rw [hexp_sq]
        -- Show y² · exp(-y²/G.varSq) ≤ G.varSq.
        have hstep := mul_le_mul_of_nonneg_left ht_le_one (le_of_lt hσ2_pos)
        rw [mul_one] at hstep
        -- LHS = G.varSq * ((y²/G.varSq) * exp(-(y²/G.varSq))) = y² * exp(-y²/G.varSq)
        have hg_ne : G.varSq ≠ 0 := ne_of_gt hσ2_pos
        have hrewrite : G.varSq * (y^2 / G.varSq * Real.exp (-(y^2 / G.varSq)))
            = y^2 * Real.exp (-y^2 / G.varSq) := by
          rw [show -(y^2 / G.varSq) = -y^2 / G.varSq from by ring]
          field_simp
        rw [hrewrite] at hstep
        exact hstep
      have := Real.sqrt_le_sqrt sq_ineq
      rw [Real.sqrt_sq hLHS_nonneg, Real.sqrt_sq (le_of_lt hσ_pos)] at this
      exact this
    have hrearrange : Real.exp (-y^2 / (2 * G.varSq)) * (|y| * Real.sqrt (2 * Real.pi))
        = (|y| * Real.exp (-y^2 / (2 * G.varSq))) * Real.sqrt (2 * Real.pi) := by ring
    rw [hrearrange]
    rw [show (1 : ℝ) * (Real.sqrt (2 * Real.pi) * σ) = σ * Real.sqrt (2 * Real.pi) from by ring]
    exact mul_le_mul_of_nonneg_right key (le_of_lt hsqrt_2pi_pos)
  linarith

end Workspace.ProofLemmas
