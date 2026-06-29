import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LqNormPartialDerivative_NegBranch

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

/-- **Interior first-order condition — negative branch.**

Under the same hypotheses as `Claim1_RuleOutInterior`, suppose furthermore
`lqNorm q (p_star - f) > 0` and `lqNorm q p_star > 0`. Then for every
index `j` with `σ j = -1` and `p_star j < 0`, the first-order condition
holds:
`(f j - p_star j)^(q-1) / (lqNorm q (p_star - f))^(q-1)
  = λ · (-(p_star j))^(q-1) / (lqNorm q p_star)^(q-1)`.

Paper reference: Block 2, Steps 2.3.1–2.3.4 (KKT negative branch);
mirror of `InteriorFOC_Pos` with sign flips. -/
theorem InteriorFOC_Neg
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma : Fin d → ℝ) (hsigma_pm : ∀ j, sigma j = 1 ∨ sigma j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma j = 1 → 0 ≤ p_star j) ∧ (sigma j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma j = 1 → 0 ≤ p j) ∧ (sigma j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (hpf_pos : 0 < lqNorm q (fun k => p_star k - f k))
    (hp_pos : 0 < lqNorm q p_star)
    (j : Fin d) (hsig : sigma j = -1) (hpneg : p_star j < 0) :
    (f j - p_star j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
      = lambda * ((-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1)) := by
  -- Mirror of InteriorFOC_Pos with sign flips.
  -- Setup
  have hpj_neg : p_star j < 0 := hpneg
  have hfj_nn : 0 ≤ f j := hf_nn j
  -- y j = p_star j - f j < 0 since p_star j < 0 and f j ≥ 0
  have hyj_neg : p_star j - f j < 0 := by linarith
  have hfj_sub_pos : 0 < f j - p_star j := by linarith
  -- Define y := p_star - f
  set y : Fin d → ℝ := fun k => p_star k - f k with hy_def
  have hyj_neg' : y j < 0 := hyj_neg
  have hy_lq_pos : 0 < lqNorm q y := hpf_pos
  -- KEY ALGEBRAIC IDENTITY:
  -- (fun k => Function.update p_star j t k - f k) = Function.update y j (t - f j)
  have h_update_sub : ∀ t : ℝ,
      (fun k => Function.update p_star j t k - f k) = Function.update y j (t - f j) := by
    intro t
    funext k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
  -- Derivative of t ↦ lqNorm q (Function.update y j (t - f j)) at t = p_star j
  -- Step 1: t ↦ t - f j has derivative 1 at t = p_star j, with value (p_star j - f j) = y j
  have h_lin : HasDerivAt (fun t : ℝ => t - f j) 1 (p_star j) := by
    have := (hasDerivAt_id (p_star j)).sub_const (f j)
    convert this
  -- Step 2: t ↦ lqNorm q (Function.update y j t) has derivative
  -- -(-(y j))^(q-1) / (lqNorm q y)^(q-1) at t = y j
  have h_lq1 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update y j t))
      (-(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (y j) :=
    LqNormPartialDerivative_NegBranch hq hd y j hyj_neg' hy_lq_pos
  -- Compose: t ↦ lqNorm q (Function.update y j (t - f j))
  -- has derivative the same value at t = p_star j (since 1 * x = x)
  have h_yj_eq : y j = p_star j - f j := by simp [hy_def]
  have h_comp1 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update y j (t - f j)))
      (-(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (p_star j) := by
    have h_at : (p_star j) - f j = y j := h_yj_eq.symm
    have := HasDerivAt.comp (p_star j) (h_at ▸ h_lq1) h_lin
    have h_simp : -(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1) * 1 =
                  -(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1) := by ring
    rw [← h_simp]
    exact this
  -- Now rewrite the result in terms of p_star - f
  have h_deriv1 : HasDerivAt (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
      (-(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (p_star j) := by
    have h_eq : (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
              = (fun t : ℝ => lqNorm q (Function.update y j (t - f j))) := by
      funext t
      rw [h_update_sub t]
    rw [h_eq]
    exact h_comp1
  -- Derivative of t ↦ lqNorm q (Function.update p_star j t) at t = p_star j
  have h_deriv2 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update p_star j t))
      (-(-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1)) (p_star j) :=
    LqNormPartialDerivative_NegBranch hq hd p_star j hpneg hp_pos
  -- Combine: derivative of φ(t) = g_lambda q lambda f (Function.update p_star j t)
  -- equals (deriv1) - lambda * (deriv2)
  set D1 : ℝ := -(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1) with hD1_def
  set D2 : ℝ := -(-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1) with hD2_def
  have h_phi_deriv : HasDerivAt
      (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t))
      (D1 - lambda * D2) (p_star j) := by
    unfold g_lambda
    exact h_deriv1.sub (h_deriv2.const_mul lambda)
  -- Now show: φ has a local min at p_star j
  obtain ⟨ε, hε_pos, hε_min⟩ := hp_loc
  have h_local_min :
      IsLocalMin (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t)) (p_star j) := by
    rw [IsLocalMin, IsMinFilter]
    have h_eventually_close : ∀ᶠ t in nhds (p_star j), |t - p_star j| < ε := by
      filter_upwards [eventually_abs_sub_lt (p_star j) hε_pos] with t ht
      exact ht
    -- We need t < 0 in a neighborhood of p_star j (since p_star j < 0)
    have h_eventually_neg : ∀ᶠ t in nhds (p_star j), t < 0 := eventually_lt_nhds hpneg
    filter_upwards [h_eventually_close, h_eventually_neg] with t ht_close ht_neg
    show g_lambda q lambda f (Function.update p_star j (p_star j)) ≤
         g_lambda q lambda f (Function.update p_star j t)
    rw [Function.update_eq_self]
    apply hε_min (Function.update p_star j t)
    · -- Orthant condition
      intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        refine ⟨fun hcontr => ?_, fun _ => le_of_lt ht_neg⟩
        rw [hsig] at hcontr; linarith
      · rw [Function.update_of_ne hk]
        exact hp_in k
    · -- Distance condition: |p k - p_star k| < ε for all k
      intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact ht_close
      · rw [Function.update_of_ne hk]
        simp only [sub_self, abs_zero]
        exact hε_pos
  -- Apply IsLocalMin.hasDerivAt_eq_zero
  have h_zero : D1 - lambda * D2 = 0 := h_local_min.hasDerivAt_eq_zero h_phi_deriv
  -- D1 = lambda * D2
  have hD1_eq_D2 : D1 = lambda * D2 := by linarith
  -- Now translate back to the goal statement
  -- D1 = -(-(y j))^(q-1) / (lqNorm q y)^(q-1)
  -- We have y j = p_star j - f j, so -(y j) = f j - p_star j
  -- Goal: (f j - p_star j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
  --     = lambda * ((-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1))
  -- Note D1 = -((f j - p_star j))^(q-1) / (lqNorm q y)^(q-1)
  --      D2 = -(-(p_star j))^(q-1) / (lqNorm q p_star)^(q-1)
  -- So D1 = lambda * D2 means:
  --   -(f j - p_star j)^(q-1) / D₁norm = lambda * -(-(p_star j))^(q-1) / D₂norm
  -- Multiply both sides by -1:
  --   (f j - p_star j)^(q-1) / D₁norm = lambda * (-(p_star j))^(q-1) / D₂norm
  show (f j - p_star j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
      = lambda * ((-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1))
  have h_y_lq : lqNorm q y = lqNorm q (fun k => p_star k - f k) := rfl
  have h_neg_yj : -(y j) = f j - p_star j := by show -(p_star j - f j) = f j - p_star j; ring
  -- Rewrite D1 using -(y j) = f j - p_star j
  have hD1_rewrite : D1 = -((f j - p_star j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)) := by
    show -(-(y j)) ^ (q - 1) / (lqNorm q y) ^ (q - 1) = _
    rw [h_neg_yj, h_y_lq]
    ring
  -- Rewrite D2
  have hD2_rewrite : D2 = -((-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1)) := by
    show -(-(p_star j)) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1) = _
    ring
  rw [hD1_rewrite, hD2_rewrite] at hD1_eq_D2
  linarith
