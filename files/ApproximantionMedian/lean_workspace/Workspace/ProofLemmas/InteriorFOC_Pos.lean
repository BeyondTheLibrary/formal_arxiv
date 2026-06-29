import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LqNormPartialDerivative_PosBranch

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem InteriorFOC_Pos
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
    (j : Fin d) (hsig : sigma j = 1) (hpf : f j < p_star j) :
    (p_star j - f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
      = lambda * ((p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1)) := by
  -- Strategy: restrict g_lambda to the line through p_star in direction e_j and
  -- apply IsLocalMin.hasDerivAt_eq_zero.
  -- Setup
  have hpj_pos : 0 < p_star j := lt_of_le_of_lt (hf_nn j) hpf
  have hpfj_pos : 0 < p_star j - f j := sub_pos.mpr hpf
  -- Define y := p_star - f and y' := p_star (so we can apply LqNormPartialDerivative_PosBranch)
  set y : Fin d → ℝ := fun k => p_star k - f k with hy_def
  have hyj_pos : 0 < y j := hpfj_pos
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
  -- (y j)^(q-1) / (lqNorm q y)^(q-1) at t = y j = p_star j - f j
  have h_lq1 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update y j t))
      ((y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (y j) :=
    LqNormPartialDerivative_PosBranch hq hd y j hyj_pos hy_lq_pos
  -- Compose: t ↦ lqNorm q (Function.update y j (t - f j))
  -- has derivative ((y j)^(q-1)/(lqNorm q y)^(q-1)) * 1 at t = p_star j
  -- (since t - f j evaluated at p_star j gives p_star j - f j = y j)
  have h_yj_eq : y j = p_star j - f j := by simp [hy_def]
  have h_comp1 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update y j (t - f j)))
      ((y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (p_star j) := by
    have h_at : (p_star j) - f j = y j := h_yj_eq.symm
    have := HasDerivAt.comp (p_star j) (h_at ▸ h_lq1) h_lin
    -- this : HasDerivAt ((fun t => lqNorm q (Function.update y j t)) ∘ (fun t => t - f j))
    --   ((y j)^(q-1)/(lqNorm q y)^(q-1) * 1) (p_star j)
    have h_simp : (y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1) * 1 =
                  (y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1) := by ring
    rw [← h_simp]
    exact this
  -- Now rewrite the result in terms of p_star - f
  have h_deriv1 : HasDerivAt (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
      ((y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1)) (p_star j) := by
    have h_eq : (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
              = (fun t : ℝ => lqNorm q (Function.update y j (t - f j))) := by
      funext t
      rw [h_update_sub t]
    rw [h_eq]
    exact h_comp1
  -- Derivative of t ↦ lqNorm q (Function.update p_star j t) at t = p_star j
  have h_deriv2 : HasDerivAt (fun t : ℝ => lqNorm q (Function.update p_star j t))
      ((p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1)) (p_star j) :=
    LqNormPartialDerivative_PosBranch hq hd p_star j hpj_pos hp_pos
  -- Combine: derivative of φ(t) = g_lambda q lambda f (Function.update p_star j t)
  -- equals (deriv1) - lambda * (deriv2)
  set D1 : ℝ := (y j) ^ (q - 1) / (lqNorm q y) ^ (q - 1) with hD1_def
  set D2 : ℝ := (p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1) with hD2_def
  have h_phi_deriv : HasDerivAt
      (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t))
      (D1 - lambda * D2) (p_star j) := by
    unfold g_lambda
    exact h_deriv1.sub (h_deriv2.const_mul lambda)
  -- Now show: φ has a local min at p_star j
  obtain ⟨ε, hε_pos, hε_min⟩ := hp_loc
  -- Pick δ = min(ε, p_star j)
  have h_local_min :
      IsLocalMin (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t)) (p_star j) := by
    -- We need: ∀ᶠ t in nhds (p_star j), φ (p_star j) ≤ φ t
    rw [IsLocalMin, IsMinFilter]
    -- Want: ∀ᶠ t in nhds (p_star j), g_lambda q lambda f p_star ≤ g_lambda q lambda f (Function.update p_star j t)
    -- Note: Function.update p_star j (p_star j) = p_star.
    have h_eventually_close : ∀ᶠ t in nhds (p_star j), |t - p_star j| < ε := by
      filter_upwards [eventually_abs_sub_lt (p_star j) hε_pos] with t ht
      exact ht
    -- Also need t in (p_star j - p_star j, ∞) i.e. t > 0 for j coordinate
    have h_eventually_pos : ∀ᶠ t in nhds (p_star j), 0 < t := eventually_gt_nhds hpj_pos
    filter_upwards [h_eventually_close, h_eventually_pos] with t ht_close ht_pos
    -- Apply hε_min to p := Function.update p_star j t
    -- After update_self, Function.update p_star j (p_star j) = p_star
    show g_lambda q lambda f (Function.update p_star j (p_star j)) ≤
         g_lambda q lambda f (Function.update p_star j t)
    rw [Function.update_eq_self]
    apply hε_min (Function.update p_star j t)
    · -- Orthant condition
      intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        refine ⟨fun _ => le_of_lt ht_pos, fun hcontr => ?_⟩
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
  -- Rewrite to obtain the goal
  -- Goal: D1 = lambda * D2
  have hD1_eq_D2 : D1 = lambda * D2 := by linarith
  -- Now translate back to the goal statement
  show (p_star j - f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
      = lambda * ((p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1))
  have h_y_lq : lqNorm q y = lqNorm q (fun k => p_star k - f k) := rfl
  rw [← h_yj_eq, ← h_y_lq]
  exact hD1_eq_D2
