import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.LqNormStrictDecrease_OfSingleCoordinateCloser
import Workspace.ProofLemmas.LqNormBoundaryFirstOrderRise
import Workspace.ProofLemmas.LqNormBoundaryUpwardExpansion

open scoped BigOperators
open Workspace.Types.LqNorm

theorem PerturbAtZero_StrictDescent
    {q : ℝ} (hq : 1 < q) {lambda : ℝ} (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_norm : lqNorm q f = 1)
    (sigma : Fin d → ℝ) (hsigma_pm : ∀ j, sigma j = 1 ∨ sigma j = -1)
    (hS_pos : ∃ k, sigma k = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ tildep : Fin d → ℝ,
      (∀ j, (sigma j = 1 → 0 ≤ tildep j) ∧ (sigma j = -1 → tildep j ≤ 0)) ∧
      (∀ j, |tildep j| < ε) ∧
      lqNorm q (fun k => tildep k - f k) - lambda * lqNorm q tildep
        < lqNorm q (fun k => -(f k)) := by
  -- Basic positivity of q
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  -- Pick k with σ k = 1
  obtain ⟨k, hsigma_k⟩ := hS_pos
  -- lqNorm q (fun k => -(f k)) = lqNorm q f = 1
  have hlq_neg_f : lqNorm q (fun k => -(f k)) = lqNorm q f := by
    unfold lqNorm
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_neg]
  have hlq_neg_f_eq_one : lqNorm q (fun k => -(f k)) = 1 := by
    rw [hlq_neg_f, hf_norm]
  -- A helper: lqNorm q (Function.update (fun _ => 0) k δ) = δ for δ ≥ 0
  have hnorm_update_zero : ∀ delta : ℝ, 0 ≤ delta →
      lqNorm q (Function.update (fun _ : Fin d => (0 : ℝ)) k delta) = delta := by
    intro delta hdelta_nn
    have h_zero_k : (fun _ : Fin d => (0 : ℝ)) k = 0 := rfl
    have hexp : lqNorm q (Function.update (fun _ : Fin d => (0 : ℝ)) k delta)
        = ((lqNorm q (fun _ : Fin d => (0 : ℝ))) ^ q + delta ^ q) ^ ((1 : ℝ) / q) :=
      LqNormBoundaryUpwardExpansion hq hd (fun _ : Fin d => (0 : ℝ)) k delta hdelta_nn h_zero_k
    rw [hexp, lqNorm_zero hq_le]
    rw [Real.zero_rpow hq_ne, zero_add]
    rw [← Real.rpow_mul hdelta_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
  -- Case split on whether f k > 0 or f k = 0
  by_cases hfk_pos : 0 < f k
  · -- ============= Case 1: f k > 0 =============
    -- Pick δ := min(ε, f k) / 2
    set δ := min ε (f k) / 2 with hδ_def
    have hδ_pos : 0 < δ := by
      apply div_pos
      · exact lt_min hε hfk_pos
      · norm_num
    have hδ_lt_ε : δ < ε := by
      have h1 : δ ≤ min ε (f k) / 1 := by
        rw [div_one]; rw [hδ_def]; linarith [min_le_left ε (f k), min_le_right ε (f k)]
      have h2 : min ε (f k) ≤ ε := min_le_left _ _
      have : min ε (f k) / 2 < min ε (f k) := by
        have : min ε (f k) > 0 := lt_min hε hfk_pos
        linarith
      linarith
    have hδ_lt_fk : δ < f k := by
      have hmin : min ε (f k) ≤ f k := min_le_right _ _
      have hpos : 0 < min ε (f k) := lt_min hε hfk_pos
      linarith
    have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
    -- Define tildep
    refine ⟨Function.update (fun _ : Fin d => (0 : ℝ)) k δ, ?_, ?_, ?_⟩
    · -- Orthant condition
      intro j
      refine ⟨?_, ?_⟩
      · intro _
        by_cases hj : j = k
        · subst hj; rw [Function.update_self]; exact hδ_nn
        · rw [Function.update_of_ne hj]
      · intro hsj
        by_cases hj : j = k
        · subst hj
          -- sigma k = 1 and sigma k = -1 simultaneously is impossible
          rw [hsigma_k] at hsj; norm_num at hsj
        · rw [Function.update_of_ne hj]
    · -- |tildep j| < ε
      intro j
      by_cases hj : j = k
      · subst hj; rw [Function.update_self]; rw [abs_of_nonneg hδ_nn]; exact hδ_lt_ε
      · rw [Function.update_of_ne hj]; rw [abs_zero]; exact hε
    · -- Strict descent
      -- lqNorm q (tildep - f) < lqNorm q (-f) using LqNormStrictDecrease_OfSingleCoordinateCloser
      have h_strict_dec :
          lqNorm q (fun j => Function.update (fun _ : Fin d => (0 : ℝ)) k δ j - f j)
            < lqNorm q (fun j => (fun _ : Fin d => (0 : ℝ)) j - f j) := by
        apply LqNormStrictDecrease_OfSingleCoordinateCloser hq hd
            (fun _ : Fin d => (0 : ℝ)) (Function.update (fun _ : Fin d => (0 : ℝ)) k δ) f k
        · intro j hj
          rw [Function.update_of_ne hj]
        · -- |tildep k - f k| < |0 - f k|
          rw [Function.update_self]
          rw [zero_sub]
          rw [abs_neg, abs_of_nonneg (hf_nn k)]
          rw [abs_of_nonpos (by linarith : δ - f k ≤ 0)]
          linarith
      -- Rewrite (fun j => 0 - f j) = (fun j => -(f j))
      have h_zero_sub : (fun j : Fin d => (fun _ : Fin d => (0 : ℝ)) j - f j) =
                        (fun j : Fin d => -(f j)) := by
        funext j; rw [zero_sub]
      rw [h_zero_sub] at h_strict_dec
      -- lqNorm q tildep ≥ 0
      have hlq_tildep_nn : 0 ≤ lqNorm q (Function.update (fun _ : Fin d => (0 : ℝ)) k δ) :=
        lqNorm_nonneg hq_le _
      have h_lambda_norm_nn :
          0 ≤ lambda * lqNorm q (Function.update (fun _ : Fin d => (0 : ℝ)) k δ) :=
        mul_nonneg (le_of_lt hlam0) hlq_tildep_nn
      linarith
  · -- ============= Case 2: f k = 0 =============
    push_neg at hfk_pos
    have hfk_eq_zero : f k = 0 := le_antisymm hfk_pos (hf_nn k)
    -- Apply LqNormBoundaryFirstOrderRise to x = -f at coordinate k
    have h_neg_f_k_zero : (fun j => -(f j)) k = 0 := by simp [hfk_eq_zero]
    have hlq_neg_f_pos : 0 < lqNorm q (fun j => -(f j)) := by
      rw [hlq_neg_f_eq_one]; norm_num
    obtain ⟨delta0, hdelta0_pos, C, hC_pos, hbound⟩ :=
      LqNormBoundaryFirstOrderRise hq hd (fun j => -(f j)) k h_neg_f_k_zero hlq_neg_f_pos
    -- Now choose δ small enough:
    --   0 < δ < δ0, δ < ε, δ < (λ / (2C))^(1/(q-1))   (so C * δ^q < λ * δ)
    -- A simple bound: pick δ ≤ (λ / (2C)) for the last condition? Actually we need
    --   C * δ^q < λ * δ ⇔ δ^(q-1) < λ/C ⇔ δ < (λ/C)^(1/(q-1)).
    -- Let `bound1 := (lambda / (2 * C))^(1/(q-1))`.
    -- Pick δ := min(delta0, ε, bound1) / 2.
    have hqm1_pos : 0 < q - 1 := by linarith
    have hqm1_inv_pos : 0 < 1 / (q - 1) := by positivity
    have h_lambda_2C_pos : 0 < lambda / (2 * C) := div_pos hlam0 (by linarith)
    set bound1 : ℝ := (lambda / (2 * C)) ^ ((1 : ℝ) / (q - 1)) with hbound1_def
    have hbound1_pos : 0 < bound1 := by
      apply Real.rpow_pos_of_pos h_lambda_2C_pos
    set δ : ℝ := min (min delta0 ε) bound1 / 2 with hδ_def
    have h_min_pos : 0 < min (min delta0 ε) bound1 := by
      exact lt_min (lt_min hdelta0_pos hε) hbound1_pos
    have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
    have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
    have hδ_lt_min : δ < min (min delta0 ε) bound1 := by
      rw [hδ_def]; linarith
    have hδ_lt_delta0 : δ < delta0 :=
      lt_of_lt_of_le hδ_lt_min (le_trans (min_le_left _ _) (min_le_left _ _))
    have hδ_lt_ε : δ < ε :=
      lt_of_lt_of_le hδ_lt_min (le_trans (min_le_left _ _) (min_le_right _ _))
    have hδ_lt_bound1 : δ < bound1 :=
      lt_of_lt_of_le hδ_lt_min (min_le_right _ _)
    -- Define tildep
    refine ⟨Function.update (fun _ : Fin d => (0 : ℝ)) k δ, ?_, ?_, ?_⟩
    · -- Orthant condition
      intro j
      refine ⟨?_, ?_⟩
      · intro _
        by_cases hj : j = k
        · subst hj; rw [Function.update_self]; exact hδ_nn
        · rw [Function.update_of_ne hj]
      · intro hsj
        by_cases hj : j = k
        · subst hj
          rw [hsigma_k] at hsj; norm_num at hsj
        · rw [Function.update_of_ne hj]
    · -- |tildep j| < ε
      intro j
      by_cases hj : j = k
      · subst hj; rw [Function.update_self]; rw [abs_of_nonneg hδ_nn]; exact hδ_lt_ε
      · rw [Function.update_of_ne hj]; rw [abs_zero]; exact hε
    · -- Strict descent via boundary first-order rise
      -- (1) Show that (tildep - f) = Function.update (-f) k δ
      have h_tildep_minus_f :
          (fun j => Function.update (fun _ : Fin d => (0 : ℝ)) k δ j - f j)
            = Function.update (fun j => -(f j)) k δ := by
        funext j
        by_cases hj : j = k
        · subst hj
          rw [Function.update_self, Function.update_self, hfk_eq_zero, sub_zero]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
          rw [zero_sub]
      rw [h_tildep_minus_f]
      -- (2) From boundary first order rise:
      have hδ_in_Ioo : δ ∈ Set.Ioo (0 : ℝ) delta0 := ⟨hδ_pos, hδ_lt_delta0⟩
      have h_rise : lqNorm q (Function.update (fun j => -(f j)) k δ)
                      ≤ lqNorm q (fun j => -(f j)) + C * δ ^ q :=
        hbound δ hδ_in_Ioo
      -- (3) lqNorm q tildep = δ
      have hnorm_tildep :
          lqNorm q (Function.update (fun _ : Fin d => (0 : ℝ)) k δ) = δ :=
        hnorm_update_zero δ hδ_nn
      rw [hnorm_tildep]
      -- (4) Final inequality:
      --   lqNorm q (-f) + C * δ^q - λ * δ < lqNorm q (-f)
      -- iff C * δ^q < λ * δ
      -- We have δ < bound1 = (λ/(2C))^(1/(q-1)), so δ^(q-1) < λ/(2C),
      -- so C * δ^q = C * δ^(q-1) * δ < (λ/2) * δ < λ * δ.
      -- Step (a): δ^(q-1) < λ/(2C)
      have h_delta_qm1_lt : δ ^ (q - 1) < lambda / (2 * C) := by
        -- δ < (λ/(2C))^(1/(q-1)) ⇒ δ^(q-1) < λ/(2C)
        have h_eq : (bound1) ^ (q - 1) = lambda / (2 * C) := by
          rw [hbound1_def]
          rw [← Real.rpow_mul (le_of_lt h_lambda_2C_pos)]
          rw [div_mul_cancel₀ 1 (by linarith : q - 1 ≠ 0)]
          exact Real.rpow_one _
        have h_step : δ ^ (q - 1) < bound1 ^ (q - 1) :=
          Real.rpow_lt_rpow hδ_nn hδ_lt_bound1 hqm1_pos
        rw [h_eq] at h_step
        exact h_step
      -- Step (b): C * δ^q < (λ/2) * δ
      have hCpos : 0 < C := hC_pos
      -- C * δ^q = C * δ * δ^(q-1)  (since δ^q = δ^(q-1) * δ^1 = δ^(q-1) * δ)
      have h_split : δ ^ q = δ ^ (q - 1) * δ := by
        have h1 : δ ^ ((q - 1) + 1) = δ ^ (q - 1) * δ ^ (1 : ℝ) :=
          Real.rpow_add hδ_pos _ _
        rw [Real.rpow_one] at h1
        have h_qm1_p1 : (q - 1) + 1 = q := by ring
        rw [h_qm1_p1] at h1
        exact h1
      have h_Cdelta_qm1 : C * δ ^ (q - 1) < lambda / 2 := by
        have h1 : C * δ ^ (q - 1) < C * (lambda / (2 * C)) :=
          mul_lt_mul_of_pos_left h_delta_qm1_lt hCpos
        have h_simp : C * (lambda / (2 * C)) = lambda / 2 := by
          field_simp
        linarith [h_simp]
      have h_C_delta_q_lt : C * δ ^ q < (lambda / 2) * δ := by
        rw [h_split]
        have heq : C * (δ ^ (q - 1) * δ) = (C * δ ^ (q - 1)) * δ := by ring
        rw [heq]
        exact mul_lt_mul_of_pos_right h_Cdelta_qm1 hδ_pos
      -- Step (c): conclude
      have h_lambda_2_lt : (lambda / 2) * δ < lambda * δ := by
        have hl : lambda / 2 < lambda := by linarith
        exact mul_lt_mul_of_pos_right hl hδ_pos
      have h_C_delta_q_lt' : C * δ ^ q < lambda * δ := lt_trans h_C_delta_q_lt h_lambda_2_lt
      linarith [h_rise]
