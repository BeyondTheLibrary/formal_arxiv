import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LqNormPartialDerivative_PosBranch_LimitAtZero
import Workspace.ProofLemmas.LqNormBoundaryUpwardExpansion

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

/-- **Left boundary forces `f j = 0` (positive branch).**

Under the same hypotheses as `Claim1_RuleOutInterior`, with the
additional assumption that `lqNorm q (p_star - f) > 0`, every index `j`
with `σ j = +1` and `p_star j = 0` satisfies `f j = 0`.

Paper reference: Block 3, Step 3.6 (companion to `RightBoundary_ForcesC0`)
of Gravin & Jia, *Approximation guarantees of Median Mechanism in ℝ^d*,
arXiv:2502.08578v2. -/
theorem LeftBoundary_ForcesFjZero
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
    (j : Fin d) (hsig : sigma j = 1) (hpz : p_star j = 0) :
    f j = 0 := by
  classical
  -- Basic facts about q.
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq1_pos : 0 < q - 1 := sub_pos.mpr hq
  have hq1_nn : (0 : ℝ) ≤ q - 1 := le_of_lt hq1_pos
  -- f j is non-negative.
  have hfj_nn : 0 ≤ f j := hf_nn j
  -- Try to derive a contradiction from f j > 0.
  by_contra hfj_ne
  have hfj_pos : 0 < f j := lt_of_le_of_ne hfj_nn (Ne.symm hfj_ne)
  -- Extract the local-min ε from hp_loc.
  obtain ⟨ε, hε_pos, hε_loc⟩ := hp_loc
  -- Set up the abbreviation L = lqNorm q (p_star - f).
  set L : ℝ := lqNorm q (fun k => p_star k - f k) with hL_def
  have hL_pos : 0 < L := hpf_pos
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  -- The first-term derivative.
  have h_deriv_first :
      HasDerivWithinAt
        (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
        (-(f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1))
        (Set.Ici (0 : ℝ)) 0 :=
    LqNormPartialDerivative_PosBranch_LimitAtZero hq hd p_star f j hpz hfj_pos hf_nn hpf_pos
  -- Define D₁ as that derivative; show D₁ < 0.
  set D₁ : ℝ := -(f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1) with hD₁_def
  have hLpow_pos : 0 < L ^ (q - 1) := Real.rpow_pos_of_pos hL_pos _
  have hfjpow_pos : 0 < (f j) ^ (q - 1) := Real.rpow_pos_of_pos hfj_pos _
  have hD₁_neg : D₁ < 0 := by
    rw [hD₁_def]
    show -(f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1) < 0
    rw [show -(f j) ^ (q - 1) / (lqNorm q (fun k => p_star k - f k)) ^ (q - 1)
          = -((f j) ^ (q - 1) / L ^ (q - 1)) by rw [hL_def]; ring]
    have hpos : 0 < (f j) ^ (q - 1) / L ^ (q - 1) := div_pos hfjpow_pos hLpow_pos
    linarith
  -- Use HasDerivWithinAt.liminf_right_slope_le with r = D₁/2 > D₁ to find a small z>0
  -- for which the slope is < D₁/2.
  -- First, set the function name explicitly.
  set F : ℝ → ℝ := fun t => lqNorm q (fun k => Function.update p_star j t k - f k) with hF_def
  have h_deriv_first' :
      HasDerivWithinAt F D₁ (Set.Ici (0 : ℝ)) 0 := h_deriv_first
  -- D₁/2 is strictly between D₁ and 0.
  have hD₁_half_lt_zero : D₁ / 2 < 0 := by linarith
  have hD₁_lt_half : D₁ < D₁ / 2 := by linarith
  -- Frequently in 𝓝[>] 0, slope F 0 z < D₁/2.
  have h_freq : ∃ᶠ z in nhdsWithin 0 (Set.Ioi (0 : ℝ)), slope F 0 z < D₁ / 2 :=
    h_deriv_first'.liminf_right_slope_le hD₁_lt_half
  -- We also need z to lie in the open interval where the local-min and t<ε hold:
  -- specifically z ∈ (0, ε) suffices.
  have h_in_nhds : Set.Ioo (0 : ℝ) ε ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio ε, isOpen_Iio, hε_pos, ?_⟩
    intro x hx
    refine ⟨hx.2, hx.1⟩
  -- Combine the frequently and the eventually-membership of (0, ε) to extract a witness.
  have h_witness : ∃ z ∈ Set.Ioo (0 : ℝ) ε, slope F 0 z < D₁ / 2 := by
    -- Filter.Frequently.exists from h_freq filtered by the eventually predicate.
    have := h_freq.and_eventually (Filter.Eventually.of_forall (p := fun z => True) (fun _ => trivial))
    have h_freq' : ∃ᶠ z in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        z ∈ Set.Ioo (0 : ℝ) ε ∧ slope F 0 z < D₁ / 2 := by
      have hev : ∀ᶠ z in nhdsWithin 0 (Set.Ioi (0 : ℝ)), z ∈ Set.Ioo (0 : ℝ) ε := h_in_nhds
      exact h_freq.and_eventually hev |>.mp (Filter.Eventually.of_forall (fun z hz => ⟨hz.2, hz.1⟩))
    rcases h_freq'.exists with ⟨z, hz⟩
    exact ⟨z, hz.1, hz.2⟩
  -- Unpack the witness.
  obtain ⟨z, hz_mem, hz_slope⟩ := h_witness
  obtain ⟨hz_pos, hz_lt_ε⟩ := hz_mem
  -- The slope is (F z - F 0) / z.
  have h_slope_eq : slope F 0 z = (F z - F 0) / z := by
    rw [slope_def_field]
    rw [sub_zero]
  rw [h_slope_eq] at hz_slope
  have hz_ne : z ≠ 0 := ne_of_gt hz_pos
  -- From slope < D₁/2 and z > 0: F z - F 0 < (D₁/2) * z.
  have h_F_diff_lt : F z - F 0 < (D₁ / 2) * z := by
    have := (div_lt_iff₀ hz_pos).mp hz_slope
    linarith
  -- Now compute: F 0 = lqNorm q (p_star - f) = L; F z = lqNorm q (update p_star j z - f).
  have hF0 : F 0 = L := by
    show lqNorm q (fun k => Function.update p_star j 0 k - f k) = L
    have h_upd : Function.update p_star j (0 : ℝ) = p_star := by
      ext k
      by_cases hk : k = j
      · subst hk; rw [Function.update_self, hpz]
      · rw [Function.update_of_ne hk]
    rw [show (fun k => Function.update p_star j 0 k - f k) = (fun k => p_star k - f k) by
          ext k; rw [h_upd]]
  -- Now we control the second term: lqNorm q (update p_star j z) ≥ lqNorm q p_star.
  -- Apply LqNormBoundaryUpwardExpansion with x := p_star, j, delta := z.
  have hz_nn : 0 ≤ z := le_of_lt hz_pos
  have h_expand : lqNorm q (Function.update p_star j z)
      = ((lqNorm q p_star) ^ q + z ^ q) ^ ((1 : ℝ) / q) :=
    LqNormBoundaryUpwardExpansion hq hd p_star j z hz_nn hpz
  -- Show lqNorm q (update p_star j z) ≥ lqNorm q p_star.
  have h_lq_pstar_nn : 0 ≤ lqNorm q p_star := lqNorm_nonneg' q p_star
  have h_lq_mono : lqNorm q p_star ≤ lqNorm q (Function.update p_star j z) := by
    rw [h_expand]
    have h_zq_nn : 0 ≤ z ^ q := Real.rpow_nonneg hz_nn q
    have h_lqq_nn : 0 ≤ (lqNorm q p_star) ^ q := Real.rpow_nonneg h_lq_pstar_nn q
    have h_le : (lqNorm q p_star) ^ q ≤ (lqNorm q p_star) ^ q + z ^ q := by linarith
    have h_inv_nn : (0 : ℝ) ≤ (1 : ℝ) / q := by positivity
    have h1 : ((lqNorm q p_star) ^ q) ^ ((1 : ℝ) / q)
        ≤ ((lqNorm q p_star) ^ q + z ^ q) ^ ((1 : ℝ) / q) :=
      Real.rpow_le_rpow h_lqq_nn h_le h_inv_nn
    have h2 : ((lqNorm q p_star) ^ q) ^ ((1 : ℝ) / q) = lqNorm q p_star := by
      rw [← Real.rpow_mul h_lq_pstar_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
    linarith [h2]
  -- Now use the local minimum: g_lambda p_star ≤ g_lambda (update p_star j z).
  -- Build the constraint hypothesis for hε_loc.
  have h_orth : ∀ k, (sigma k = 1 → 0 ≤ Function.update p_star j z k) ∧
                     (sigma k = -1 → Function.update p_star j z k ≤ 0) := by
    intro k
    refine ⟨?_, ?_⟩
    · intro hsk
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact hz_nn
      · rw [Function.update_of_ne hk]
        exact (hp_in k).1 hsk
    · intro hsk
      by_cases hk : k = j
      · subst hk
        -- sigma j = -1 contradicts hsig : sigma j = 1
        rw [hsig] at hsk; linarith
      · rw [Function.update_of_ne hk]
        exact (hp_in k).2 hsk
  -- ε-closeness condition.
  have h_close : ∀ k, |Function.update p_star j z k - p_star k| < ε := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, hpz, sub_zero, abs_of_pos hz_pos]
      exact hz_lt_ε
    · rw [Function.update_of_ne hk, sub_self, abs_zero]
      exact hε_pos
  -- Apply the local-min property.
  have h_g_le := hε_loc (Function.update p_star j z) h_orth h_close
  -- Now we want to derive a contradiction.
  -- g_lambda f p_star = L - λ * lqNorm q p_star
  -- g_lambda f (update p_star j z) = F z - λ * lqNorm q (update p_star j z)
  -- h_g_le: L - λ*A ≤ F z - λ*B, where A = lqNorm q p_star, B = lqNorm q (update p_star j z).
  -- h_lq_mono: A ≤ B → -λ*B ≤ -λ*A → ... So we have F z ≥ L + λ*(B - A) ≥ L.
  -- But h_F_diff_lt: F z < L + (D₁/2) * z, with (D₁/2)*z < 0, so F z < L. Contradiction.
  have h_lambda_ineq : -lambda * lqNorm q (Function.update p_star j z) ≤
      -lambda * lqNorm q p_star := by
    have hlam_nn : 0 ≤ lambda := le_of_lt hlam0
    have := mul_le_mul_of_nonneg_left h_lq_mono hlam_nn
    linarith
  -- Unfold g_lambda.
  have h_g_unfold : g_lambda q lambda f p_star ≤ g_lambda q lambda f (Function.update p_star j z) :=
    h_g_le
  -- Recall g_lambda q lambda f p = lqNorm q (p - f) - lambda * lqNorm q p
  have h_g_p_star : g_lambda q lambda f p_star = L - lambda * lqNorm q p_star := by
    show lqNorm q (fun k => p_star k - f k) - lambda * lqNorm q p_star = L - lambda * lqNorm q p_star
    rfl
  have h_g_update : g_lambda q lambda f (Function.update p_star j z)
      = F z - lambda * lqNorm q (Function.update p_star j z) := by
    show lqNorm q (fun k => Function.update p_star j z k - f k) - lambda * lqNorm q (Function.update p_star j z)
        = F z - lambda * lqNorm q (Function.update p_star j z)
    rfl
  rw [h_g_p_star, h_g_update] at h_g_unfold
  -- Now: L - λ * lqNorm q p_star ≤ F z - λ * lqNorm q (Function.update p_star j z)
  -- With h_lq_mono: λ * lqNorm q p_star ≤ λ * lqNorm q (Function.update p_star j z).
  have hlam_nn : 0 ≤ lambda := le_of_lt hlam0
  have h_lq_lam_mono : lambda * lqNorm q p_star ≤ lambda * lqNorm q (Function.update p_star j z) :=
    mul_le_mul_of_nonneg_left h_lq_mono hlam_nn
  -- From h_g_unfold and h_lq_lam_mono: L ≤ F z + (λ * lqNorm q p_star - λ * lqNorm q (update))
  -- Wait, let's just rearrange.
  -- L - λ*A ≤ F z - λ*B
  -- L ≤ F z - λ*B + λ*A = F z - λ*(B - A) ≤ F z (since B ≥ A and λ > 0)
  have h_L_le_Fz : L ≤ F z := by
    have hsub : 0 ≤ lambda * lqNorm q (Function.update p_star j z) - lambda * lqNorm q p_star := by
      linarith
    linarith
  -- But h_F_diff_lt: F z - L < (D₁/2) * z, and (D₁/2) * z < 0 (since z > 0 and D₁/2 < 0).
  have hD₁_half_z_neg : (D₁ / 2) * z < 0 := by
    exact mul_neg_of_neg_of_pos hD₁_half_lt_zero hz_pos
  have h_Fz_lt_L : F z < L := by
    have : F z - L < 0 := by
      have := h_F_diff_lt
      rw [hF0] at this
      linarith
    linarith
  -- Contradiction.
  linarith
