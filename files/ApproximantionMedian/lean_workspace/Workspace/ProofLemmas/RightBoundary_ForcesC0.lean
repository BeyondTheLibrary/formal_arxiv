import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LqNormBoundaryRightDeriv
import Workspace.ProofLemmas.LqNormPartialDerivative_PosBranch

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem RightBoundary_ForcesC0
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
    (j : Fin d) (hsig : sigma j = 1) (hpf_eq : p_star j = f j) (hfj_pos : 0 < f j) :
    lqNorm q (fun k => p_star k - f k) = 0 := by
  -- The proof strategy: we derive False from the hypotheses.
  -- We compute the right-derivative of t ↦ g_lambda q lambda f (Function.update p_star j t)
  -- on Ici (p_star j) at t = p_star j. It is strictly negative, contradicting
  -- the local-min hypothesis.
  exfalso
  -- Useful basic facts.
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq1_pos : 0 < q - 1 := sub_pos.mpr hq
  have hq1_ne : q - 1 ≠ 0 := ne_of_gt hq1_pos
  have hpj_pos : 0 < p_star j := by rw [hpf_eq]; exact hfj_pos
  have hpj_nn : 0 ≤ p_star j := le_of_lt hpj_pos
  -- Notation: pmf = p_star - f.
  set pmf : Fin d → ℝ := fun k => p_star k - f k with hpmf_def
  have hpmf_j_zero : pmf j = 0 := by
    simp [hpmf_def, hpf_eq]
  have hpmf_pos : 0 < lqNorm q pmf := hpf_pos
  have hpmf_nn : 0 ≤ lqNorm q pmf := le_of_lt hpmf_pos
  have hpmf_ne : lqNorm q pmf ≠ 0 := ne_of_gt hpmf_pos
  -- ============================================================
  -- Step 1: Compute right derivative of (t ↦ lqNorm q (update p_star j t - f))
  -- at t = p_star j on Ici (p_star j). Equals 0.
  -- ============================================================
  -- Use LqNormBoundaryRightDeriv on pmf at index j.
  -- That gives derivative on Ici (pmf j) = Ici 0 of t ↦ lqNorm q (update pmf j t).
  have hH : HasDerivWithinAt
      (fun s : ℝ => lqNorm q (Function.update pmf j s))
      ((pmf j) ^ (q - 1) / (lqNorm q pmf) ^ (q - 1))
      (Set.Ici (pmf j)) (pmf j) :=
    LqNormBoundaryRightDeriv hq hd pmf j (le_of_eq hpmf_j_zero.symm) hpmf_pos
  -- The derivative simplifies to 0 since pmf j = 0.
  have hH_zero : HasDerivWithinAt
      (fun s : ℝ => lqNorm q (Function.update pmf j s))
      0 (Set.Ici (0 : ℝ)) 0 := by
    have hcoef : (pmf j) ^ (q - 1) / (lqNorm q pmf) ^ (q - 1) = 0 := by
      rw [hpmf_j_zero, Real.zero_rpow hq1_ne, zero_div]
    rw [hcoef] at hH
    rw [hpmf_j_zero] at hH
    exact hH
  -- Now translate from `s` to `t = s + p_star j`, i.e. `s = t - p_star j`.
  -- The function `t ↦ lqNorm q (update p_star j t - f)` equals
  -- `t ↦ lqNorm q (update pmf j (t - p_star j))` pointwise.
  have h_update_eq : ∀ t : ℝ,
      (fun k => Function.update p_star j t k - f k) = Function.update pmf j (t - p_star j) := by
    intro t
    funext k
    by_cases hk : k = j
    · subst hk
      simp [Function.update_self, hpmf_def, hpf_eq]
    · simp [Function.update_of_ne hk, hpmf_def]
  -- Compose with the affine map `t ↦ t - p_star j` to obtain HasDerivWithinAt on Ici (p_star j).
  have h_inner : HasDerivAt (fun t : ℝ => t - p_star j) 1 (p_star j) := by
    have := (hasDerivAt_id (p_star j)).sub_const (p_star j)
    simpa using this
  -- MapsTo: t ∈ Ici (p_star j) → t - p_star j ∈ Ici 0
  have h_maps : Set.MapsTo (fun t : ℝ => t - p_star j) (Set.Ici (p_star j)) (Set.Ici (0 : ℝ)) := by
    intro t ht
    simp only [Set.mem_Ici] at ht ⊢
    linarith
  have h_inner_within : HasDerivWithinAt (fun t : ℝ => t - p_star j) 1
      (Set.Ici (p_star j)) (p_star j) := h_inner.hasDerivWithinAt
  have h_comp_at_zero : (fun t : ℝ => t - p_star j) (p_star j) = 0 := by ring
  have hG_pre : HasDerivWithinAt
      (fun t : ℝ => lqNorm q (Function.update pmf j (t - p_star j)))
      (1 * 0) (Set.Ici (p_star j)) (p_star j) := by
    have hH_at : HasDerivWithinAt
        (fun s : ℝ => lqNorm q (Function.update pmf j s))
        0 (Set.Ici (0 : ℝ)) ((fun t : ℝ => t - p_star j) (p_star j)) := by
      rw [h_comp_at_zero]
      exact hH_zero
    have := HasDerivWithinAt.scomp (x := p_star j)
      (g₁ := fun s : ℝ => lqNorm q (Function.update pmf j s))
      (h := fun t : ℝ => t - p_star j)
      (g₁' := (0 : ℝ)) (h' := (1 : ℝ))
      (t' := Set.Ici (0 : ℝ)) (s := Set.Ici (p_star j))
      hH_at h_inner_within h_maps
    -- this : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x
    -- which is: HasDerivWithinAt (fun t => lqNorm q (update pmf j (t - p_star j))) (1 • 0) (Ici (p_star j)) (p_star j)
    convert this using 1
  have hG : HasDerivWithinAt
      (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
      0 (Set.Ici (p_star j)) (p_star j) := by
    have h_eq_fun : (fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k))
        = fun t : ℝ => lqNorm q (Function.update pmf j (t - p_star j)) := by
      funext t
      rw [h_update_eq t]
    rw [h_eq_fun]
    have : (1 : ℝ) * 0 = 0 := by ring
    rw [← this]
    exact hG_pre
  -- ============================================================
  -- Step 2: Compute derivative of (t ↦ lqNorm q (update p_star j t)) at t = p_star j.
  -- Equals (p_star j)^(q-1) / (lqNorm q p_star)^(q-1) > 0.
  -- ============================================================
  have hP : HasDerivAt
      (fun t : ℝ => lqNorm q (Function.update p_star j t))
      ((p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1))
      (p_star j) :=
    LqNormPartialDerivative_PosBranch hq hd p_star j hpj_pos hp_pos
  set deriv_p : ℝ := (p_star j) ^ (q - 1) / (lqNorm q p_star) ^ (q - 1) with hdp_def
  have hdp_pos : 0 < deriv_p := by
    rw [hdp_def]
    apply div_pos
    · exact Real.rpow_pos_of_pos hpj_pos _
    · exact Real.rpow_pos_of_pos hp_pos _
  -- Lift hP to HasDerivWithinAt on Ici (p_star j).
  have hP_within : HasDerivWithinAt
      (fun t : ℝ => lqNorm q (Function.update p_star j t))
      deriv_p (Set.Ici (p_star j)) (p_star j) := hP.hasDerivWithinAt
  -- ============================================================
  -- Step 3: Compute right derivative of g_lambda(update p_star j t) at p_star j.
  -- ============================================================
  -- g_lambda q lambda f p = lqNorm q (p - f) - lambda * lqNorm q p
  -- Right deriv = (deriv of first) - lambda * (deriv of second) = 0 - lambda * deriv_p
  -- = -lambda * deriv_p < 0.
  have hP_within_smul : HasDerivWithinAt
      (fun t : ℝ => lambda * lqNorm q (Function.update p_star j t))
      (lambda * deriv_p) (Set.Ici (p_star j)) (p_star j) :=
    hP_within.const_mul lambda
  have hG_total : HasDerivWithinAt
      (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t))
      (0 - lambda * deriv_p) (Set.Ici (p_star j)) (p_star j) := by
    -- g_lambda q lambda f (update p_star j t) = lqNorm q (update p_star j t - f) - lambda * lqNorm q (update p_star j t)
    have h_eq : (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t))
        = fun t : ℝ => lqNorm q (fun k => Function.update p_star j t k - f k)
                      - lambda * lqNorm q (Function.update p_star j t) := by
      funext t
      simp [g_lambda]
    rw [h_eq]
    exact hG.sub hP_within_smul
  -- The derivative is strictly negative.
  set D : ℝ := 0 - lambda * deriv_p with hD_def
  have hD_neg : D < 0 := by
    rw [hD_def, zero_sub]
    apply neg_neg_iff_pos.mpr
    exact mul_pos hlam0 hdp_pos
  -- ============================================================
  -- Step 4: Use HasDerivWithinAt.liminf_right_slope_le to find a point z > p_star j
  -- arbitrarily close, with slope < 0.
  -- ============================================================
  have h_freq : ∃ᶠ z in (nhdsWithin (p_star j) (Set.Ioi (p_star j))),
      slope (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t)) (p_star j) z < 0 :=
    hG_total.liminf_right_slope_le hD_neg
  -- ============================================================
  -- Step 5: Pull a specific z out of the frequently filter.
  -- The local-min radius gives ε > 0.
  -- ============================================================
  obtain ⟨ε, hε_pos, hε_loc⟩ := hp_loc
  -- We want z ∈ (p_star j, p_star j + ε), with slope < 0.
  -- Build a neighborhood: (p_star j, p_star j + ε) is a punctured-right neighborhood.
  have h_nbhd : Set.Ioo (p_star j) (p_star j + ε) ∈ (nhdsWithin (p_star j) (Set.Ioi (p_star j))) := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio (p_star j + ε), isOpen_Iio, ?_, ?_⟩
    · show p_star j < p_star j + ε
      linarith
    · intro x hx
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo] at hx ⊢
      exact ⟨hx.2, hx.1⟩
  -- Combine the frequently-witness with the neighborhood.
  have h_freq_strong : ∃ᶠ z in (nhdsWithin (p_star j) (Set.Ioi (p_star j))),
      z ∈ Set.Ioo (p_star j) (p_star j + ε) ∧
      slope (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t)) (p_star j) z < 0 :=
    (Filter.eventually_of_mem h_nbhd (fun _ h => h)).and_frequently h_freq
  -- Extract one such z.
  obtain ⟨z, ⟨hz_lo, hz_hi⟩, h_slope⟩ := h_freq_strong.exists
  have hz_gt : p_star j < z := hz_lo
  have hz_close : z < p_star j + ε := hz_hi
  -- ============================================================
  -- Step 6: Show update_p_star_j_z is in the orthant and within ε.
  -- ============================================================
  set tildep : Fin d → ℝ := Function.update p_star j z with htildep_def
  have htildep_at_j : tildep j = z := by simp [htildep_def, Function.update_self]
  have htildep_off_j : ∀ k : Fin d, k ≠ j → tildep k = p_star k := by
    intro k hk
    simp [htildep_def, Function.update_of_ne hk]
  have hz_pos : 0 < z := lt_trans hpj_pos hz_gt
  have hz_nn : 0 ≤ z := le_of_lt hz_pos
  -- tildep is in the orthant.
  have htildep_in : ∀ k, (sigma k = 1 → 0 ≤ tildep k) ∧ (sigma k = -1 → tildep k ≤ 0) := by
    intro k
    by_cases hk : k = j
    · subst hk
      refine ⟨fun _ => ?_, fun hsig_neg => ?_⟩
      · rw [htildep_at_j]; exact hz_nn
      · exfalso; rw [hsig] at hsig_neg; linarith
    · rw [htildep_off_j k hk]
      exact hp_in k
  -- |tildep k - p_star k| < ε for all k.
  have htildep_close : ∀ k, |tildep k - p_star k| < ε := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [htildep_at_j]
      have hzk_pos : 0 < z - p_star k := by linarith
      rw [abs_of_pos hzk_pos]
      linarith
    · rw [htildep_off_j k hk]
      have : p_star k - p_star k = 0 := by ring
      rw [this, abs_zero]
      exact hε_pos
  -- ============================================================
  -- Step 7: From local-min hypothesis: g_lambda(p_star) ≤ g_lambda(tildep).
  -- ============================================================
  have hg_le : g_lambda q lambda f p_star ≤ g_lambda q lambda f tildep :=
    hε_loc tildep htildep_in htildep_close
  -- Note: tildep = update p_star j z, and at j: p_star = update p_star j (p_star j).
  -- So slope (fun t => g_lambda(update p_star j t)) (p_star j) z =
  --        (g_lambda(update p_star j z) - g_lambda(update p_star j (p_star j))) / (z - p_star j)
  --      = (g_lambda(tildep) - g_lambda(p_star)) / (z - p_star j) ≥ 0
  -- This contradicts slope < 0.
  have h_update_pstar : Function.update p_star j (p_star j) = p_star := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [Function.update_self]
    · simp [Function.update_of_ne hk]
  have h_slope_eq :
      slope (fun t : ℝ => g_lambda q lambda f (Function.update p_star j t)) (p_star j) z
        = (z - p_star j)⁻¹ * (g_lambda q lambda f tildep - g_lambda q lambda f p_star) := by
    unfold slope
    simp only [vsub_eq_sub, smul_eq_mul]
    rw [h_update_pstar]
  rw [h_slope_eq] at h_slope
  have hz_diff_pos : 0 < z - p_star j := by linarith
  have hz_inv_pos : 0 < (z - p_star j)⁻¹ := inv_pos.mpr hz_diff_pos
  have h_sub_nn : 0 ≤ g_lambda q lambda f tildep - g_lambda q lambda f p_star := by linarith
  have h_prod_nn : 0 ≤ (z - p_star j)⁻¹ * (g_lambda q lambda f tildep - g_lambda q lambda f p_star) :=
    mul_nonneg (le_of_lt hz_inv_pos) h_sub_nn
  linarith
