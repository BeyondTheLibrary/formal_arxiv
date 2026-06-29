import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LqNormStrictDecrease_OfSingleCoordinateCloser
import Workspace.ProofLemmas.LqNormStrictIncrease_OfSingleCoordinateLarger

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem Claim1_RuleOutInterior
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
    (j : Fin d) (hsig : sigma j = 1) :
    p_star j = 0 ∨ f j ≤ p_star j := by
  -- Proof by contradiction: suppose 0 < p_star j and p_star j < f j.
  by_contra hcon
  push_neg at hcon
  obtain ⟨hpj_ne, hpj_lt_fj⟩ := hcon
  -- From hp_in and σ_j = 1, p_star j ≥ 0; combined with ≠ 0 gives 0 < p_star j.
  have hpj_nn : 0 ≤ p_star j := (hp_in j).1 hsig
  have hpj_pos : 0 < p_star j := lt_of_le_of_ne hpj_nn (Ne.symm hpj_ne)
  -- Get the local-min radius ε > 0.
  obtain ⟨ε, hε_pos, hε_loc⟩ := hp_loc
  -- Define δ := min(ε/2, (f j - p_star j)/2) > 0.
  have hgap_pos : 0 < f j - p_star j := sub_pos.mpr hpj_lt_fj
  set δ : ℝ := min (ε / 2) ((f j - p_star j) / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_le_eps_half : δ ≤ ε / 2 := min_le_left _ _
  have hδ_le_gap_half : δ ≤ (f j - p_star j) / 2 := min_le_right _ _
  -- Define t := p_star j + δ.
  set t : ℝ := p_star j + δ with ht_def
  have ht_gt_pj : p_star j < t := by rw [ht_def]; linarith
  have ht_lt_fj : t < f j := by
    rw [ht_def]
    have : (f j - p_star j) / 2 < f j - p_star j := by linarith
    linarith
  have ht_pos : 0 < t := lt_trans hpj_pos ht_gt_pj
  have ht_nn : 0 ≤ t := le_of_lt ht_pos
  -- Define the perturbation tildep := update p_star j t.
  set tildep : Fin d → ℝ := Function.update p_star j t with htildep_def
  -- tildep j = t.
  have htildep_at_j : tildep j = t := by
    simp [htildep_def, Function.update_self]
  -- For k ≠ j, tildep k = p_star k.
  have htildep_off_j : ∀ k : Fin d, k ≠ j → tildep k = p_star k := by
    intro k hk
    simp [htildep_def, Function.update_of_ne hk]
  -- tildep is in the orthant.
  have htildep_in : ∀ k, (sigma k = 1 → 0 ≤ tildep k) ∧ (sigma k = -1 → tildep k ≤ 0) := by
    intro k
    by_cases hk : k = j
    · subst hk
      refine ⟨fun _ => ?_, fun hsig_neg => ?_⟩
      · rw [htildep_at_j]; exact ht_nn
      · -- σ k = 1, but hypothesis says σ k = -1. Contradiction.
        exfalso
        rw [hsig] at hsig_neg
        linarith
    · rw [htildep_off_j k hk]
      exact hp_in k
  -- |tildep k - p_star k| < ε for all k.
  have htildep_close : ∀ k, |tildep k - p_star k| < ε := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [htildep_at_j, ht_def]
      have : p_star k + δ - p_star k = δ := by ring
      rw [this]
      rw [abs_of_pos hδ_pos]
      linarith
    · rw [htildep_off_j k hk]
      have : p_star k - p_star k = 0 := by ring
      rw [this, abs_zero]
      exact hε_pos
  -- By local-min: g(p_star) ≤ g(tildep).
  have hg_le : g_lambda q lambda f p_star ≤ g_lambda q lambda f tildep :=
    hε_loc tildep htildep_in htildep_close
  -- Now derive a strict inequality the other way.
  -- Step (a): lqNorm q (tildep - f) < lqNorm q (p_star - f).
  -- Need |tildep j - f j| < |p_star j - f j|.
  -- |tildep j - f j| = |t - f j| = f j - t (since t < f j).
  -- |p_star j - f j| = f j - p_star j (since p_star j < f j).
  -- And f j - t < f j - p_star j since p_star j < t.
  have h_abs_strict_decrease : |tildep j - f j| < |p_star j - f j| := by
    rw [htildep_at_j]
    have h1 : t - f j < 0 := sub_neg.mpr ht_lt_fj
    have h2 : p_star j - f j < 0 := sub_neg.mpr hpj_lt_fj
    rw [abs_of_neg h1, abs_of_neg h2]
    linarith
  have h_eq_off_decrease : ∀ k : Fin d, k ≠ j → tildep k = p_star k := htildep_off_j
  have hnorm_decrease :
      lqNorm q (fun k => tildep k - f k) < lqNorm q (fun k => p_star k - f k) :=
    LqNormStrictDecrease_OfSingleCoordinateCloser hq hd p_star tildep f j h_eq_off_decrease h_abs_strict_decrease
  -- Step (b): lqNorm q p_star < lqNorm q tildep.
  -- |p_star j| = p_star j, |tildep j| = t, p_star j < t.
  have h_abs_strict_increase : |p_star j| < |tildep j| := by
    rw [htildep_at_j]
    rw [abs_of_pos hpj_pos, abs_of_pos ht_pos]
    exact ht_gt_pj
  have h_eq_off_increase : ∀ k : Fin d, k ≠ j → tildep k = p_star k := htildep_off_j
  have hnorm_increase : lqNorm q p_star < lqNorm q tildep :=
    LqNormStrictIncrease_OfSingleCoordinateLarger hq hd p_star tildep j h_eq_off_increase h_abs_strict_increase
  -- Combine: g_lambda q lambda f tildep < g_lambda q lambda f p_star.
  have hg_strict_lt : g_lambda q lambda f tildep < g_lambda q lambda f p_star := by
    unfold g_lambda
    -- LHS = lqNorm q (tildep - f) - lambda * lqNorm q tildep
    -- RHS = lqNorm q (p_star - f) - lambda * lqNorm q p_star
    -- LHS < RHS ↔ lqNorm q (tildep - f) - lqNorm q (p_star - f) < lambda * (lqNorm q tildep - lqNorm q p_star)
    -- We have: lqNorm q (tildep - f) < lqNorm q (p_star - f) (so LHS_decrease < 0)
    -- and: lambda * (lqNorm q tildep - lqNorm q p_star) > 0 (so RHS positive).
    have h1 : lqNorm q (fun k => tildep k - f k) - lqNorm q (fun k => p_star k - f k) < 0 := by
      linarith
    have h2 : 0 < lambda * (lqNorm q tildep - lqNorm q p_star) := by
      apply mul_pos hlam0
      linarith
    linarith
  -- Contradiction.
  linarith
