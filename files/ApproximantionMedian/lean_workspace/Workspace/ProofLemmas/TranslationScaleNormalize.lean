import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.SocialCostMinExists
import Workspace.ProofLemmas.SocialCostTranslationInvariance
import Workspace.ProofLemmas.MedianTranslationInvariance
import Workspace.ProofLemmas.MedianCoordinateReflection
import Workspace.ProofLemmas.MainTheoremTrivialCases
import Workspace.ProofLemmas.LqNormZeroIffEqZero

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ProofLemmas.UBDef

namespace TranslationScaleNormalizeProof3

/-- Reflecting a vector by signs preserves its lqNorm. -/
private lemma lqNorm_coord_reflection {q : ℝ} {d : ℕ}
    (eps : Fin d → ℝ) (heps : ∀ j, eps j = 1 ∨ eps j = -1) (x : Fin d → ℝ) :
    lqNorm q (fun j => eps j * x j) = lqNorm q x := by
  unfold lqNorm
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show |eps j * x j| ^ q = |x j| ^ q
  rw [abs_mul]
  rcases heps j with h1 | h1
  · rw [h1]; simp
  · rw [h1]; simp

/-- Sign-flip on coordinates preserves SC. -/
private lemma socialCost_coord_reflection (q : ℝ) {n d : ℕ}
    (eps : Fin d → ℝ) (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ) :
    socialCost q (fun (i : Fin n) (j : Fin d) => eps j * P i j)
      (fun j => eps j * f j) = socialCost q P f := by
  unfold socialCost
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have heq : (fun j => eps j * P i j - eps j * f j)
              = (fun j => eps j * (P i j - f j)) := by
    funext j; ring
  rw [heq]
  exact lqNorm_coord_reflection eps heps _

/-- Scaling: socialCost q (αP) (αf) = α · socialCost q P f for α ≥ 0. -/
private lemma socialCost_scale {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (α : ℝ) (hα : 0 ≤ α) (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ) :
    socialCost q (fun i j => α * P i j) (fun j => α * f j)
      = α * socialCost q P f := by
  unfold socialCost
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have heq : (fun j => α * P i j - α * f j) = (fun j => α * (P i j - f j)) := by
    funext j; ring
  rw [heq, lqNorm_smul hq α, abs_of_nonneg hα]

/-- Median predicate is invariant under positive scaling. -/
private lemma median_scale {n d : ℕ} (P : Fin n → Fin d → ℝ) (m : Fin d → ℝ)
    (α : ℝ) (hα : 0 < α) :
    IsCoordinateMedian m P ↔
    IsCoordinateMedian (fun j => α * m j) (fun (i : Fin n) (j : Fin d) => α * P i j) := by
  unfold IsCoordinateMedian
  refine forall_congr' (fun j => ?_)
  have hlt : (Finset.univ.filter (fun i : Fin n => P i j < m j)) =
      (Finset.univ.filter (fun i : Fin n => α * P i j < α * m j)) := by
    apply Finset.filter_congr; intros i _
    constructor
    · intro h; exact mul_lt_mul_of_pos_left h hα
    · intro h; exact lt_of_mul_lt_mul_left h hα.le
  have hgt : (Finset.univ.filter (fun i : Fin n => P i j > m j)) =
      (Finset.univ.filter (fun i : Fin n => α * P i j > α * m j)) := by
    apply Finset.filter_congr; intros i _
    constructor
    · intro h; exact mul_lt_mul_of_pos_left h hα
    · intro h; exact lt_of_mul_lt_mul_left h hα.le
  rw [hlt, hgt]

end TranslationScaleNormalizeProof3

open TranslationScaleNormalizeProof3

theorem TranslationScaleNormalize
    (h_norm : ∀ q : ℝ, 1 < q → ∀ {n d : ℕ}, 0 < n → Even n → 1 ≤ d →
      ∀ (P_norm : Fin n → Fin d → ℝ),
      IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P_norm →
      ∀ (f : Fin d → ℝ), (∀ j, 0 ≤ f j) → lqNorm q f = 1 →
      socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ)) ≤ UB q * socialCost q P_norm f) :
    ∀ q : ℝ, 1 < q → ∀ {n d : ℕ}, 0 < n → Even n → 1 ≤ d →
      ∀ (P : Fin n → Fin d → ℝ),
      ∀ (m : Fin d → ℝ), IsCoordinateMedian m P →
      0 < optSocialCost q P →
      socialCost q P m ≤ UB q * optSocialCost q P := by
  intro q hq n d hn hn_even hd P m hm hopt
  have hq_le : 1 ≤ q := le_of_lt hq
  -- Get the optimal facility f*
  obtain ⟨fstar, hfstar⟩ := SocialCostMinExists q hq_le hd P
  have hsc_fstar : socialCost q P fstar = optSocialCost q P := hfstar
  set OPT : ℝ := optSocialCost q P with hOPT_def
  have hOPT_pos : 0 < OPT := hopt
  have hOPT_nn : 0 ≤ OPT := le_of_lt hOPT_pos
  -- v = fstar - m: optimum after translating m to 0.
  set v : Fin d → ℝ := fun j => fstar j - m j with hv_def
  -- ε_j = 1 if v_j ≥ 0, else -1.
  classical
  set eps : Fin d → ℝ := fun j => if 0 ≤ v j then 1 else -1 with heps_def
  have heps_pm : ∀ j, eps j = 1 ∨ eps j = -1 := by
    intro j
    rw [heps_def]
    by_cases h : 0 ≤ v j
    · simp [h]
    · simp [h]
  have heps_v_nonneg : ∀ j, 0 ≤ eps j * v j := by
    intro j
    rw [heps_def]
    by_cases h : 0 ≤ v j
    · simp [h]
    · simp [h]
      have : v j < 0 := lt_of_not_ge h
      linarith
  -- P_tr_refl i j = eps j * (P i j - m j); v_refl j = eps j * v j ≥ 0.
  set P_tr_refl : Fin n → Fin d → ℝ := fun i j => eps j * (P i j - m j) with hP_tr_def
  set v_refl : Fin d → ℝ := fun j => eps j * v j with hv_refl_def
  have hv_refl_nn : ∀ j, 0 ≤ v_refl j := heps_v_nonneg
  -- Median 0 of (P i j - m j).
  have hmed_tr : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
      (fun (i : Fin n) (j : Fin d) => P i j - m j) := by
    have h1 := (MedianTranslationInvariance P m m).mp hm
    have heq : (fun j => m j - m j) = (fun (_ : Fin d) => (0 : ℝ)) := by
      funext j; ring
    rw [heq] at h1
    exact h1
  -- Median 0 of P_tr_refl.
  have hmed_tr_refl : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P_tr_refl := by
    have := MedianCoordinateReflection (fun i j => P i j - m j) eps heps_pm hmed_tr
    exact this
  -- SC(P_tr_refl, v_refl) = OPT.
  have hsc_tr_refl : socialCost q P_tr_refl v_refl = OPT := by
    have h1 : socialCost q (fun (i : Fin n) (j : Fin d) => P i j - m j) v
              = socialCost q P fstar := by
      have := SocialCostTranslationInvariance q P m fstar
      convert this using 2
    have h2 : socialCost q P_tr_refl v_refl =
              socialCost q (fun i j => P i j - m j) v := by
      rw [hP_tr_def, hv_refl_def]
      exact socialCost_coord_reflection q eps heps_pm _ _
    rw [h2, h1, hsc_fstar]
  -- SC(P_tr_refl, 0) = SC(P, m).
  have hsc_tr_refl_0 : socialCost q P_tr_refl (fun (_ : Fin d) => (0 : ℝ))
      = socialCost q P m := by
    have h1 : socialCost q P_tr_refl (fun (_ : Fin d) => (0 : ℝ))
              = socialCost q (fun (i : Fin n) (j : Fin d) => P i j - m j)
                  (fun (_ : Fin d) => (0 : ℝ)) := by
      rw [hP_tr_def]
      have heq : (fun (_ : Fin d) => (0 : ℝ)) = (fun (j : Fin d) => eps j * 0) := by
        funext j; ring
      conv_lhs => rw [heq]
      exact socialCost_coord_reflection q eps heps_pm _ _
    have h2 : socialCost q (fun (i : Fin n) (j : Fin d) => P i j - m j)
                (fun (_ : Fin d) => (0 : ℝ)) = socialCost q P m := by
      have := SocialCostTranslationInvariance q P m m
      have heq : (fun j => m j - m j) = (fun (_ : Fin d) => (0 : ℝ)) := by
        funext j; ring
      rw [heq] at this
      exact this
    rw [h1, h2]
  -- Now we case-split on whether v_refl is the zero vector
  -- (equivalently, whether lqNorm q v_refl = 0).
  set u : ℝ := lqNorm q v_refl with hu_def
  have hu_nn : 0 ≤ u := lqNorm_nonneg hq_le _
  by_cases hu_zero : u = 0
  · -- Degenerate: v_refl = 0, so fstar = m, so OPT = SC(P, m).
    have hv_refl_eq_zero : v_refl = (fun _ => 0) := by
      have := (LqNormZeroIffEqZero q hq_le hd v_refl).mp hu_zero
      ext j
      have := congr_fun this j
      simpa using this
    -- v_refl j = eps j * v j = 0 and eps j ≠ 0, so v j = 0.
    have hv_zero : ∀ j, v j = 0 := by
      intro j
      have hvr : eps j * v j = 0 := by
        have := congr_fun hv_refl_eq_zero j
        simpa [hv_refl_def] using this
      rcases heps_pm j with h1 | h1
      · rw [h1] at hvr; linarith
      · rw [h1] at hvr; linarith
    -- So fstar = m
    have hfstar_eq_m : fstar = m := by
      funext j
      have := hv_zero j
      simp [hv_def] at this
      linarith
    -- SC(P, m) = OPT
    have hSC_eq_OPT : socialCost q P m = OPT := by
      rw [← hfstar_eq_m]
      exact hsc_fstar
    rw [hSC_eq_OPT]
    -- Goal: OPT ≤ UB q * OPT
    have hUB_ge_one : 1 ≤ UB q := UBDef.1 q hq_le
    nlinarith [hOPT_pos]
  · -- Generic: u > 0. Scale by σ = 1/u.
    have hu_pos : 0 < u := lt_of_le_of_ne hu_nn (Ne.symm hu_zero)
    set σ : ℝ := 1 / u with hσ_def
    have hσ_pos : 0 < σ := by rw [hσ_def]; positivity
    have hσ_nn : 0 ≤ σ := le_of_lt hσ_pos
    set P_norm : Fin n → Fin d → ℝ := fun i j => σ * P_tr_refl i j with hP_norm_def
    set f_norm : Fin d → ℝ := fun j => σ * v_refl j with hf_norm_def
    -- Median 0 of P_norm.
    have hmed_norm : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P_norm := by
      have h := (median_scale P_tr_refl (fun (_ : Fin d) => (0 : ℝ)) σ hσ_pos).mp hmed_tr_refl
      have heq : (fun j => σ * (0 : ℝ)) = (fun (_ : Fin d) => (0 : ℝ)) := by
        funext j; ring
      rw [heq] at h
      exact h
    -- f_norm ≥ 0.
    have hf_norm_nn : ∀ j, 0 ≤ f_norm j := by
      intro j
      rw [hf_norm_def]
      exact mul_nonneg hσ_nn (hv_refl_nn j)
    -- lqNorm q f_norm = 1.
    have hf_norm_unit : lqNorm q f_norm = 1 := by
      rw [hf_norm_def]
      rw [lqNorm_smul hq_le σ v_refl]
      rw [abs_of_nonneg hσ_nn]
      rw [hσ_def, ← hu_def]
      field_simp
    -- SC(P_norm, f_norm) = σ * OPT.
    have hsc_norm : socialCost q P_norm f_norm = σ * OPT := by
      rw [hP_norm_def, hf_norm_def]
      rw [socialCost_scale hq_le σ hσ_nn P_tr_refl v_refl]
      rw [hsc_tr_refl]
    -- SC(P_norm, 0) = σ * SC(P, m).
    have hsc_norm_0 : socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ))
        = σ * socialCost q P m := by
      rw [hP_norm_def]
      have heq : (fun (_ : Fin d) => (0 : ℝ)) = (fun j => σ * 0) := by
        funext j; ring
      conv_lhs => rw [heq]
      rw [socialCost_scale hq_le σ hσ_nn P_tr_refl _]
      rw [hsc_tr_refl_0]
    -- Apply h_norm.
    have happ : socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ))
                ≤ UB q * socialCost q P_norm f_norm :=
      h_norm q hq hn hn_even hd P_norm hmed_norm f_norm hf_norm_nn hf_norm_unit
    -- Substitute and clear σ.
    rw [hsc_norm_0, hsc_norm] at happ
    -- happ: σ * SC(P, m) ≤ UB q * (σ * OPT)
    -- Multiply by 1/σ = u (since σ > 0).
    have happ' : σ * socialCost q P m ≤ σ * (UB q * OPT) := by linarith
    exact le_of_mul_le_mul_left happ' hσ_pos
