import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.SocialCostTranslationInvariance
import Workspace.ProofLemmas.MedianTranslationInvariance
import Workspace.ProofLemmas.MedianCoordinateReflection
import Workspace.ProofLemmas.LqNormZeroIffEqZero
import Workspace.ProofLemmas.RGLambda2InUnitInterval

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem
open Workspace.ProofLemmas.RGDefs

namespace Workspace.ProofLemmas.RGTranslationScaleNormalize

/-! ### Private invariance helpers (ported verbatim from `CGTranslationScaleNormalize`). -/

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

/-- `augment` commutes with a pointwise affine transform `g j * (· - m j)`
applied to every report and to the appended point `pred` simultaneously:
transforming the augmented instance equals augmenting the transformed instance.
(Generic over the appended point; here applied to `pred`.) -/
private lemma augment_transform {n d : ℕ} (P : Fin n → Fin d → ℝ)
    (pred m : Fin d → ℝ) (g : Fin d → ℝ) (k : ℕ) :
    (fun (i : Fin (n + k)) (j : Fin d) =>
        g j * (augment P pred k i j - m j))
      = augment (fun (i : Fin n) (j : Fin d) => g j * (P i j - m j))
          (fun j => g j * (pred j - m j)) k := by
  funext i j
  unfold augment
  refine Fin.addCases ?_ ?_ i <;> intro i' <;> simp

theorem RGTranslationScaleNormalize
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h_norm : ∀ {n d : ℕ}, 0 < n → Even (n + ⌊c * (n : ℝ)⌋₊) → 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P_norm : Fin n → Fin d → ℝ),
      ∀ (pred : Fin d → ℝ), (∀ j, pred j ≠ 0) →
      ∀ (f : Fin d → ℝ), (∀ j, 0 ≤ f j) → (∀ j, 0 < f j) → lqNorm 2 f = 1 →
      IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
        (augment P_norm pred (⌊c * (n : ℝ)⌋₊)) →
      socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ))
        ≤ Workspace.RobustnessTheorem.RG c * socialCost 2 P_norm f) :
    ∀ {n d : ℕ}, 0 < n → Even (n + ⌊c * (n : ℝ)⌋₊) → 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
        0 < optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P pred (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        (∀ j, pred j ≠ m j) →
        socialCost 2 P m ≤ Workspace.RobustnessTheorem.RG c * optSocialCost 2 P := by
  intro n d hn hne hd hcn P pred fstar hsc_fstar hopt m hm hgp hgp_pred
  have hq : (1 : ℝ) ≤ 2 := by norm_num
  set k : ℕ := ⌊c * (n : ℝ)⌋₊ with hk_def
  set OPT : ℝ := optSocialCost 2 P with hOPT_def
  have hOPT_pos : 0 < OPT := hopt
  have hOPT_nn : 0 ≤ OPT := le_of_lt hOPT_pos
  -- v = fstar - m: optimum after translating m to 0.
  set v : Fin d → ℝ := fun j => fstar j - m j with hv_def
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
  -- General position of the optimum: v j = fstar j - m j ≠ 0.
  have hv_ne : ∀ j, v j ≠ 0 := by
    intro j hvj
    have : fstar j - m j = 0 := by rw [hv_def] at hvj; exact hvj
    exact hgp j (sub_eq_zero.mp this)
  have heps_v_pos : ∀ j, 0 < eps j * v j := by
    intro j
    have hne : eps j * v j ≠ 0 := by
      rw [heps_def]
      by_cases h : 0 ≤ v j
      · simp only [h, if_true, one_mul]; exact hv_ne j
      · simp only [h, if_false, neg_one_mul, neg_ne_zero]; exact hv_ne j
    exact lt_of_le_of_ne (heps_v_nonneg j) (Ne.symm hne)
  -- General position of the prediction: w j = pred j - m j ≠ 0.
  set w : Fin d → ℝ := fun j => pred j - m j with hw_def
  have hw_ne : ∀ j, w j ≠ 0 := by
    intro j hwj
    have : pred j - m j = 0 := by rw [hw_def] at hwj; exact hwj
    exact hgp_pred j (sub_eq_zero.mp this)
  -- P_tr_refl i j = eps j * (P i j - m j); v_refl j = eps j * v j > 0.
  set P_tr_refl : Fin n → Fin d → ℝ := fun i j => eps j * (P i j - m j) with hP_tr_def
  set v_refl : Fin d → ℝ := fun j => eps j * v j with hv_refl_def
  have hv_refl_nn : ∀ j, 0 ≤ v_refl j := heps_v_nonneg
  have hv_refl_pos : ∀ j, 0 < v_refl j := heps_v_pos
  -- pred_refl j = eps j * w j: the reflected prediction.  Nonzero by general position.
  set pred_refl : Fin d → ℝ := fun j => eps j * w j with hpred_refl_def
  have hpred_refl_ne : ∀ j, pred_refl j ≠ 0 := by
    intro j
    show eps j * w j ≠ 0
    rcases heps_pm j with h1 | h1
    · rw [h1, one_mul]; exact hw_ne j
    · rw [h1, neg_one_mul, neg_ne_zero]; exact hw_ne j
  -- Median 0 of the *augmented* translated+reflected instance.
  -- Q := augment P pred k; transport median m of Q to median 0 of the transform.
  have hmed_aug_tr : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
      (fun (i : Fin (n + k)) (j : Fin d) => augment P pred k i j - m j) := by
    have h1 := (MedianTranslationInvariance (augment P pred k) m m).mp hm
    have heq : (fun j => m j - m j) = (fun (_ : Fin d) => (0 : ℝ)) := by
      funext j; ring
    rw [heq] at h1
    exact h1
  have hmed_aug_tr_refl : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
      (fun (i : Fin (n + k)) (j : Fin d) => eps j * (augment P pred k i j - m j)) := by
    exact MedianCoordinateReflection
      (fun i j => augment P pred k i j - m j) eps heps_pm hmed_aug_tr
  -- SC(P_tr_refl, v_refl) = OPT.
  have hsc_tr_refl : socialCost 2 P_tr_refl v_refl = OPT := by
    have h1 : socialCost 2 (fun (i : Fin n) (j : Fin d) => P i j - m j) v
              = socialCost 2 P fstar := by
      have := SocialCostTranslationInvariance 2 P m fstar
      convert this using 2
    have h2 : socialCost 2 P_tr_refl v_refl =
              socialCost 2 (fun i j => P i j - m j) v := by
      rw [hP_tr_def, hv_refl_def]
      exact socialCost_coord_reflection 2 eps heps_pm _ _
    rw [h2, h1, hsc_fstar]
  -- SC(P_tr_refl, 0) = SC(P, m).
  have hsc_tr_refl_0 : socialCost 2 P_tr_refl (fun (_ : Fin d) => (0 : ℝ))
      = socialCost 2 P m := by
    have h1 : socialCost 2 P_tr_refl (fun (_ : Fin d) => (0 : ℝ))
              = socialCost 2 (fun (i : Fin n) (j : Fin d) => P i j - m j)
                  (fun (_ : Fin d) => (0 : ℝ)) := by
      rw [hP_tr_def]
      have heq : (fun (_ : Fin d) => (0 : ℝ)) = (fun (j : Fin d) => eps j * 0) := by
        funext j; ring
      conv_lhs => rw [heq]
      exact socialCost_coord_reflection 2 eps heps_pm _ _
    have h2 : socialCost 2 (fun (i : Fin n) (j : Fin d) => P i j - m j)
                (fun (_ : Fin d) => (0 : ℝ)) = socialCost 2 P m := by
      have := SocialCostTranslationInvariance 2 P m m
      have heq : (fun j => m j - m j) = (fun (_ : Fin d) => (0 : ℝ)) := by
        funext j; ring
      rw [heq] at this
      exact this
    rw [h1, h2]
  -- Case split on the norm of v_refl.
  set u : ℝ := lqNorm 2 v_refl with hu_def
  have hu_nn : 0 ≤ u := lqNorm_nonneg hq _
  by_cases hu_zero : u = 0
  · -- Degenerate: v_refl = 0, so fstar = m, so OPT = SC(P, m).
    have hv_refl_eq_zero : v_refl = (fun _ => 0) := by
      have := (LqNormZeroIffEqZero 2 hq hd v_refl).mp hu_zero
      ext j
      have := congr_fun this j
      simpa using this
    have hv_zero : ∀ j, v j = 0 := by
      intro j
      have hvr : eps j * v j = 0 := by
        have := congr_fun hv_refl_eq_zero j
        simpa [hv_refl_def] using this
      rcases heps_pm j with h1 | h1
      · rw [h1] at hvr; linarith
      · rw [h1] at hvr; linarith
    have hfstar_eq_m : fstar = m := by
      funext j
      have := hv_zero j
      simp [hv_def] at this
      linarith
    have hSC_eq_OPT : socialCost 2 P m = OPT := by
      rw [← hfstar_eq_m]
      exact hsc_fstar
    rw [hSC_eq_OPT]
    have hRG_ge_one : 1 ≤ Workspace.RobustnessTheorem.RG c :=
      (Workspace.ProofLemmas.RGLambda2InUnitInterval.RGLambda2InUnitInterval c hc0 hc1).2.2.le
    nlinarith [hOPT_pos]
  · -- Generic: u > 0. Scale by σ = 1/u.
    have hu_pos : 0 < u := lt_of_le_of_ne hu_nn (Ne.symm hu_zero)
    set σ : ℝ := 1 / u with hσ_def
    have hσ_pos : 0 < σ := by rw [hσ_def]; positivity
    have hσ_nn : 0 ≤ σ := le_of_lt hσ_pos
    set P_norm : Fin n → Fin d → ℝ := fun i j => σ * P_tr_refl i j with hP_norm_def
    set f_norm : Fin d → ℝ := fun j => σ * v_refl j with hf_norm_def
    -- The normalized prediction: pred_norm j = σ * pred_refl j.
    set pred_norm : Fin d → ℝ := fun j => σ * pred_refl j with hpred_norm_def
    -- pred_norm in general position.
    have hpred_norm_ne : ∀ j, pred_norm j ≠ 0 := by
      intro j
      rw [hpred_norm_def]
      exact mul_ne_zero (ne_of_gt hσ_pos) (hpred_refl_ne j)
    -- Median 0 of the augmented normalized instance (appended copies sit at pred_norm).
    have hmed_aug_norm : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
        (augment P_norm pred_norm k) := by
      have hscale := (median_scale
        (fun (i : Fin (n + k)) (j : Fin d) => eps j * (augment P pred k i j - m j))
        (fun (_ : Fin d) => (0 : ℝ)) σ hσ_pos).mp hmed_aug_tr_refl
      have heq0 : (fun j => σ * (0 : ℝ)) = (fun (_ : Fin d) => (0 : ℝ)) := by
        funext j; ring
      rw [heq0] at hscale
      -- Rewrite the scaled+reflected augmented instance as augment of P_norm/pred_norm.
      have hcomm := augment_transform P pred m (fun j => σ * eps j) k
      have hinst : (fun (i : Fin (n + k)) (j : Fin d) =>
            σ * (eps j * (augment P pred k i j - m j)))
          = augment P_norm pred_norm k := by
        rw [hP_norm_def, hpred_norm_def, hP_tr_def, hpred_refl_def, hw_def]
        rw [show (fun (i : Fin (n + k)) (j : Fin d) =>
              σ * (eps j * (augment P pred k i j - m j)))
            = (fun (i : Fin (n + k)) (j : Fin d) =>
              (fun j => σ * eps j) j * (augment P pred k i j - m j)) by
          funext i j; ring]
        rw [hcomm]
        congr 1
        · funext i j; ring
        · funext j; ring
      rw [hinst] at hscale
      exact hscale
    -- f_norm ≥ 0.
    have hf_norm_nn : ∀ j, 0 ≤ f_norm j := by
      intro j
      rw [hf_norm_def]
      exact mul_nonneg hσ_nn (hv_refl_nn j)
    -- f_norm > 0 (general position): each coordinate is σ·v_refl j with σ, v_refl j > 0.
    have hf_norm_pos : ∀ j, 0 < f_norm j := by
      intro j
      rw [hf_norm_def]
      exact mul_pos hσ_pos (hv_refl_pos j)
    -- lqNorm 2 f_norm = 1.
    have hf_norm_unit : lqNorm 2 f_norm = 1 := by
      rw [hf_norm_def]
      rw [lqNorm_smul hq σ v_refl]
      rw [abs_of_nonneg hσ_nn]
      rw [hσ_def, ← hu_def]
      field_simp
    -- SC(P_norm, f_norm) = σ * OPT.
    have hsc_norm : socialCost 2 P_norm f_norm = σ * OPT := by
      rw [hP_norm_def, hf_norm_def]
      rw [socialCost_scale hq σ hσ_nn P_tr_refl v_refl]
      rw [hsc_tr_refl]
    -- SC(P_norm, 0) = σ * SC(P, m).
    have hsc_norm_0 : socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ))
        = σ * socialCost 2 P m := by
      rw [hP_norm_def]
      have heq : (fun (_ : Fin d) => (0 : ℝ)) = (fun j => σ * 0) := by
        funext j; ring
      conv_lhs => rw [heq]
      rw [socialCost_scale hq σ hσ_nn P_tr_refl _]
      rw [hsc_tr_refl_0]
    -- Apply h_norm with pred := pred_norm, f := f_norm.
    have happ : socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ))
                ≤ Workspace.RobustnessTheorem.RG c * socialCost 2 P_norm f_norm :=
      h_norm hn hne hd hcn P_norm pred_norm hpred_norm_ne f_norm hf_norm_nn hf_norm_pos
        hf_norm_unit hmed_aug_norm
    rw [hsc_norm_0, hsc_norm] at happ
    have happ' : σ * socialCost 2 P m ≤ σ * (Workspace.RobustnessTheorem.RG c * OPT) := by
      nlinarith [happ]
    exact le_of_mul_le_mul_left happ' hσ_pos

end Workspace.ProofLemmas.RGTranslationScaleNormalize
