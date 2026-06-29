import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.RGMedianConstraintFromAugment
import Workspace.ProofLemmas.RGWorstCasePredictionSignature
import Workspace.ProofLemmas.RGRelaxedConstraint
import Workspace.ProofLemmas.RGRelaxedCoreNonneg
import Workspace.ProofLemmas.RGLambda2InUnitInterval
import Workspace.ProofLemmas.RGDeltaLambda
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.LocalOptimumCharacterization
import Workspace.ProofLemmas.GLambdaLowerBound_h

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem
open Workspace.ProofLemmas.RGDefs
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.LambdaDeltaIdentity

namespace Workspace.ProofLemmas.RGNormalizedCoreInequality

namespace RGNormalizedCoreInequalityProof

-- Auxiliary lemma: lqNorm bounds individual coordinates.
private lemma lqNorm_ge_abs_coord {q : ℝ} (hq : 1 ≤ q) {d : ℕ}
    (x : Fin d → ℝ) (j : Fin d) :
    |x j| ≤ lqNorm q x := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_pos : 0 < (1 : ℝ) / q := by positivity
  have h_pos : ∀ k, 0 ≤ |x k| ^ q := fun k => Real.rpow_nonneg (abs_nonneg _) q
  have h_le : |x j| ^ q ≤ ∑ k, |x k| ^ q := by
    have := Finset.single_le_sum (f := fun k => |x k| ^ q)
      (s := Finset.univ) (a := j)
      (fun k _ => h_pos k) (Finset.mem_univ j)
    exact this
  have h_lhs_nn : 0 ≤ |x j| ^ q := h_pos j
  have h_rhs_nn : 0 ≤ ∑ k, |x k| ^ q := sum_abs_rpow_nonneg q x
  have h2 : (|x j| ^ q) ^ ((1 : ℝ) / q) ≤ (∑ k, |x k| ^ q) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow h_lhs_nn h_le (le_of_lt h_inv_pos)
  have habs_nn : (0 : ℝ) ≤ |x j| := abs_nonneg _
  have h3 : (|x j| ^ q) ^ ((1 : ℝ) / q) = |x j| := by
    rw [← Real.rpow_mul habs_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
  rw [h3] at h2
  exact h2

-- Continuity of lqNorm
private lemma lqNorm_continuous {q : ℝ} (hq : 1 ≤ q) {d : ℕ} :
    Continuous (fun x : Fin d → ℝ => lqNorm q x) := by
  unfold lqNorm
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h_inv_nn : 0 ≤ (1 : ℝ) / q := by positivity
  have hq_nn : 0 ≤ q := le_of_lt hq_pos
  have h_inner : Continuous (fun x : Fin d → ℝ => ∑ j, |x j| ^ q) := by
    apply continuous_finset_sum
    intro j _
    exact (Real.continuous_rpow_const hq_nn).comp ((continuous_apply j).abs)
  exact (Real.continuous_rpow_const h_inv_nn).comp h_inner

-- Continuity of g_lambda in p
private lemma g_lambda_continuous {q : ℝ} (hq : 1 ≤ q) (lambda : ℝ) {d : ℕ}
    (f : Fin d → ℝ) :
    Continuous (fun p : Fin d → ℝ => g_lambda q lambda f p) := by
  unfold g_lambda
  have h_arg : Continuous (fun p : Fin d → ℝ => fun j => p j - f j) := by
    apply continuous_pi
    intro j
    exact (continuous_apply j).sub continuous_const
  have h1 : Continuous (fun p : Fin d → ℝ => lqNorm q (fun j => p j - f j)) :=
    (lqNorm_continuous hq).comp h_arg
  have h2 : Continuous (fun p : Fin d → ℝ => lqNorm q p) := lqNorm_continuous hq
  exact h1.sub (continuous_const.mul h2)

-- Sum of g_lambda is continuous
private lemma sum_g_lambda_continuous {q : ℝ} (hq : 1 ≤ q) (lambda : ℝ) {n d : ℕ}
    (f : Fin d → ℝ) :
    Continuous (fun p : Fin n → Fin d → ℝ => ∑ i, g_lambda q lambda f (p i)) := by
  apply continuous_finset_sum
  intro i _
  exact (g_lambda_continuous hq lambda f).comp (continuous_apply i)

-- Coercive lower bound
private lemma g_lambda_lower_bound {q : ℝ} (hq : 1 ≤ q) {lambda : ℝ}
    {d : ℕ} (f : Fin d → ℝ) (hf_norm : lqNorm q f = 1) (p : Fin d → ℝ) :
    (1 - lambda) * lqNorm q p - 1 ≤ g_lambda q lambda f p := by
  unfold g_lambda
  have h := LqNormSubReverseTriangle hq p f
  rw [hf_norm] at h
  linarith

/-- **RG constrained-min existence** (constraint-free; the column-sum constraint
is unused in the consistency `CGConstrainedMinExists` / `ConstrainedMinExists`
existence argument, which only needs the `±1` signature). For the worst-case
prediction signature `(−1,…,−1)` the constraint is `∑ σ = ⌊cn⌋`, so neither
`ConstrainedMinExists` (`∑ = 0`) nor `CGConstrainedMinExists` (`∑ = −⌊cn⌋`)
applies directly; we inline the existence proof here as instructed (no new
RG* node file). -/
private theorem rgConstrainedMinExists
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {n d : ℕ}
    (f : Fin d → ℝ) (hf_norm : lqNorm q f = 1)
    (sigma_assign : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma_assign i j = 1 ∨ sigma_assign i j = -1) :
    ∃ p_star : Fin n → Fin d → ℝ,
      (∀ i j, (sigma_assign i j = 1 → 0 ≤ p_star i j) ∧
              (sigma_assign i j = -1 → p_star i j ≤ 0)) ∧
      (∀ p : Fin n → Fin d → ℝ,
        (∀ i j, (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                (sigma_assign i j = -1 → p i j ≤ 0)) →
        (∑ i, g_lambda q lambda f (p_star i)) ≤ (∑ i, g_lambda q lambda f (p i))) := by
  classical
  have hq_le : 1 ≤ q := le_of_lt hq
  set S : Set (Fin n → Fin d → ℝ) :=
    {p | ∀ i j, (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                (sigma_assign i j = -1 → p i j ≤ 0)} with hS_def
  set G : (Fin n → Fin d → ℝ) → ℝ :=
    fun p => ∑ i, g_lambda q lambda f (p i) with hG_def
  have hG_cont : Continuous G := sum_g_lambda_continuous hq_le lambda f
  have h0_mem : (fun _ _ => (0 : ℝ)) ∈ S := by
    intro i j
    refine ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩
  have hS_closed : IsClosed S := by
    have : S = ⋂ (i : Fin n) (j : Fin d),
        {p : Fin n → Fin d → ℝ | (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                                  (sigma_assign i j = -1 → p i j ≤ 0)} := by
      ext p
      simp only [Set.mem_iInter, Set.mem_setOf_eq, hS_def]
    rw [this]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    have h_eq : {p : Fin n → Fin d → ℝ | (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                                  (sigma_assign i j = -1 → p i j ≤ 0)} =
        {p | sigma_assign i j = 1 → 0 ≤ p i j} ∩
        {p | sigma_assign i j = -1 → p i j ≤ 0} := by
      ext p; simp [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [h_eq]
    apply IsClosed.inter
    · rcases hsigma_pm i j with h1 | h1
      · have heq : {p : Fin n → Fin d → ℝ | sigma_assign i j = 1 → 0 ≤ p i j}
            = {p : Fin n → Fin d → ℝ | 0 ≤ p i j} := by
          ext p; simp [h1]
        rw [heq]
        have h_cont : Continuous (fun p : Fin n → Fin d → ℝ => p i j) :=
          (continuous_apply j).comp (continuous_apply i)
        exact isClosed_le continuous_const h_cont
      · have heq : {p : Fin n → Fin d → ℝ | sigma_assign i j = 1 → 0 ≤ p i j}
            = Set.univ := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro hcontr
          rw [h1] at hcontr
          linarith
        rw [heq]; exact isClosed_univ
    · rcases hsigma_pm i j with h1 | h1
      · have heq : {p : Fin n → Fin d → ℝ | sigma_assign i j = -1 → p i j ≤ 0}
            = Set.univ := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro hcontr
          rw [h1] at hcontr
          linarith
        rw [heq]; exact isClosed_univ
      · have heq : {p : Fin n → Fin d → ℝ | sigma_assign i j = -1 → p i j ≤ 0}
            = {p : Fin n → Fin d → ℝ | p i j ≤ 0} := by
          ext p; simp [h1]
        rw [heq]
        have h_cont : Continuous (fun p : Fin n → Fin d → ℝ => p i j) :=
          (continuous_apply j).comp (continuous_apply i)
        exact isClosed_le h_cont continuous_const
  set K : ℝ := G (fun _ _ => 0) with hK_def
  set T : Set (Fin n → Fin d → ℝ) := S ∩ {p | G p ≤ K} with hT_def
  have hT_closed : IsClosed T := hS_closed.inter (isClosed_le hG_cont continuous_const)
  have hT_bdd : Bornology.IsBounded T := by
    have h_one_lam_pos : 0 < 1 - lambda := by linarith
    have h_one_lam_nn : 0 ≤ 1 - lambda := le_of_lt h_one_lam_pos
    set R : ℝ := (K + n) / (1 - lambda) with hR_def
    have h_pj_bound : ∀ p ∈ T, ∀ i j, |p i j| ≤ R := by
      intro p hp i j
      obtain ⟨hpS, hpK⟩ := hp
      simp only [Set.mem_setOf_eq] at hpK
      have h_each : ∀ i', (1 - lambda) * lqNorm q (p i') - 1 ≤ g_lambda q lambda f (p i') :=
        fun i' => g_lambda_lower_bound hq_le f hf_norm (p i')
      have h_sum : (1 - lambda) * (∑ i', lqNorm q (p i')) - n ≤ ∑ i', g_lambda q lambda f (p i') := by
        have h1 : (∑ i' : Fin n, ((1 - lambda) * lqNorm q (p i') - 1)) ≤
                   ∑ i', g_lambda q lambda f (p i') := by
          apply Finset.sum_le_sum
          intro i' _
          exact h_each i'
        have h2 : (∑ i' : Fin n, ((1 - lambda) * lqNorm q (p i') - 1)) =
                  (1 - lambda) * (∑ i', lqNorm q (p i')) - n := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum]
          simp
        linarith [h1, h2.symm.le, h2.le]
      have h_sum2 : (1 - lambda) * (∑ i', lqNorm q (p i')) ≤ K + n := by
        have : ∑ i', g_lambda q lambda f (p i') = G p := rfl
        linarith
      have h_nn : ∀ i', 0 ≤ lqNorm q (p i') := fun i' => lqNorm_nonneg hq_le _
      have h_single_le_sum : lqNorm q (p i) ≤ ∑ i', lqNorm q (p i') := by
        exact Finset.single_le_sum (f := fun i' => lqNorm q (p i'))
          (s := Finset.univ) (a := i)
          (fun i' _ => h_nn i') (Finset.mem_univ _)
      have h_pi_bound : (1 - lambda) * lqNorm q (p i) ≤ K + n := by
        calc (1 - lambda) * lqNorm q (p i) ≤ (1 - lambda) * (∑ i', lqNorm q (p i')) := by
              exact mul_le_mul_of_nonneg_left h_single_le_sum h_one_lam_nn
          _ ≤ K + n := h_sum2
      have h_lqnorm_le_R : lqNorm q (p i) ≤ R := by
        rw [hR_def]
        rw [le_div_iff₀ h_one_lam_pos]
        linarith [mul_comm (1 - lambda) (lqNorm q (p i))]
      have h_abs_le : |p i j| ≤ lqNorm q (p i) := lqNorm_ge_abs_coord hq_le (p i) j
      linarith
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin n → Fin d → ℝ)]
    refine ⟨R, ?_⟩
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    have hR_nn : 0 ≤ R := by
      rw [hR_def]
      apply div_nonneg
      · have h_g0 : ∀ i : Fin n, g_lambda q lambda f ((fun (_ : Fin n) (_ : Fin d) => (0 : ℝ)) i) = 1 := by
          intro i
          unfold g_lambda
          have h_pi : ((fun (_ : Fin n) (_ : Fin d) => (0 : ℝ)) i) = (fun (_ : Fin d) => (0 : ℝ)) := rfl
          rw [h_pi]
          have h_eq : (fun j : Fin d => ((fun (_ : Fin d) => (0 : ℝ)) j) - f j) = (fun j => -f j) := by
            funext j; simp
          rw [h_eq]
          have h_neg : lqNorm q (fun j : Fin d => -f j) = lqNorm q f := by
            have h1 := lqNorm_smul hq_le (-1 : ℝ) f
            have h2 : (fun j : Fin d => (-1 : ℝ) * f j) = (fun j => -f j) := by
              funext j; ring
            rw [h2] at h1
            simp at h1
            exact h1
          rw [h_neg, hf_norm]
          have h_zero : lqNorm q (fun (_ : Fin d) => (0 : ℝ)) = 0 := lqNorm_zero hq_le
          rw [h_zero]
          ring
        have hK_val : K = n := by
          show G (fun (_ : Fin n) (_ : Fin d) => (0 : ℝ)) = n
          show (∑ i : Fin n, g_lambda q lambda f ((fun (_ : Fin n) (_ : Fin d) => (0 : ℝ)) i)) = n
          rw [Finset.sum_congr rfl (fun i _ => h_g0 i)]
          simp
        rw [hK_val]
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      · exact h_one_lam_nn
    rw [pi_norm_le_iff_of_nonneg hR_nn]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR_nn]
    intro j
    simp only [Real.norm_eq_abs]
    exact h_pj_bound p hp i j
  have hT_compact : IsCompact T :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hT_closed, hT_bdd⟩
  have hT_nonempty : T.Nonempty := by
    refine ⟨fun _ _ => 0, h0_mem, ?_⟩
    simp only [Set.mem_setOf_eq]
    rfl
  have hG_cont_on : ContinuousOn G T := hG_cont.continuousOn
  obtain ⟨p_star, hp_star_T, hp_star_min⟩ :=
    hT_compact.exists_isMinOn hT_nonempty hG_cont_on
  refine ⟨p_star, hp_star_T.1, ?_⟩
  intro p hp
  by_cases hpK : G p ≤ K
  · have hpT : p ∈ T := ⟨hp, hpK⟩
    exact hp_star_min hpT
  · push_neg at hpK
    have hp_star_K : G p_star ≤ K := hp_star_T.2
    linarith

end RGNormalizedCoreInequalityProof

open RGNormalizedCoreInequalityProof

theorem RGNormalizedCoreInequality_fpos
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n d : ℕ} (hn_pos : 0 < n) (hne : Even (n + ⌊c * (n : ℝ)⌋₊)) (hd : 1 ≤ d)
    (hcn : (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ))
    (P_norm : Fin n → Fin d → ℝ)
    (pred : Fin d → ℝ) (hpred_gp : ∀ j, pred j ≠ 0)
    (f : Fin d → ℝ) (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j)
    (hf_norm : lqNorm 2 f = 1)
    (hP_med : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
                (augment P_norm pred (⌊c * (n : ℝ)⌋₊))) :
    socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ))
      ≤ Workspace.RobustnessTheorem.RG c * socialCost 2 P_norm f := by
  classical
  -- Fix q = 2 and lambda := lambda2 c.
  have hq : (1 : ℝ) < (2 : ℝ) := by norm_num
  have hq_le : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hq_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hq_ne : (2 : ℝ) ≠ 0 := by norm_num
  set lambda : ℝ := lambda2 c with hlam_def
  -- 0 < lambda2 c, lambda2 c < 1, 1 < RG c.
  obtain ⟨hlam_pos, hlam_lt_one, hRG_gt_one⟩ :=
    Workspace.ProofLemmas.RGLambda2InUnitInterval.RGLambda2InUnitInterval c hc0 hc1
  -- The relation RG c = 1 / lambda2 c (cite RG_eq_inv_lambda2).
  have h_RG_eq : Workspace.RobustnessTheorem.RG c = 1 / lambda := by
    rw [hlam_def]; exact RG_eq_inv_lambda2 c hc0 hc1
  -- Rewrite the goal: SC(0) ≤ RG c · SC(f) ↔ lambda · SC(0) ≤ SC(f).
  rw [h_RG_eq]
  rw [show (1 : ℝ) / lambda * socialCost 2 P_norm f = socialCost 2 P_norm f / lambda by ring]
  rw [le_div_iff₀ hlam_pos]
  -- f satisfies ∑ (f j)^2 = 1 since lqNorm 2 f = 1.
  have hf_pow_sum : (∑ j, (f j) ^ (2 : ℝ)) = 1 := by
    have h1 : lqNorm 2 f = (∑ j, |f j| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := rfl
    rw [h1] at hf_norm
    have h_inner_nn : 0 ≤ ∑ j, |f j| ^ (2 : ℝ) := sum_abs_rpow_nonneg 2 f
    have hsum_eq : (∑ j, |f j| ^ (2 : ℝ)) = 1 := by
      have h2 : ((∑ j, |f j| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := by
        rw [hf_norm]
      rw [← Real.rpow_mul h_inner_nn, one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one,
          Real.one_rpow] at h2
      exact h2
    have h_abs : ∀ j, |f j| ^ (2 : ℝ) = (f j) ^ (2 : ℝ) := by
      intro j; rw [abs_of_nonneg (hf_nn j)]
    rw [show (∑ j, (f j) ^ (2 : ℝ)) = (∑ j, |f j| ^ (2 : ℝ)) from
      Finset.sum_congr rfl (fun j _ => (h_abs j).symm)]
    exact hsum_eq
  -- Prediction signature s = σ(pred).
  set s : Fin d → ℝ := fun j => if pred j > 0 then (1 : ℝ) else (-1 : ℝ) with hs_def
  have hs_pm : ∀ j, s j = 1 ∨ s j = -1 := by
    intro j; rw [hs_def]; by_cases h : pred j > 0 <;> simp [h]
  have hs_pos : ∀ j, pred j > 0 → s j = 1 := by
    intro j hj; rw [hs_def]; simp [hj]
  have hs_neg : ∀ j, pred j < 0 → s j = -1 := by
    intro j hj; rw [hs_def]
    have : ¬ (pred j > 0) := by linarith
    simp [this]
  -- Step (3): obtain sigma via RGMedianConstraintFromAugment (SIGNED constraint).
  obtain ⟨sigma, hsigma_pm, hsigma_pos, hsigma_neg, hsigma_cons, hsigma_balance⟩ :=
    Workspace.ProofLemmas.RGMedianConstraintFromAugment.RGMedianConstraintFromAugment
      c hc0 hc1 hne f hf_pow_sum pred hpred_gp s hs_pm hs_pos hs_neg P_norm hP_med
  -- NEW step: reduce to worst-case prediction signature (−1,…,−1).
  obtain ⟨P', sigma', hsigma'_pm, hsigma'_pos, hsigma'_neg, hsigma'_cons, hg_le⟩ :=
    Workspace.ProofLemmas.RGWorstCasePredictionSignature.RGWorstCasePredictionSignature
      c hc0 hc1 lambda f hf_pos P_norm s hs_pm sigma hsigma_pm hsigma_pos hsigma_neg hsigma_cons
  -- The worst-case constraint: ∑ sigma' i j = ⌊cn⌋.
  have hsigma'_eq : ∀ j, ∑ i, sigma' i j = (⌊c * (n : ℝ)⌋₊ : ℝ) := by
    intro j; have := hsigma'_cons j; simpa using this
  -- Step (4): apply RG constrained-min existence to sigma' → p_star.
  obtain ⟨p_star, hp_star_in, hp_star_min⟩ :=
    rgConstrainedMinExists 2 hq lambda hlam_pos hlam_lt_one
      f hf_norm sigma' hsigma'_pm
  -- P' itself satisfies the orthant constraint w.r.t. sigma'.
  have hP'_in : ∀ i j, (sigma' i j = 1 → 0 ≤ P' i j) ∧
                       (sigma' i j = -1 → P' i j ≤ 0) := by
    intro i j
    refine ⟨?_, ?_⟩
    · intro hsig
      by_contra h_neg
      push_neg at h_neg
      have := hsigma'_neg i j h_neg
      rw [this] at hsig
      norm_num at hsig
    · intro hsig
      by_contra h_pos
      push_neg at h_pos
      have := hsigma'_pos i j h_pos
      rw [this] at hsig
      norm_num at hsig
  -- The minimization gives: ∑ g(p_star) ≤ ∑ g(P').
  have h_p_star_le : (∑ i, g_lambda 2 lambda f (p_star i))
      ≤ (∑ i, g_lambda 2 lambda f (P' i)) := hp_star_min P' hP'_in
  -- Define x_i := ∑_{j ∈ S_i} (f j)^2, where S_i := {j : sigma' i j = 1}.
  set x : Fin n → ℝ := fun i =>
    ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1)), (f j) ^ (2 : ℝ) with hx_def
  have hx_nn : ∀ i, 0 ≤ x i := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) (2 : ℝ)
  have hx_le_one : ∀ i, x i ≤ 1 := by
    intro i
    have h_split := Finset.sum_compl_add_sum
      (s := (Finset.univ.filter (fun j : Fin d => sigma' i j = 1)))
      (f := fun j => (f j) ^ (2 : ℝ))
    have h_compl_nn : 0 ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1))ᶜ, (f j) ^ (2 : ℝ) := by
      apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (hf_nn j) (2 : ℝ)
    have hf_sum_eq :
        (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1))ᶜ, (f j) ^ (2 : ℝ)) +
          (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1)), (f j) ^ (2 : ℝ)) =
        ∑ j, (f j) ^ (2 : ℝ) := h_split
    rw [hf_pow_sum] at hf_sum_eq
    show (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1)), (f j) ^ (2 : ℝ)) ≤ 1
    linarith
  -- ∑ x i = (1+c)/2 · n by RGRelaxedConstraint.
  -- First convert the worst-case column-sum to the card-balance form.
  have hbalance : ∀ j,
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma' i j = 1)).card : ℝ)
        = ((n : ℝ) + ⌊c * (n : ℝ)⌋₊) / 2 := by
    intro j
    -- ∑ sigma' i j = ⌊cn⌋, with σ ∈ {−1,1}: #{+1} − #{−1} = ⌊cn⌋, #{+1}+#{−1}=n.
    have hcol := hsigma'_eq j
    set Sp := (Finset.univ : Finset (Fin n)).filter (fun i => sigma' i j = 1) with hSp_def
    set Sm := (Finset.univ : Finset (Fin n)).filter (fun i => sigma' i j = -1) with hSm_def
    -- The sum splits as #Sp - #Sm.
    have hsum_split : ∑ i, sigma' i j = (Sp.card : ℝ) - (Sm.card : ℝ) := by
      rw [hSp_def, hSm_def]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun i => sigma' i j = 1)]
      have h1 : ∑ i ∈ Finset.univ.filter (fun i => sigma' i j = 1), sigma' i j
          = (Sp.card : ℝ) := by
        rw [hSp_def]
        rw [Finset.sum_congr rfl (fun i hi => by
          simp only [Finset.mem_filter] at hi; exact hi.2)]
        simp
      have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ sigma' i j = 1), sigma' i j
          = -(Sm.card : ℝ) := by
        have hset : (Finset.univ.filter (fun i => ¬ sigma' i j = 1))
            = Finset.univ.filter (fun i => sigma' i j = -1) := by
          apply Finset.filter_congr
          intro i _
          constructor
          · intro h
            rcases hsigma'_pm i j with h' | h'
            · exact absurd h' h
            · exact h'
          · intro h
            rw [h]; norm_num
        rw [hset, ← hSm_def]
        rw [Finset.sum_congr rfl (fun i hi => by
          simp only [Finset.mem_filter, hSm_def] at hi; exact hi.2)]
        simp
      rw [h1, h2, ← hSp_def, ← hSm_def]; ring
    -- #Sp + #Sm = n.
    have hcard_total : (Sp.card : ℝ) + (Sm.card : ℝ) = (n : ℝ) := by
      have : Sp.card + Sm.card = Fintype.card (Fin n) := by
        rw [hSp_def, hSm_def]
        have hneg : (Finset.univ.filter (fun i => sigma' i j = -1))
            = (Finset.univ.filter (fun i => ¬ sigma' i j = 1)) := by
          apply Finset.filter_congr
          intro i _
          constructor
          · intro h hcontr; rw [h] at hcontr; norm_num at hcontr
          · intro h
            rcases hsigma'_pm i j with h' | h'
            · exact absurd h' h
            · exact h'
        rw [hneg, Finset.filter_card_add_filter_neg_card_eq_card (p := fun i => sigma' i j = 1),
          Finset.card_univ]
      have := this
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    rw [hsum_split] at hcol
    rw [hSp_def] at hcol ⊢
    linarith
  have hx_sum : (∑ i, x i) = (1 + c) / 2 * (n : ℝ) := by
    have := Workspace.ProofLemmas.RGRelaxedConstraint.RGRelaxedConstraint
      c hcn f hf_pow_sum sigma' hsigma'_pm hbalance
    exact this
  -- Define the lower-bound delta (= delta2 c definitionally).
  set delta : ℝ := delta_of_lambda 2 lambda with hdelta_def
  -- Per-agent local-min argument.
  have h_per_agent_min : ∀ i (p_i : Fin d → ℝ),
      (∀ j, (sigma' i j = 1 → 0 ≤ p_i j) ∧ (sigma' i j = -1 → p_i j ≤ 0)) →
      g_lambda 2 lambda f (p_star i) ≤ g_lambda 2 lambda f p_i := by
    intro i p_i hp_i_in
    let p' : Fin n → Fin d → ℝ := fun i' => if i' = i then p_i else p_star i'
    have hp'_in : ∀ i' j, (sigma' i' j = 1 → 0 ≤ p' i' j) ∧
                          (sigma' i' j = -1 → p' i' j ≤ 0) := by
      intro i' j
      by_cases hi' : i' = i
      · subst hi'
        show (sigma' i' j = 1 → 0 ≤ (if i' = i' then p_i else p_star i') j) ∧
             (sigma' i' j = -1 → (if i' = i' then p_i else p_star i') j ≤ 0)
        simp only [if_true]
        exact hp_i_in j
      · show (sigma' i' j = 1 → 0 ≤ (if i' = i then p_i else p_star i') j) ∧
             (sigma' i' j = -1 → (if i' = i then p_i else p_star i') j ≤ 0)
        simp only [if_neg hi']
        exact hp_star_in i' j
    have h_global := hp_star_min p' hp'_in
    have h_at_i : p' i = p_i := by simp [p']
    have h_off_i : ∀ i' ∈ Finset.univ.erase i, p' i' = p_star i' := by
      intro i' hi'
      rw [Finset.mem_erase] at hi'
      simp [p', hi'.1]
    have h_sum_p' :
        (∑ i', g_lambda 2 lambda f (p' i')) =
          g_lambda 2 lambda f p_i + ∑ i' ∈ Finset.univ.erase i, g_lambda 2 lambda f (p_star i') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      congr 1
      · rw [h_at_i]
      · apply Finset.sum_congr rfl
        intro i' hi'
        rw [h_off_i i' hi']
    have h_sum_pstar :
        (∑ i', g_lambda 2 lambda f (p_star i')) =
          g_lambda 2 lambda f (p_star i) + ∑ i' ∈ Finset.univ.erase i, g_lambda 2 lambda f (p_star i') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [h_sum_p', h_sum_pstar] at h_global
    linarith
  have h_local_min : ∀ i,
      ∃ ε > (0 : ℝ),
        ∀ p_i : Fin d → ℝ,
          (∀ j, (sigma' i j = 1 → 0 ≤ p_i j) ∧ (sigma' i j = -1 → p_i j ≤ 0)) →
          (∀ j, |p_i j - p_star i j| < ε) →
          g_lambda 2 lambda f (p_star i) ≤ g_lambda 2 lambda f p_i := by
    intro i
    refine ⟨1, by norm_num, ?_⟩
    intro p_i hp_i_in _
    exact h_per_agent_min i p_i hp_i_in
  -- Per-agent g ≥ h via LocalOptimumCharacterization + GLambdaLowerBound_h.
  have h_per_agent_g_ge_h : ∀ i,
      lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2))
        ≤ g_lambda 2 lambda f (p_star i) := by
    intro i
    have hp_star_i_in : ∀ j, (sigma' i j = 1 → 0 ≤ p_star i j) ∧
                              (sigma' i j = -1 → p_star i j ≤ 0) := hp_star_in i
    have hsigma_i_pm : ∀ j, sigma' i j = 1 ∨ sigma' i j = -1 := fun j => hsigma'_pm i j
    have h_local := LocalOptimumCharacterization 2 hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma' i) hsigma_i_pm (p_star i)
      hp_star_i_in (h_local_min i)
    have h_glb := GLambdaLowerBound_h 2 hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma' i) hsigma_i_pm (p_star i) h_local
    show lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2))
      ≤ g_lambda 2 lambda f (p_star i)
    have hx_eq : x i =
        ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma' i j = 1)), (f j) ^ (2 : ℝ) := rfl
    have hdelta_eq : delta = delta_of_lambda 2 lambda := rfl
    rw [hx_eq, hdelta_eq]
    exact h_glb
  have h_g_ge_h : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2)))
      ≤ (∑ i, g_lambda 2 lambda f (p_star i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact h_per_agent_g_ge_h i
  -- ∑ h_q(x i) ≥ 0 via RGRelaxedCoreNonneg.
  have h_sum_h_nn : 0 ≤ (∑ i, h_q 2 lambda delta (x i)) := by
    have hdelta2 : delta = delta2 c := by
      rw [hdelta_def, hlam_def]; rfl
    have := Workspace.ProofLemmas.RGRelaxedCoreNonneg.RGRelaxedCoreNonneg
      c hc0 hc1 x hx_nn hx_le_one hx_sum
    rw [hdelta2, hlam_def]
    exact this
  -- Convert the LHS of h_g_ge_h to the h_q form.
  have h_lhs_eq : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2)))
      = (∑ i, h_q 2 lambda delta (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [h_lhs_eq] at h_g_ge_h
  -- Chain: 0 ≤ ∑ h ≤ ∑ g(p_star) ≤ ∑ g(P') ≤ ∑ g(P_norm).
  have h_main_chain : 0 ≤ ∑ i, g_lambda 2 lambda f (P_norm i) := by
    have h1 : 0 ≤ ∑ i, g_lambda 2 lambda f (p_star i) :=
      le_trans h_sum_h_nn h_g_ge_h
    have h2 : 0 ≤ ∑ i, g_lambda 2 lambda f (P' i) :=
      le_trans h1 h_p_star_le
    linarith [hg_le]
  -- Unfold g_lambda and conclude.
  have h_sum_eq : (∑ i, g_lambda 2 lambda f (P_norm i))
      = socialCost 2 P_norm f - lambda * socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ)) := by
    unfold g_lambda socialCost
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h_ext : (fun j => P_norm i j - (fun (_ : Fin d) => (0 : ℝ)) j) = fun j => P_norm i j := by
      funext j; ring
    rw [h_ext]
  rw [h_sum_eq] at h_main_chain
  linarith

end Workspace.ProofLemmas.RGNormalizedCoreInequality
