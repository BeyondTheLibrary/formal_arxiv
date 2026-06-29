import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.CGDefs

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.CGDefs

namespace Workspace.ProofLemmas.CGConstrainedMinExists

namespace CGConstrainedMinExistsProof

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

-- Coercive lower bound: g_lambda q lambda f p ≥ (1 - lambda) * lqNorm q p - 1
private lemma g_lambda_lower_bound {q : ℝ} (hq : 1 ≤ q) {lambda : ℝ}
    {d : ℕ} (f : Fin d → ℝ) (hf_norm : lqNorm q f = 1) (p : Fin d → ℝ) :
    (1 - lambda) * lqNorm q p - 1 ≤ g_lambda q lambda f p := by
  unfold g_lambda
  have h := LqNormSubReverseTriangle hq p f
  rw [hf_norm] at h
  linarith

end CGConstrainedMinExistsProof

open CGConstrainedMinExistsProof

/-- **CGConstrainedMinExists** (proof_nlp.md §2.0–§2.1, `prediction.tex` line 38;
consistency analog of Theorem-1's `ConstrainedMinExists`, Claim 1).

Fix `q = 2` and `λ₁ = lambda1 c ∈ (0,1)`.  In the normalized setting
(`f j ≥ 0`, `‖f‖₂ = 1`), the minimum of `∑ᵢ g_lambda 2 λ₁ f (pᵢ)` over the
signature-fixed orthant — but now with the *consistency* orthant constraint
`∑ᵢ σ(pᵢ) j = −⌊cn⌋` (the output of `CGMedianConstraintFromAugment`) in place of
Theorem-1's `∑ᵢ σ(pᵢ) j = 0` — is attained.

This is the exact analog of `ConstrainedMinExists`: the only change to the
signature is the `hsigma_zero` hypothesis, which becomes the consistency form
`∀ j, ∑ i, sigma_assign i j = -(⌊c * n⌋₊ : ℝ)`.  (The orthant set is determined
by the per-coordinate signs `σ i j ∈ {−1,+1}` exactly as before; the constraint
on the *column sums* only restricts which `σ` arises, not the orthant geometry,
so the compactness/coercivity existence argument is unchanged.) -/
theorem CGConstrainedMinExists
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hlam0 : 0 < lambda1 c) (hlam1 : lambda1 c < 1)
    {n d : ℕ} (hd : 1 ≤ d)
    (f : Fin d → ℝ) (hf_norm : lqNorm 2 f = 1) (hf_nn : ∀ j, 0 ≤ f j)
    (sigma_assign : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma_assign i j = 1 ∨ sigma_assign i j = -1)
    (hsigma_cons : ∀ j, ∑ i, sigma_assign i j = -(⌊c * (n : ℝ)⌋₊ : ℝ)) :
    ∃ p_star : Fin n → Fin d → ℝ,
      (∀ i j, (sigma_assign i j = 1 → 0 ≤ p_star i j) ∧
              (sigma_assign i j = -1 → p_star i j ≤ 0)) ∧
      (∀ p : Fin n → Fin d → ℝ,
        (∀ i j, (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                (sigma_assign i j = -1 → p i j ≤ 0)) →
        (∑ i, g_lambda 2 (lambda1 c) f (p_star i)) ≤ (∑ i, g_lambda 2 (lambda1 c) f (p i))) := by
  classical
  -- Abbreviate the fixed exponent and constant.
  set q : ℝ := 2 with hq_def
  set lambda : ℝ := lambda1 c with hlambda_def
  have hq : (1 : ℝ) < q := by rw [hq_def]; norm_num
  have hq_le : 1 ≤ q := le_of_lt hq
  -- Define the constraint set
  set S : Set (Fin n → Fin d → ℝ) :=
    {p | ∀ i j, (sigma_assign i j = 1 → 0 ≤ p i j) ∧
                (sigma_assign i j = -1 → p i j ≤ 0)} with hS_def
  -- Define the objective
  set G : (Fin n → Fin d → ℝ) → ℝ :=
    fun p => ∑ i, g_lambda q lambda f (p i) with hG_def
  -- G is continuous
  have hG_cont : Continuous G := sum_g_lambda_continuous hq_le lambda f
  -- 0 ∈ S
  have h0_mem : (fun _ _ => (0 : ℝ)) ∈ S := by
    intro i j
    refine ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩
  -- S is closed
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
  -- Set K := G 0
  set K : ℝ := G (fun _ _ => 0) with hK_def
  -- Define T := S ∩ {p | G p ≤ K}
  set T : Set (Fin n → Fin d → ℝ) := S ∩ {p | G p ≤ K} with hT_def
  -- T is closed
  have hT_closed : IsClosed T := hS_closed.inter (isClosed_le hG_cont continuous_const)
  -- T is bounded
  have hT_bdd : Bornology.IsBounded T := by
    have h_one_lam_pos : 0 < 1 - lambda := by rw [hlambda_def]; linarith
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
  -- T is compact
  have hT_compact : IsCompact T :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hT_closed, hT_bdd⟩
  -- T is nonempty
  have hT_nonempty : T.Nonempty := by
    refine ⟨fun _ _ => 0, h0_mem, ?_⟩
    simp only [Set.mem_setOf_eq]
    rfl
  -- G is continuous on T
  have hG_cont_on : ContinuousOn G T := hG_cont.continuousOn
  -- Apply IsCompact.exists_isMinOn
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

end Workspace.ProofLemmas.CGConstrainedMinExists
