import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.CGMedianConstraintFromAugment
import Workspace.ProofLemmas.CGConstrainedMinExists
import Workspace.ProofLemmas.CGRelaxedConstraint
import Workspace.ProofLemmas.CGRelaxedCoreNonneg
import Workspace.ProofLemmas.CGLambda1InUnitInterval
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
open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.LambdaDeltaIdentity

namespace Workspace.ProofLemmas.CGNormalizedCoreInequality

/-- The `f > 0` (strictly positive) version of `CGNormalizedCoreInequality`
(consistency analog of `NormalizedCoreInequality_fpos`, at `q = 2`).

This carries the paper's normalization hypothesis `hf_pos : ∀ j, 0 < f j`,
required by `LocalOptimumCharacterization` / `GLambdaLowerBound_h`.  In the
normalized setting (`m = 0`, the prediction equals the normalized minimizer `f`
with all-positive coordinates and `‖f‖₂ = 1`), if `0` is a coordinate-wise
median of the *augmented* instance `augment P_norm f ⌊cn⌋` and `n + ⌊cn⌋` is
even, then `SC(P_norm, 0) ≤ CG c · SC(P_norm, f)`.

(Its eventual proof assembles `CGMedianConstraintFromAugment` →
`CGConstrainedMinExists` → `GLambdaLowerBound_h` (external) → `CGRelaxedConstraint`
→ `CGRelaxedCoreNonneg` → `CGLambda1InUnitInterval`, exactly mirroring
`NormalizedCoreInequality_fpos` with `UB 2` replaced by `CG c`, the median-of-`P`
hypothesis replaced by median-of-augmented, the even-`n` hypothesis replaced by
`Even (n + ⌊cn⌋)`, and the constraint `∑ x = n/2` replaced by `∑ x = (1-c)/2·n`.) -/
theorem CGNormalizedCoreInequality_fpos
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n d : ℕ} (hn_pos : 0 < n) (hne : Even (n + ⌊c * (n : ℝ)⌋₊)) (hd : 1 ≤ d)
    (hcn : (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ))
    (P_norm : Fin n → Fin d → ℝ)
    (f : Fin d → ℝ) (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j)
    (hf_norm : lqNorm 2 f = 1)
    (hP_med : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
                (augment P_norm f (⌊c * (n : ℝ)⌋₊))) :
    socialCost 2 P_norm (fun (_ : Fin d) => (0 : ℝ))
      ≤ Workspace.ConsistencyTheorem.CG c * socialCost 2 P_norm f := by
  classical
  -- Fix q = 2 and lambda := lambda1 c.
  have hq : (1 : ℝ) < (2 : ℝ) := by norm_num
  have hq_le : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hq_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hq_ne : (2 : ℝ) ≠ 0 := by norm_num
  set lambda : ℝ := lambda1 c with hlam_def
  -- 0 < lambda1 c, lambda1 c < 1, 1 < CG c.
  obtain ⟨hlam_pos, hlam_lt_one, hCG_gt_one⟩ :=
    Workspace.ProofLemmas.CGLambda1InUnitInterval.CGLambda1InUnitInterval c hc0 hc1
  -- The relation CG c = 1 / lambda1 c (equivalently lambda1 c * CG c = 1).
  have h_CG_eq : Workspace.ConsistencyTheorem.CG c = 1 / lambda := by
    -- Prove via the closed forms in both branches.
    rw [hlam_def]
    unfold lambda1 Workspace.ConsistencyTheorem.CG
    by_cases hcase : c < 1 / 2
    · rw [if_pos hcase, if_pos hcase]
      set D := 4 * Real.sqrt (2 * c + 3) * c + 6 * Real.sqrt (2 * c + 3) - 10 * c - 8 with hD_def
      -- 0 < D from CGLambda1InUnitInterval (low branch positivity).
      have hDpos : 0 < D := by
        have hs_nonneg : 0 ≤ Real.sqrt (2 * c + 3) := Real.sqrt_nonneg _
        have hs2 : (Real.sqrt (2 * c + 3)) ^ 2 = 2 * c + 3 := by
          rw [sq, Real.mul_self_sqrt (by linarith)]
        have hs_ge : (1 : ℝ) ≤ Real.sqrt (2 * c + 3) := by nlinarith [hs2, hs_nonneg]
        rw [hD_def]
        nlinarith [hs2, hs_nonneg, hs_ge, hc0, hcase, sq_nonneg (Real.sqrt (2 * c + 3) - 1),
          mul_nonneg hs_nonneg hc0]
      have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
      have hc1pos : (0 : ℝ) < c + 1 := by linarith
      field_simp
    · rw [if_neg hcase, if_neg hcase]
      have hc1pos : (0 : ℝ) < c + 1 := by linarith
      have hhalf_pos : (0 : ℝ) < (c + 1) / 2 := by linarith
      have hsqrt_pos : 0 < Real.sqrt ((c + 1) / 2) := Real.sqrt_pos.mpr hhalf_pos
      rw [eq_div_iff (ne_of_gt hsqrt_pos)]
      rw [← Real.sqrt_mul (by positivity)]
      rw [show (2 / (c + 1)) * ((c + 1) / 2) = 1 by field_simp]
      exact Real.sqrt_one
  -- Rewrite the goal: SC(0) ≤ CG c · SC(f) ↔ lambda · SC(0) ≤ SC(f).
  rw [h_CG_eq]
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
  -- Step (c): obtain sigma via CGMedianConstraintFromAugment.
  obtain ⟨sigma, hsigma_pm, hsigma_pos, hsigma_neg, hsigma_cons, hsigma_balance⟩ :=
    Workspace.ProofLemmas.CGMedianConstraintFromAugment.CGMedianConstraintFromAugment
      c hc0 hc1 hne f hf_pos hf_pow_sum P_norm hP_med
  -- Step (d): apply CGConstrainedMinExists to get p_star.
  obtain ⟨p_star, hp_star_in, hp_star_min⟩ :=
    Workspace.ProofLemmas.CGConstrainedMinExists.CGConstrainedMinExists
      c hc0 hc1 (by rw [← hlam_def] at *; exact hlam_pos) (by rw [← hlam_def] at *; exact hlam_lt_one)
      hd f hf_norm hf_nn sigma hsigma_pm hsigma_cons
  -- P_norm itself satisfies the orthant constraint w.r.t. sigma.
  have hP_in : ∀ i j, (sigma i j = 1 → 0 ≤ P_norm i j) ∧
                       (sigma i j = -1 → P_norm i j ≤ 0) := by
    intro i j
    refine ⟨?_, ?_⟩
    · intro hsig
      by_contra h_neg
      push_neg at h_neg
      have := hsigma_neg i j h_neg
      rw [this] at hsig
      norm_num at hsig
    · intro hsig
      by_contra h_pos
      push_neg at h_pos
      have := hsigma_pos i j h_pos
      rw [this] at hsig
      norm_num at hsig
  -- The minimization gives: ∑ g_lambda f (p_star i) ≤ ∑ g_lambda f (P_norm i).
  have h_p_star_le : (∑ i, g_lambda 2 lambda f (p_star i))
      ≤ (∑ i, g_lambda 2 lambda f (P_norm i)) := hp_star_min P_norm hP_in
  -- Define x_i := ∑_{j ∈ S_i} (f j)^2, where S_i := {j : sigma i j = 1}.
  set x : Fin n → ℝ := fun i =>
    ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ (2 : ℝ) with hx_def
  have hx_nn : ∀ i, 0 ≤ x i := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) (2 : ℝ)
  have hx_le_one : ∀ i, x i ≤ 1 := by
    intro i
    have h_split := Finset.sum_compl_add_sum
      (s := (Finset.univ.filter (fun j : Fin d => sigma i j = 1)))
      (f := fun j => (f j) ^ (2 : ℝ))
    have h_compl_nn : 0 ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1))ᶜ, (f j) ^ (2 : ℝ) := by
      apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (hf_nn j) (2 : ℝ)
    have hf_sum_eq :
        (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1))ᶜ, (f j) ^ (2 : ℝ)) +
          (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ (2 : ℝ)) =
        ∑ j, (f j) ^ (2 : ℝ) := h_split
    rw [hf_pow_sum] at hf_sum_eq
    show (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ (2 : ℝ)) ≤ 1
    linarith
  -- ∑ x i = (1-c)/2 · n by CGRelaxedConstraint.
  -- First convert the nat balance (card * 2 = n - ⌊cn⌋) to the real form.
  have hk_le_n : (⌊c * (n : ℝ)⌋₊ : ℕ) ≤ n := by
    have hcn_lt : c * (n : ℝ) < (n : ℝ) := by
      have : c * (n : ℝ) < 1 * (n : ℝ) := by
        apply mul_lt_mul_of_pos_right hc1
        exact_mod_cast hn_pos
      simpa using this
    have hcn_nonneg : 0 ≤ c * (n : ℝ) := mul_nonneg hc0 (by positivity)
    have hle : (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ c * (n : ℝ) := Nat.floor_le hcn_nonneg
    have hlt : (⌊c * (n : ℝ)⌋₊ : ℝ) < (n : ℝ) := lt_of_le_of_lt hle hcn_lt
    have : (⌊c * (n : ℝ)⌋₊ : ℕ) < n := by exact_mod_cast hlt
    omega
  have hbalance : ∀ j,
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ)
        = ((n : ℝ) - ⌊c * (n : ℝ)⌋₊) / 2 := by
    intro j
    have hnat := hsigma_balance j
    -- hnat : card * 2 = n - ⌊cn⌋  (nat subtraction)
    have hk : (⌊c * (n : ℝ)⌋₊ : ℕ) ≤ n := hk_le_n
    have hreal : (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ) * 2
        = (n : ℝ) - (⌊c * (n : ℝ)⌋₊ : ℝ) := by
      have h1 : ((((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card * 2 : ℕ) : ℝ)
          = ((n - ⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_mul, Nat.cast_sub hk] at h1
      push_cast at h1
      linarith
    linarith
  have hx_sum : (∑ i, x i) = (1 - c) / 2 * (n : ℝ) := by
    have := Workspace.ProofLemmas.CGRelaxedConstraint.CGRelaxedConstraint
      c hcn f hf_pow_sum sigma hsigma_pm hbalance
    exact this
  -- Define the lower-bound delta (= delta1 c definitionally).
  set delta : ℝ := delta_of_lambda 2 lambda with hdelta_def
  -- Per-agent local-min argument.
  have h_per_agent_min : ∀ i (p_i : Fin d → ℝ),
      (∀ j, (sigma i j = 1 → 0 ≤ p_i j) ∧ (sigma i j = -1 → p_i j ≤ 0)) →
      g_lambda 2 lambda f (p_star i) ≤ g_lambda 2 lambda f p_i := by
    intro i p_i hp_i_in
    let p' : Fin n → Fin d → ℝ := fun i' => if i' = i then p_i else p_star i'
    have hp'_in : ∀ i' j, (sigma i' j = 1 → 0 ≤ p' i' j) ∧
                          (sigma i' j = -1 → p' i' j ≤ 0) := by
      intro i' j
      by_cases hi' : i' = i
      · subst hi'
        show (sigma i' j = 1 → 0 ≤ (if i' = i' then p_i else p_star i') j) ∧
             (sigma i' j = -1 → (if i' = i' then p_i else p_star i') j ≤ 0)
        simp only [if_true]
        exact hp_i_in j
      · show (sigma i' j = 1 → 0 ≤ (if i' = i then p_i else p_star i') j) ∧
             (sigma i' j = -1 → (if i' = i then p_i else p_star i') j ≤ 0)
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
          (∀ j, (sigma i j = 1 → 0 ≤ p_i j) ∧ (sigma i j = -1 → p_i j ≤ 0)) →
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
    have hp_star_i_in : ∀ j, (sigma i j = 1 → 0 ≤ p_star i j) ∧
                              (sigma i j = -1 → p_star i j ≤ 0) := hp_star_in i
    have hsigma_i_pm : ∀ j, sigma i j = 1 ∨ sigma i j = -1 := fun j => hsigma_pm i j
    have h_local := LocalOptimumCharacterization 2 hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma i) hsigma_i_pm (p_star i)
      hp_star_i_in (h_local_min i)
    have h_glb := GLambdaLowerBound_h 2 hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma i) hsigma_i_pm (p_star i) h_local
    show lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2))
      ≤ g_lambda 2 lambda f (p_star i)
    have hx_eq : x i =
        ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ (2 : ℝ) := rfl
    have hdelta_eq : delta = delta_of_lambda 2 lambda := rfl
    rw [hx_eq, hdelta_eq]
    exact h_glb
  have h_g_ge_h : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2)))
      ≤ (∑ i, g_lambda 2 lambda f (p_star i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact h_per_agent_g_ge_h i
  -- ∑ h_q(x i) ≥ 0 via CGRelaxedCoreNonneg.
  have h_sum_h_nn : 0 ≤ (∑ i, h_q 2 lambda delta (x i)) := by
    have hdelta1 : delta = delta1 c := by
      rw [hdelta_def, hlam_def]; rfl
    have := Workspace.ProofLemmas.CGRelaxedCoreNonneg.CGRelaxedCoreNonneg
      c hc0 hc1 x hx_nn hx_le_one hx_sum
    rw [hdelta1, hlam_def]
    exact this
  -- Convert the LHS of h_g_ge_h to the h_q form.
  have h_lhs_eq : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / 2) - (x i) ^ ((1 : ℝ) / 2)))
      = (∑ i, h_q 2 lambda delta (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [h_lhs_eq] at h_g_ge_h
  have h_main_chain : 0 ≤ ∑ i, g_lambda 2 lambda f (P_norm i) := by
    have h1 : 0 ≤ ∑ i, g_lambda 2 lambda f (p_star i) :=
      le_trans h_sum_h_nn h_g_ge_h
    linarith
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

end Workspace.ProofLemmas.CGNormalizedCoreInequality
