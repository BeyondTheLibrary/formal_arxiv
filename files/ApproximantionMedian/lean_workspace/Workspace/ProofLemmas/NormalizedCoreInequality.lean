import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LambdaStarDef
import Workspace.ProofLemmas.DeltaStarDef
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.MedianConstraintFromCWMedian
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LocalOptimumCharacterization
import Workspace.ProofLemmas.GLambdaLowerBound_h
import Workspace.ProofLemmas.MedianConstraintToSumX
import Workspace.ProofLemmas.HSecondDerivative
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.RelaxedCoreDual

open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ProofLemmas.UBDef
open Workspace.ProofLemmas.LambdaStarDef
open Workspace.ProofLemmas.DeltaStarDef
open Workspace.ProofLemmas.LambdaDeltaIdentity
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.HSecondDerivative
open Workspace.ProofLemmas.FqHasUniqueInteriorZero

set_option maxHeartbeats 8000000

/-- The `f > 0` (strictly positive) version of `NormalizedCoreInequality`.
This carries the paper's normalization hypothesis `hf_pos : ∀ j, 0 < f j`,
which is required by `LocalOptimumCharacterization` / `GLambdaLowerBound_h`.
The `f ≥ 0` version `NormalizedCoreInequality` is derived from this one via
the paper's ε-perturbation device (approx.tex line 9). The `∑ h_q ≥ 0` step
uses the FULLY-PROVEN dual lemma
`Workspace.ProofLemmas.RelaxedCoreDual.relaxedFeasibleSumNonneg_dual`, so this
theorem has NO `sorry` in its dependency closure. -/
theorem NormalizedCoreInequality_fpos :
    ∀ (q : ℝ), 1 < q →
      ∀ {n d : ℕ}, 0 < n → Even n → 1 ≤ d →
      ∀ (P_norm : Fin n → Fin d → ℝ),
      IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P_norm →
      ∀ (f : Fin d → ℝ), (∀ j, 0 ≤ f j) → (∀ j, 0 < f j) → lqNorm q f = 1 →
      socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ)) ≤ UB q * socialCost q P_norm f := by
  intro q hq n d hn_pos hn_even hd P_norm hP_med f hf_nn hf_pos hf_norm
  -- Basic setup.
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_q_pos : (0 : ℝ) < 1 / q := by positivity
  have h_inv_q_ne : (1 : ℝ) / q ≠ 0 := ne_of_gt h_inv_q_pos
  -- Define lambda := lambda_star q. By LambdaStarDef, 0 < lambda < 1 (strict since q > 1).
  set lambda : ℝ := lambda_star q with hlam_def
  have hLam := (LambdaStarDef.1 q hq_le)
  have hlam_pos : 0 < lambda := hLam.1
  have hlam_le_one : lambda ≤ 1 := hLam.2
  -- For q > 1 we have lambda < 1 strictly.
  have hlam_lt_one : lambda < 1 := by
    have hq_ne1 : q ≠ 1 := ne_of_gt hq
    have h_unfold : lambda_star q =
        (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)) := by
      unfold lambda_star
      rw [if_neg hq_ne1, if_pos hq]
    have hqm1_pos : (0 : ℝ) < q - 1 := by linarith
    have hD_ge_one : 1 ≤ delta_star q := (DeltaStarDef q hq).1
    have hD_pos : 0 < delta_star q := lt_of_lt_of_le one_pos hD_ge_one
    have h_exp1_pos : 0 < q / (q - 1) := div_pos hq_pos hqm1_pos
    have h_dpow_ge_one : 1 ≤ (delta_star q) ^ (q / (q - 1)) :=
      Real.one_le_rpow hD_ge_one (le_of_lt h_exp1_pos)
    have h_sum_gt_one : 1 < 1 + (delta_star q) ^ (q / (q - 1)) := by linarith
    have h_sum_pos : 0 < 1 + (delta_star q) ^ (q / (q - 1)) := by linarith
    have h_exp2_neg : -((q - 1) / q) < 0 := by
      have hp : 0 < (q - 1) / q := div_pos hqm1_pos hq_pos
      linarith
    have h_lt : (1 + (delta_star q) ^ (q / (q - 1))) ^ (-((q - 1) / q)) < 1 := by
      have h := Real.rpow_lt_one_of_one_lt_of_neg h_sum_gt_one h_exp2_neg
      exact h
    show lambda < 1
    rw [hlam_def, h_unfold]
    exact h_lt
  -- UB q = 1 / lambda.
  have h_UB_eq : UB q = 1 / lambda := by
    show UB q = 1 / lambda_star q
    unfold UB
    rw [if_pos hq_le]
  -- Goal rewrite: SC(P,0) ≤ (1/lambda) * SC(P,f) ↔ lambda * SC(P,0) ≤ SC(P,f)
  rw [h_UB_eq]
  rw [show (1 : ℝ) / lambda * socialCost q P_norm f = socialCost q P_norm f / lambda by ring]
  rw [le_div_iff₀ hlam_pos]
  -- Step (c): obtain sigma : Fin n → Fin d → ℝ via MedianConstraintFromCWMedian.
  obtain ⟨sigma, hsigma_pm, hsigma_pos, hsigma_neg, hsigma_zero⟩ :=
    MedianConstraintFromCWMedian hn_even P_norm hP_med
  -- f satisfies sum f^q = 1 since lqNorm q f = 1.
  have hf_pow_sum : (∑ j, (f j) ^ q) = 1 := by
    have h1 : lqNorm q f = (∑ j, |f j| ^ q) ^ ((1 : ℝ) / q) := rfl
    rw [h1] at hf_norm
    have h_inner_nn : 0 ≤ ∑ j, |f j| ^ q := sum_abs_rpow_nonneg q f
    have hsum_eq : (∑ j, |f j| ^ q) = 1 := by
      have h2 : ((∑ j, |f j| ^ q) ^ ((1 : ℝ) / q)) ^ q = (1 : ℝ) ^ q := by rw [hf_norm]
      rw [← Real.rpow_mul h_inner_nn, one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one,
          Real.one_rpow] at h2
      exact h2
    have h_abs : ∀ j, |f j| ^ q = (f j) ^ q := by
      intro j
      rw [abs_of_nonneg (hf_nn j)]
    rw [show (∑ j, (f j) ^ q) = (∑ j, |f j| ^ q) from
      Finset.sum_congr rfl (fun j _ => (h_abs j).symm)]
    exact hsum_eq
  -- Step (d): apply ConstrainedMinExists to get p_star which minimizes
  -- ∑ g_lambda(p_i) subject to the orthant constraint.
  obtain ⟨p_star, hp_star_in, hp_star_min⟩ :=
    ConstrainedMinExists q hq lambda hlam_pos hlam_lt_one hd f hf_norm hf_nn
      sigma hsigma_pm hsigma_zero
  -- Establish that P_norm itself satisfies the orthant constraint w.r.t. sigma.
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
  have h_p_star_le : (∑ i, g_lambda q lambda f (p_star i))
      ≤ (∑ i, g_lambda q lambda f (P_norm i)) := hp_star_min P_norm hP_in
  -- Define x_i := ∑_{j ∈ S_i} (f j)^q, where S_i := {j : sigma i j = 1}.
  classical
  set x : Fin n → ℝ := fun i =>
    ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ q with hx_def
  -- x i ∈ [0, 1] for each i.
  have hx_nn : ∀ i, 0 ≤ x i := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) q
  have hx_le_one : ∀ i, x i ≤ 1 := by
    intro i
    have h_split := Finset.sum_compl_add_sum
      (s := (Finset.univ.filter (fun j : Fin d => sigma i j = 1)))
      (f := fun j => (f j) ^ q)
    have h_compl_nn : 0 ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1))ᶜ, (f j) ^ q := by
      apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (hf_nn j) q
    have hf_sum_eq :
        (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1))ᶜ, (f j) ^ q) +
          (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ q) =
        ∑ j, (f j) ^ q := h_split
    rw [hf_pow_sum] at hf_sum_eq
    show (∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ q) ≤ 1
    linarith
  -- ∑ x i = n / 2 by MedianConstraintToSumX.
  have hx_sum : (∑ i, x i) = (n : ℝ) / 2 :=
    MedianConstraintToSumX hn_even q f hf_nn hf_pow_sum sigma hsigma_pm hsigma_zero
  -- Define the lower bound function.
  set delta : ℝ := delta_of_lambda q lambda with hdelta_def
  -- Per-agent local-min argument: from the GLOBAL minimum hypothesis on p_star,
  -- each component p_star i is a global (and hence local) minimum of g_lambda
  -- on the per-agent orthant orthant(σ i).
  have h_per_agent_min : ∀ i (p_i : Fin d → ℝ),
      (∀ j, (sigma i j = 1 → 0 ≤ p_i j) ∧ (sigma i j = -1 → p_i j ≤ 0)) →
      g_lambda q lambda f (p_star i) ≤ g_lambda q lambda f p_i := by
    intro i p_i hp_i_in
    -- Construct p' = p_star with i-th replaced by p_i.
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
    -- Sums differ only at i.
    have h_at_i : p' i = p_i := by simp [p']
    have h_off_i : ∀ i' ∈ Finset.univ.erase i, p' i' = p_star i' := by
      intro i' hi'
      rw [Finset.mem_erase] at hi'
      simp [p', hi'.1]
    have h_sum_p' :
        (∑ i', g_lambda q lambda f (p' i')) =
          g_lambda q lambda f p_i + ∑ i' ∈ Finset.univ.erase i, g_lambda q lambda f (p_star i') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      congr 1
      · rw [h_at_i]
      · apply Finset.sum_congr rfl
        intro i' hi'
        rw [h_off_i i' hi']
    have h_sum_pstar :
        (∑ i', g_lambda q lambda f (p_star i')) =
          g_lambda q lambda f (p_star i) + ∑ i' ∈ Finset.univ.erase i, g_lambda q lambda f (p_star i') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [h_sum_p', h_sum_pstar] at h_global
    linarith
  -- Each per-agent point is a "local minimum" with any positive ε; we use ε = 1.
  have h_local_min : ∀ i,
      ∃ ε > (0 : ℝ),
        ∀ p_i : Fin d → ℝ,
          (∀ j, (sigma i j = 1 → 0 ≤ p_i j) ∧ (sigma i j = -1 → p_i j ≤ 0)) →
          (∀ j, |p_i j - p_star i j| < ε) →
          g_lambda q lambda f (p_star i) ≤ g_lambda q lambda f p_i := by
    intro i
    refine ⟨1, by norm_num, ?_⟩
    intro p_i hp_i_in _
    exact h_per_agent_min i p_i hp_i_in
  -- Per-agent g ≥ h via LocalOptimumCharacterization + GLambdaLowerBound_h.
  have h_per_agent_g_ge_h : ∀ i,
      lambda * (delta * (1 - x i) ^ ((1 : ℝ) / q) - (x i) ^ ((1 : ℝ) / q))
        ≤ g_lambda q lambda f (p_star i) := by
    intro i
    have hp_star_i_in : ∀ j, (sigma i j = 1 → 0 ≤ p_star i j) ∧
                              (sigma i j = -1 → p_star i j ≤ 0) := hp_star_in i
    have hsigma_i_pm : ∀ j, sigma i j = 1 ∨ sigma i j = -1 := fun j => hsigma_pm i j
    have h_local := LocalOptimumCharacterization q hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma i) hsigma_i_pm (p_star i)
      hp_star_i_in (h_local_min i)
    have h_glb := GLambdaLowerBound_h q hq lambda hlam_pos hlam_lt_one
      hd f hf_nn hf_pos hf_pow_sum (sigma i) hsigma_i_pm (p_star i) h_local
    show lambda * (delta * (1 - x i) ^ ((1 : ℝ) / q) - (x i) ^ ((1 : ℝ) / q))
      ≤ g_lambda q lambda f (p_star i)
    have hx_eq : x i =
        ∑ j ∈ (Finset.univ.filter (fun j : Fin d => sigma i j = 1)), (f j) ^ q := rfl
    have hdelta_eq : delta = delta_of_lambda q lambda := rfl
    rw [hx_eq, hdelta_eq]
    exact h_glb
  -- Sum the per-agent bound.
  have h_g_ge_h : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / q) - (x i) ^ ((1 : ℝ) / q)))
      ≤ (∑ i, g_lambda q lambda f (p_star i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact h_per_agent_g_ge_h i
  -- Now establish ∑ h_q(x i) ≥ 0 via the FULLY-PROVEN dual lemma.
  have h_sum_h_nn : 0 ≤ (∑ i, h_q q lambda delta (x i)) := by
    exact Workspace.ProofLemmas.RelaxedCoreDual.relaxedFeasibleSumNonneg_dual q hq hn_pos hn_even
      lambda hlam_def delta hdelta_def x hx_nn hx_le_one hx_sum
  -- Convert the LHS of h_g_ge_h to the h_q form.
  have h_lhs_eq : (∑ i, lambda * (delta * (1 - x i) ^ ((1 : ℝ) / q) - (x i) ^ ((1 : ℝ) / q)))
      = (∑ i, h_q q lambda delta (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    show lambda * (delta * (1 - x i) ^ ((1 : ℝ) / q) - (x i) ^ ((1 : ℝ) / q))
       = h_q q lambda delta (x i)
    rfl
  rw [h_lhs_eq] at h_g_ge_h
  -- Combine: 0 ≤ ∑ h_q(x i) ≤ ∑ g_lambda(p_star i) ≤ ∑ g_lambda(P_norm i).
  have h_main_chain : 0 ≤ ∑ i, g_lambda q lambda f (P_norm i) := by
    have h1 : 0 ≤ ∑ i, g_lambda q lambda f (p_star i) :=
      le_trans h_sum_h_nn h_g_ge_h
    linarith
  -- Unfold g_lambda and conclude.
  have h_sum_eq : (∑ i, g_lambda q lambda f (P_norm i))
      = socialCost q P_norm f - lambda * socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ)) := by
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

theorem NormalizedCoreInequality :
    ∀ (q : ℝ), 1 < q →
      ∀ {n d : ℕ}, 0 < n → Even n → 1 ≤ d →
      ∀ (P_norm : Fin n → Fin d → ℝ),
      IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P_norm →
      ∀ (f : Fin d → ℝ), (∀ j, 0 ≤ f j) → lqNorm q f = 1 →
      socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ)) ≤ UB q * socialCost q P_norm f := by
  intro q hq n d hn_pos hn_even hd P_norm hP_med f hf_nn hf_norm
  -- ===================================================================
  -- ε-PERTURBATION DEVICE (approx.tex line 9): derive the f ≥ 0 statement
  -- from the f > 0 statement `NormalizedCoreInequality_fpos`. For ε > 0 we
  -- replace f by the strictly-positive normalized perturbation
  --   f_eps ε j := (f j + ε) / lqNorm q (fun k => f k + ε),
  -- apply `_fpos`, and let ε → 0⁺ along the sequence ε_k = 1/(k+1),
  -- using continuity of `g ↦ socialCost q P_norm g`.
  -- ===================================================================
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hq_pos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_q_nn : (0 : ℝ) ≤ 1 / q := by positivity
  -- (1) `socialCost q P_norm` is continuous in its facility-location argument.
  have h_cont_sc : Continuous (fun g : Fin d → ℝ => socialCost q P_norm g) := by
    show Continuous (fun g : Fin d → ℝ => ∑ i, lqNorm q (fun j => P_norm i j - g j))
    apply continuous_finset_sum
    intro i _
    show Continuous (fun g : Fin d → ℝ =>
      (∑ j, |P_norm i j - g j| ^ q) ^ ((1 : ℝ) / q))
    apply Continuous.rpow_const
    · apply continuous_finset_sum
      intro j _
      apply Continuous.rpow_const
      · exact (continuous_const.sub (continuous_apply j)).abs
      · intro x; right; exact le_of_lt hq_pos
    · intro x; right; exact h_inv_q_nn
  -- (2) The normalizing constant c ε = lqNorm q (f + ε), as a function of ε.
  set c : ℝ → ℝ := fun ε => lqNorm q (fun k => f k + ε) with hc_def
  -- c is continuous (in ε).
  have h_cont_c : Continuous c := by
    show Continuous (fun ε : ℝ => (∑ k, |f k + ε| ^ q) ^ ((1 : ℝ) / q))
    apply Continuous.rpow_const
    · apply continuous_finset_sum
      intro k _
      apply Continuous.rpow_const
      · exact (continuous_const.add continuous_id).abs
      · intro x; right; exact le_of_lt hq_pos
    · intro x; right; exact h_inv_q_nn
  -- c 0 = lqNorm q f = 1.
  have hc_zero : c 0 = 1 := by
    have h_eq : (fun k => f k + (0:ℝ)) = f := by funext k; ring
    show lqNorm q (fun k => f k + (0:ℝ)) = 1
    rw [h_eq]; exact hf_norm
  -- For ε > 0 : c ε > 0  (since each f k + ε > 0 and d ≥ 1).
  have hc_pos : ∀ ε : ℝ, 0 < ε → 0 < c ε := by
    intro ε hε
    show 0 < lqNorm q (fun k => f k + ε)
    have h_inner_pos : 0 < ∑ k, |f k + ε| ^ q := by
      obtain ⟨j0⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le one_pos hd)
      have hpos_term : 0 < |f j0 + ε| ^ q := by
        have hfe : 0 < f j0 + ε := by have := hf_nn j0; linarith
        apply Real.rpow_pos_of_pos
        rw [abs_of_pos hfe]; exact hfe
      have h_nn : ∀ k ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |f k + ε| ^ q :=
        fun k _ => Real.rpow_nonneg (abs_nonneg _) q
      calc (0:ℝ) < |f j0 + ε| ^ q := hpos_term
        _ ≤ ∑ k, |f k + ε| ^ q := Finset.single_le_sum h_nn (Finset.mem_univ j0)
    show 0 < (∑ k, |f k + ε| ^ q) ^ ((1 : ℝ) / q)
    exact Real.rpow_pos_of_pos h_inner_pos _
  -- (3) The perturbed, normalized feasible point.
  set f_eps : ℝ → (Fin d → ℝ) := fun ε j => (f j + ε) / c ε with hfeps_def
  -- For ε > 0 : f_eps ε j > 0.
  have hfeps_pos : ∀ ε : ℝ, 0 < ε → ∀ j, 0 < f_eps ε j := by
    intro ε hε j
    show 0 < (f j + ε) / c ε
    apply div_pos
    · have := hf_nn j; linarith
    · exact hc_pos ε hε
  have hfeps_nn : ∀ ε : ℝ, 0 < ε → ∀ j, 0 ≤ f_eps ε j :=
    fun ε hε j => le_of_lt (hfeps_pos ε hε j)
  -- For ε > 0 : lqNorm q (f_eps ε) = 1 (scaling by 1/c ε).
  have hfeps_norm : ∀ ε : ℝ, 0 < ε → lqNorm q (f_eps ε) = 1 := by
    intro ε hε
    have hcε_pos : 0 < c ε := hc_pos ε hε
    have hcε_ne : c ε ≠ 0 := ne_of_gt hcε_pos
    have h_smul : f_eps ε = (fun j => (1 / c ε) * (f j + ε)) := by
      funext j; show (f j + ε) / c ε = (1 / c ε) * (f j + ε); rw [one_div]; ring
    rw [h_smul]
    rw [lqNorm_smul hq_le (1 / c ε) (fun k => f k + ε)]
    have h_abs : |1 / c ε| = 1 / c ε := abs_of_pos (by positivity)
    rw [h_abs]
    show (1 / c ε) * c ε = 1
    rw [one_div, inv_mul_cancel₀ hcε_ne]
  -- (4) The sequence ε_k = 1/(k+1) → 0⁺.
  set aε : ℕ → ℝ := fun k => 1 / (k + 1) with haε_def
  have haε_pos : ∀ k, 0 < aε k := by
    intro k; show 0 < 1 / ((k : ℝ) + 1)
    apply div_pos one_pos; positivity
  have haε_tendsto : Filter.Tendsto aε Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h
  -- (5) c (aε k) → c 0 = 1  (continuity of c at 0).
  have hc_tendsto : Filter.Tendsto (fun k => c (aε k)) Filter.atTop (nhds 1) := by
    have h := (h_cont_c.tendsto 0).comp haε_tendsto
    rw [hc_zero] at h
    exact h
  -- (6) f_eps (aε k) → f  pointwise (in the product topology).
  have hfeps_tendsto : Filter.Tendsto (fun k => f_eps (aε k)) Filter.atTop (nhds f) := by
    rw [tendsto_pi_nhds]
    intro j
    show Filter.Tendsto (fun k => (f j + aε k) / c (aε k)) Filter.atTop (nhds (f j))
    have h_num : Filter.Tendsto (fun k => f j + aε k) Filter.atTop (nhds (f j + 0)) :=
      Filter.Tendsto.const_add (f j) haε_tendsto
    rw [add_zero] at h_num
    have h_div := Filter.Tendsto.div h_num hc_tendsto (by norm_num : (1:ℝ) ≠ 0)
    rw [div_one] at h_div
    exact h_div
  -- (7) socialCost q P_norm (f_eps (aε k)) → socialCost q P_norm f  (continuity).
  have hsc_tendsto :
      Filter.Tendsto (fun k => socialCost q P_norm (f_eps (aε k)))
        Filter.atTop (nhds (socialCost q P_norm f)) :=
    (h_cont_sc.tendsto f).comp hfeps_tendsto
  -- (8) Multiply by the constant factor UB q.
  have hub_tendsto :
      Filter.Tendsto (fun k => UB q * socialCost q P_norm (f_eps (aε k)))
        Filter.atTop (nhds (UB q * socialCost q P_norm f)) :=
    Filter.Tendsto.const_mul (UB q) hsc_tendsto
  -- (9) Each term obeys the f > 0 inequality from `_fpos`.
  have h_each : ∀ k,
      socialCost q P_norm (fun (_ : Fin d) => (0 : ℝ))
        ≤ UB q * socialCost q P_norm (f_eps (aε k)) := by
    intro k
    exact NormalizedCoreInequality_fpos q hq hn_pos hn_even hd P_norm hP_med
      (f_eps (aε k)) (hfeps_nn (aε k) (haε_pos k)) (hfeps_pos (aε k) (haε_pos k))
      (hfeps_norm (aε k) (haε_pos k))
  -- (10) Pass to the limit: the constant LHS ≤ limit of the RHS.
  exact ge_of_tendsto' hub_tendsto h_each
