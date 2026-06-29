import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.ConstrainedMinExists

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem
open Workspace.ProofLemmas.ConstrainedMinExists

namespace Workspace.ProofLemmas.RGWorstCasePredictionSignature

/-- L2 norm is monotone under coordinatewise absolute-value domination. -/
private lemma lqNorm2_mono {d : ℕ} (x y : Fin d → ℝ) (h : ∀ j, |x j| ≤ |y j|) :
    lqNorm 2 x ≤ lqNorm 2 y := by
  unfold lqNorm
  apply Real.rpow_le_rpow (sum_abs_rpow_nonneg 2 x)
  · apply Finset.sum_le_sum
    intro j _
    exact Real.rpow_le_rpow (abs_nonneg _) (h j) (by norm_num)
  · norm_num

/-- L2 norm is determined by coordinatewise absolute values. -/
private lemma lqNorm2_congr {d : ℕ} (x y : Fin d → ℝ) (h : ∀ j, |x j| = |y j|) :
    lqNorm 2 x = lqNorm 2 y := by
  unfold lqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [h j]

/-- A ±1 sum equals (# of +1's) − (# of −1's). -/
private lemma sum_pm_eq_card {n : ℕ} (sg : Fin n → ℝ) (hpm : ∀ i, sg i = 1 ∨ sg i = -1) :
    ∑ i, sg i =
      ((Finset.univ.filter (fun i => sg i = 1)).card : ℝ)
      - ((Finset.univ.filter (fun i => sg i = -1)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => sg i = 1)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => sg i = 1), sg i
      = ((Finset.univ.filter (fun i => sg i = 1)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ sg i = 1), sg i
      = - ((Finset.univ.filter (fun i => sg i = -1)).card : ℝ) := by
    have heq : (Finset.univ.filter (fun i => ¬ sg i = 1))
        = (Finset.univ.filter (fun i => sg i = -1)) := by
      apply Finset.filter_congr
      intro i _
      constructor
      · intro hne
        rcases hpm i with h | h
        · exact absurd h hne
        · exact h
      · intro h hcontra; rw [h] at hcontra; norm_num at hcontra
    rw [heq, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp
  rw [h1, h2]; ring

/-- Cardinalities of the +1 and −1 sets sum to `n`. -/
private lemma card_pos_add_card_neg {n : ℕ} (sg : Fin n → ℝ)
    (hpm : ∀ i, sg i = 1 ∨ sg i = -1) :
    (Finset.univ.filter (fun i => sg i = 1)).card
      + (Finset.univ.filter (fun i => sg i = -1)).card = n := by
  classical
  have heq : (Finset.univ.filter (fun i => ¬ sg i = 1))
      = (Finset.univ.filter (fun i => sg i = -1)) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro hne
      rcases hpm i with h | h
      · exact absurd h hne
      · exact h
    · intro h hcontra; rw [h] at hcontra; norm_num at hcontra
  have := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => sg i = 1)
  rw [heq] at this
  simpa using this

theorem RGWorstCasePredictionSignature
    {n d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (lambda : ℝ)
    (f : Fin d → ℝ) (hf_pos : ∀ j, 0 < f j)
    (P : Fin n → Fin d → ℝ) (s : Fin d → ℝ)
    (hs_pm : ∀ j, s j = 1 ∨ s j = -1)
    -- `(P, s)` is feasible: there is a consistent ±1 signature assignment `σ`
    -- realizing the per-coordinate constraint `∑_i σ(pᵢ) j = −⌊cn⌋ · s j`.
    (sigma : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma i j = 1 ∨ sigma i j = -1)
    (hsigma_pos : ∀ i j, P i j > 0 → sigma i j = 1)
    (hsigma_neg : ∀ i j, P i j < 0 → sigma i j = -1)
    (hconstraint : ∀ j, ∑ i, sigma i j = -(⌊c * (n : ℝ)⌋₊ : ℝ) * s j) :
    -- There is a feasible configuration with prediction signature `(−1,…,−1)`
    -- whose objective is no larger.
    ∃ (P' : Fin n → Fin d → ℝ) (sigma' : Fin n → Fin d → ℝ),
      (∀ i j, sigma' i j = 1 ∨ sigma' i j = -1) ∧
      (∀ i j, P' i j > 0 → sigma' i j = 1) ∧
      (∀ i j, P' i j < 0 → sigma' i j = -1) ∧
      (∀ j, ∑ i, sigma' i j = -(⌊c * (n : ℝ)⌋₊ : ℝ) * (-1)) ∧
      (∑ i, g_lambda 2 lambda f (P' i)) ≤ (∑ i, g_lambda 2 lambda f (P i)) := by
  classical
  set m : ℕ := ⌊c * (n : ℝ)⌋₊ with hm
  -- The "negative-signature" set for coordinate j.
  set T : Fin d → Finset (Fin n) := fun j => Finset.univ.filter (fun i => sigma i j = -1) with hT
  -- m ≤ n.
  have hmn : m ≤ n := by
    rw [hm]
    have : c * (n : ℝ) ≤ (n : ℝ) := by
      have : c * (n : ℝ) ≤ 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hc1) (by positivity)
      simpa using this
    calc ⌊c * (n : ℝ)⌋₊ ≤ ⌊(n : ℝ)⌋₊ := Nat.floor_le_floor this
      _ = n := Nat.floor_natCast n
  -- When s j = 1, the negative set has at least m elements.
  have hcard_T : ∀ j, s j = 1 → m ≤ (T j).card := by
    intro j hsj
    have hsum := hconstraint j
    rw [hsj, mul_one] at hsum
    have hpmj : ∀ i, sigma i j = 1 ∨ sigma i j = -1 := fun i => hsigma_pm i j
    rw [sum_pm_eq_card (fun i => sigma i j) hpmj] at hsum
    have hcard := card_pos_add_card_neg (fun i => sigma i j) hpmj
    -- Let A = #{+1}, B = #{-1} = (T j).card. A - B = -m, A + B = n  ⇒ B = (n+m)/2 ≥ m
    set A := (Finset.univ.filter (fun i => sigma i j = 1)).card with hA
    set B := (Finset.univ.filter (fun i => sigma i j = -1)).card with hB
    have hBcard : (T j).card = B := by rw [hT, hB]
    -- cast equations to ℝ
    have hsumcard_real : (A : ℝ) + (B : ℝ) = (n : ℝ) := by
      have : ((A + B : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hcard
      push_cast at this; linarith
    have hB_ge : (m : ℝ) ≤ (B : ℝ) := by
      have hmn_real : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      nlinarith [hsum]
    exact_mod_cast hB_ge
  -- Choose, for each coordinate j with s j = 1, an m-subset S j ⊆ T j.
  -- For s j = -1 we use ∅.
  have hSexists : ∀ j, ∃ (Sj : Finset (Fin n)), Sj ⊆ T j ∧ (s j = 1 → Sj.card = m) := by
    intro j
    by_cases hsj : s j = 1
    · obtain ⟨Sj, hsub, hcard⟩ := Finset.exists_subset_card_eq (hcard_T j hsj)
      exact ⟨Sj, hsub, fun _ => hcard⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hsj⟩
  choose S hS_sub hS_card using hSexists
  -- "flip" predicate.
  set flip : Fin n → Fin d → Prop := fun i j => s j = 1 ∧ i ∈ S j with hflip
  have flip_dec : ∀ i j, Decidable (flip i j) := by
    intro i j; rw [hflip]; infer_instance
  -- The new configuration.
  set P' : Fin n → Fin d → ℝ :=
    fun i j => if flip i j then -(P i j) else P i j with hP'
  set sigma' : Fin n → Fin d → ℝ :=
    fun i j => if flip i j then -(sigma i j) else sigma i j with hsig'
  -- Key fact: if flip i j then P i j ≤ 0 and sigma i j = -1.
  have hflip_neg : ∀ i j, flip i j → sigma i j = -1 ∧ P i j ≤ 0 := by
    intro i j hf
    have hiT : i ∈ T j := hS_sub j hf.2
    have hsig_neg : sigma i j = -1 := (Finset.mem_filter.mp hiT).2
    refine ⟨hsig_neg, ?_⟩
    by_contra hcontra
    push_neg at hcontra
    have := hsigma_pos i j hcontra
    rw [hsig_neg] at this; norm_num at this
  refine ⟨P', sigma', ?_, ?_, ?_, ?_, ?_⟩
  · -- sigma' is ±1
    intro i j
    rw [hsig']
    by_cases hf : flip i j
    · simp only [hf, if_true]
      rcases hsigma_pm i j with h | h
      · right; rw [h]
      · left; rw [h]; norm_num
    · simp only [hf, if_false]; exact hsigma_pm i j
  · -- P' i j > 0 → sigma' i j = 1
    intro i j hpos
    rw [hsig']
    rw [hP'] at hpos
    by_cases hf : flip i j
    · simp only [hf, if_true]
      simp only [hf, if_true] at hpos
      -- P' i j = -(P i j) > 0 ⇒ P i j < 0; but flip ⇒ P i j ≤ 0 and sigma i j = -1 ⇒ -sigma = 1
      have := (hflip_neg i j hf).1
      rw [this]; norm_num
    · simp only [hf, if_false]
      simp only [hf, if_false] at hpos
      exact hsigma_pos i j hpos
  · -- P' i j < 0 → sigma' i j = -1
    intro i j hneg
    rw [hsig']
    rw [hP'] at hneg
    by_cases hf : flip i j
    · -- contradiction: flip ⇒ P i j ≤ 0 ⇒ -(P i j) ≥ 0, but P' = -(P i j) < 0
      exfalso
      simp only [hf, if_true] at hneg
      have := (hflip_neg i j hf).2
      linarith
    · simp only [hf, if_false]
      simp only [hf, if_false] at hneg
      exact hsigma_neg i j hneg
  · -- constraint sum = m  (= -m·(-1))
    intro j
    rw [hsig']
    simp only [neg_neg, mul_neg, mul_one]
    have hrewrite : ∀ x, (if flip x j then -sigma x j else sigma x j)
        = sigma x j + (if flip x j then (-2 * sigma x j) else 0) := by
      intro x
      by_cases hf : flip x j
      · simp only [hf, if_true]; ring
      · simp only [hf, if_false]; ring
    rw [Finset.sum_congr rfl (fun x _ => hrewrite x), Finset.sum_add_distrib]
    have hsum_sigma : ∑ x, sigma x j = -(m : ℝ) * s j := hconstraint j
    by_cases hsj : s j = 1
    · -- flipped coordinate
      rw [hsj, mul_one] at hsum_sigma
      rw [hsum_sigma]
      -- ∑ (if flip then -2 sigma else 0) = ∑_{i ∈ S j} 2 = 2 m
      have hflip_iff : ∀ x, flip x j ↔ x ∈ S j := by
        intro x; rw [hflip]; simp only [hsj, true_and]
      have hinner : (∑ x, (if flip x j then (-2 * sigma x j) else 0)) = 2 * (m : ℝ) := by
        rw [Finset.sum_ite]
        have hfilter : (Finset.univ.filter (fun x => flip x j)) = S j := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hflip_iff x
        rw [hfilter]
        rw [Finset.sum_const_zero, add_zero]
        have hval : ∀ x ∈ S j, -2 * sigma x j = (2 : ℝ) := by
          intro x hx
          have hfx : flip x j := (hflip_iff x).mpr hx
          rw [(hflip_neg x j hfx).1]; ring
        rw [Finset.sum_congr rfl hval, Finset.sum_const]
        rw [hS_card j hsj]
        simp [mul_comm]
      rw [hinner]; ring
    · -- s j = -1, no flips
      have hsj' : s j = -1 := (hs_pm j).resolve_left hsj
      rw [hsj'] at hsum_sigma
      rw [hsum_sigma]
      have hno_flip : ∀ x, ¬ flip x j := by
        intro x hf; exact hsj (hf.1)
      have hinner : (∑ x, (if flip x j then (-2 * sigma x j) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        simp only [hno_flip x, if_false]
      rw [hinner]; ring
  · -- objective does not increase
    -- Prove it term-wise: for each i, g_lambda 2 lambda f (P' i) ≤ g_lambda 2 lambda f (P i).
    apply Finset.sum_le_sum
    intro i _
    -- Pointwise relation between P' i and P i.
    have hPval : ∀ j, P' i j = (if flip i j then -(P i j) else P i j) := by
      intro j; rw [hP']
    -- Absolute values of P' i j equal those of P i j (sign reflection).
    have habs_eq : ∀ j, |P' i j| = |P i j| := by
      intro j
      rw [hPval j]
      by_cases hf : flip i j
      · simp only [hf, if_true, abs_neg]
      · simp only [hf, if_false]
    -- Distance: |P' i j - f j| ≤ |P i j - f j| for all j.
    have hdist_le : ∀ j, |P' i j - f j| ≤ |P i j - f j| := by
      intro j
      rw [hPval j]
      by_cases hf : flip i j
      · simp only [hf, if_true]
        -- flip ⇒ P i j ≤ 0 < f j; reflection inequality |-(P i j) - f j| ≤ |P i j - f j|.
        have hpneg : P i j ≤ 0 := (hflip_neg i j hf).2
        have hfpos : 0 < f j := hf_pos j
        have hPf_eq : |P i j - f j| = f j - P i j := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [hPf_eq, abs_le]
        constructor
        · linarith
        · linarith
      · simp only [hf, if_false]; exact le_refl _
    -- Now combine via the g_lambda definition.
    unfold g_lambda
    have hnorm_eq : lqNorm 2 (P' i) = lqNorm 2 (P i) :=
      lqNorm2_congr (P' i) (P i) habs_eq
    have hdistnorm_le :
        lqNorm 2 (fun j => P' i j - f j) ≤ lqNorm 2 (fun j => P i j - f j) :=
      lqNorm2_mono (fun j => P' i j - f j) (fun j => P i j - f j) hdist_le
    have hnorm_eq' : lqNorm 2 (fun j => P' i j) = lqNorm 2 (fun j => P i j) := hnorm_eq
    rw [hnorm_eq']
    linarith [hdistnorm_le]

end Workspace.ProofLemmas.RGWorstCasePredictionSignature
