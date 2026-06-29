import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.InteriorFOC_Neg

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

theorem LocalOptimumCharacterization_CaseSEmpty
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma_i j = 1 → 0 ≤ p_star j) ∧
                  (sigma_i j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma_i j = 1 → 0 ≤ p j) ∧
                (sigma_i j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (S : Finset (Fin d))
    (hS_def : S = Finset.univ.filter (fun j : Fin d => sigma_i j = 1))
    (hS_eq : S = ∅) :
    ∃ T : Finset (Fin d), ∃ c' : ℝ, 1 < c' ∧
      (∀ j ∈ T, -(p_star j) = f j / (c' - 1)) ∧
      (∀ j ∉ T, p_star j = 0) ∧
      (∀ j, p_star j ≤ 0) := by
  classical
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_le : 1 ≤ q := le_of_lt hq
  have hq1_pos : 0 < q - 1 := by linarith
  have hq1_ne : (q - 1) ≠ 0 := ne_of_gt hq1_pos
  -- Step 5.2.1: every σ_j = -1, hence p_star j ≤ 0 for all j
  have hsig_neg : ∀ j, sigma_i j = -1 := by
    intro j
    rcases hsigma_pm j with h1 | hm
    · -- σ_j = 1 ⇒ j ∈ S, but S = ∅
      exfalso
      have hj_in : j ∈ S := by
        rw [hS_def]
        simp [Finset.mem_filter, h1]
      rw [hS_eq] at hj_in
      exact (Finset.notMem_empty j) hj_in
    · exact hm
  have hpstar_le : ∀ j, p_star j ≤ 0 := fun j => (hp_in j).2 (hsig_neg j)
  -- Step 5.2.2: define T
  set T : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => p_star j < 0) with hT_def
  have hT_mem : ∀ j, j ∈ T ↔ p_star j < 0 := by
    intro j
    rw [hT_def, Finset.mem_filter]
    simp
  -- Step 5.2.3: case on whether T is empty.  T may legitimately be empty
  -- (the all-zero point is a genuine local min when every σ = −1); in that
  -- case the conclusion holds vacuously with c' = 2.
  rcases Finset.eq_empty_or_nonempty T with hT_empty | hT_ne
  · -- T = ∅ ⇒ ∀ j, p_star j = 0.  Witnesses: T (= ∅), c' = 2.
    have hpstar_zero : ∀ j, p_star j = 0 := by
      intro j
      have hnotmem : j ∉ T := by
        rw [hT_empty]; exact Finset.notMem_empty j
      have hnot_lt : ¬ p_star j < 0 := by
        intro h_lt
        exact hnotmem ((hT_mem j).mpr h_lt)
      have h_ge : 0 ≤ p_star j := not_lt.mp hnot_lt
      linarith [hpstar_le j]
    refine ⟨T, 2, by norm_num, ?_, ?_, hpstar_le⟩
    · intro j hjT
      rw [hT_empty] at hjT
      exact absurd hjT (Finset.notMem_empty j)
    · intro j _
      exact hpstar_zero j
  -- Step 5.2.4: define c' (T nonempty branch)
  -- First we need lqNorm q p_star > 0 and lqNorm q (p_star - f) > 0
  -- Pick j₀ ∈ T
  obtain ⟨j₀, hj₀_T⟩ := hT_ne
  have hj₀_neg : p_star j₀ < 0 := (hT_mem j₀).mp hj₀_T
  -- lqNorm q p_star > 0 because |p_star j₀| > 0
  have hp_norm_pos : 0 < lqNorm q p_star := by
    -- Use that |p_star j₀|^q > 0 ≤ ∑ j, |p_star j|^q, so the sum is positive
    have h_abs_pos : 0 < |p_star j₀| := abs_pos.mpr (ne_of_lt hj₀_neg)
    have h_each_nn : ∀ j, 0 ≤ |p_star j| ^ q :=
      fun j => Real.rpow_nonneg (abs_nonneg _) q
    have h_j₀_pow_pos : 0 < |p_star j₀| ^ q := Real.rpow_pos_of_pos h_abs_pos q
    have h_sum_pos : 0 < ∑ j, |p_star j| ^ q := by
      have h_le := Finset.single_le_sum (f := fun j => |p_star j| ^ q)
        (s := Finset.univ) (a := j₀)
        (fun k _ => h_each_nn k) (Finset.mem_univ j₀)
      linarith
    unfold lqNorm
    exact Real.rpow_pos_of_pos h_sum_pos _
  have hp_norm_ne : lqNorm q p_star ≠ 0 := ne_of_gt hp_norm_pos
  -- lqNorm q (p_star - f) > 0 because |p_star j₀ - f j₀| > 0
  have hpf_norm_pos : 0 < lqNorm q (fun k => p_star k - f k) := by
    -- p_star j₀ < 0 ≤ f j₀, so p_star j₀ - f j₀ < 0
    have h_sub_neg : p_star j₀ - f j₀ < 0 := by
      have := hf_nn j₀
      linarith
    have h_sub_ne : p_star j₀ - f j₀ ≠ 0 := ne_of_lt h_sub_neg
    have h_abs_pos : 0 < |p_star j₀ - f j₀| := abs_pos.mpr h_sub_ne
    have h_each_nn : ∀ j, 0 ≤ |p_star j - f j| ^ q :=
      fun j => Real.rpow_nonneg (abs_nonneg _) q
    have h_j₀_pow_pos : 0 < |p_star j₀ - f j₀| ^ q := Real.rpow_pos_of_pos h_abs_pos q
    have h_sum_pos : 0 < ∑ j, |p_star j - f j| ^ q := by
      have h_le := Finset.single_le_sum (f := fun j => |p_star j - f j| ^ q)
        (s := Finset.univ) (a := j₀)
        (fun k _ => h_each_nn k) (Finset.mem_univ j₀)
      linarith
    unfold lqNorm
    exact Real.rpow_pos_of_pos h_sum_pos _
  have hpf_norm_ne : lqNorm q (fun k => p_star k - f k) ≠ 0 := ne_of_gt hpf_norm_pos
  -- Define c'
  set c' : ℝ := Real.rpow lambda (1 / (q - 1)) * lqNorm q (fun k => p_star k - f k) / lqNorm q p_star with hc'_def
  have hlam_pow_pos : 0 < Real.rpow lambda (1 / (q - 1)) := Real.rpow_pos_of_pos hlam0 _
  have hc'_pos : 0 < c' := by
    rw [hc'_def]
    exact div_pos (mul_pos hlam_pow_pos hpf_norm_pos) hp_norm_pos
  -- Step 5.2.5: equation (⋆_-) on T (using InteriorFOC_Neg)
  -- For j ∈ T, derive (f j - p_star j) / (-(p_star j)) = c'
  have hFOC_eq : ∀ j ∈ T, (f j - p_star j) / (-(p_star j)) = c' := by
    intro j hjT
    have hp_j_neg : p_star j < 0 := (hT_mem j).mp hjT
    have hsig_j : sigma_i j = -1 := hsig_neg j
    -- Apply InteriorFOC_Neg
    have hFOC := InteriorFOC_Neg q hq lambda hlam0 hlam1 hd f hf_nn hf_sum sigma_i hsigma_pm
        p_star hp_in hp_loc hpf_norm_pos hp_norm_pos j hsig_j hp_j_neg
    -- hFOC : (f j - p_star j)^(q-1) / N1^(q-1) = lambda * ((-(p_star j))^(q-1) / N2^(q-1))
    -- where N1 = lqNorm q (fun k => p_star k - f k), N2 = lqNorm q p_star
    set N1 : ℝ := lqNorm q (fun k => p_star k - f k) with hN1
    set N2 : ℝ := lqNorm q p_star with hN2
    have hA_pos : 0 < f j - p_star j := by
      have := hf_nn j
      linarith
    have hB_pos : 0 < -(p_star j) := by linarith
    have hN1_pos : 0 < N1 := hpf_norm_pos
    have hN2_pos : 0 < N2 := hp_norm_pos
    have hA_q1_pos : 0 < (f j - p_star j) ^ (q - 1) := Real.rpow_pos_of_pos hA_pos _
    have hB_q1_pos : 0 < (-(p_star j)) ^ (q - 1) := Real.rpow_pos_of_pos hB_pos _
    have hN1_q1_pos : 0 < N1 ^ (q - 1) := Real.rpow_pos_of_pos hN1_pos _
    have hN2_q1_pos : 0 < N2 ^ (q - 1) := Real.rpow_pos_of_pos hN2_pos _
    -- Manipulate hFOC: cross-multiply
    -- A^(q-1) / N1^(q-1) = lambda * (B^(q-1) / N2^(q-1))
    -- A^(q-1) * N2^(q-1) = lambda * B^(q-1) * N1^(q-1)
    -- (A/B)^(q-1) = lambda * (N1/N2)^(q-1)
    -- = (lambda^(1/(q-1)))^(q-1) * (N1/N2)^(q-1)
    -- = (lambda^(1/(q-1)) * N1/N2)^(q-1) = (c')^(q-1)
    have h_eq1 : ((f j - p_star j) / (-(p_star j))) ^ (q - 1) = c' ^ (q - 1) := by
      -- Step 1: (f j - p_star j) / (-(p_star j)) ^(q-1) = ((f j - p_star j)^(q-1)) / ((-(p_star j))^(q-1))
      have hA_nn : 0 ≤ f j - p_star j := le_of_lt hA_pos
      have hB_nn : 0 ≤ -(p_star j) := le_of_lt hB_pos
      have hN1_nn : 0 ≤ N1 := le_of_lt hN1_pos
      have hN2_nn : 0 ≤ N2 := le_of_lt hN2_pos
      have hlam_nn : 0 ≤ lambda := le_of_lt hlam0
      have hlam_pow_nn : 0 ≤ Real.rpow lambda (1 / (q - 1)) := le_of_lt hlam_pow_pos
      -- (A/B)^(q-1) = A^(q-1) / B^(q-1)
      rw [Real.div_rpow hA_nn hB_nn]
      -- c'^(q-1) = (lambda^(1/(q-1)) * N1 / N2)^(q-1) = (lambda^(1/(q-1)))^(q-1) * (N1/N2)^(q-1)
      --   = lambda * (N1/N2)^(q-1) = lambda * N1^(q-1) / N2^(q-1)
      have hc'_eq : c' ^ (q - 1)
          = lambda * (N1 ^ (q - 1) / N2 ^ (q - 1)) := by
        rw [hc'_def]
        rw [show Real.rpow lambda (1 / (q - 1)) * N1 / N2
            = (Real.rpow lambda (1 / (q - 1)) * N1) * (N2)⁻¹ by ring]
        -- ((λ^{1/(q-1)} * N1) * N2⁻¹)^(q-1) = (λ^{1/(q-1)})^(q-1) * N1^(q-1) * (N2⁻¹)^(q-1)
        --   = λ * N1^(q-1) * N2^(-1*(q-1)) -- wait, easier to use Real.div_rpow & Real.mul_rpow
        rw [show Real.rpow lambda (1 / (q - 1)) * N1 * N2⁻¹
            = (Real.rpow lambda (1 / (q - 1)) * N1) / N2 by ring]
        rw [Real.div_rpow (mul_nonneg hlam_pow_nn hN1_nn) hN2_nn]
        rw [Real.mul_rpow hlam_pow_nn hN1_nn]
        -- (λ^{1/(q-1)})^(q-1) = λ
        have h_pow : (Real.rpow lambda (1 / (q - 1))) ^ (q - 1) = lambda := by
          show (lambda ^ (1 / (q - 1) : ℝ)) ^ (q - 1 : ℝ) = lambda
          rw [← Real.rpow_mul hlam_nn]
          rw [show (1/(q-1) : ℝ) * (q-1) = 1 from by field_simp]
          exact Real.rpow_one _
        rw [h_pow]
        ring
      rw [hc'_eq]
      -- Now we have A^(q-1) / B^(q-1) = lambda * (N1^(q-1) / N2^(q-1))
      -- From hFOC : A^(q-1) / N1^(q-1) = lambda * (B^(q-1) / N2^(q-1))
      -- Need: A^(q-1) / B^(q-1) = lambda * N1^(q-1) / N2^(q-1)
      -- From hFOC: A^(q-1) * N2^(q-1) = lambda * B^(q-1) * N1^(q-1) (cross multiply)
      -- Divide both sides by B^(q-1) * N2^(q-1): A^(q-1)/B^(q-1) = lambda * N1^(q-1) / N2^(q-1)
      have hN1_q1_ne : N1 ^ (q - 1) ≠ 0 := ne_of_gt hN1_q1_pos
      have hN2_q1_ne : N2 ^ (q - 1) ≠ 0 := ne_of_gt hN2_q1_pos
      have hB_q1_ne : (-(p_star j)) ^ (q - 1) ≠ 0 := ne_of_gt hB_q1_pos
      field_simp at hFOC
      field_simp
      linarith
    -- Now A/B and c' are both positive; their (q-1)-th powers are equal
    have hAB_pos : 0 < (f j - p_star j) / (-(p_star j)) := div_pos hA_pos hB_pos
    have hAB_nn : 0 ≤ (f j - p_star j) / (-(p_star j)) := le_of_lt hAB_pos
    have hc'_nn : 0 ≤ c' := le_of_lt hc'_pos
    exact (Real.rpow_left_inj hAB_nn hc'_nn hq1_ne).mp h_eq1
  -- Step 5.2.6: c' > 1, derived directly from the witness j₀ ∈ T.
  -- FOC at j₀ gives (f j₀ - p_star j₀) / (-(p_star j₀)) = c'; since f j₀ > 0
  -- (by hf_pos) the numerator exceeds the denominator, forcing c' > 1.
  have hFOC_j0 : (f j₀ - p_star j₀) / (-(p_star j₀)) = c' := hFOC_eq j₀ hj₀_T
  have hB_j0_pos : 0 < -(p_star j₀) := by linarith
  have hc'_gt1 : 1 < c' := by
    rw [← hFOC_j0]
    rw [lt_div_iff₀ hB_j0_pos]
    linarith [hf_pos j₀]
  -- Step 5.2.7: closed form -p_star j = f j / (c' - 1) for j ∈ T
  have hc'1_pos : 0 < c' - 1 := by linarith
  have hc'1_ne : c' - 1 ≠ 0 := ne_of_gt hc'1_pos
  have heqT : ∀ j ∈ T, -(p_star j) = f j / (c' - 1) := by
    intro j hjT
    have hp_j_neg : p_star j < 0 := (hT_mem j).mp hjT
    have hB_j_pos : 0 < -(p_star j) := by linarith
    have hB_j_ne : -(p_star j) ≠ 0 := ne_of_gt hB_j_pos
    have h_eq := hFOC_eq j hjT
    -- (f j - p_star j) / (-(p_star j)) = c'
    -- ⇒ f j - p_star j = c' * (-(p_star j))
    have h1 : f j - p_star j = c' * (-(p_star j)) := by
      have := (div_eq_iff hB_j_ne).mp h_eq
      linarith
    -- f j = c' * (-(p_star j)) + p_star j = (c' - 1) * (-(p_star j))
    have h2 : f j = (c' - 1) * (-(p_star j)) := by linarith
    -- Hence -(p_star j) = f j / (c' - 1)
    rw [h2]
    field_simp
  -- Step 5.2.8: For j ∉ T, p_star j = 0
  have heqTc : ∀ j ∉ T, p_star j = 0 := by
    intro j hjnotT
    have hnot_lt : ¬ p_star j < 0 := by
      intro h_lt
      exact hjnotT ((hT_mem j).mpr h_lt)
    have h_ge : 0 ≤ p_star j := not_lt.mp hnot_lt
    exact le_antisymm (hpstar_le j) h_ge
  -- Assemble
  exact ⟨T, c', hc'_gt1, heqT, heqTc, hpstar_le⟩
