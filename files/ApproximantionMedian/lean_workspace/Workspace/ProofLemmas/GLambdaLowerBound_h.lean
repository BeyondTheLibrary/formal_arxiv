import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.LambdaDeltaIdentity
import Workspace.ProofLemmas.LocalMinEmptyS

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists
open Workspace.ProofLemmas.LambdaDeltaIdentity

theorem GLambdaLowerBound_h
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma_i : Fin d → ℝ) (hsigma_pm : ∀ j, sigma_i j = 1 ∨ sigma_i j = -1)
    (p_star : Fin d → ℝ)
    (h_local :
      let S := Finset.univ.filter (fun j : Fin d => sigma_i j = 1)
      ( S.Nonempty ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
          (∀ j ∈ S, p_star j = f j / (1 - c)) ∧
          (∀ j ∉ S, p_star j = 0) )
      ∨
      ( S = ∅ ∧ ∃ T : Finset (Fin d), ∃ c' : ℝ, 1 < c' ∧
          (∀ j ∈ T, -(p_star j) = f j / (c' - 1)) ∧
          (∀ j ∉ T, p_star j = 0) ∧
          (∀ j, p_star j ≤ 0) )) :
    let S := Finset.univ.filter (fun j : Fin d => sigma_i j = 1)
    let x := ∑ j ∈ S, (f j) ^ q
    lambda *
      (delta_of_lambda q lambda * (1 - x) ^ ((1 : ℝ) / q) - x ^ ((1 : ℝ) / q))
      ≤ g_lambda q lambda f p_star := by
  classical
  intro S
  intro x
  -- Set up basic positivity / arithmetic facts
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_sub_pos : 0 < q - 1 := by linarith
  have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hq_sub_pos
  have hq_le : (1 : ℝ) ≤ q := le_of_lt hq
  have h_inv_q_pos : 0 < (1 : ℝ) / q := by positivity
  have h_inv_q_nn : 0 ≤ (1 : ℝ) / q := le_of_lt h_inv_q_pos
  have hlam_nn : (0 : ℝ) ≤ lambda := le_of_lt hlam0
  have hlam_le : lambda ≤ 1 := le_of_lt hlam1
  -- r := q / (q - 1)
  set r : ℝ := q / (q - 1) with hr_def
  have hr_pos : 0 < r := div_pos hq_pos hq_sub_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hlam_r_pos : 0 < lambda ^ r := Real.rpow_pos_of_pos hlam0 _
  have hlam_r_nn : 0 ≤ lambda ^ r := le_of_lt hlam_r_pos
  -- 1 - lambda^r > 0
  have h_lam_r_lt_one : lambda ^ r < 1 := by
    have h1 : lambda ^ r < (1 : ℝ) ^ r :=
      Real.rpow_lt_rpow hlam_nn hlam1 hr_pos
    simpa using h1
  have h_one_sub_pos : 0 < 1 - lambda ^ r := by linarith
  have h_one_sub_nn : 0 ≤ 1 - lambda ^ r := le_of_lt h_one_sub_pos
  -- lambda * delta = (1 - lambda^r)^((q-1)/q)
  have h_lam_delta : lambda * delta_of_lambda q lambda
        = (1 - lambda ^ r) ^ ((q - 1) / q) := by
    have := LambdaDeltaIdentity q hq lambda hlam0 hlam_le
    simpa [hr_def] using this
  -- f j ≥ 0, so |f j| = f j
  have hf_abs : ∀ j, |f j| = f j := fun j => abs_of_nonneg (hf_nn j)
  -- 1 - x = sum over complement of S
  have h_one_sub_x : (1 : ℝ) - x = ∑ j ∈ Sᶜ, (f j) ^ q := by
    have h_split := Finset.sum_compl_add_sum (s := S) (f := fun j => (f j) ^ q)
    have : (∑ j ∈ Sᶜ, (f j) ^ q) + (∑ j ∈ S, (f j) ^ q) = ∑ j, (f j) ^ q := by
      simpa using h_split
    rw [hf_sum] at this
    linarith
  -- x ≥ 0, 1 - x ≥ 0
  have hx_nn : 0 ≤ x := by
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) q
  have h_one_sub_x_nn : 0 ≤ 1 - x := by
    rw [h_one_sub_x]
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (hf_nn j) q
  -- Now do the case split
  rcases h_local with ⟨hS_ne, c, hc0, hc1, hp_in, hp_out⟩ | ⟨hS_emp, hcase2⟩
  · -- Case (i): S nonempty
    have h1c_pos : 0 < 1 - c := by linarith
    have h1c_ne : 1 - c ≠ 0 := ne_of_gt h1c_pos
    have h1c_nn : 0 ≤ 1 - c := le_of_lt h1c_pos
    have hc_nn : 0 ≤ c := hc0
    have h_c_over : 0 ≤ c / (1 - c) := div_nonneg hc_nn h1c_nn
    -- For j ∈ S: |p_star j|^q = f j^q / (1-c)^q
    have h_ps_in : ∀ j ∈ S, |p_star j| ^ q = (f j) ^ q / (1 - c) ^ q := by
      intro j hj
      have h_eq : p_star j = f j / (1 - c) := hp_in j hj
      have h_nn : 0 ≤ p_star j := by
        rw [h_eq]; exact div_nonneg (hf_nn j) h1c_nn
      rw [abs_of_nonneg h_nn, h_eq]
      rw [Real.div_rpow (hf_nn j) h1c_nn]
    -- For j ∈ S: |p_star j - f j|^q = (c/(1-c))^q * f j^q
    have h_ps_diff_in : ∀ j ∈ S, |p_star j - f j| ^ q
        = (c / (1 - c)) ^ q * (f j) ^ q := by
      intro j hj
      have h_eq : p_star j = f j / (1 - c) := hp_in j hj
      have h_diff : p_star j - f j = f j * (c / (1 - c)) := by
        rw [h_eq]; field_simp; ring
      have h_diff_nn : 0 ≤ p_star j - f j := by
        rw [h_diff]; exact mul_nonneg (hf_nn j) h_c_over
      rw [abs_of_nonneg h_diff_nn, h_diff]
      rw [Real.mul_rpow (hf_nn j) h_c_over]
      ring
    -- For j ∉ S: |p_star j|^q = 0
    have h_ps_out : ∀ j ∉ S, |p_star j| ^ q = 0 := by
      intro j hj
      rw [hp_out j hj, abs_zero, Real.zero_rpow hq_ne]
    -- For j ∉ S: |p_star j - f j|^q = f j^q
    have h_ps_diff_out : ∀ j ∉ S, |p_star j - f j| ^ q = (f j) ^ q := by
      intro j hj
      rw [hp_out j hj, zero_sub, abs_neg, hf_abs j]
    -- Compute sum |p_star|^q
    have h_sum_ps : (∑ j, |p_star j| ^ q) = x / (1 - c) ^ q := by
      have hsplit := Finset.sum_compl_add_sum (s := S) (f := fun j => |p_star j| ^ q)
      have hSc : (∑ j ∈ Sᶜ, |p_star j| ^ q) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hj' : j ∉ S := by
          intro hjS
          exact (Finset.mem_compl.mp hj) hjS
        exact h_ps_out j hj'
      have hSi : (∑ j ∈ S, |p_star j| ^ q) = ∑ j ∈ S, (f j) ^ q / (1 - c) ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h_ps_in j hj
      have h_total : (∑ j, |p_star j| ^ q) = ∑ j ∈ S, (f j) ^ q / (1 - c) ^ q := by
        calc (∑ j, |p_star j| ^ q)
            = (∑ j ∈ Sᶜ, |p_star j| ^ q) + (∑ j ∈ S, |p_star j| ^ q) := hsplit.symm
          _ = 0 + (∑ j ∈ S, |p_star j| ^ q) := by rw [hSc]
          _ = ∑ j ∈ S, |p_star j| ^ q := by rw [zero_add]
          _ = ∑ j ∈ S, (f j) ^ q / (1 - c) ^ q := hSi
      rw [h_total]
      rw [show x = ∑ j ∈ S, (f j) ^ q from rfl]
      rw [← Finset.sum_div]
    -- Compute sum |p_star - f|^q
    have h_sum_ps_diff : (∑ j, |p_star j - f j| ^ q)
        = (c / (1 - c)) ^ q * x + (1 - x) := by
      have hsplit := Finset.sum_compl_add_sum (s := S) (f := fun j => |p_star j - f j| ^ q)
      have hSc : (∑ j ∈ Sᶜ, |p_star j - f j| ^ q) = ∑ j ∈ Sᶜ, (f j) ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ∉ S := by
          intro hjS
          exact (Finset.mem_compl.mp hj) hjS
        exact h_ps_diff_out j hj'
      have hSi : (∑ j ∈ S, |p_star j - f j| ^ q)
          = ∑ j ∈ S, (c / (1 - c)) ^ q * (f j) ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h_ps_diff_in j hj
      have h_total : (∑ j, |p_star j - f j| ^ q)
          = (∑ j ∈ Sᶜ, (f j) ^ q) + (c / (1 - c)) ^ q * x := by
        calc (∑ j, |p_star j - f j| ^ q)
            = (∑ j ∈ Sᶜ, |p_star j - f j| ^ q) + (∑ j ∈ S, |p_star j - f j| ^ q) :=
              hsplit.symm
          _ = (∑ j ∈ Sᶜ, (f j) ^ q) + (∑ j ∈ S, (c / (1 - c)) ^ q * (f j) ^ q) := by
              rw [hSc, hSi]
          _ = (∑ j ∈ Sᶜ, (f j) ^ q) + (c / (1 - c)) ^ q * (∑ j ∈ S, (f j) ^ q) := by
              rw [Finset.mul_sum]
          _ = (∑ j ∈ Sᶜ, (f j) ^ q) + (c / (1 - c)) ^ q * x := rfl
      rw [h_total]
      rw [show (∑ j ∈ Sᶜ, (f j) ^ q) = 1 - x from h_one_sub_x.symm]
      ring
    -- Compute lqNorm q p_star = x^(1/q) / (1-c)
    have h_norm_ps : lqNorm q p_star = x ^ ((1 : ℝ) / q) / (1 - c) := by
      unfold lqNorm
      rw [h_sum_ps]
      rw [Real.div_rpow hx_nn (Real.rpow_nonneg h1c_nn q)]
      have h_pow : ((1 - c) ^ q) ^ ((1 : ℝ) / q) = 1 - c := by
        rw [← Real.rpow_mul h1c_nn]
        rw [mul_one_div, div_self hq_ne, Real.rpow_one]
      rw [h_pow]
    -- Compute lqNorm q (p_star - f) = ((c/(1-c))^q * x + (1-x))^(1/q)
    have h_norm_psf : lqNorm q (fun j => p_star j - f j)
        = ((c / (1 - c)) ^ q * x + (1 - x)) ^ ((1 : ℝ) / q) := by
      unfold lqNorm
      rw [h_sum_ps_diff]
    -- g_lambda q lambda f p_star
    have h_g : g_lambda q lambda f p_star
        = ((c / (1 - c)) ^ q * x + (1 - x)) ^ ((1 : ℝ) / q)
            - lambda * (x ^ ((1 : ℝ) / q) / (1 - c)) := by
      unfold g_lambda
      rw [h_norm_ps, h_norm_psf]
    -- Apply two-term Hölder
    -- HolderConjugate q r where r = q/(q-1)
    have hr_q_conj : (q : ℝ).HolderConjugate r := by
      rw [Real.holderConjugate_iff]
      refine ⟨hq, ?_⟩
      rw [hr_def]
      field_simp
      ring
    -- Define vectors A and B
    -- A 0 = (c/(1-c)) * x^(1/q),  A 1 = (1-x)^(1/q)
    -- B 0 = lambda,                B 1 = (1 - lambda^r)^((q-1)/q)
    -- ∑ A*B ≤ (∑|A|^q)^(1/q) * (∑|B|^r)^(1/r)
    have h_x_inv_q_nn : 0 ≤ x ^ ((1 : ℝ) / q) := Real.rpow_nonneg hx_nn _
    have h_one_x_inv_q_nn : 0 ≤ (1 - x) ^ ((1 : ℝ) / q) :=
      Real.rpow_nonneg h_one_sub_x_nn _
    have h_lamr_pow_nn : 0 ≤ (1 - lambda ^ r) ^ ((q - 1) / q) :=
      Real.rpow_nonneg h_one_sub_nn _
    let A : Fin 2 → ℝ := fun i => if i = 0 then (c / (1 - c)) * x ^ ((1 : ℝ) / q)
                                  else (1 - x) ^ ((1 : ℝ) / q)
    let B : Fin 2 → ℝ := fun i => if i = 0 then lambda
                                  else (1 - lambda ^ r) ^ ((q - 1) / q)
    have hA0 : A 0 = (c / (1 - c)) * x ^ ((1 : ℝ) / q) := by simp [A]
    have hA1 : A 1 = (1 - x) ^ ((1 : ℝ) / q) := by simp [A]
    have hB0 : B 0 = lambda := by simp [B]
    have hB1 : B 1 = (1 - lambda ^ r) ^ ((q - 1) / q) := by simp [B]
    -- ∑ A*B
    have h_sum_AB : (∑ i, A i * B i)
        = (c / (1 - c)) * x ^ ((1 : ℝ) / q) * lambda
            + (1 - x) ^ ((1 : ℝ) / q) * (1 - lambda ^ r) ^ ((q - 1) / q) := by
      rw [Fin.sum_univ_two, hA0, hA1, hB0, hB1]
    -- ∑ |A i|^q
    have h_A0_nn : 0 ≤ A 0 := by
      rw [hA0]; exact mul_nonneg h_c_over h_x_inv_q_nn
    have h_A1_nn : 0 ≤ A 1 := by
      rw [hA1]; exact h_one_x_inv_q_nn
    have h_B0_nn : 0 ≤ B 0 := by rw [hB0]; exact hlam_nn
    have h_B1_nn : 0 ≤ B 1 := by rw [hB1]; exact h_lamr_pow_nn
    have h_pow_xinvq : (x ^ ((1 : ℝ) / q)) ^ q = x := by
      rw [← Real.rpow_mul hx_nn, one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
    have h_pow_oneminusx : ((1 - x) ^ ((1 : ℝ) / q)) ^ q = 1 - x := by
      rw [← Real.rpow_mul h_one_sub_x_nn, one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]
    have h_sum_Aq : (∑ i, |A i| ^ q) = (c / (1 - c)) ^ q * x + (1 - x) := by
      rw [Fin.sum_univ_two]
      rw [hA0, hA1]
      rw [abs_of_nonneg (mul_nonneg h_c_over h_x_inv_q_nn)]
      rw [abs_of_nonneg h_one_x_inv_q_nn]
      rw [Real.mul_rpow h_c_over h_x_inv_q_nn]
      rw [h_pow_xinvq, h_pow_oneminusx]
    -- ∑ |B i|^r
    have h_pow_lamr : ((1 - lambda ^ r) ^ ((q - 1) / q)) ^ r = 1 - lambda ^ r := by
      rw [← Real.rpow_mul h_one_sub_nn]
      have h_prod : (q - 1) / q * r = 1 := by
        rw [hr_def]; field_simp
      rw [h_prod, Real.rpow_one]
    have h_sum_Br : (∑ i, |B i| ^ r) = 1 := by
      rw [Fin.sum_univ_two]
      rw [hB0, hB1]
      rw [abs_of_nonneg hlam_nn]
      rw [abs_of_nonneg h_lamr_pow_nn]
      rw [h_pow_lamr]
      linarith
    -- Apply Hölder
    have h_holder := Real.inner_le_Lp_mul_Lq Finset.univ A B hr_q_conj
    rw [h_sum_AB, h_sum_Aq, h_sum_Br] at h_holder
    have h_one_rpow : (1 : ℝ) ^ ((1 : ℝ) / r) = 1 := Real.one_rpow _
    rw [h_one_rpow, mul_one] at h_holder
    -- h_holder: (c/(1-c))*x^(1/q)*lambda + (1-x)^(1/q)*(1-lambda^r)^((q-1)/q)
    --           ≤ ((c/(1-c))^q * x + (1-x))^(1/q)
    rw [h_g]
    -- Goal: lambda * (delta * (1-x)^(1/q) - x^(1/q))
    --      ≤ ((c/(1-c))^q * x + (1-x))^(1/q) - lambda * (x^(1/q)/(1-c))
    -- Step: rewrite LHS using h_lam_delta
    have h_LHS : lambda * (delta_of_lambda q lambda * (1 - x) ^ ((1 : ℝ) / q)
          - x ^ ((1 : ℝ) / q))
        = (1 - lambda ^ r) ^ ((q - 1) / q) * (1 - x) ^ ((1 : ℝ) / q)
            - lambda * x ^ ((1 : ℝ) / q) := by
      have h1 : lambda * delta_of_lambda q lambda * (1 - x) ^ ((1 : ℝ) / q)
            = (1 - lambda ^ r) ^ ((q - 1) / q) * (1 - x) ^ ((1 : ℝ) / q) := by
        rw [h_lam_delta]
      have h2 : lambda * (delta_of_lambda q lambda * (1 - x) ^ ((1 : ℝ) / q)
            - x ^ ((1 : ℝ) / q))
          = lambda * delta_of_lambda q lambda * (1 - x) ^ ((1 : ℝ) / q)
              - lambda * x ^ ((1 : ℝ) / q) := by ring
      rw [h2, h1]
    rw [h_LHS]
    -- Now need to show:
    -- (1-lambda^r)^((q-1)/q) * (1-x)^(1/q) - lambda * x^(1/q)
    -- ≤ ((c/(1-c))^q*x + (1-x))^(1/q) - lambda * (x^(1/q)/(1-c))
    -- Equivalently: lambda*(x^(1/q)/(1-c)) - lambda * x^(1/q)
    --            ≤ ((c/(1-c))^q*x + (1-x))^(1/q) - (1-lambda^r)^((q-1)/q)*(1-x)^(1/q)
    -- And: lambda*(x^(1/q)/(1-c)) - lambda*x^(1/q) = lambda * x^(1/q) * c/(1-c)
    --                                              = (c/(1-c)) * x^(1/q) * lambda
    -- So we need ((c/(1-c)) * x^(1/q) * lambda) + (1-lambda^r)^((q-1)/q) * (1-x)^(1/q)
    --           ≤ ((c/(1-c))^q*x + (1-x))^(1/q)
    -- which is h_holder (with the second term reordered).
    have h_eq_form : lambda * (x ^ ((1 : ℝ) / q) / (1 - c)) - lambda * x ^ ((1 : ℝ) / q)
        = (c / (1 - c)) * x ^ ((1 : ℝ) / q) * lambda := by
      have : x ^ ((1 : ℝ) / q) / (1 - c) - x ^ ((1 : ℝ) / q)
          = (c / (1 - c)) * x ^ ((1 : ℝ) / q) := by
        field_simp; ring
      have hmul : lambda * (x ^ ((1 : ℝ) / q) / (1 - c) - x ^ ((1 : ℝ) / q))
          = lambda * ((c / (1 - c)) * x ^ ((1 : ℝ) / q)) := by
        rw [this]
      have hl : lambda * (x ^ ((1 : ℝ) / q) / (1 - c) - x ^ ((1 : ℝ) / q))
          = lambda * (x ^ ((1 : ℝ) / q) / (1 - c)) - lambda * x ^ ((1 : ℝ) / q) := by ring
      have hr : lambda * ((c / (1 - c)) * x ^ ((1 : ℝ) / q))
          = (c / (1 - c)) * x ^ ((1 : ℝ) / q) * lambda := by ring
      linarith [hmul, hl, hr]
    linarith [h_holder, h_eq_form]
  · -- Case (ii): S = ∅
    -- x = 0 in this case
    have hx_zero : x = 0 := by
      show (∑ j ∈ S, (f j) ^ q) = 0
      have : S = ∅ := hS_emp
      rw [this, Finset.sum_empty]
    obtain ⟨T, c', hc'_lt, hp_in, hp_out, hp_nonpos⟩ := hcase2
    rw [hx_zero]
    have h_one_sub_zero : (1 : ℝ) - 0 = 1 := by ring
    rw [h_one_sub_zero]
    have h_one_pow : (1 : ℝ) ^ ((1 : ℝ) / q) = 1 := Real.one_rpow _
    have h_zero_pow : (0 : ℝ) ^ ((1 : ℝ) / q) = 0 :=
      Real.zero_rpow (ne_of_gt h_inv_q_pos)
    rw [h_one_pow, h_zero_pow]
    have h_calc : lambda * (delta_of_lambda q lambda * 1 - 0)
        = lambda * delta_of_lambda q lambda := by ring
    rw [h_calc, h_lam_delta]
    rcases Finset.eq_empty_or_nonempty T with hT_emp | hT_ne
    · -- T = ∅ : every p_star j = 0, so g_lambda = 1 and the bound is ≤ 1
      have hp0 : ∀ j, p_star j = 0 := by
        intro j
        exact hp_out j (hT_emp ▸ Finset.notMem_empty j)
      -- g_lambda q lambda f p_star = 1
      have h_g_one : g_lambda q lambda f p_star = 1 := by
        unfold g_lambda
        have h_norm_ps : lqNorm q p_star = 0 := by
          unfold lqNorm
          have : (∑ j, |p_star j| ^ q) = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hp0 j, abs_zero, Real.zero_rpow hq_ne]
          rw [this, Real.zero_rpow (ne_of_gt h_inv_q_pos)]
        have h_norm_psf : lqNorm q (fun j => p_star j - f j) = 1 := by
          unfold lqNorm
          have hsum : (∑ j, |p_star j - f j| ^ q) = 1 := by
            have : (∑ j, |p_star j - f j| ^ q) = ∑ j, (f j) ^ q := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hp0 j, zero_sub, abs_neg, hf_abs j]
            rw [this, hf_sum]
          rw [hsum, Real.one_rpow]
        rw [h_norm_ps, h_norm_psf]
        ring
      rw [h_g_one]
      -- Goal: (1 - lambda^r)^((q-1)/q) ≤ 1
      apply Real.rpow_le_one h_one_sub_nn (by linarith [hlam_r_nn]) (by positivity)
    · -- T nonempty : existing LocalMinEmptyS path
      have h_min := LocalMinEmptyS q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
          T hT_ne c' hc'_lt p_star hp_in hp_out hp_nonpos
      exact h_min
