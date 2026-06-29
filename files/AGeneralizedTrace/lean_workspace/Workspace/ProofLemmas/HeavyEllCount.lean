import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound

set_option maxHeartbeats 4000000

open Classical
open Workspace.Types.AlternatingSumExpression

theorem HeavyEllCount :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j))
      let P_H : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
            ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ)
      (P_H.card : ℝ) ≤ (n : ℝ) * Real.exp (Real.sqrt n / 2) := by
  intro n hn hmod
  -- Unfold the let bindings
  simp only
  -- Set up basic constants
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'def
  set α : ℝ := c' * Real.sqrt n with hαdef
  -- Sanity facts
  have hn_pos : (0 : ℝ) < n := by
    have h1 : (10 : ℝ) ^ 12 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < (10 : ℝ) ^ 12 := by norm_num
    linarith
  have hn_one : (1 : ℕ) ≤ n := by
    have : (1 : ℕ) ≤ 10 ^ 12 := by norm_num
    exact this.trans hn
  have hsqrtn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hexp2_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hc'_pos : 0 < c' := by
    rw [hc'def]; positivity
  have hα_pos : 0 < α := by
    rw [hαdef]; exact mul_pos hc'_pos hsqrtn_pos
  have hα_nn : 0 ≤ α := le_of_lt hα_pos
  -- S_er r j ≥ 0: binPMFInt ≥ 0 and α ≥ 0.
  have hS_er_nn : ∀ (r : ℤ) (j : ℕ), 0 ≤ α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) := by
    intro r j
    apply mul_nonneg hα_nn
    unfold binPMFInt
    split_ifs with hcase
    · unfold binPMF
      split_ifs with hcase2
      · positivity
      · norm_num
    · norm_num
  -- S_er r j ≤ 1: from BinomialPmfMaxBound.
  have hα_binPMF_le : ∀ (r : ℤ) (j : ℕ),
      α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ c' * Real.sqrt (2 / Real.pi) := by
    intro r j
    set k := r + ((n : ℤ) / 4) + (j : ℤ) with hkdef
    have hbin_bound : binPMFInt n (1/2) k ≤ Real.sqrt (2 / (Real.pi * n)) := by
      unfold binPMFInt
      split_ifs with hcase
      · unfold binPMF
        split_ifs with hcase2
        · have hbin := BinomialPmfMaxBound n hn_one k.toNat
          -- hbin: C(n,k.toNat) * (2^n)⁻¹ ≤ √(2/(π·n))
          -- Want: C(n,k.toNat) * (1/2)^k.toNat * (1-1/2)^(n-k.toNat) ≤ √(2/(π·n))
          have hpow : ((1 : ℝ) / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)
              = (2 ^ n : ℝ)⁻¹ := by
            rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
            rw [show ((1 : ℝ) / 2) ^ k.toNat * (1 / 2) ^ (n - k.toNat)
                  = (1 / 2) ^ (k.toNat + (n - k.toNat)) by rw [← pow_add]]
            rw [Nat.add_sub_of_le hcase2]
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by ring]
            rw [inv_pow]
          have hrearr : (n.choose k.toNat : ℝ) * (1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)
              = (n.choose k.toNat : ℝ) * ((1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)) := by
            ring
          rw [hrearr, hpow]
          exact hbin
        · push_neg at hcase2
          obtain ⟨hk_nn, hk_le⟩ := hcase
          have : k.toNat ≤ n := by
            have hk_int : (k.toNat : ℤ) ≤ (n : ℤ) := by
              rw [Int.toNat_of_nonneg hk_nn]; exact hk_le
            exact_mod_cast hk_int
          omega
      · positivity
    have hα_eq : α = c' * Real.sqrt n := hαdef
    calc α * binPMFInt n (1/2) k
        ≤ α * Real.sqrt (2 / (Real.pi * n)) := by
          apply mul_le_mul_of_nonneg_left hbin_bound hα_nn
      _ = c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) := by rw [hα_eq]
      _ = c' * (Real.sqrt n * Real.sqrt (2 / (Real.pi * n))) := by ring
      _ = c' * Real.sqrt (n * (2 / (Real.pi * n))) := by
          rw [← Real.sqrt_mul (le_of_lt hn_pos)]
      _ = c' * Real.sqrt (2 / Real.pi) := by
          congr 2
          field_simp
  -- Now we need c' · √(2/π) ≤ 1.
  have hsqrt2pi_lower : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  have hexp1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have hexp2_lower : 1 ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hdenom_pos : 0 < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hdenom_ge_one : 1 ≤ 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
    have h1 : (1 : ℝ) ≤ 4 := by norm_num
    have h2 : 1 ≤ Real.exp 2 := hexp2_lower
    have h3 : 1 ≤ Real.sqrt (2 * Real.pi) := hsqrt2pi_lower
    nlinarith [hexp2_pos, hsqrt2pi_pos]
  have hc'_lt_one : c' ≤ 1 := by
    rw [hc'def, div_le_one hdenom_pos]; exact hdenom_ge_one
  have hsqrt_2_div_pi_le_one : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_one hpi_pos]
    linarith [Real.pi_gt_three]
  have hsqrt_2_div_pi_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hc'_nn : 0 ≤ c' := le_of_lt hc'_pos
  have hS_er_le_one : ∀ (r : ℤ) (j : ℕ),
      α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) ≤ 1 := by
    intro r j
    calc α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
        ≤ c' * Real.sqrt (2 / Real.pi) := hα_binPMF_le r j
      _ ≤ 1 * 1 := by
          apply mul_le_mul hc'_lt_one hsqrt_2_div_pi_le_one hsqrt_2_div_pi_nn
          linarith
      _ = 1 := by ring
  -- Define S_er, μ.
  set S_er : ℤ → ℕ → ℝ := fun r j =>
        α * binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)) with hS_er_def
  have hS_er_nn' : ∀ (r : ℤ) (j : ℕ), 0 ≤ S_er r j := hS_er_nn
  have hS_er_le_one' : ∀ (r : ℤ) (j : ℕ), S_er r j ≤ 1 := hS_er_le_one
  set μ : ℤ → Finset ℕ → ℝ := fun r ℓ =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ ℓ then S_er r j else (1 - S_er r j)) with hμ_def
  have hμ_nn : ∀ (r : ℤ) (ℓ : Finset ℕ), 0 ≤ μ r ℓ := by
    intro r ℓ
    apply Finset.prod_nonneg
    intro j _
    by_cases hj : j ∈ ℓ
    · simp [hj]; exact hS_er_nn' r j
    · simp [hj]; linarith [hS_er_le_one' r j]
  -- Total mass.
  have htotal : ∀ (r : ℤ),
      ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset), μ r ℓ = 1 := by
    intro r
    have hprodadd : ∏ j ∈ Finset.Icc 1 (n / 2), (S_er r j + (1 - S_er r j))
        = ∑ t ∈ (Finset.Icc 1 (n / 2)).powerset,
            (∏ j ∈ t, S_er r j) * (∏ j ∈ Finset.Icc 1 (n / 2) \ t, (1 - S_er r j)) :=
      Finset.prod_add (S_er r) (fun j => 1 - S_er r j) (Finset.Icc 1 (n / 2))
    have hLHS : ∏ j ∈ Finset.Icc 1 (n / 2), (S_er r j + (1 - S_er r j)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      ring
    have hμ_eq : ∀ ℓ ∈ (Finset.Icc 1 (n / 2)).powerset,
        μ r ℓ = (∏ j ∈ ℓ, S_er r j) * (∏ j ∈ Finset.Icc 1 (n / 2) \ ℓ, (1 - S_er r j)) := by
      intro ℓ hℓ
      rw [Finset.mem_powerset] at hℓ
      simp only [hμ_def]
      rw [Finset.prod_ite (S_er r) (fun j => 1 - S_er r j)]
      congr 1
      · apply Finset.prod_congr _ (fun _ _ => rfl)
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨_, hxℓ⟩; exact hxℓ
        · intro hxℓ
          have hx_in : x ∈ Finset.Icc 1 (n / 2) := hℓ hxℓ
          rw [Finset.mem_Icc] at hx_in
          exact ⟨hx_in, hxℓ⟩
      · apply Finset.prod_congr _ (fun _ _ => rfl)
        ext x
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
    rw [hprodadd] at hLHS
    rw [show ∑ ℓ ∈ (Finset.Icc 1 (n / 2)).powerset, μ r ℓ
          = ∑ t ∈ (Finset.Icc 1 (n / 2)).powerset,
              (∏ j ∈ t, S_er r j) * (∏ j ∈ Finset.Icc 1 (n / 2) \ t, (1 - S_er r j)) from
            Finset.sum_congr rfl hμ_eq]
    exact hLHS
  -- Markov bound for each r.
  have hHr_bound : ∀ (r : ℤ),
      ((((Finset.Icc 1 (n / 2)).powerset).filter
          (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card : ℝ)
        ≤ Real.exp (Real.sqrt n / 2) := by
    intro r
    set Hr := (((Finset.Icc 1 (n / 2)).powerset).filter
        (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)) with hHr_def
    have hHr_sum_le : ∑ ℓ ∈ Hr, μ r ℓ ≤ ∑ ℓ ∈ (Finset.Icc 1 (n / 2)).powerset, μ r ℓ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intros ℓ _ _; exact hμ_nn r ℓ
    have hHr_sum_le_one : ∑ ℓ ∈ Hr, μ r ℓ ≤ 1 := by
      rw [← htotal r]; exact hHr_sum_le
    have hthresh : ∀ ℓ ∈ Hr, Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ := by
      intro ℓ hℓ
      simp only [hHr_def, Finset.mem_filter] at hℓ
      exact hℓ.2
    have hexp_pos : 0 < Real.exp (-(Real.sqrt n / 2)) := Real.exp_pos _
    have hcount : (Hr.card : ℝ) * Real.exp (-(Real.sqrt n / 2)) ≤ ∑ ℓ ∈ Hr, μ r ℓ := by
      rw [show (Hr.card : ℝ) * Real.exp (-(Real.sqrt n / 2))
            = ∑ _ℓ ∈ Hr, Real.exp (-(Real.sqrt n / 2)) from by
          rw [Finset.sum_const, nsmul_eq_mul]]
      exact Finset.sum_le_sum hthresh
    have hbound : (Hr.card : ℝ) * Real.exp (-(Real.sqrt n / 2)) ≤ 1 :=
      le_trans hcount hHr_sum_le_one
    have hcardbound : (Hr.card : ℝ) ≤ 1 / Real.exp (-(Real.sqrt n / 2)) := by
      rw [le_div_iff₀ hexp_pos]; exact hbound
    rw [show Real.exp (Real.sqrt n / 2) = 1 / Real.exp (-(Real.sqrt n / 2)) from by
        rw [one_div, ← Real.exp_neg]; congr 1; ring]
    exact hcardbound
  -- P_H
  set P_H : Finset (Finset ℕ) :=
        ((Finset.Icc 1 (n / 2)).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
            ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ) with hP_H_def
  set R := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4) with hR_def
  have hP_H_subset : ∀ ℓ ∈ P_H, ∃ r ∈ R, ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
      (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ) := by
    intro ℓ hℓ
    simp only [hP_H_def, Finset.mem_filter, Finset.mem_powerset] at hℓ
    obtain ⟨hℓ_sub, _, r, hr_in, hbound⟩ := hℓ
    refine ⟨r, hr_in, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hℓ_sub, hbound⟩
  have hP_H_in_biUnion : P_H ⊆ R.biUnion (fun r =>
      ((Finset.Icc 1 (n / 2)).powerset).filter
        (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)) := by
    intro ℓ hℓ
    simp only [Finset.mem_biUnion]
    exact hP_H_subset ℓ hℓ
  have hcard_PH_le : P_H.card ≤ ∑ r ∈ R,
      (((Finset.Icc 1 (n / 2)).powerset).filter
        (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card := by
    calc P_H.card ≤ (R.biUnion (fun r =>
          ((Finset.Icc 1 (n / 2)).powerset).filter
            (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ))).card :=
            Finset.card_le_card hP_H_in_biUnion
      _ ≤ ∑ r ∈ R,
            (((Finset.Icc 1 (n / 2)).powerset).filter
              (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card :=
            Finset.card_biUnion_le
  have hcard_PH_le_real : (P_H.card : ℝ) ≤ ∑ r ∈ R, Real.exp (Real.sqrt n / 2) := by
    have hcast : (P_H.card : ℝ) ≤ ((∑ r ∈ R,
        (((Finset.Icc 1 (n / 2)).powerset).filter
          (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card : ℕ) : ℝ) := by
      exact_mod_cast hcard_PH_le
    have hsum_eq : ((∑ r ∈ R,
        (((Finset.Icc 1 (n / 2)).powerset).filter
          (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card : ℕ) : ℝ)
        = ∑ r ∈ R, ((((Finset.Icc 1 (n / 2)).powerset).filter
          (fun ℓ => Real.exp (-(Real.sqrt n / 2)) ≤ μ r ℓ)).card : ℝ) := by
      push_cast; rfl
    rw [hsum_eq] at hcast
    refine hcast.trans ?_
    apply Finset.sum_le_sum
    intro r _
    exact hHr_bound r
  have hsum_const : ∑ r ∈ R, Real.exp (Real.sqrt n / 2) =
      (R.card : ℝ) * Real.exp (Real.sqrt n / 2) := by
    rw [Finset.sum_const]; ring
  rw [hsum_const] at hcard_PH_le_real
  -- R.card ≤ n. R = Icc (-(n/4)) (n/4) so R.card = (2*(n/4) + 1).toNat ≤ n.
  have hR_card : (R.card : ℝ) ≤ (n : ℝ) := by
    rw [hR_def, Int.card_Icc]
    -- Goal: ((↑n / 4 + 1 - -(↑n / 4)).toNat : ℝ) ≤ ↑n
    have hn_ge : (4 : ℤ) ≤ (n : ℤ) := by
      have : (4 : ℕ) ≤ n := by
        have : (4 : ℕ) ≤ 10 ^ 12 := by norm_num
        exact this.trans hn
      exact_mod_cast this
    -- Use omega via Int arithmetic
    have hbound : 2 * ((n : ℤ) / 4) + 1 ≤ (n : ℤ) := by omega
    have hpos : (0 : ℤ) ≤ (n : ℤ) / 4 + 1 - -((n : ℤ) / 4) := by omega
    have hsimplify : ((n : ℤ) / 4 + 1 - -((n : ℤ) / 4)).toNat ≤ n := by
      have h1 : ((n : ℤ) / 4 + 1 - -((n : ℤ) / 4)).toNat = (2 * ((n : ℤ) / 4) + 1).toNat := by
        congr 1; ring
      rw [h1]
      have h2 : (2 * ((n : ℤ) / 4) + 1).toNat ≤ ((n : ℤ)).toNat := by
        apply Int.toNat_le_toNat hbound
      have h3 : ((n : ℤ)).toNat = n := Int.toNat_natCast n
      omega
    exact_mod_cast hsimplify
  have hexp_sqrt_pos : 0 ≤ Real.exp (Real.sqrt n / 2) := le_of_lt (Real.exp_pos _)
  calc (P_H.card : ℝ) ≤ (R.card : ℝ) * Real.exp (Real.sqrt n / 2) := hcard_PH_le_real
    _ ≤ (n : ℝ) * Real.exp (Real.sqrt n / 2) := by
        apply mul_le_mul_of_nonneg_right hR_card hexp_sqrt_pos
