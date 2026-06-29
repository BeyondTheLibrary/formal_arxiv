import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.ParitySwapOddThree

open Workspace.Types.BinVec
open Workspace.Types.AlternatingSumExpression

/-! Helper lemma: α * b_i ≤ 1/2 for all i (using BinomialPmfMaxBound). -/
private lemma alpha_b_le_half_M (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (i : ℕ) :
    (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
        ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1 / 2 := by
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  have hn_ge_one : (1 : ℕ) ≤ n := hn_pos
  have hbm := BinomialPmfMaxBound n hn_ge_one i
  set bi : ℝ := (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹ with hbi_def
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα_def
  have hbi_nonneg : 0 ≤ bi := by rw [hbi_def]; positivity
  have h_e_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h_sqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_2pi_pos
  have h_alpha_nonneg : 0 ≤ α := by rw [hα_def]; positivity
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hπn_pos : 0 < Real.pi * n := by positivity
  have hα_bi_le : α * bi ≤ α * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hbm h_alpha_nonneg
  have hsqrt_n : Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = Real.sqrt (2 / Real.pi) := by
    rw [← Real.sqrt_mul (by exact_mod_cast hn_pos.le : (0 : ℝ) ≤ n)]
    congr 1
    field_simp
  have hkey : Real.pi * Real.sqrt (2 / Real.pi) = Real.sqrt (2 * Real.pi) := by
    rw [show (2 * Real.pi) = Real.pi^2 * (2 / Real.pi) by field_simp]
    rw [Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq hπ_pos.le]
  have h_simplify : α * Real.sqrt (2 / (Real.pi * n)) = 1 / (4 * Real.exp 2 * Real.pi) := by
    rw [hα_def]
    rw [show (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
                * Real.sqrt (2 / (Real.pi * n)) =
              (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)))
                * (Real.sqrt n * Real.sqrt (2 / (Real.pi * n))) from by ring]
    rw [hsqrt_n]
    rw [div_mul_eq_mul_div, one_mul]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hkey, h_alpha_nonneg, Real.sqrt_nonneg (2/Real.pi)]
  rw [h_simplify] at hα_bi_le
  have h_e2_ge : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hπ_ge : 3 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hgoal2 : 1 / (4 * Real.exp 2 * Real.pi) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [h_e2_ge, hπ_ge]
  linarith

theorem MiddleWeightExplicit :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 2 = 1 →
      ∀ (Se So : Workspace.Types.ProbVec.ProbVec n),
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∀ i : Fin n, So.p i =
          (if (i.val) % 2 = 1
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        ∀ (m : BinVec (n / 2)) (r : ℤ),
          0 ≤ r + (n / 4 : ℤ) → r + (n / 4 : ℤ) + (n / 2 : ℤ) ≤ (n : ℤ) →
          -- index map from Fin (n/2) into Fin n
          ∀ (idx : Fin (n / 2) → Fin n),
            (∀ j : Fin (n / 2),
                (idx j).val = ((n / 4 : ℤ) + r + (j : ℕ)).toNat) →
          let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                       Real.sqrt n
          let b : ℕ → ℝ := fun i => (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹
          let cM_e : ℝ :=
            ∏ j : Fin (n / 2),
              (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
          let cM_o : ℝ :=
            ∏ j : Fin (n / 2),
              (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
          let ell : Finset (Fin (n / 2)) :=
            (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
          let parity : Fin (n / 2) → ℤ :=
            fun j => ((n / 4 : ℤ) + r + (j : ℕ)) % 2
          let Q_e : ℝ :=
            ∏ j ∈ (Finset.univ : Finset (Fin (n / 2))).filter
                     (fun j => parity j = 0),
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let Q_o : ℝ :=
            ∏ j ∈ (Finset.univ : Finset (Fin (n / 2))).filter
                     (fun j => parity j = 1),
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let ellProd : ℝ :=
            ∏ j ∈ ell,
              (α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat) /
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let mixedParity : Prop :=
            ∃ j₁ ∈ ell, ∃ j₂ ∈ ell, parity j₁ ≠ parity j₂
          (((1 : ℝ) / 2) ^ (n / 2) ≤ Q_e ∧ Q_e ≤ 1) ∧
          (((1 : ℝ) / 2) ^ (n / 2) ≤ Q_o ∧ Q_o ≤ 1) ∧
          (mixedParity → cM_e = 0 ∧ cM_o = 0) ∧
          (ell = ∅ → cM_e = Q_e ∧ cM_o = Q_o) ∧
          (∀ p ∈ ({0, 1} : Finset ℤ),
              ell.Nonempty →
              (∀ j ∈ ell, parity j = p) →
              ((p = 1 → cM_e = 0) ∧
               (p = 0 → cM_e = Q_e * ellProd)) ∧
              ((p = 0 → cM_o = 0) ∧
               (p = 1 → cM_o = Q_o * ellProd))) := by
  intro n hn hmod Se So hSe hSo m r hr1 hr2 idx hidx
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h4 | h4
  case inr =>
    exact ParitySwapOddThree.MiddleWeightExplicit_oddThree n hn h4 Se So hSe hSo m r hr1 hr2 idx hidx
  intro α b cM_e cM_o ell parity Q_e Q_o ellProd mixedParity
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  have hidx_nonneg : ∀ j : Fin (n/2), 0 ≤ (n/4 : ℤ) + r + (j : ℕ) := by
    intro j
    have h1 : (0 : ℤ) ≤ (j : ℕ) := by positivity
    linarith
  have hidx_eq : ∀ j : Fin (n/2),
      ((n/4 : ℤ) + r + (j : ℕ)) = ((idx j).val : ℤ) := by
    intro j
    rw [hidx j]
    exact (Int.toNat_of_nonneg (hidx_nonneg j)).symm
  have hidx_toNat : ∀ j : Fin (n/2),
      ((n/4 : ℤ) + r + (j : ℕ)).toNat = (idx j).val := by
    intro j; exact (hidx j).symm
  have hSe_idx : ∀ j : Fin (n/2),
      Se.p (idx j) = if ((idx j).val) % 2 = 0
                     then α * b (idx j).val
                     else 0 := by
    intro j; rw [hSe (idx j)]
  have hSo_idx : ∀ j : Fin (n/2),
      So.p (idx j) = if ((idx j).val) % 2 = 1
                     then α * b (idx j).val
                     else 0 := by
    intro j; rw [hSo (idx j)]
  have hαb_le_half : ∀ j : Fin (n/2), α * b (idx j).val ≤ 1/2 := by
    intro j
    show (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
         ((Nat.choose n (idx j).val : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1/2
    exact alpha_b_le_half_M n hn (idx j).val
  have hαb_nonneg : ∀ j : Fin (n/2), 0 ≤ α * b (idx j).val := by
    intro j
    show 0 ≤ (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
            ((Nat.choose n (idx j).val : ℝ) * (2 ^ n : ℝ)⁻¹)
    have h1 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have h2 : 0 ≤ (Nat.choose n (idx j).val : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    have hπ_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have h_factor_form : ∀ j : Fin (n/2),
      (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) = 1 - α * b (idx j).val := by
    intro j; rw [hidx_toNat j]
  have h_factor_lb : ∀ j : Fin (n/2),
      (1 : ℝ)/2 ≤ 1 - α * b (idx j).val := by
    intro j; linarith [hαb_le_half j]
  have h_factor_ub : ∀ j : Fin (n/2),
      1 - α * b (idx j).val ≤ 1 := by
    intro j; linarith [hαb_nonneg j]
  have h_factor_nonneg : ∀ j : Fin (n/2),
      (0 : ℝ) ≤ 1 - α * b (idx j).val := by
    intro j; linarith [h_factor_lb j]
  have h_factor_pos : ∀ j : Fin (n/2),
      (0 : ℝ) < 1 - α * b (idx j).val := by
    intro j; linarith [h_factor_lb j]
  have h_factor_ne_zero : ∀ j : Fin (n/2),
      (1 - α * b (idx j).val) ≠ 0 := by
    intro j; linarith [h_factor_pos j]
  have hQ_bound : ∀ (S : Finset (Fin (n/2))),
      ((1 : ℝ)/2) ^ S.card ≤
      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1 := by
    intro S
    refine ⟨?_, ?_⟩
    · have hprod_ge : ∏ j ∈ S, ((1:ℝ)/2) ≤
                      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) := by
        apply Finset.prod_le_prod
        · intros; norm_num
        · intro j _; rw [h_factor_form j]; exact h_factor_lb j
      simpa [Finset.prod_const] using hprod_ge
    · apply Finset.prod_le_one
      · intro j _; rw [h_factor_form j]; exact h_factor_nonneg j
      · intro j _; rw [h_factor_form j]; exact h_factor_ub j
  have hcard_filter_e : (Finset.univ.filter
        (fun j : Fin (n/2) => parity j = 0)).card ≤ n / 2 := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  have hcard_filter_o : (Finset.univ.filter
        (fun j : Fin (n/2) => parity j = 1)).card ≤ n / 2 := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  have hpow_le_half : ∀ k : ℕ, k ≤ n / 2 → ((1:ℝ)/2)^(n/2) ≤ ((1:ℝ)/2)^k := by
    intro k hk
    apply pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
                                (by norm_num : (1:ℝ)/2 ≤ 1) hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((1:ℝ)/2)^(n/2) ≤ Q_e ∧ Q_e ≤ 1
    show ((1:ℝ)/2)^(n/2) ≤ ∏ j ∈ Finset.univ.filter (fun j => parity j = 0),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
         ∏ j ∈ Finset.univ.filter (fun j => parity j = 0),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1
    obtain ⟨hlow, hup⟩ := hQ_bound (Finset.univ.filter (fun j => parity j = 0))
    refine ⟨le_trans (hpow_le_half _ hcard_filter_e) hlow, hup⟩
  · show ((1:ℝ)/2)^(n/2) ≤ Q_o ∧ Q_o ≤ 1
    show ((1:ℝ)/2)^(n/2) ≤ ∏ j ∈ Finset.univ.filter (fun j => parity j = 1),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
         ∏ j ∈ Finset.univ.filter (fun j => parity j = 1),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1
    obtain ⟨hlow, hup⟩ := hQ_bound (Finset.univ.filter (fun j => parity j = 1))
    refine ⟨le_trans (hpow_le_half _ hcard_filter_o) hlow, hup⟩
  · show mixedParity → cM_e = 0 ∧ cM_o = 0
    intro hmixed
    obtain ⟨j₁, hj₁_ell, j₂, hj₂_ell, hpar_diff⟩ := hmixed
    have hbit_j1 : m.bit j₁ = true := by
      have : j₁ ∈ ell := hj₁_ell
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hbit_j2 : m.bit j₂ = true := by
      have : j₂ ∈ ell := hj₂_ell
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hpar_j1 : ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 = 0 ∨
                   ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 = 1 := by omega
    have hpar_j2 : ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 = 0 ∨
                   ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 = 1 := by omega
    have hparity_j1 : parity j₁ = ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 := rfl
    have hparity_j2 : parity j₂ = ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 := rfl
    rw [hparity_j1, hparity_j2] at hpar_diff
    rcases hpar_j1 with hp1 | hp1 <;> rcases hpar_j2 with hp2 | hp2
    · exact absurd (hp1.trans hp2.symm) hpar_diff
    · have hidx_j1_par : (idx j₁).val % 2 = 0 := by have := hidx_eq j₁; omega
      have hidx_j2_par : (idx j₂).val % 2 = 1 := by have := hidx_eq j₂; omega
      refine ⟨?_, ?_⟩
      · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₂)
        rw [if_pos hbit_j2, hSe_idx j₂]
        rw [if_neg (by omega : ¬ ((idx j₂).val % 2 = 0))]
      · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₁)
        rw [if_pos hbit_j1, hSo_idx j₁]
        rw [if_neg (by omega : ¬ ((idx j₁).val % 2 = 1))]
    · have hidx_j1_par : (idx j₁).val % 2 = 1 := by have := hidx_eq j₁; omega
      have hidx_j2_par : (idx j₂).val % 2 = 0 := by have := hidx_eq j₂; omega
      refine ⟨?_, ?_⟩
      · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₁)
        rw [if_pos hbit_j1, hSe_idx j₁]
        rw [if_neg (by omega : ¬ ((idx j₁).val % 2 = 0))]
      · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₂)
        rw [if_pos hbit_j2, hSo_idx j₂]
        rw [if_neg (by omega : ¬ ((idx j₂).val % 2 = 1))]
    · exact absurd (hp1.trans hp2.symm) hpar_diff
  · show ell = ∅ → cM_e = Q_e ∧ cM_o = Q_o
    intro hell_empty
    have hbits_false : ∀ j : Fin (n/2), m.bit j = false := by
      intro j
      by_contra h
      have hj_in : j ∈ ell := by
        simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hb : m.bit j
        · simp [hb] at h
        · rfl
      rw [hell_empty] at hj_in
      exact (Finset.notMem_empty j) hj_in
    refine ⟨?_, ?_⟩
    · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
         = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 0),
              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)))
                = ∏ j : Fin (n/2), (1 - Se.p (idx j))
            from Finset.prod_congr rfl (fun j _ => by rw [if_neg (by rw [hbits_false j]; simp)])]
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (1 - Se.p (idx j)))
                = ∏ j : Fin (n/2),
                    if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1
            from Finset.prod_congr rfl (fun j _ => by
              rw [hSe_idx j]
              by_cases hpar : (idx j).val % 2 = 0
              · rw [if_pos hpar, if_pos hpar]
              · rw [if_neg hpar, if_neg hpar]; ring)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => (idx j).val % 2 = 0)]
      have heven : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                      if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                      (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_pos hj]
      have hodd : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ (idx j).val % 2 = 0),
                      if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [heven, hodd, mul_one]
      apply Finset.prod_congr ?_ ?_
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; show parity j = 0
          have := hidx_eq j
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0
          omega
        · intro h
          show (idx j).val % 2 = 0
          have hpj : ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0 := h
          have := hidx_eq j
          omega
      · intro j hj
        rw [h_factor_form j]
    · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
         = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 1),
              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)))
                = ∏ j : Fin (n/2), (1 - So.p (idx j))
            from Finset.prod_congr rfl (fun j _ => by rw [if_neg (by rw [hbits_false j]; simp)])]
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (1 - So.p (idx j)))
                = ∏ j : Fin (n/2),
                    if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1
            from Finset.prod_congr rfl (fun j _ => by
              rw [hSo_idx j]
              by_cases hpar : (idx j).val % 2 = 1
              · rw [if_pos hpar, if_pos hpar]
              · rw [if_neg hpar, if_neg hpar]; ring)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => (idx j).val % 2 = 1)]
      have hodd_part : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_pos hj]
      have heven_part : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ (idx j).val % 2 = 1),
                          if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                    = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hodd_part, heven_part, mul_one]
      apply Finset.prod_congr ?_ ?_
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; show parity j = 1
          have := hidx_eq j
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1
          omega
        · intro h
          show (idx j).val % 2 = 1
          have hpj : ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1 := h
          have := hidx_eq j
          omega
      · intro j hj
        rw [h_factor_form j]
  · -- (4) Same-parity case (corrected statement, p-only conditions).
    intro p hp_mem hell_ne hpar_all
    have hp_cases : p = 0 ∨ p = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      exact hp_mem
    have hidx_par_of_ell : ∀ j ∈ ell, ((idx j).val : ℤ) % 2 = p := by
      intro j hj
      have hpj : parity j = p := hpar_all j hj
      have hp1 : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
      rw [hp1] at hpj
      have := hidx_eq j
      omega
    have hbit_of_ell : ∀ j ∈ ell, m.bit j = true := by
      intro j hj
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · -- p = 1 → cM_e = 0
      intro hp1
      -- pick j₀ ∈ ell, parity j₀ = 1, so (idx j₀).val % 2 = 1, Se.p (idx j₀) = 0
      obtain ⟨j₀, hj₀⟩ := hell_ne
      have hbit_j0 : m.bit j₀ = true := hbit_of_ell j₀ hj₀
      have hidxj0 := hidx_par_of_ell j₀ hj₀
      rw [hp1] at hidxj0
      have hidx_par1 : (idx j₀).val % 2 = 1 := by
        have h1 : ((idx j₀).val : ℤ) % 2 = 1 := hidxj0
        omega
      show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j₀)
      rw [if_pos hbit_j0, hSe_idx j₀]
      rw [if_neg (by omega : ¬ ((idx j₀).val % 2 = 0))]
    · -- p = 0 → cM_e = Q_e * ellProd
      intro hp0
      have hidx_par_ell : ∀ j ∈ ell, (idx j).val % 2 = 0 := by
        intro j hj
        have h1 := hidx_par_of_ell j hj
        rw [hp0] at h1
        omega
      have h_parity_eq_idx : ∀ j : Fin (n/2),
          parity j = 0 ↔ (idx j).val % 2 = 0 := by
        intro j
        have := hidx_eq j
        constructor
        · intro h
          show (idx j).val % 2 = 0
          have hp1 : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
          rw [hp1] at h
          omega
        · intro h
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0
          omega
      have hQe_filter_eq :
          (Finset.univ.filter (fun j : Fin (n/2) => parity j = 0)) =
          (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_parity_eq_idx j
      show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
         = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 0),
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)) *
           (∏ j ∈ ell,
                (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat))
      rw [hQe_filter_eq]
      have hQe_simp : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                        (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                        (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _; rw [h_factor_form j]
      rw [hQe_simp]
      have hellProd_simp : ∏ j ∈ ell,
                              (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                        = ∏ j ∈ ell,
                              (α * b (idx j).val) / (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _
        rw [hidx_toNat j]
      rw [hellProd_simp]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => m.bit j = true)]
      have hell_filter : (Finset.univ.filter (fun j : Fin (n/2) => m.bit j = true)) = ell := rfl
      rw [hell_filter]
      have hLHS_ell : ∏ j ∈ ell,
                        (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
                    = ∏ j ∈ ell, Se.p (idx j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_pos (hbit_of_ell j hj)]
      rw [hLHS_ell]
      have hLHS_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
                        = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (1 - Se.p (idx j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hLHS_notell]
      have hSe_ell : ∏ j ∈ ell, Se.p (idx j)
                    = ∏ j ∈ ell, α * b (idx j).val := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hSe_idx j, if_pos (hidx_par_ell j hj)]
      rw [hSe_ell]
      have hSe_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (1 - Se.p (idx j))
                      = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [hSe_idx j]
        by_cases hpar : (idx j).val % 2 = 0
        · rw [if_pos hpar, if_pos hpar]
        · rw [if_neg hpar, if_neg hpar]; ring
      rw [hSe_notell]
      have hQe_split : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                          (1 - α * b (idx j).val)
                      = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                        (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                            ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
                          (1 - α * b (idx j).val)) := by
        rw [show ell = Finset.univ.filter (fun j : Fin (n/2) =>
                m.bit j = true ∧ (idx j).val % 2 = 0) from by
              ext j
              simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; refine ⟨h, ?_⟩
                exact hidx_par_ell j (by simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
              · intro ⟨h1, _⟩; exact h1]
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0))
              (fun j => m.bit j = true)]
        congr 1
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
      rw [hQe_split]
      have hLHS_notell_split :
          ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
            (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
          = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
              ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
            (1 - α * b (idx j).val)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true))
              (fun j => (idx j).val % 2 = 0)]
        have h1 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => (idx j).val % 2 = 0),
                    (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                        ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
                    (1 - α * b (idx j).val) := by
          rw [show (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                    (fun j : Fin (n/2) => (idx j).val % 2 = 0)
              = Finset.univ.filter (fun j : Fin (n/2) =>
                    ¬ m.bit j = true ∧ (idx j).val % 2 = 0) from by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
          apply Finset.prod_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_pos hj.2]
        have h2 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => ¬ (idx j).val % 2 = 0),
                    (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_neg hj.2]
        rw [h1, h2, mul_one]
      rw [hLHS_notell_split]
      have hProd_combine : (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                           (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val))
                         = ∏ j ∈ ell, α * b (idx j).val := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        field_simp [h_factor_ne_zero j]
      calc (∏ j ∈ ell, α * b (idx j).val) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val)
          = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
            (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val) := by
            rw [hProd_combine]
        _ = ((∏ j ∈ ell, (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val)) *
            ∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val) := by ring
    · -- p = 0 → cM_o = 0
      intro hp0
      -- pick j₀ ∈ ell, parity j₀ = 0, so (idx j₀).val % 2 = 0, So.p (idx j₀) = 0
      obtain ⟨j₀, hj₀⟩ := hell_ne
      have hbit_j0 : m.bit j₀ = true := hbit_of_ell j₀ hj₀
      have hidxj0 := hidx_par_of_ell j₀ hj₀
      rw [hp0] at hidxj0
      have hidx_par0 : (idx j₀).val % 2 = 0 := by
        have h1 : ((idx j₀).val : ℤ) % 2 = 0 := hidxj0
        omega
      show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j₀)
      rw [if_pos hbit_j0, hSo_idx j₀]
      rw [if_neg (by omega : ¬ ((idx j₀).val % 2 = 1))]
    · -- p = 1 → cM_o = Q_o * ellProd
      intro hp1
      have hidx_par_ell : ∀ j ∈ ell, (idx j).val % 2 = 1 := by
        intro j hj
        have h1 := hidx_par_of_ell j hj
        rw [hp1] at h1
        omega
      have h_parity_eq_idx : ∀ j : Fin (n/2),
          parity j = 1 ↔ (idx j).val % 2 = 1 := by
        intro j
        have := hidx_eq j
        constructor
        · intro h
          show (idx j).val % 2 = 1
          have hp_def : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
          rw [hp_def] at h
          omega
        · intro h
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1
          omega
      have hQo_filter_eq :
          (Finset.univ.filter (fun j : Fin (n/2) => parity j = 1)) =
          (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_parity_eq_idx j
      show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
         = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 1),
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)) *
           (∏ j ∈ ell,
                (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat))
      rw [hQo_filter_eq]
      have hQo_simp : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                        (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                        (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _; rw [h_factor_form j]
      rw [hQo_simp]
      have hellProd_simp : ∏ j ∈ ell,
                              (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                        = ∏ j ∈ ell,
                              (α * b (idx j).val) / (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _
        rw [hidx_toNat j]
      rw [hellProd_simp]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => m.bit j = true)]
      have hell_filter : (Finset.univ.filter (fun j : Fin (n/2) => m.bit j = true)) = ell := rfl
      rw [hell_filter]
      have hLHS_ell : ∏ j ∈ ell,
                        (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
                    = ∏ j ∈ ell, So.p (idx j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_pos (hbit_of_ell j hj)]
      rw [hLHS_ell]
      have hLHS_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
                        = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (1 - So.p (idx j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hLHS_notell]
      have hSo_ell : ∏ j ∈ ell, So.p (idx j)
                    = ∏ j ∈ ell, α * b (idx j).val := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hSo_idx j, if_pos (hidx_par_ell j hj)]
      rw [hSo_ell]
      have hSo_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (1 - So.p (idx j))
                      = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [hSo_idx j]
        by_cases hpar : (idx j).val % 2 = 1
        · rw [if_pos hpar, if_pos hpar]
        · rw [if_neg hpar, if_neg hpar]; ring
      rw [hSo_notell]
      have hQo_split : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val)
                      = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                        (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                            ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val)) := by
        rw [show ell = Finset.univ.filter (fun j : Fin (n/2) =>
                m.bit j = true ∧ (idx j).val % 2 = 1) from by
              ext j
              simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; refine ⟨h, ?_⟩
                exact hidx_par_ell j (by simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
              · intro ⟨h1, _⟩; exact h1]
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1))
              (fun j => m.bit j = true)]
        congr 1
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
      rw [hQo_split]
      have hLHS_notell_split :
          ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
            (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
          = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
              ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
            (1 - α * b (idx j).val)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true))
              (fun j => (idx j).val % 2 = 1)]
        have h1 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => (idx j).val % 2 = 1),
                    (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                        ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
                    (1 - α * b (idx j).val) := by
          rw [show (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                    (fun j : Fin (n/2) => (idx j).val % 2 = 1)
              = Finset.univ.filter (fun j : Fin (n/2) =>
                    ¬ m.bit j = true ∧ (idx j).val % 2 = 1) from by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
          apply Finset.prod_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_pos hj.2]
        have h2 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => ¬ (idx j).val % 2 = 1),
                    (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_neg hj.2]
        rw [h1, h2, mul_one]
      rw [hLHS_notell_split]
      have hProd_combine : (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                           (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val))
                         = ∏ j ∈ ell, α * b (idx j).val := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        field_simp [h_factor_ne_zero j]
      calc (∏ j ∈ ell, α * b (idx j).val) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val)
          = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
            (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val) := by
            rw [hProd_combine]
        _ = ((∏ j ∈ ell, (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val)) *
            ∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val) := by ring
