import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.BinomialPmfMaxBound

set_option maxHeartbeats 8000000

open Workspace.Types.AlternatingSumExpression

namespace T4L1NormBoundAux

/-- `binPMFInt n (1/2) k ≥ 0` always. -/
lemma binPMFInt_nonneg (n : ℕ) (k : ℤ) : 0 ≤ binPMFInt n (1 / 2 : ℝ) k := by
  unfold binPMFInt
  split_ifs with h
  · unfold binPMF
    split_ifs with hkn
    · apply mul_nonneg
      · apply mul_nonneg
        · exact Nat.cast_nonneg _
        · exact pow_nonneg (by norm_num) _
      · exact pow_nonneg (by norm_num) _
    · exact le_refl 0
  · exact le_refl 0

/-- When out of support, `binPMFInt` is `0`. -/
lemma binPMFInt_zero_of_out (n : ℕ) (k : ℤ) (h : ¬ (0 ≤ k ∧ k ≤ (n : ℤ))) :
    binPMFInt n (1 / 2 : ℝ) k = 0 := by
  unfold binPMFInt
  rw [if_neg h]

/-- The standard form: `binPMFInt n (1/2) k ≤ √(2/(π n))` for n ≥ 1. -/
lemma binPMFInt_le_max (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    binPMFInt n (1 / 2 : ℝ) k ≤ Real.sqrt (2 / (Real.pi * n)) := by
  unfold binPMFInt
  split_ifs with h
  · unfold binPMF
    split_ifs with hkn
    · -- in support: apply BinomialPmfMaxBound
      have key := BinomialPmfMaxBound n hn k.toNat
      -- key: (Nat.choose n k.toNat : ℝ) * (2 ^ n)⁻¹ ≤ √(2/(π n))
      have h1 : (1 / 2 : ℝ) ^ k.toNat * (1 - 1 / 2 : ℝ) ^ (n - k.toNat) =
                (2 ^ n : ℝ)⁻¹ := by
        have hh : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
        rw [hh, ← pow_add]
        have h_sum : k.toNat + (n - k.toNat) = n := by omega
        rw [h_sum]
        rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num]
        rw [inv_pow]
      calc (Nat.choose n k.toNat : ℝ) * (1 / 2 : ℝ) ^ k.toNat *
              (1 - 1 / 2 : ℝ) ^ (n - k.toNat)
          = (Nat.choose n k.toNat : ℝ) * ((1 / 2 : ℝ) ^ k.toNat *
                (1 - 1 / 2 : ℝ) ^ (n - k.toNat)) := by ring
        _ = (Nat.choose n k.toNat : ℝ) * (2 ^ n : ℝ)⁻¹ := by rw [h1]
        _ ≤ Real.sqrt (2 / (Real.pi * n)) := key
    · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

/-- The key `α · X ≤ 1/(4 π e²)` bound. -/
lemma alpha_X_le (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    α * binPMFInt n (1 / 2 : ℝ) k ≤ 1 / (4 * Real.pi * Real.exp 2) := by
  intro α
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos 2
  have hα_nn : 0 ≤ α := by
    simp only [α]
    apply mul_nonneg
    · apply div_nonneg one_pos.le
      positivity
    · exact Real.sqrt_nonneg _
  have hbin_nn := binPMFInt_nonneg n k
  have hbin_le := binPMFInt_le_max n hn k
  have step1 : α * binPMFInt n (1 / 2 : ℝ) k ≤ α * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hbin_le hα_nn
  have step2 : α * Real.sqrt (2 / (Real.pi * n)) = 1 / (4 * Real.pi * Real.exp 2) := by
    simp only [α]
    have hn_nn : (0 : ℝ) ≤ n := le_of_lt hn_pos
    have h2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt h2pi_pos
    have h_combine : Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * n)) =
                     Real.sqrt (2 / Real.pi) := by
      rw [← Real.sqrt_mul hn_nn]
      congr 1
      field_simp
    have h_rearr : (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                    Real.sqrt (2 / (Real.pi * n)) =
                   (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                    (Real.sqrt n * Real.sqrt (2 / (Real.pi * n))) := by ring
    rw [h_rearr, h_combine]
    have hsqrt_2_div_pi_pos : 0 < Real.sqrt (2 / Real.pi) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hexp2_ne : Real.exp 2 ≠ 0 := ne_of_gt hexp_pos
    have h_sqrt_2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
    -- Use the fact: √(2/π) · √(2π) = √(4) = 2
    have h_prod : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      have hh1 : (2 / Real.pi) * (2 * Real.pi) = 4 := by
        field_simp
        ring
      rw [hh1]
      have hh2 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
      exact hh2
    -- So √(2/π) = 2 / √(2π)
    have h_eq_form : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) := by
      rw [eq_div_iff h_sqrt_2pi_ne]
      exact h_prod
    rw [h_eq_form]
    have h_sqrt_sq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    linarith [h_sqrt_sq]
  linarith

/-- Numerical bound: 1/(4πe²) < 1/2. -/
lemma one_over_4pi_e2_lt_half : (1 / (4 * Real.pi * Real.exp 2) : ℝ) < 1 / 2 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have h_denom_pos : (0 : ℝ) < 4 * Real.pi * Real.exp 2 := by positivity
  have hpi_gt : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hexp_gt_1 : (1 : ℝ) < Real.exp 2 := by
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    have := Real.add_one_lt_exp h2_ne
    linarith
  -- 4 · π · e² > 4 · 3 · 1 = 12 > 2
  have h_denom_gt : (2 : ℝ) < 4 * Real.pi * Real.exp 2 := by nlinarith
  exact one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 2) h_denom_gt

/-- Each ellFactor ∈ [0, 1] when summing nonneg over a support. -/
lemma ellFactor_in_unit_interval (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (j : ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    0 ≤ ellFactor n α r j ∧ ellFactor n α r j ≤ 1 := by
  intro α
  unfold ellFactor
  have hbin_nn := binPMFInt_nonneg n (r + (n / 4 : ℤ) + (j : ℤ))
  have hα_nn : 0 ≤ α := by
    simp only [α]
    apply mul_nonneg
    · apply div_nonneg one_pos.le
      positivity
    · exact Real.sqrt_nonneg _
  have hαX_nn : 0 ≤ α * binPMFInt n (1 / 2 : ℝ) (r + (n / 4 : ℤ) + (j : ℤ)) :=
    mul_nonneg hα_nn hbin_nn
  have hαX_le : α * binPMFInt n (1 / 2 : ℝ) (r + (n / 4 : ℤ) + (j : ℤ)) ≤
                1 / (4 * Real.pi * Real.exp 2) := alpha_X_le n hn _
  have h_lt_half : 1 / (4 * Real.pi * Real.exp 2) < (1 / 2 : ℝ) :=
    one_over_4pi_e2_lt_half
  have hαX_lt_half : α * binPMFInt n (1 / 2 : ℝ) (r + (n / 4 : ℤ) + (j : ℤ)) < (1 / 2 : ℝ) :=
    lt_of_le_of_lt hαX_le h_lt_half
  have h_one_minus_pos : 0 < 1 - α * binPMFInt n (1 / 2 : ℝ) (r + (n / 4 : ℤ) + (j : ℤ)) := by
    linarith
  refine ⟨?_, ?_⟩
  · exact div_nonneg hαX_nn h_one_minus_pos.le
  · rw [div_le_one h_one_minus_pos]
    linarith

/-- Product of ellFactors is in [0, 1]. -/
lemma prod_ellFactor_in_unit_interval (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (ℓ : Finset ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    0 ≤ ∏ j ∈ ℓ, ellFactor n α r j ∧ ∏ j ∈ ℓ, ellFactor n α r j ≤ 1 := by
  intro α
  refine ⟨?_, ?_⟩
  · apply Finset.prod_nonneg
    intro j _
    exact (ellFactor_in_unit_interval n hn r j).1
  · apply Finset.prod_le_one
    · intro j _
      exact (ellFactor_in_unit_interval n hn r j).1
    · intro j _
      exact (ellFactor_in_unit_interval n hn r j).2

/-- Support of ellFactor: if `r + n/4 + j ∉ [0, n]`, then ellFactor = 0. -/
lemma ellFactor_zero_of_out_support (n : ℕ) (α : ℝ) (r : ℤ) (j : ℕ)
    (h : ¬ (0 ≤ r + (n / 4 : ℤ) + (j : ℤ) ∧ r + (n / 4 : ℤ) + (j : ℤ) ≤ (n : ℤ))) :
    ellFactor n α r j = 0 := by
  unfold ellFactor
  have hb : binPMFInt n (1 / 2 : ℝ) (r + (n / 4 : ℤ) + (j : ℤ)) = 0 :=
    binPMFInt_zero_of_out n _ h
  -- ellFactor = α · X / (1 - α · X). With X = 0, this is 0/1 = 0.
  show (let X : ℝ := binPMFInt n (1 / 2) (r + (n / 4 : ℤ) + (j : ℤ));
        α * X / (1 - α * X)) = 0
  rw [hb]
  simp

/-- Support of T₄: if `ℓ` is nonempty and there is some `j₀ ∈ ℓ` with
    `r + n/4 + j₀ ∉ [0, n]`, then T₄(r) = 0. -/
lemma T4_zero_of_out_support (n : ℕ) (α : ℝ) (r : ℤ) (ℓ : Finset ℕ)
    (j₀ : ℕ) (hj₀ : j₀ ∈ ℓ)
    (h : ¬ (0 ≤ r + (n / 4 : ℤ) + (j₀ : ℤ) ∧ r + (n / 4 : ℤ) + (j₀ : ℤ) ≤ (n : ℤ))) :
    ∏ j ∈ ℓ, ellFactor n α r j = 0 :=
  Finset.prod_eq_zero hj₀ (ellFactor_zero_of_out_support n α r j₀ h)

end T4L1NormBoundAux

theorem T4L1NormBound :
    ∀ (n : ℕ), (10 : ℕ) ^ 12 ≤ n → n % 8 = 1 →
    ∀ (ℓ : Finset ℕ), ℓ ⊆ Finset.Icc 1 (n / 2) → 1 ≤ ℓ.card →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let T4 : ℤ → ℝ := fun r => ∏ j ∈ ℓ, ellFactor n α r j
      (∀ r : ℤ, 0 ≤ T4 r ∧ T4 r ≤ 1) ∧
      (∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r ≤ (n : ℝ) + 1) ∧
      (∀ ξ : ℝ,
        |∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r * Real.cos (ξ * (r : ℝ))|
          ≤ (n : ℝ) + 1) := by
  intro n hn hmod ℓ hℓ hℓ_card α T4
  have hn_pos : 1 ≤ n := by
    have h1 : (10 : ℕ) ^ 12 ≤ n := hn
    have h_ge_1 : 1 ≤ (10 : ℕ) ^ 12 := by norm_num
    omega
  have hℓ_nonempty : ℓ.Nonempty := Finset.card_pos.mp hℓ_card
  obtain ⟨j₀, hj₀⟩ := hℓ_nonempty
  have hj₀_range : j₀ ∈ Finset.Icc 1 (n / 2) := hℓ hj₀
  have hj₀_lb : 1 ≤ j₀ := (Finset.mem_Icc.mp hj₀_range).1
  have hj₀_ub : j₀ ≤ n / 2 := (Finset.mem_Icc.mp hj₀_range).2
  -- Part 1
  have part1 : ∀ r : ℤ, 0 ≤ T4 r ∧ T4 r ≤ 1 := by
    intro r
    exact T4L1NormBoundAux.prod_ellFactor_in_unit_interval n hn_pos r ℓ
  -- Part 2: L¹ bound
  set S : Finset ℤ := Finset.Icc (-(n / 4 : ℤ) - j₀) ((n : ℤ) - (n / 4 : ℤ) - j₀) with hS_def
  have hS_card : S.card = n + 1 := by
    rw [hS_def, Int.card_Icc]
    -- ((n - n/4 - j₀) - (-(n/4) - j₀) + 1).toNat = n + 1
    -- n - n/4 - j₀ + n/4 + j₀ + 1 = n + 1
    have h_diff : ((n : ℤ) - (n / 4 : ℤ) - j₀ + 1) - (-(n / 4 : ℤ) - j₀) = (n : ℤ) + 1 := by
      ring
    rw [h_diff]
    -- Goal: ((n : ℤ) + 1).toNat = n + 1
    omega
  have hT4_zero_outside : ∀ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), r ∉ S → T4 r = 0 := by
    intro r _ hr_notS
    have h_not_supp : ¬ (0 ≤ r + (n / 4 : ℤ) + (j₀ : ℤ) ∧
                         r + (n / 4 : ℤ) + (j₀ : ℤ) ≤ (n : ℤ)) := by
      intro ⟨h1, h2⟩
      apply hr_notS
      rw [hS_def, Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    show ∏ j ∈ ℓ, ellFactor n α r j = 0
    exact T4L1NormBoundAux.T4_zero_of_out_support n α r ℓ j₀ hj₀ h_not_supp
  have part2 : ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r ≤ (n : ℝ) + 1 := by
    -- Sum over Icc -n n equals sum over the filter (∈ S)
    have h_sum_split :
        ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r =
          ∑ r ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S), T4 r := by
      symm
      apply Finset.sum_filter_of_ne
      intro r hr hne
      by_contra hr_notS
      exact hne (hT4_zero_outside r hr hr_notS)
    rw [h_sum_split]
    have h_le_S_card :
        ∑ r ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S), T4 r ≤
          (((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card : ℝ) := by
      have h_each : ∀ r ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S),
                    T4 r ≤ 1 := fun r _ => (part1 r).2
      calc ∑ r ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S), T4 r
          ≤ ∑ _r ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S), (1 : ℝ) :=
            Finset.sum_le_sum (fun r hr => h_each r hr)
        _ = (((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card : ℝ) := by
            simp
    have h_filter_le_S : ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card ≤
                         S.card := by
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_filter] at hr
      exact hr.2
    have h_filter_le : ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card ≤ n + 1 := by
      rw [← hS_card]; exact h_filter_le_S
    have h_cast : (((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card : ℝ) ≤
                  (n : ℝ) + 1 := by
      have hh : (((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun r => r ∈ S)).card : ℝ) ≤
             ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h_filter_le
      push_cast at hh
      linarith
    linarith
  -- Part 3: Fourier sup-norm bound
  have part3 : ∀ ξ : ℝ,
        |∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r * Real.cos (ξ * (r : ℝ))|
          ≤ (n : ℝ) + 1 := by
    intro ξ
    have h_tri : |∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r * Real.cos (ξ * (r : ℝ))| ≤
                 ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), |T4 r * Real.cos (ξ * (r : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_each : ∀ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
                  |T4 r * Real.cos (ξ * (r : ℝ))| ≤ T4 r := by
      intro r _
      rw [abs_mul]
      have hT4r_nn := (part1 r).1
      have hT4r_abs : |T4 r| = T4 r := abs_of_nonneg hT4r_nn
      have hcos_le : |Real.cos (ξ * (r : ℝ))| ≤ 1 := Real.abs_cos_le_one _
      calc |T4 r| * |Real.cos (ξ * (r : ℝ))| ≤ |T4 r| * 1 :=
            mul_le_mul_of_nonneg_left hcos_le (abs_nonneg _)
        _ = T4 r := by rw [mul_one, hT4r_abs]
    have h_sum_abs_le : ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), |T4 r * Real.cos (ξ * (r : ℝ))|
                      ≤ ∑ r ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), T4 r :=
      Finset.sum_le_sum h_each
    linarith [part2]
  exact ⟨part1, part2, part3⟩
