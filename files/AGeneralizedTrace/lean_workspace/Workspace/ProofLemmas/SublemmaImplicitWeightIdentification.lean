import Mathlib
import Workspace.Types.AlternatingSumExpression

set_option maxHeartbeats 800000

theorem SublemmaImplicitWeightIdentification :
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
      let Zprime_er : ℤ → ℝ := fun r =>
        ∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j)
      ∀ (r : ℤ),
        -((n : ℤ) / 4) ≤ r → r ≤ ((n : ℤ) / 4) →
        ∀ (ℓ : Finset ℕ),
          ℓ ⊆ Finset.Icc 1 n_h →
          Workspace.Types.AlternatingSumExpression.sameParity ℓ →
          (∀ j ∈ Finset.Icc 1 n_h, S_er r j < 1) →
          (∏ j ∈ ℓ, (S_er r j) / (1 - S_er r j))
            = (widetildeMu_er r ℓ) / (Zprime_er r) := by
  intro n hn hmod
  intro c' α n_h S_er widetildeMu_er Zprime_er
  intro r _hr_lb _hr_ub ℓ hℓ_sub _hℓ_par hS_lt_one
  -- Unfold all let-bindings.
  show (∏ j ∈ ℓ, (S_er r j) / (1 - S_er r j))
      = (∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ ℓ then S_er r j else (1 - S_er r j)))
        / (∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j))
  -- Each `1 - S_er r j` is positive on Icc 1 n_h, hence nonzero.
  have h_pos_one_sub : ∀ j ∈ Finset.Icc 1 n_h, 0 < 1 - S_er r j := by
    intro j hj
    have := hS_lt_one j hj
    linarith
  -- ℓ ⊆ Icc 1 n_h, so each `1 - S_er r j ≠ 0` for j ∈ ℓ as well.
  have h_pos_one_sub_ℓ : ∀ j ∈ ℓ, 0 < 1 - S_er r j := by
    intro j hj
    exact h_pos_one_sub j (hℓ_sub hj)
  -- Step 1: split the numerator using `Finset.prod_ite`.
  have h_num_split :
      (∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ ℓ then S_er r j else (1 - S_er r j)))
        = (∏ j ∈ Finset.Icc 1 (n / 2) with j ∈ ℓ, S_er r j)
          * (∏ j ∈ Finset.Icc 1 (n / 2) with j ∉ ℓ, (1 - S_er r j)) := by
    classical
    exact Finset.prod_ite _ _
  -- The filter (· ∈ ℓ) on Icc 1 n_h is just ℓ (using ℓ ⊆ Icc).
  have h_filter_in :
      (Finset.Icc 1 (n / 2)).filter (· ∈ ℓ) = ℓ := by
    classical
    rw [Finset.filter_mem_eq_inter]
    -- Now need: Icc 1 (n/2) ∩ ℓ = ℓ.
    exact Finset.inter_eq_right.mpr hℓ_sub
  -- The filter (· ∉ ℓ) on Icc 1 n_h is Icc \ ℓ.
  have h_filter_out :
      (Finset.Icc 1 (n / 2)).filter (· ∉ ℓ) = Finset.Icc 1 (n / 2) \ ℓ := by
    classical
    rw [Finset.sdiff_eq_filter]
  -- Rewrite the numerator.
  rw [h_num_split, h_filter_in, h_filter_out]
  -- Step 2: split the denominator using `Finset.prod_sdiff`.
  -- (∏ j ∈ Icc \ ℓ, (1 - S)) * (∏ j ∈ ℓ, (1 - S)) = ∏ j ∈ Icc, (1 - S)
  have h_den_split :
      (∏ j ∈ Finset.Icc 1 (n / 2), (1 - S_er r j))
        = (∏ j ∈ Finset.Icc 1 (n / 2) \ ℓ, (1 - S_er r j))
          * (∏ j ∈ ℓ, (1 - S_er r j)) := by
    classical
    have := Finset.prod_sdiff (s₁ := ℓ) (s₂ := Finset.Icc 1 (n / 2))
              (f := fun j => (1 - S_er r j)) hℓ_sub
    -- this : (∏ x ∈ Icc \ ℓ, (1 - S_er r x)) * (∏ x ∈ ℓ, (1 - S_er r x))
    --       = ∏ x ∈ Icc, (1 - S_er r x)
    linarith [this]
  rw [h_den_split]
  -- Now the goal is:
  -- (∏ j ∈ ℓ, S/(1-S)) = (∏ j ∈ ℓ, S) * (∏ j ∈ Icc\ℓ, (1-S))
  --                       / ((∏ j ∈ Icc\ℓ, (1-S)) * (∏ j ∈ ℓ, (1-S)))
  -- The product over Icc\ℓ of (1-S) is nonzero since each factor > 0.
  have h_prod_sdiff_pos :
      0 < (∏ j ∈ Finset.Icc 1 (n / 2) \ ℓ, (1 - S_er r j)) := by
    apply Finset.prod_pos
    intro j hj
    rw [Finset.mem_sdiff] at hj
    exact h_pos_one_sub j hj.1
  have h_prod_sdiff_ne :
      (∏ j ∈ Finset.Icc 1 (n / 2) \ ℓ, (1 - S_er r j)) ≠ 0 :=
    ne_of_gt h_prod_sdiff_pos
  have h_prod_ℓ_pos :
      0 < (∏ j ∈ ℓ, (1 - S_er r j)) := by
    apply Finset.prod_pos
    intro j hj
    exact h_pos_one_sub_ℓ j hj
  have h_prod_ℓ_ne :
      (∏ j ∈ ℓ, (1 - S_er r j)) ≠ 0 := ne_of_gt h_prod_ℓ_pos
  -- Now the algebra.
  rw [Finset.prod_div_distrib]
  -- Goal: (∏ j ∈ ℓ, S) / (∏ j ∈ ℓ, (1 - S))
  --       = (∏ j ∈ ℓ, S) * (∏ j ∈ Icc\ℓ, (1-S))
  --         / ((∏ j ∈ Icc\ℓ, (1-S)) * (∏ j ∈ ℓ, (1-S)))
  field_simp
