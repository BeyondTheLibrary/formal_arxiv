import Mathlib

theorem TailBoundExpDecay :
    ∀ (c A : ℝ) (N : ℕ),
      0 < c → 0 < A →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          A * Real.exp (-1 / (c * ε^2)) ≤ ε ^ N := by
  intro c A N hc hA
  -- Let M = max 1 (A * (N+1)! * c^(N+1)).
  set M : ℝ := max 1 (A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1)) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM_ge_one : 1 ≤ M := le_max_left _ _
  have hM_ge : A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) ≤ M := le_max_right _ _
  refine ⟨1 / M, by positivity, ?_⟩
  intro ε hε hε_le
  -- Step 1: bound exp(-1/(c·ε²)) using exp(x) ≥ x^(N+1)/(N+1)! at x = 1/(c·ε²).
  have hcε2_pos : 0 < c * ε ^ 2 := by positivity
  have hinv_nn : (0 : ℝ) ≤ 1 / (c * ε ^ 2) := by positivity
  -- x^(N+1)/(N+1)! ≤ exp x where x = 1/(c·ε²)
  have hkey :
      (1 / (c * ε ^ 2)) ^ (N + 1) / (Nat.factorial (N + 1) : ℝ) ≤
        Real.exp (1 / (c * ε ^ 2)) :=
    Real.pow_div_factorial_le_exp (1 / (c * ε ^ 2)) hinv_nn (N + 1)
  -- Take reciprocals: exp(-x) ≤ (N+1)! / (1/(c·ε²))^(N+1) = (N+1)! · (c·ε²)^(N+1)
  have hfact_pos : (0 : ℝ) < (Nat.factorial (N + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (N + 1)
  have hcε2pow_pos : 0 < (c * ε ^ 2) ^ (N + 1) := by positivity
  have hLHS_pos : (0 : ℝ) < (1 / (c * ε ^ 2)) ^ (N + 1) / (Nat.factorial (N + 1) : ℝ) := by
    apply div_pos
    · exact pow_pos (by positivity) _
    · exact hfact_pos
  -- exp(1/(c·ε²)) > 0 trivially
  have hexp_pos : 0 < Real.exp (1 / (c * ε ^ 2)) := Real.exp_pos _
  -- Rewrite Real.exp (-1/(c·ε²)) = 1/Real.exp(1/(c·ε²))
  have hneg_exp :
      Real.exp (-1 / (c * ε ^ 2)) = 1 / Real.exp (1 / (c * ε ^ 2)) := by
    rw [neg_div, Real.exp_neg]
    simp [one_div]
  -- Inverse inequality
  have hinv_le :
      1 / Real.exp (1 / (c * ε ^ 2)) ≤
        1 / ((1 / (c * ε ^ 2)) ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)) := by
    apply one_div_le_one_div_of_le hLHS_pos hkey
  -- Simplify RHS
  have hsimp :
      1 / ((1 / (c * ε ^ 2)) ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)) =
        (Nat.factorial (N + 1) : ℝ) * (c * ε ^ 2) ^ (N + 1) := by
    rw [one_div_div]
    rw [div_pow, one_pow]
    field_simp
  -- Combine
  have hbound :
      Real.exp (-1 / (c * ε ^ 2)) ≤
        (Nat.factorial (N + 1) : ℝ) * (c * ε ^ 2) ^ (N + 1) := by
    rw [hneg_exp]
    exact hinv_le.trans (le_of_eq hsimp)
  -- Multiply by A
  have hAbound :
      A * Real.exp (-1 / (c * ε ^ 2)) ≤
        A * ((Nat.factorial (N + 1) : ℝ) * (c * ε ^ 2) ^ (N + 1)) :=
    mul_le_mul_of_nonneg_left hbound hA.le
  -- Now show A * (N+1)! * (c·ε²)^(N+1) ≤ ε^N
  -- (c·ε²)^(N+1) = c^(N+1) · ε^(2(N+1))
  have hexpand :
      (c * ε ^ 2) ^ (N + 1) = c ^ (N + 1) * ε ^ (2 * (N + 1)) := by
    rw [mul_pow, ← pow_mul]
  -- So A · (N+1)! · (c·ε²)^(N+1) = A · (N+1)! · c^(N+1) · ε^(2(N+1))
  -- And 2(N+1) = N + (N+2)
  have h2split : 2 * (N + 1) = N + (N + 2) := by ring
  -- So ε^(2(N+1)) = ε^N · ε^(N+2)
  have hε_pow_split :
      ε ^ (2 * (N + 1)) = ε ^ N * ε ^ (N + 2) := by
    rw [h2split, pow_add]
  -- ε ≤ 1/M ≤ 1, so ε^(N+2) ≤ ε ≤ 1/M
  have hε_le_one : ε ≤ 1 := by
    have : (1 : ℝ) / M ≤ 1 := by
      rw [div_le_one hM_pos]
      exact hM_ge_one
    linarith
  have hε_pow_le : ε ^ (N + 2) ≤ ε := by
    have hN2 : 1 ≤ N + 2 := by omega
    calc ε ^ (N + 2) ≤ ε ^ 1 := by
            apply pow_le_pow_of_le_one hε.le hε_le_one hN2
      _ = ε := pow_one ε
  -- M · ε^(N+2) ≤ M · ε ≤ 1
  have hMε_le_1 : M * ε ^ (N + 2) ≤ 1 := by
    have step1 : M * ε ^ (N + 2) ≤ M * ε := mul_le_mul_of_nonneg_left hε_pow_le hM_pos.le
    have step2 : M * ε ≤ M * (1 / M) := mul_le_mul_of_nonneg_left hε_le hM_pos.le
    have step3 : M * (1 / M) = 1 := mul_one_div_cancel (ne_of_gt hM_pos)
    linarith
  -- A · (N+1)! · c^(N+1) · ε^(N+2) ≤ M · ε^(N+2) ≤ 1
  have hAfc_pos : (0 : ℝ) ≤ A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) := by positivity
  have hAfc_ε_le_1 :
      A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) * ε ^ (N + 2) ≤ 1 := by
    have step1 :
        A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) * ε ^ (N + 2) ≤
          M * ε ^ (N + 2) :=
      mul_le_mul_of_nonneg_right hM_ge (by positivity)
    linarith
  -- Combine the pieces
  -- We have:
  --   A * exp(-1/(cε²)) ≤ A · (N+1)! · (cε²)^(N+1)
  --                    = A · (N+1)! · c^(N+1) · ε^(2(N+1))
  --                    = (A · (N+1)! · c^(N+1) · ε^(N+2)) · ε^N
  --                    ≤ 1 · ε^N = ε^N
  have hεN_nn : (0 : ℝ) ≤ ε ^ N := by positivity
  calc A * Real.exp (-1 / (c * ε ^ 2))
      ≤ A * ((Nat.factorial (N + 1) : ℝ) * (c * ε ^ 2) ^ (N + 1)) := hAbound
    _ = A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) * ε ^ (2 * (N + 1)) := by
          rw [hexpand]; ring
    _ = A * (Nat.factorial (N + 1) : ℝ) * c ^ (N + 1) * ε ^ (N + 2) * ε ^ N := by
          rw [hε_pow_split]; ring
    _ ≤ 1 * ε ^ N := mul_le_mul_of_nonneg_right hAfc_ε_le_1 hεN_nn
    _ = ε ^ N := one_mul _
