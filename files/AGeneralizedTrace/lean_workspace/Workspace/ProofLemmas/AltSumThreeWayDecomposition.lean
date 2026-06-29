import Mathlib
import Workspace.Types.AlternatingSumExpression

set_option maxHeartbeats 4000000

open Classical

theorem AltSumThreeWayDecomposition :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt (n : ℝ) ≤ δ → δ ≤ 1/2 →
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
      let P_L : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)))
      let T_I : ℝ :=
        ∑ ℓ ∈ P_H,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
      let T_II : ℝ :=
        ∑ ℓ ∈ P_H,
          ((∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            +
           (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))
      let T_III : ℝ :=
        ∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
      Workspace.Types.AlternatingSumExpression.altSum n δ α = T_I + T_II + T_III := by
  intro n hn hmod δ hδ_lb hδ_ub
  intro c' α n_h S_er widetildeMu_er P_H P_L T_I T_II T_III
  -- Abbreviate the inner z-double-sum.
  set F : Finset ℕ → ℝ := fun ℓ =>
    ∑ zMinus ∈ Finset.range (n / 2 + 1),
      ∑ zPlus ∈ Finset.range (n / 2 + 1),
        |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ| with hF_def
  -- Useful arithmetic facts.
  have h_card : (Finset.Icc 1 (n / 2)).card = n / 2 := by
    rw [Nat.card_Icc]; omega
  have h_n16_le : n / 16 ≤ n / 2 + 1 := by
    have h1 : n / 16 ≤ n / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
    omega
  -- Step 1 & 2: Unfold altSum and re-bracket the (k, ℓ)-double-sum.
  have h_altSum_unfold :
      Workspace.Types.AlternatingSumExpression.altSum n δ α
        = ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
            Workspace.Types.AlternatingSumExpression.sameParity, F ℓ := by
    show (∑ k ∈ Finset.range (n / 2 + 1),
            ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powersetCard k).filter
              Workspace.Types.AlternatingSumExpression.sameParity, F ℓ)
        = ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
              Workspace.Types.AlternatingSumExpression.sameParity, F ℓ
    rw [show n / 2 + 1 = (Finset.Icc 1 (n / 2)).card + 1 from by rw [h_card]]
    simp only [Finset.sum_filter]
    rw [Finset.sum_powerset]
  rw [h_altSum_unfold]
  -- Step 3: Split by extra-predicate (∃ r ...).
  have h_split :
      (∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
            Workspace.Types.AlternatingSumExpression.sameParity, F ℓ)
        = (∑ ℓ ∈ P_H, F ℓ) + (∑ ℓ ∈ P_L, F ℓ) := by
    have key := (Finset.sum_filter_add_sum_filter_not
        (((Finset.Icc 1 (n / 2)).powerset).filter
          Workspace.Types.AlternatingSumExpression.sameParity)
        (fun ℓ => ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ) F).symm
    rw [key]
    congr 1
    · -- Identify P_H using set-equality on filters.
      have hPH_set :
          (((Finset.Icc 1 (n / 2)).powerset).filter
              Workspace.Types.AlternatingSumExpression.sameParity).filter
            (fun ℓ => ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ) = P_H := by
        apply Finset.ext
        intro ℓ
        constructor
        · intro hmem
          simp only [Finset.mem_filter] at hmem
          obtain ⟨⟨h_pow, h_sp⟩, h_ext⟩ := hmem
          show ℓ ∈ P_H
          simp only [P_H, Finset.mem_filter]
          exact ⟨h_pow, h_sp, h_ext⟩
        · intro hmem
          have hmem' : ℓ ∈ P_H := hmem
          simp only [P_H, Finset.mem_filter] at hmem'
          obtain ⟨h_pow, h_sp, h_ext⟩ := hmem'
          simp only [Finset.mem_filter]
          exact ⟨⟨h_pow, h_sp⟩, h_ext⟩
      rw [hPH_set]
    · -- Identify P_L.
      have hPL_set :
          (((Finset.Icc 1 (n / 2)).powerset).filter
              Workspace.Types.AlternatingSumExpression.sameParity).filter
            (fun ℓ => ¬ ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
              Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ) = P_L := by
        apply Finset.ext
        intro ℓ
        constructor
        · intro hmem
          simp only [Finset.mem_filter] at hmem
          obtain ⟨⟨h_pow, h_sp⟩, h_ne⟩ := hmem
          show ℓ ∈ P_L
          simp only [P_L, Finset.mem_filter]
          refine ⟨h_pow, h_sp, ?_⟩
          intro r hr
          by_contra hlt
          push_neg at hlt
          exact h_ne ⟨r, hr, hlt⟩
        · intro hmem
          have hmem' : ℓ ∈ P_L := hmem
          simp only [P_L, Finset.mem_filter] at hmem'
          obtain ⟨h_pow, h_sp, h_all⟩ := hmem'
          simp only [Finset.mem_filter]
          refine ⟨⟨h_pow, h_sp⟩, ?_⟩
          rintro ⟨r, hr, hge⟩
          exact (lt_irrefl _) (lt_of_le_of_lt hge (h_all r hr))
      rw [hPL_set]
  rw [h_split]
  -- Now goal: (∑ ℓ ∈ P_H, F ℓ) + (∑ ℓ ∈ P_L, F ℓ) = T_I + T_II + T_III
  show (∑ ℓ ∈ P_H, F ℓ) + (∑ ℓ ∈ P_L, F ℓ) = T_I + T_II + T_III
  have hT_III : T_III = ∑ ℓ ∈ P_L, F ℓ := rfl
  rw [hT_III]
  suffices h_PH_split : (∑ ℓ ∈ P_H, F ℓ) = T_I + T_II by linarith
  have hTI : T_I = ∑ ℓ ∈ P_H,
      (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
        ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|) := rfl
  have hTII : T_II = ∑ ℓ ∈ P_H,
      ((∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        +
       (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)) := rfl
  rw [hTI, hTII, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _hℓ
  show (∑ zMinus ∈ Finset.range (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
      = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        +
        ((∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          +
         (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))
  -- Convert all `range` to `Ico 0` for uniformity.
  simp only [Finset.range_eq_Ico]
  -- Now LHS is: ∑ zMinus ∈ Ico 0 (n/2+1), ∑ zPlus ∈ Ico 0 (n/2+1), ... (similarly RHS)
  -- Outer split: Ico 0 (n/2+1) = Ico 0 (n/16) ⊔ Ico (n/16) (n/2+1).
  rw [← Finset.sum_Ico_consecutive (fun zMinus =>
        ∑ zPlus ∈ Finset.Ico 0 (n / 2 + 1),
          |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        (Nat.zero_le _) h_n16_le]
  -- In the Ico (n/16) (n/2+1) z₋ block, split inner zPlus sum.
  have h_inner_split :
      (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.Ico 0 (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.Ico 0 (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          + (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro zMinus _
    rw [← Finset.sum_Ico_consecutive (fun zPlus =>
          |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          (Nat.zero_le _) h_n16_le]
  rw [h_inner_split]
  ring
