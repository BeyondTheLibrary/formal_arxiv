import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.CoinFlipDist
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.WitnessCoinFlipFormula

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

theorem MixedParityVanishes :
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
      ∀ (δ : Workspace.Types.DelProb.DelProb),
        (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
        ∀ (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
          (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
        ∀ (m : Workspace.Types.BinVec.BinVec (n / 2)),
          (∃ j₁ j₂ : Fin (n / 2),
            m.bit j₁ = true ∧ m.bit j₂ = true ∧ (j₁.val) % 2 ≠ (j₂.val) % 2) →
          ∀ (zMinus zPlus : ℕ),
            ((lenE.toPMF (m, zMinus, zPlus)).toReal)
              = ((lenO.toPMF (m, zMinus, zPlus)).toReal) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO m hmix zMinus zPlus
  obtain ⟨Ce⟩ := CoinFlipDistExists Se
  obtain ⟨Co⟩ := CoinFlipDistExists So
  have hwitness := fun b => WitnessCoinFlipFormula n hn hmod Se So hSe hSo Ce Co b
  have hE_zero : lenE.toPMF (m, zMinus, zPlus) = 0 := by
    have hcomp := lenE.composition_law Ce m zMinus zPlus
    rw [hcomp]
    rw [ENNReal.tsum_eq_zero]
    intro b
    rw [ENNReal.tsum_eq_zero]
    intro r
    by_cases hmid : middleIndicator n b m r = 0
    · rw [hmid]; ring
    · have hCe_zero : Ce.toPMF b = 0 := by
        rw [middleIndicator] at hmid
        split_ifs at hmid with h₁ h₂
        · obtain ⟨j₁, j₂, hbj₁, hbj₂, hpar⟩ := hmix
          have hb1 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat,
              by
                have hj := h₁ j₁
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₁
            rw [this]; exact hbj₁
          have hb2 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat,
              by
                have hj := h₁ j₂
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₂
            rw [this]; exact hbj₂
          set i₁ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat, _⟩ with hi₁_def
          set i₂ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat, _⟩ with hi₂_def
          have hpar_i : i₁.val % 2 ≠ i₂.val % 2 := by
            have hj₁' := h₁ j₁
            have hj₂' := h₁ j₂
            have h0₁ : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hj₁'.1
            have h0₂ : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hj₂'.1
            intro heq
            apply hpar
            have ki₁ : (i₁.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := h0₁
            have ki₂ : (i₂.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := h0₂
            have hmod_eq : (i₁.val : ℤ) % 2 = (i₂.val : ℤ) % 2 := by
              have : ((i₁.val % 2 : ℕ) : ℤ) = ((i₂.val % 2 : ℕ) : ℤ) := by exact_mod_cast heq
              calc (i₁.val : ℤ) % 2
                  = ((i₁.val % 2 : ℕ) : ℤ) := by push_cast; rfl
                _ = ((i₂.val % 2 : ℕ) : ℤ) := this
                _ = (i₂.val : ℤ) % 2 := by push_cast; rfl
            rw [ki₁, ki₂] at hmod_eq
            have : ((j₁.val : ℤ)) % 2 = ((j₂.val : ℤ)) % 2 := by omega
            zify
            exact this
          have ⟨hCe_eq, _⟩ := hwitness b
          rw [hCe_eq]
          rw [ENNReal.ofReal_eq_zero]
          set P_e_odd := ∏ i : Fin n, (if (i.val) % 2 = 1
              then (if b.bit i = false then (1 : ℝ) else 0) else 1) with hP_def
          set P_e_even := ∏ i : Fin n, (if (i.val) % 2 = 0
              then (if b.bit i
                    then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 -
                          (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) with hPe_def
          show P_e_odd * P_e_even ≤ 0
          have hP_e_odd : P_e_odd = 0 := by
            by_cases hi1 : i₁.val % 2 = 1
            · apply Finset.prod_eq_zero (Finset.mem_univ i₁)
              simp [hi1, hb1]
            · have hi2 : i₂.val % 2 = 1 := by
                have h_or : i₁.val % 2 = 0 ∨ i₁.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                cases h_or with
                | inl h =>
                  have h_or2 : i₂.val % 2 = 0 ∨ i₂.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                  cases h_or2 with
                  | inl h2 => exact absurd (h.trans h2.symm) hpar_i
                  | inr h2 => exact h2
                | inr h => exact absurd h hi1
              apply Finset.prod_eq_zero (Finset.mem_univ i₂)
              simp [hi2, hb2]
          rw [hP_e_odd, zero_mul]
        · exfalso; exact hmid rfl
        · exfalso; exact hmid rfl
      rw [hCe_zero]
      ring
  have hO_zero : lenO.toPMF (m, zMinus, zPlus) = 0 := by
    have hcomp := lenO.composition_law Co m zMinus zPlus
    rw [hcomp]
    rw [ENNReal.tsum_eq_zero]
    intro b
    rw [ENNReal.tsum_eq_zero]
    intro r
    by_cases hmid : middleIndicator n b m r = 0
    · rw [hmid]; ring
    · have hCo_zero : Co.toPMF b = 0 := by
        rw [middleIndicator] at hmid
        split_ifs at hmid with h₁ h₂
        · obtain ⟨j₁, j₂, hbj₁, hbj₂, hpar⟩ := hmix
          have hb1 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat,
              by
                have hj := h₁ j₁
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₁
            rw [this]; exact hbj₁
          have hb2 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat,
              by
                have hj := h₁ j₂
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₂
            rw [this]; exact hbj₂
          set i₁ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat, _⟩ with hi₁_def
          set i₂ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat, _⟩ with hi₂_def
          have hpar_i : i₁.val % 2 ≠ i₂.val % 2 := by
            have hj₁' := h₁ j₁
            have hj₂' := h₁ j₂
            have h0₁ : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hj₁'.1
            have h0₂ : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hj₂'.1
            intro heq
            apply hpar
            have ki₁ : (i₁.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := h0₁
            have ki₂ : (i₂.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := h0₂
            have hmod_eq : (i₁.val : ℤ) % 2 = (i₂.val : ℤ) % 2 := by
              have : ((i₁.val % 2 : ℕ) : ℤ) = ((i₂.val % 2 : ℕ) : ℤ) := by exact_mod_cast heq
              calc (i₁.val : ℤ) % 2
                  = ((i₁.val % 2 : ℕ) : ℤ) := by push_cast; rfl
                _ = ((i₂.val % 2 : ℕ) : ℤ) := this
                _ = (i₂.val : ℤ) % 2 := by push_cast; rfl
            rw [ki₁, ki₂] at hmod_eq
            have : ((j₁.val : ℤ)) % 2 = ((j₂.val : ℤ)) % 2 := by omega
            zify
            exact this
          have ⟨_, hCo_eq⟩ := hwitness b
          rw [hCo_eq]
          rw [ENNReal.ofReal_eq_zero]
          set P_o_even := ∏ i : Fin n, (if (i.val) % 2 = 0
              then (if b.bit i = false then (1 : ℝ) else 0) else 1) with hP_def
          set P_o_odd := ∏ i : Fin n, (if (i.val) % 2 = 1
              then (if b.bit i
                    then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 -
                          (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) with hPo_def
          show P_o_even * P_o_odd ≤ 0
          have hP_o_even : P_o_even = 0 := by
            by_cases hi1 : i₁.val % 2 = 0
            · apply Finset.prod_eq_zero (Finset.mem_univ i₁)
              simp [hi1, hb1]
            · have hi2 : i₂.val % 2 = 0 := by
                have h_or : i₁.val % 2 = 0 ∨ i₁.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                cases h_or with
                | inl h => exact absurd h hi1
                | inr h =>
                  have h_or2 : i₂.val % 2 = 0 ∨ i₂.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                  cases h_or2 with
                  | inl h2 => exact h2
                  | inr h2 => exact absurd (h.trans h2.symm) hpar_i
              apply Finset.prod_eq_zero (Finset.mem_univ i₂)
              simp [hi2, hb2]
          rw [hP_o_even, zero_mul]
        · exfalso; exact hmid rfl
        · exfalso; exact hmid rfl
      rw [hCo_zero]
      ring
  rw [hE_zero, hO_zero]
