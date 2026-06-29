import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist

open Workspace.Types.BinVec

theorem WitnessCoinFlipFormula :
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
        ∀ (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
          (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So) (b : BinVec n),
          (Ce.toPMF b =
              ENNReal.ofReal
                ((∏ i : Fin n, (if (i.val) % 2 = 1
                    then (if b.bit i = false then (1 : ℝ) else 0)
                    else 1)) *
                 (∏ i : Fin n, (if (i.val) % 2 = 0
                    then (if b.bit i
                          then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                          else 1 -
                                (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                    else 1)))) ∧
          (Co.toPMF b =
              ENNReal.ofReal
                ((∏ i : Fin n, (if (i.val) % 2 = 0
                    then (if b.bit i = false then (1 : ℝ) else 0)
                    else 1)) *
                 (∏ i : Fin n, (if (i.val) % 2 = 1
                    then (if b.bit i
                          then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                          else 1 -
                                (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                    else 1)))) := by
  intro n _ _ Se So hSe hSo Ce Co b
  -- The "α" prefactor
  set C : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hC
  have key_e : ∀ i : Fin n,
      (if b.bit i then Se.p i else 1 - Se.p i) =
      (if (i.val) % 2 = 1
          then (if b.bit i = false then (1 : ℝ) else 0)
          else 1) *
      (if (i.val) % 2 = 0
          then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
          else 1) := by
    intro i
    have hSei := hSe i
    rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
    · -- i.val % 2 = 0
      have hpar1ne : ¬ (i.val % 2 = 1) := by omega
      rw [if_neg hpar1ne, if_pos hpar, one_mul]
      rw [hSei, if_pos hpar]
    · -- i.val % 2 = 1
      have hpar0ne : ¬ (i.val % 2 = 0) := by omega
      rw [if_pos hpar, if_neg hpar0ne, mul_one]
      rw [hSei, if_neg hpar0ne]
      by_cases hb : b.bit i
      · simp [hb]
      · simp [hb]
  have key_o : ∀ i : Fin n,
      (if b.bit i then So.p i else 1 - So.p i) =
      (if (i.val) % 2 = 0
          then (if b.bit i = false then (1 : ℝ) else 0)
          else 1) *
      (if (i.val) % 2 = 1
          then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
          else 1) := by
    intro i
    have hSoi := hSo i
    rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
    · -- i.val % 2 = 0
      have hpar1ne : ¬ (i.val % 2 = 1) := by omega
      rw [if_pos hpar, if_neg hpar1ne, mul_one]
      rw [hSoi, if_neg hpar1ne]
      by_cases hb : b.bit i
      · simp [hb]
      · simp [hb]
    · -- i.val % 2 = 1
      have hpar0ne : ¬ (i.val % 2 = 0) := by omega
      rw [if_neg hpar0ne, if_pos hpar, one_mul]
      rw [hSoi, if_pos hpar]
  refine ⟨?_, ?_⟩
  · -- Even case
    have hnonneg_e : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 1
              then (if b.bit i = false then (1 : ℝ) else 0)
              else 1) := by
      intro i; split_ifs <;> norm_num
    have hnonneg_o : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 0
              then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) := by
      intro i
      by_cases hpar : (i.val) % 2 = 0
      · rw [if_pos hpar]
        have h0 : 0 ≤ Se.p i := Se.nonneg i
        have h1 : Se.p i ≤ 1 := Se.le_one i
        have hSei := hSe i
        rw [hSei, if_pos hpar] at h0 h1
        split_ifs
        · exact h0
        · linarith
      · rw [if_neg hpar]; norm_num
    rw [Ce.prod_factorisation b]
    -- Step 1: rewrite each LHS factor pointwise via key_e
    have step1 : (∏ i : Fin n, ENNReal.ofReal (if b.bit i then Se.p i else 1 - Se.p i)) =
                 (∏ i : Fin n, ENNReal.ofReal
                    ((if (i.val) % 2 = 1
                        then (if b.bit i = false then (1 : ℝ) else 0)
                        else 1) *
                     (if (i.val) % 2 = 0
                        then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                              else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                        else 1))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [key_e i]
    rw [step1]
    -- Step 2: combine ofReals into one ofReal of the product
    rw [← ENNReal.ofReal_prod_of_nonneg
          (fun i _ => mul_nonneg (hnonneg_e i) (hnonneg_o i))]
    -- Step 3: split product
    rw [Finset.prod_mul_distrib]
  · -- Odd case (symmetric)
    have hnonneg_e : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 0
              then (if b.bit i = false then (1 : ℝ) else 0)
              else 1) := by
      intro i; split_ifs <;> norm_num
    have hnonneg_o : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 1
              then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) := by
      intro i
      by_cases hpar : (i.val) % 2 = 1
      · rw [if_pos hpar]
        have h0 : 0 ≤ So.p i := So.nonneg i
        have h1 : So.p i ≤ 1 := So.le_one i
        have hSoi := hSo i
        rw [hSoi, if_pos hpar] at h0 h1
        split_ifs
        · exact h0
        · linarith
      · rw [if_neg hpar]; norm_num
    rw [Co.prod_factorisation b]
    have step1 : (∏ i : Fin n, ENNReal.ofReal (if b.bit i then So.p i else 1 - So.p i)) =
                 (∏ i : Fin n, ENNReal.ofReal
                    ((if (i.val) % 2 = 0
                        then (if b.bit i = false then (1 : ℝ) else 0)
                        else 1) *
                     (if (i.val) % 2 = 1
                        then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                              else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                        else 1))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [key_o i]
    rw [step1]
    rw [← ENNReal.ofReal_prod_of_nonneg
          (fun i _ => mul_nonneg (hnonneg_e i) (hnonneg_o i))]
    rw [Finset.prod_mul_distrib]
