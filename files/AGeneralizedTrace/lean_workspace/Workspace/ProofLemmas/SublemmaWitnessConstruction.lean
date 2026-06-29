import Mathlib
import Workspace.Types.ProbVec
import Workspace.ProofLemmas.SublemmaCentralBinomialBounds

open Workspace.Types.ProbVec

/--
There exist length-`n` probability vectors `Se, So : ProbVec n` such that, with
`α := c' * √n` and `c' := 1 / (4 * e^2 * √(2π))`, for every index
`i : Fin n` we have `Se.p i = α * bin(n, 1/2, i)` when `i.val` is even and
`0` otherwise, and dually `So.p i = α * bin(n, 1/2, i)` when `i.val` is odd and
`0` otherwise. The non-trivial content is `ProbVec` membership, i.e. that all
the assigned reals lie in `[0,1]`, via the central-binomial upper bound
`α * bin(n, 1/2, i) ≤ c' * √(2/π) < 1`.
-/
theorem SublemmaWitnessConstruction :
    ∀ n : ℕ, 1 ≤ n →
      ∃ Se So : ProbVec n,
        (∀ i : Fin n,
            Se.p i =
              (if i.val % 2 = 0
               then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                      Real.sqrt (n : ℝ) *
                      ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
               else 0)) ∧
        (∀ i : Fin n,
            So.p i =
              (if i.val % 2 = 1
               then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                      Real.sqrt (n : ℝ) *
                      ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
               else 0)) := by
  intro n hn
  -- Setup
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_nonneg : (0 : ℝ) ≤ n := le_of_lt hn_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have he_pos : 0 < Real.exp 2 := Real.exp_pos 2
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  have hdenom_pos : 0 < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hc'_pos : 0 < c' := by
    rw [hc'_def]; positivity
  have hc'_nonneg : 0 ≤ c' := le_of_lt hc'_pos
  have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h2n_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have h2n_inv_nonneg : (0 : ℝ) ≤ (2 ^ n : ℝ)⁻¹ := by positivity
  have hchoose_nonneg : ∀ k : ℕ, (0 : ℝ) ≤ (Nat.choose n k : ℝ) := fun k => by
    exact_mod_cast Nat.zero_le _
  -- Central binomial upper bound from imported sorry-lemma
  have hCB : ∀ i : ℕ,
      ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
    (Workspace.ProofLemmas.SublemmaCentralBinomialBounds n hn).1
  -- The key bound: c' * √n * √(2/(π·n)) ≤ 1
  have hkey : c' * Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * (n : ℝ))) ≤ 1 := by
    have h_combine :
        Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * (n : ℝ))) =
          Real.sqrt (2 / Real.pi) := by
      rw [← Real.sqrt_mul hn_nonneg]
      congr 1
      field_simp
    rw [show c' * Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * (n : ℝ))) =
        c' * (Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * (n : ℝ)))) by ring]
    rw [h_combine, hc'_def]
    rw [div_mul_eq_mul_div, one_mul]
    rw [div_le_one hdenom_pos]
    have he_one : 1 ≤ Real.exp 2 := by
      have : Real.exp 0 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      rwa [Real.exp_zero] at this
    have hlhs : Real.sqrt (2 / Real.pi) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      rw [div_le_one hpi_pos]
      linarith [Real.pi_gt_three]
    have h2pi_one : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      linarith [Real.pi_gt_three]
    nlinarith [Real.exp_pos 2, Real.sqrt_nonneg (2 * Real.pi)]
  -- Helper: c' * √n * (C(n,i) * 2^(-n)) ≤ 1 for any i
  have hbound : ∀ i : ℕ,
      c' * Real.sqrt (n : ℝ) * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1 := by
    intro i
    have h1 : c' * Real.sqrt (n : ℝ) * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤
              c' * Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * (n : ℝ))) := by
      have hc'sqrt_nonneg : 0 ≤ c' * Real.sqrt (n : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (hCB i) hc'sqrt_nonneg
    linarith
  -- Helper: nonnegativity for any i
  have hnonneg : ∀ i : ℕ,
      0 ≤ c' * Real.sqrt (n : ℝ) * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro i
    have : 0 ≤ (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹ :=
      mul_nonneg (hchoose_nonneg i) h2n_inv_nonneg
    have : 0 ≤ c' * Real.sqrt (n : ℝ) := by positivity
    positivity
  -- Build the even-indexed function
  let fe : Fin n → ℝ := fun i =>
    if i.val % 2 = 0
    then c' * Real.sqrt (n : ℝ) * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
    else 0
  let fo : Fin n → ℝ := fun i =>
    if i.val % 2 = 1
    then c' * Real.sqrt (n : ℝ) * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
    else 0
  have hfe_nonneg : ∀ i : Fin n, 0 ≤ fe i := by
    intro i
    show (if i.val % 2 = 0 then _ else 0) ≥ 0
    split_ifs with h
    · exact hnonneg i.val
    · exact le_refl 0
  have hfe_le_one : ∀ i : Fin n, fe i ≤ 1 := by
    intro i
    show (if i.val % 2 = 0 then _ else 0) ≤ 1
    split_ifs with h
    · exact hbound i.val
    · linarith
  have hfo_nonneg : ∀ i : Fin n, 0 ≤ fo i := by
    intro i
    show (if i.val % 2 = 1 then _ else 0) ≥ 0
    split_ifs with h
    · exact hnonneg i.val
    · exact le_refl 0
  have hfo_le_one : ∀ i : Fin n, fo i ≤ 1 := by
    intro i
    show (if i.val % 2 = 1 then _ else 0) ≤ 1
    split_ifs with h
    · exact hbound i.val
    · linarith
  refine ⟨⟨fe, hfe_nonneg, hfe_le_one⟩, ⟨fo, hfo_nonneg, hfo_le_one⟩, ?_, ?_⟩
  · intro i; rfl
  · intro i; rfl
