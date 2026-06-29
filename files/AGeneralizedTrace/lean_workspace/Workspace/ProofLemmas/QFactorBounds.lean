import Mathlib
import Workspace.ProofLemmas.BinomialPmfMaxBound

open scoped BigOperators

/-!
# QFactorBounds

Discrepancy (3) of paper Lemma 6's inner alternating sum: the `Q_e`/`Q_o` marginal
factors, each a product of terms `1 - α·B` with `α = (1/(4·e²·√(2π)))·√n` and
`B = C(n,k)·2⁻ⁿ`, lie in `[0, 1]`.  Since they are per-`r` factors bounded by `1`, they
can be dropped from the magnitude of each alternating-sum summand (Q ≤ 1) while keeping
nonnegativity (Q ≥ 0).
-/

namespace Workspace.ProofLemmas.QFactorBounds

/-- `α · B ≤ 1` for `α = (1/(4·e²·√(2π)))·√n` and `B = C(n,k)·2⁻ⁿ`.  (Mirror of the
private `alphaB_le_one` in `PerSummandBoundLengthsDiff`, exposed here for reuse.) -/
lemma alphaB_le_one (n : ℕ) (hn1 : 1 ≤ n) (k : ℕ) :
    (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
        ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1 := by
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hsqrt2pi : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hdenpos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hc'pos : (0 : ℝ) < c' := by rw [hc']; positivity
  have hB : ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
    BinomialPmfMaxBound n hn1 k
  have hcoef_nn : (0 : ℝ) ≤ c' * Real.sqrt n := by positivity
  have hstep : c' * Real.sqrt n * ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹)
      ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hB hcoef_nn
  refine le_trans hstep ?_
  have hmul : Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = Real.sqrt (2 / Real.pi) := by
    rw [← Real.sqrt_mul (le_of_lt hnpos)]
    congr 1
    field_simp
  have hrew : c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n))
      = c' * Real.sqrt (2 / Real.pi) := by
    rw [mul_assoc, hmul]
  rw [hrew, hc', one_div, inv_mul_le_iff₀ hdenpos, mul_one]
  have h1 : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_one hpi]; linarith [Real.pi_gt_d2]
  have h2 : (1 : ℝ) ≤ 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
    have he : (1 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_d2]
    nlinarith [hs, he, Real.exp_pos 2, hsqrt2pi]
  linarith [h1, h2]

variable {n : ℕ}

/-- Each marginal factor `1 - α·B` lies in `[0,1]`. -/
lemma factor_mem (hn1 : 1 ≤ n) (α : ℝ)
    (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) (k : ℕ) :
    0 ≤ 1 - α * ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ∧
      1 - α * ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1 := by
  subst hα
  have hle := alphaB_le_one n hn1 k
  have hnn : (0 : ℝ) ≤ (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
      ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) := by positivity
  constructor <;> linarith

/-- **Q ∈ [0,1].**  Any finite product `∏_{j ∈ s} (1 - α·B(g j))` with `α` the
witness scaling parameter is nonnegative and at most `1`. -/
lemma Q_mem_unitInterval (hn1 : 1 ≤ n) (α : ℝ)
    (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
    {ι : Type*} (s : Finset ι) (g : ι → ℕ) :
    0 ≤ ∏ j ∈ s, (1 - α * ((Nat.choose n (g j) : ℝ) * (2 ^ n : ℝ)⁻¹)) ∧
      ∏ j ∈ s, (1 - α * ((Nat.choose n (g j) : ℝ) * (2 ^ n : ℝ)⁻¹)) ≤ 1 := by
  constructor
  · apply Finset.prod_nonneg
    intro j _
    exact (factor_mem hn1 α hα (g j)).1
  · apply Finset.prod_le_one
    · intro j _; exact (factor_mem hn1 α hα (g j)).1
    · intro j _; exact (factor_mem hn1 α hα (g j)).2

end Workspace.ProofLemmas.QFactorBounds
