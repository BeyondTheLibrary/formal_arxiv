import Mathlib

/-!
# From a polynomial bound on the `i`-th prime `≡ 1 (mod 3)` to the `O(ℓ log ℓ)` log-sum

Reduction of the `PrimesOneModThreeLogSum` estimate (PNT in arithmetic progressions) to the
much smaller quantitative bound `Workspace.ProofLemmas.PrimesOneModThreePolyBound`
("the `i`-th prime `≡ 1 (mod 3)` is at most `(i+2)^A` for some absolute `A`").

Given that bound, `∑_{i < ℓ} log pᵢ ≤ ℓ · A · log(ℓ+1) ≤ 2A · ℓ log ℓ` for `ℓ ≥ 2`, using
`ℓ + 1 ≤ ℓ²`.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PrimesOneModThreeReduction

/-- The predicate "prime and `≡ 1 (mod 3)`". -/
abbrev POne : ℕ → Prop := fun n => n.Prime ∧ n % 3 = 1

/-- **Reduction.**  A polynomial bound on the `i`-th prime `≡ 1 (mod 3)` gives the
`O(ℓ log ℓ)` bound on the sum of the logarithms of the first `ℓ` of them. -/
theorem logSum_le_of_poly_bound
    (A : ℕ) (hA : 0 < A) (hbd : ∀ i : ℕ, Nat.nth POne i ≤ (i + 2) ^ A) :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth POne i : ℝ)))
        ≤ (2 * A : ℝ) * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  intro ℓ hℓ
  have hℓR : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hlogℓ : (0 : ℝ) < Real.log (ℓ : ℝ) := Real.log_pos (by linarith)
  -- each term is at most `A * log (ℓ + 1)`
  have hterm : ∀ i ∈ Finset.range ℓ,
      Real.log ((Nat.nth POne i : ℝ)) ≤ (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ((Nat.nth POne i : ℕ) : ℝ) ≤ (((i + 2) ^ A : ℕ) : ℝ) := by
      exact_mod_cast hbd i
    have h2 : (((i + 2) ^ A : ℕ) : ℝ) ≤ (((ℓ : ℝ) + 1)) ^ A := by
      push_cast
      have : ((i : ℝ) + 2) ≤ (ℓ : ℝ) + 1 := by
        have : (i : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
        linarith
      gcongr
    have h3 : ((Nat.nth POne i : ℕ) : ℝ) ≤ ((ℓ : ℝ) + 1) ^ A := le_trans h1 h2
    calc Real.log ((Nat.nth POne i : ℝ))
        ≤ Real.log (((ℓ : ℝ) + 1) ^ A) := by
          rcases eq_or_lt_of_le (Nat.cast_nonneg (Nat.nth POne i) : (0:ℝ) ≤ _) with h0 | h0
          · rw [← h0, Real.log_zero]
            have : (0 : ℝ) ≤ Real.log (((ℓ : ℝ) + 1) ^ A) := by
              apply Real.log_nonneg
              have : (1 : ℝ) ≤ (ℓ : ℝ) + 1 := by linarith
              exact one_le_pow₀ this
            exact this
          · exact Real.log_le_log h0 h3
      _ = (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := by
          rw [Real.log_pow]
  -- and `log (ℓ + 1) ≤ 2 log ℓ` for `ℓ ≥ 2`
  have hlog2 : Real.log ((ℓ : ℝ) + 1) ≤ 2 * Real.log (ℓ : ℝ) := by
    have h1 : (ℓ : ℝ) + 1 ≤ (ℓ : ℝ) ^ 2 := by nlinarith
    calc Real.log ((ℓ : ℝ) + 1) ≤ Real.log ((ℓ : ℝ) ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log (ℓ : ℝ) := by rw [Real.log_pow]; push_cast; ring
  calc (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth POne i : ℝ)))
      ≤ ∑ _i ∈ Finset.range ℓ, (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := Finset.sum_le_sum hterm
    _ = (ℓ : ℝ) * ((A : ℝ) * Real.log ((ℓ : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (ℓ : ℝ) * ((A : ℝ) * (2 * Real.log (ℓ : ℝ))) := by
        have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
        have hl0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
        gcongr
    _ = (2 * A : ℝ) * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by ring

end Workspace.ProofLemmas.PrimesOneModThreeReduction
