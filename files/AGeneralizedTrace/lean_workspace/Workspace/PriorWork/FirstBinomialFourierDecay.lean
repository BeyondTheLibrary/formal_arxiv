-- First-binomial Fourier decay facts for Lemma 8
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, line 375).
--
-- The first binomial factor in the deletion process has Fourier transform with
-- magnitude `|cos(ξ/2)|^m` (this is the modulus of `BinomialFourierClosedForm`,
-- since `|exp(-iξm/2)| = 1`). These standalone real lemmas give the trivial bound
-- and the off-axis exponential decay of `|cos(ξ/2)|^m` on `1/3 ≤ |ξ| ≤ π`.
import Mathlib

set_option maxHeartbeats 1000000

/-- Numeric helper: `cos (1/6) ≤ 1 - 1/73` (i.e. `1 - cos(1/6) ≥ 1/73 ≈ 0.0137`).
Proved from the Taylor remainder bound `Real.cos_bound`. -/
theorem cos_sixth_le : Real.cos (1 / 6) ≤ 1 - 1 / 73 := by
  have h := Real.cos_bound (x := (1 / 6 : ℝ)) (by rw [abs_of_pos] <;> norm_num)
  rw [abs_le] at h
  nlinarith [h.1, h.2]

/--
**(1a) Trivial magnitude bound.** For every `m`, `|cos(ξ/2)|^m ≤ 1`.
This is the modulus of the first-binomial Fourier transform, bounded by `1`.
-/
theorem firstBinomial_abs_cos_pow_le_one (ξ : ℝ) (m : ℕ) :
    |Real.cos (ξ / 2)| ^ m ≤ 1 := by
  apply pow_le_one₀ (abs_nonneg _)
  exact Real.abs_cos_le_one _

/--
**(1b) Off-axis pointwise bound.** For `1/3 ≤ |ξ| ≤ π`,
`|cos(ξ/2)| ≤ 1 - 1/73`. Here `|ξ|/2 ∈ [1/6, π/2]`, where `cos` is nonnegative
and decreasing, so `|cos(ξ/2)| = cos(|ξ|/2) ≤ cos(1/6) ≤ 1 - 1/73`.
-/
theorem firstBinomial_abs_cos_le (ξ : ℝ) (hξ : 1 / 3 ≤ |ξ|) (hξπ : |ξ| ≤ Real.pi) :
    |Real.cos (ξ / 2)| ≤ 1 - 1 / 73 := by
  -- |ξ|/2 ∈ [1/6, π/2]
  have hlo : (1 : ℝ) / 6 ≤ |ξ| / 2 := by linarith
  have hhi : |ξ| / 2 ≤ Real.pi / 2 := by linarith
  -- cos is nonnegative on [-π/2, π/2], in particular at |ξ|/2
  have hcos_nonneg : 0 ≤ Real.cos (|ξ| / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hhi
  -- |cos(ξ/2)| = cos(|ξ|/2)
  have hcos_even : Real.cos (ξ / 2) = Real.cos (|ξ| / 2) := by
    rw [← Real.cos_abs (ξ / 2), abs_div, Nat.abs_ofNat]
  have habs : |Real.cos (ξ / 2)| = Real.cos (|ξ| / 2) := by
    rw [hcos_even, abs_of_nonneg hcos_nonneg]
  rw [habs]
  -- cos decreasing on [1/6, π/2]: cos(|ξ|/2) ≤ cos(1/6)
  have hmono : Real.cos (|ξ| / 2) ≤ Real.cos (1 / 6) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_pos]) hlo
  exact le_trans hmono cos_sixth_le

/--
**(1c) Off-axis exponential decay.** For `1/3 ≤ |ξ| ≤ π` and any `m`,
`|cos(ξ/2)|^m ≤ exp(- m / 73)`. The explicit decay constant is `c = 1/73`.
Derived from `|cos(ξ/2)| ≤ 1 - 1/73 ≤ exp(-1/73)`, raised to the `m`-th power.
-/
theorem firstBinomial_abs_cos_pow_decay (ξ : ℝ) (m : ℕ)
    (hξ : 1 / 3 ≤ |ξ|) (hξπ : |ξ| ≤ Real.pi) :
    |Real.cos (ξ / 2)| ^ m ≤ Real.exp (- (m : ℝ) / 73) := by
  have hbase : |Real.cos (ξ / 2)| ≤ Real.exp (- (1 : ℝ) / 73) := by
    have h1 : |Real.cos (ξ / 2)| ≤ 1 - 1 / 73 := firstBinomial_abs_cos_le ξ hξ hξπ
    have h2 : (1 : ℝ) - 1 / 73 ≤ Real.exp (- (1 : ℝ) / 73) := by
      have := Real.add_one_le_exp (- (1 : ℝ) / 73)
      linarith
    exact le_trans h1 h2
  calc |Real.cos (ξ / 2)| ^ m
      ≤ (Real.exp (- (1 : ℝ) / 73)) ^ m := by
        apply pow_le_pow_left₀ (abs_nonneg _) hbase
    _ = Real.exp (- (m : ℝ) / 73) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
