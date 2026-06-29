import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Workspace.Lemmas.BernoulliIneq

/-- Bernoulli-style upper bound:
For `0 ≤ q ≤ 1` and `s : ℕ`, we have `1 - (1 - q)^s ≤ s · q`.

This is the standard form of Bernoulli's inequality `(1 - q)^s ≥ 1 - s·q`,
rewritten as an upper bound on `1 - (1-q)^s`.

The hypothesis `q ≤ 1` is essential: for `q > 1` the inequality fails
(e.g., `q = 4, s = 3` gives `1 - (-3)^3 = 28` and `s·q = 12`).
-/
theorem bernoulli_ineq (q : ℝ) (s : ℕ) (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) :
    1 - (1 - q) ^ s ≤ (s : ℝ) * q := by
  induction s with
  | zero => simp
  | succ n ih =>
    -- (1-q)^n is in [0, 1] for q ∈ [0, 1]
    have h1mq_nonneg : (0 : ℝ) ≤ 1 - q := by linarith
    have h_pow_nonneg : (0 : ℝ) ≤ (1 - q) ^ n := pow_nonneg h1mq_nonneg n
    have h_pow_le_one : (1 - q) ^ n ≤ 1 :=
      pow_le_one₀ h1mq_nonneg (by linarith)
    -- Algebraic identity: 1 - (1-q)^(n+1) = 1 - (1-q)^n + q · (1-q)^n
    have h_step : 1 - (1 - q) ^ (n + 1) = (1 - (1 - q) ^ n) + q * (1 - q) ^ n := by ring
    rw [h_step]
    -- Bound: q · (1-q)^n ≤ q · 1 = q
    have h_tail : q * (1 - q) ^ n ≤ q := by
      calc q * (1 - q) ^ n
          ≤ q * 1 := mul_le_mul_of_nonneg_left h_pow_le_one hq_nonneg
        _ = q := mul_one q
    -- ih : 1 - (1-q)^n ≤ n * q
    -- Goal: (1 - (1-q)^n) + q * (1-q)^n ≤ (n+1) * q
    push_cast
    linarith

end Workspace.Lemmas.BernoulliIneq
