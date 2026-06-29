import Mathlib

theorem SublemmaBinomialCoefficientBound :
    ∀ i j k : ℕ, i ≤ j → j ≤ k → Nat.choose j i ≤ 2 ^ k := by
  intro i j k _hij hjk
  calc Nat.choose j i ≤ 2 ^ j := Nat.choose_le_two_pow j i
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
