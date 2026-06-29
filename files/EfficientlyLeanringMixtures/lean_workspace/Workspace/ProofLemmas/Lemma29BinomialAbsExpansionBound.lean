import Mathlib

namespace Workspace.ProofLemmas

/--
Elementary expansion bound: for every `μ, u : ℝ` and every `i : ℕ`,

  `|u + μ|^i ≤ 2^i * (|u|^i + |μ|^i)`.
-/
theorem Lemma29BinomialAbsExpansionBound :
    ∀ (μ u : ℝ) (i : ℕ), |u + μ| ^ i ≤ (2 : ℝ) ^ i * (|u| ^ i + |μ| ^ i) := by
  intro μ u i
  -- Step 1: |u + μ| ≤ |u| + |μ|
  have h1 : |u + μ| ≤ |u| + |μ| := abs_add_le u μ
  have habsu : (0 : ℝ) ≤ |u| := abs_nonneg u
  have habsμ : (0 : ℝ) ≤ |μ| := abs_nonneg μ
  have habsum : (0 : ℝ) ≤ |u + μ| := abs_nonneg _
  -- Step 2: |u + μ|^i ≤ (|u| + |μ|)^i
  have h2 : |u + μ| ^ i ≤ (|u| + |μ|) ^ i := by
    exact pow_le_pow_left₀ habsum h1 i
  -- Step 3: (|u| + |μ|)^i ≤ 2^(i-1) * (|u|^i + |μ|^i) ≤ 2^i * (|u|^i + |μ|^i)
  have h3 : (|u| + |μ|) ^ i ≤ (2 : ℝ) ^ (i - 1) * (|u| ^ i + |μ| ^ i) :=
    add_pow_le habsu habsμ i
  have h4 : (2 : ℝ) ^ (i - 1) ≤ (2 : ℝ) ^ i := by
    apply pow_le_pow_right₀
    · norm_num
    · exact Nat.sub_le i 1
  have hsum_nonneg : (0 : ℝ) ≤ |u| ^ i + |μ| ^ i := by
    have : (0 : ℝ) ≤ |u| ^ i := pow_nonneg habsu i
    have : (0 : ℝ) ≤ |μ| ^ i := pow_nonneg habsμ i
    positivity
  have h5 : (2 : ℝ) ^ (i - 1) * (|u| ^ i + |μ| ^ i) ≤ (2 : ℝ) ^ i * (|u| ^ i + |μ| ^ i) :=
    mul_le_mul_of_nonneg_right h4 hsum_nonneg
  calc |u + μ| ^ i
      ≤ (|u| + |μ|) ^ i := h2
    _ ≤ (2 : ℝ) ^ (i - 1) * (|u| ^ i + |μ| ^ i) := h3
    _ ≤ (2 : ℝ) ^ i * (|u| ^ i + |μ| ^ i) := h5

end Workspace.ProofLemmas
