import Mathlib

open scoped BigOperators

namespace Workspace.Types.LqNorm

/-- The `L_q` norm of a vector `x : Fin d → ℝ`, defined directly via
`Real.rpow`:
`lqNorm q x = (∑ j, |x j| ^ q) ^ (1/q)`.

We avoid `PiLp` / `EuclideanSpace` so the formula textually matches the
paper. The dimension `d` is implicit; the function is total in `q : ℝ`,
but the meaningful basic properties (non-negativity, scaling by a real)
are stated with `1 ≤ q` as required. -/
noncomputable def lqNorm (q : ℝ) {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  (∑ j, |x j| ^ q) ^ ((1 : ℝ) / q)

/-- The inner sum `∑ j, |x j| ^ q` is non-negative. -/
lemma sum_abs_rpow_nonneg (q : ℝ) {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ ∑ j, |x j| ^ q :=
  Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) q)

/-- `lqNorm q x` is non-negative for any real `q` (since the inner sum
is non-negative and `Real.rpow` of a non-negative base is non-negative). -/
lemma lqNorm_nonneg' (q : ℝ) {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ lqNorm q x :=
  Real.rpow_nonneg (sum_abs_rpow_nonneg q x) _

/-- Spec-named non-negativity (with the `1 ≤ q` hypothesis). -/
lemma lqNorm_nonneg {q : ℝ} (_hq : 1 ≤ q) {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ lqNorm q x :=
  lqNorm_nonneg' q x

/-- The L_q norm of the zero vector is 0. We use `Real.zero_rpow` and
the fact that `∑ j, |0|^q = 0`. -/
lemma lqNorm_zero {q : ℝ} (hq : 1 ≤ q) {d : ℕ} :
    lqNorm q (fun _ : Fin d => (0 : ℝ)) = 0 := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_ne : (1 : ℝ) / q ≠ 0 := by
    rw [one_div]; exact inv_ne_zero hq_ne
  unfold lqNorm
  have hsum : (∑ _j : Fin d, |(0 : ℝ)| ^ q) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [abs_zero, Real.zero_rpow hq_ne]
  rw [hsum, Real.zero_rpow h_inv_ne]

/-- The L_1 norm is the sum of absolute values. -/
lemma lqNorm_one_eq_sum_abs {d : ℕ} (x : Fin d → ℝ) :
    lqNorm 1 x = ∑ j, |x j| := by
  unfold lqNorm
  simp [Real.rpow_one]

/-- Scaling by a real `c`: `lqNorm q (c • x) = |c| * lqNorm q x`. -/
lemma lqNorm_smul {q : ℝ} (hq : 1 ≤ q) {d : ℕ} (c : ℝ) (x : Fin d → ℝ) :
    lqNorm q (fun j => c * x j) = |c| * lqNorm q x := by
  unfold lqNorm
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  -- Step 1: |c * x j| ^ q = |c|^q * |x j|^q, then factor the sum
  have h1 : (∑ j, |c * x j| ^ q) = |c| ^ q * ∑ j, |x j| ^ q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [h1]
  -- Step 2: distribute the outer rpow over the product
  have hcq_nn : 0 ≤ |c| ^ q := Real.rpow_nonneg (abs_nonneg _) q
  have hsum_nn : 0 ≤ ∑ j, |x j| ^ q := sum_abs_rpow_nonneg q x
  rw [Real.mul_rpow hcq_nn hsum_nn]
  -- Step 3: (|c|^q)^(1/q) = |c|, since q * (1/q) = 1 and |c| ≥ 0.
  have habs_nn : (0 : ℝ) ≤ |c| := abs_nonneg _
  have h2 : (|c| ^ q) ^ ((1 : ℝ) / q) = |c| := by
    rw [← Real.rpow_mul habs_nn, mul_one_div, div_self hq_ne, Real.rpow_one]
  rw [h2]

/-- (Optional, sanity) `lqNorm q` on a 1-dimensional vector is `|x 0|`. -/
lemma lqNorm_dim_one {q : ℝ} (hq : 1 ≤ q) (x : Fin 1 → ℝ) :
    lqNorm q x = |x 0| := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  unfold lqNorm
  rw [Fin.sum_univ_one]
  rw [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self hq_ne, Real.rpow_one]

/-- (Optional, sanity) `lqNorm q` on a 0-dimensional vector is `0`. -/
lemma lqNorm_dim_zero {q : ℝ} (hq : 1 ≤ q) (x : Fin 0 → ℝ) :
    lqNorm q x = 0 := by
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have h_inv_ne : (1 : ℝ) / q ≠ 0 := by
    rw [one_div]; exact inv_ne_zero hq_ne
  unfold lqNorm
  have : (∑ j : Fin 0, |x j| ^ q) = 0 := by
    rw [Fin.sum_univ_zero]
  rw [this, Real.zero_rpow h_inv_ne]

end Workspace.Types.LqNorm
