import Mathlib
import Workspace.Types.DelProb
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# EllShiftReindex

The ell-shift reindexing identity. The map `j ↦ j.val + 1` is injective on
`Fin (n/2)`, so it induces a bijection between `ℓ ⊆ Fin (n/2)` and
`σ ℓ := ℓ.image (fun j => j.val + 1) ⊆ Finset.Icc 1 (n/2)`. Consequently the
inner product

    ∏ j ∈ ℓ, α · B(j) / (1 - α · B(j))      with  B(j) = C(n, (n/4 + r + j).toNat) · 2⁻ⁿ

equals the same product reindexed over `σ ℓ`, where each factor at `j' ∈ σ ℓ`
uses the predecessor index `j' - 1`:

    ∏ j' ∈ σ ℓ, α · B'(j') / (1 - α · B'(j'))   with  B'(j') = C(n, (n/4 + r + (j'-1)).toNat) · 2⁻ⁿ.

This is the genuine "reindex ℓ by +1" content the lemma is named for, and it is a
pure reindexing equality (proved via `Finset.prod_image`), so it holds term by
term inside the outer `r`-sum.

NOTE (faithfulness fix): a previous version of this lemma claimed the LHS
`r`-sum was `≤ 8 · √δ · |altRSum …|`. That claim was removed because it is
mathematically FALSE: the LHS is a sum of NONNEGATIVE products (an O(1)
probability mass), whereas `altRSum` is an ALTERNATING sum (sign `(-1)^|r|`)
with exponential cancellation, so it is exponentially small — an O(1) nonneg
quantity cannot be bounded by `8√δ ·` (something exponentially small). The
paper (arXiv:2412.00674v1, Lemma 6) never converts to a nonneg triangle bound
and back to the alternating sum; it keeps the `(-1)^r` sign throughout. The
faithful content of this step is the reindexing bijection captured here.
-/

theorem EllShiftReindex :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : Workspace.Types.DelProb.DelProb),
      (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
    ∀ (ell : Finset (Fin (n / 2))) (zMinus zPlus : ℕ),
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let σ_ell : Finset ℕ := ell.image (fun j => j.val + 1)
      ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
          (Workspace.Types.PartialDeletionProcess.offsetWeight n r).toReal *
          (Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r zMinus).toReal *
          (Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r zPlus).toReal *
          (∏ j ∈ ell,
            α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) /
            (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)))
        =
      ∑ r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ),
          (Workspace.Types.PartialDeletionProcess.offsetWeight n r).toReal *
          (Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r zMinus).toReal *
          (Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r zPlus).toReal *
          (∏ j' ∈ σ_ell,
            α * ((Nat.choose n ((n / 4 : ℤ) + r + ((j' - 1 : ℕ) : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) /
            (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + ((j' - 1 : ℕ) : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))) := by
  intro n _ _ δ _ _ ell zMinus zPlus
  simp only
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  -- reindex the inner product over `ell` to `σ_ell = ell.image (· + 1)`
  rw [Finset.prod_image]
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    -- the predecessor index `(j.val + 1) - 1` equals `j.val`
    have hjv : (j.val + 1 - 1 : ℕ) = (j : ℕ) := by omega
    rw [hjv]
  · -- the map `j ↦ j.val + 1` is injective on `Fin (n/2)`
    intro a _ b _ hab
    simp only at hab
    have : a.val = b.val := by omega
    exact Fin.ext this
