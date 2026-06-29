import Mathlib
import Workspace.PriorWork.ConvolutionTheoremDiscrete

open scoped Real Complex

set_option maxHeartbeats 4000000

namespace KFoldConvolutionTheorem

/-- Discrete Fourier transform on `ℤ` of a function `f : ℤ → ℂ`. -/
noncomputable def FT (f : ℤ → ℂ) (ξ : ℝ) : ℂ :=
  ∑' n : ℤ, f n * Complex.exp (-(Complex.I * (ξ : ℂ) * (n : ℂ)))

/-- Circular convolution on `ℝ/(2πℤ)` of two functions `F G : ℝ → ℂ`. -/
noncomputable def circConv (F G : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ η in (-Real.pi)..Real.pi, F η * G (ξ - η)

/-- Partial product of the first `k` factors of `f : ℕ → (ℤ → ℂ)`, evaluated at `n`. -/
noncomputable def partialProd (f : ℕ → (ℤ → ℂ)) (k : ℕ) (n : ℤ) : ℂ :=
  ∏ j ∈ Finset.range k, f j n

/-- `k`-fold circular convolution of the Fourier transforms `FT (f 0), …, FT (f (k-1))`.
For `k = 0` it is the constant `0` (a placeholder; the theorem only speaks of `k ≥ 1`).
For `k = 1` it is `FT (f 0)`.  The recurrence builds it as
`kConv (k+1) = circConv (kConv k) (FT (f k))`. -/
noncomputable def kConv (f : ℕ → (ℤ → ℂ)) : ℕ → ℝ → ℂ
  | 0 => fun _ => 0
  | 1 => FT (f 0)
  | (k + 2) => fun ξ => circConv (kConv f (k + 1)) (FT (f (k + 1))) ξ

@[simp] lemma kConv_one (f : ℕ → (ℤ → ℂ)) : kConv f 1 = FT (f 0) := rfl

lemma kConv_succ_succ (f : ℕ → (ℤ → ℂ)) (k : ℕ) :
    kConv f (k + 2) = fun ξ => circConv (kConv f (k + 1)) (FT (f (k + 1))) ξ := rfl

/-- `partialProd f 1 = f 0`. -/
lemma partialProd_one (f : ℕ → (ℤ → ℂ)) : partialProd f 1 = f 0 := by
  funext n
  simp [partialProd]

/-- The partial product satisfies `partialProd f (k+1) n = partialProd f k n * f k n`. -/
lemma partialProd_succ (f : ℕ → (ℤ → ℂ)) (k : ℕ) (n : ℤ) :
    partialProd f (k + 1) n = partialProd f k n * f k n := by
  simp [partialProd, Finset.prod_range_succ]

/--
**`k`-fold discrete convolution theorem.**

Let `f : ℕ → (ℤ → ℂ)` be a sequence of functions on `ℤ`.  Suppose:
* every individual factor `f j` (for `j < k`) is in `ℓ¹(ℤ)`, and
* every NON-EMPTY partial product `partialProd f m` (for `1 ≤ m ≤ k`) is in `ℓ¹(ℤ)`.

The summability hypothesis on the partial product is only required for `m ≥ 1`:
the empty partial product `partialProd f 0 = (fun _ => 1)` is the constant `1`,
which is NOT summable on `ℤ`, and is never needed by the recursion (whose base
case is at one factor, `m = 1`).

Then the discrete Fourier transform of the `k`-fold pointwise product equals the
`k`-fold circular convolution of the individual Fourier transforms:

  `FT (partialProd f k) ξ = kConv f k ξ`   for every `ξ : ℝ`,  whenever `1 ≤ k`.

The proof is by induction on `k`.  The base case `k = 1` is definitional
(`partialProd f 1 = f 0` and `kConv f 1 = FT (f 0)`).  The inductive step writes
`partialProd f (k+1) = partialProd f k · f k`, applies the pairwise
`ConvolutionTheoremDiscrete` with the two `ℓ¹` factors `partialProd f k` and
`f k`, and rewrites the resulting circular convolution using the induction
hypothesis `FT (partialProd f k) = kConv f k`.
-/
theorem kFoldConvolutionTheorem
    (f : ℕ → (ℤ → ℂ))
    (hf_sum : ∀ j : ℕ, Summable (fun n : ℤ => ‖f j n‖))
    (hpp_sum : ∀ m : ℕ, 1 ≤ m → Summable (fun n : ℤ => ‖partialProd f m n‖)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ ξ : ℝ, FT (partialProd f k) ξ = kConv f k ξ := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (by norm_num)
  | succ k ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0: target is `FT (partialProd f 1) ξ = kConv f 1 ξ`.
      subst hk0
      rw [partialProd_one, kConv_one]
    · -- k ≥ 1: inductive step. Write k = k'+1 so that k+1 = k'+2.
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hkpos)
      have ih' : ∀ η : ℝ, FT (partialProd f (k' + 1)) η = kConv f (k' + 1) η := ih hkpos
      -- Apply ConvolutionTheoremDiscrete to F := partialProd f (k'+1), G := f (k'+1).
      have hconv := ConvolutionTheoremDiscrete (partialProd f (k' + 1)) (f (k' + 1))
        (hpp_sum (k' + 1) (by omega)) (hf_sum (k' + 1)) ξ
      -- hconv :
      --   ∑' n, (partialProd f k n * f k n) * exp(-iξn)
      --     = (1/2π) ∫_{-π}^{π} (∑' n, partialProd f k n * exp(-iηn))
      --                        * (∑' n, f k n * exp(-i(ξ-η)n))
      -- Unfold FT on the LHS and match it.
      have hLHS : FT (partialProd f (k' + 1 + 1)) ξ
          = ∑' n : ℤ, (partialProd f (k' + 1) n * f (k' + 1) n)
              * Complex.exp (-(Complex.I * (ξ : ℂ) * (n : ℂ))) := by
        rw [FT]
        apply tsum_congr
        intro n
        rw [partialProd_succ]
      rw [hLHS, hconv]
      -- Now the RHS is the circular convolution circConv (FT (partialProd f (k'+1))) (FT (f (k'+1))) ξ,
      -- with FT (partialProd f (k'+1)) rewritten via ih'.
      rw [kConv_succ_succ]
      simp only
      rw [circConv]
      -- Match the two integrals: the integrand sums ARE FT (...) η and FT (f k) (ξ-η).
      congr 1
      apply intervalIntegral.integral_congr
      intro η _
      simp only
      -- LHS factor 1: ∑' n, partialProd f (k'+1) n * exp(-iηn) = kConv f (k'+1) η
      have hfac1 : (∑' n : ℤ, partialProd f (k' + 1) n
          * Complex.exp (-(Complex.I * (η : ℂ) * (n : ℂ)))) = kConv f (k' + 1) η := by
        rw [← ih']
        rw [FT]
      -- LHS factor 2: ∑' n, f (k'+1) n * exp(-i(ξ-η)n) = FT (f (k'+1)) (ξ-η)
      have hfac2 : (∑' n : ℤ, f (k' + 1) n
          * Complex.exp (-(Complex.I * ((ξ : ℂ) - (η : ℂ)) * (n : ℂ)))) = FT (f (k' + 1)) (ξ - η) := by
        rw [FT]
        apply tsum_congr
        intro n
        push_cast
        ring_nf
      rw [hfac1, hfac2]

end KFoldConvolutionTheorem
