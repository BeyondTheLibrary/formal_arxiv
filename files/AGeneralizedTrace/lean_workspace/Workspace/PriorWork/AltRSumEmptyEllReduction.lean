-- Supporting (SORRY-FREE) lemmas for the k = 0 / empty-ℓ case of Lemma 8
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, line 381, k = 0).
--
-- These lemmas implement Step 1 of the plan for de-axiomatizing
-- `AltRSumFourierBoundEmpty`: with ℓ = ∅, the `ellFactor` product is empty
-- (= 1), so the inner term `Fterm n δ α r z₋ z₊ ∅` collapses to a product of
-- exactly three binomial factors, and `altRSum n δ α z₋ z₊ ∅` becomes a finite
-- alternating Fourier-style sum over r ∈ Icc (-(n/4)) (n/4) of
-- (-1)^|r| · (three binomial factors). This is exactly the discrete Fourier
-- transform (at ξ = π, via (-1)^r = e^{iπr}) of a pointwise product of three
-- binomial PMFs — the starting point of the convolution argument.
--
-- These are real, sorry-free reductions. They do NOT prove the full Fourier
-- convolution bound (that requires the 3-fold circular convolution assembly,
-- region split, and integral bounds — see the report).
import Mathlib
import Workspace.Types.AlternatingSumExpression

namespace Workspace.PriorWork.AltRSumEmptyEllReduction

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression

/-- The `ellFactor` product over the empty set is `1`. -/
theorem ellFactor_prod_empty (n : ℕ) (α : ℝ) (r : ℤ) :
    (∏ j ∈ (∅ : Finset ℕ), ellFactor n α r j) = 1 := by
  simp

/-- **Empty-ℓ collapse of `Fterm`.** With `ℓ = ∅`, the inner term reduces to the
product of exactly the three binomial factors (the `ellFactor` product is `1`). -/
theorem Fterm_empty (n : ℕ) (δ α : ℝ) (r : ℤ) (zMinus zPlus : ℕ) :
    Fterm n δ α r zMinus zPlus ∅
      = binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus := by
  unfold Fterm
  rw [Finset.prod_empty, mul_one]

/-- **Empty-ℓ reduction of `altRSum`.** With `ℓ = ∅`, the alternating r-sum is a
finite alternating sum over `r ∈ Icc (-(n/4)) (n/4)` of `(-1)^|r|` times the
product of the three binomial factors. This is the finite Fourier sum (at
`ξ = π`, since `(-1)^r = e^{iπr}`) of a product of three binomial PMFs. -/
theorem altRSum_empty (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) :
    altRSum n δ α zMinus zPlus ∅
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          (-1 : ℝ) ^ r.natAbs *
            (binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
  unfold altRSum
  apply Finset.sum_congr rfl
  intro r _
  rw [Fterm_empty]

/-- **Sign-encoding identity (real form), `(-1)^|r|` as a `zpow`.** For an
integer `r`, the natural-number power `(-1)^r.natAbs` equals the integer power
`(-1)^r`. This is the real shadow of the identity `(-1)^r = e^{iπr}` used at
`ξ = π`: it lets the alternating sign in `altRSum` be absorbed into a phase. -/
theorem neg_one_natAbs_eq_zpow (r : ℤ) :
    (-1 : ℝ) ^ r.natAbs = ((-1 : ℝ) ^ r) := by
  rcases Int.even_or_odd r with h | h
  · rw [Even.neg_one_pow (Int.natAbs_even.mpr h), Even.neg_one_zpow h]
  · rw [Odd.neg_one_pow (Odd.natAbs h), Odd.neg_one_zpow h]

/-- **Sign-encoding identity (real, cosine form).** `(-1)^|r| = cos(π · r)`.
This is the real part of `e^{iπr} = (-1)^r`; it is the exact bridge that turns
the alternating r-sum (with sign `(-1)^|r|`) into a Fourier transform evaluated
at `ξ = π`. -/
theorem neg_one_natAbs_eq_cos_pi_mul (r : ℤ) :
    (-1 : ℝ) ^ r.natAbs = Real.cos ((r : ℝ) * Real.pi) := by
  rw [neg_one_natAbs_eq_zpow, Real.cos_int_mul_pi r]

/-- **`altRSum(∅)` as a real Fourier-style sum at `ξ = π`.** Combining
`altRSum_empty` with the sign-encoding identity, the empty-ℓ alternating r-sum is
`∑_r cos(π r) · (three binomial factors)`. This is the explicit real form of the
ξ = π Fourier transform of the product of the three binomial PMFs — the object
the convolution argument bounds. -/
theorem altRSum_empty_cos (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) :
    altRSum n δ α zMinus zPlus ∅
      = ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          Real.cos ((r : ℝ) * Real.pi) *
            (binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
  rw [altRSum_empty]
  apply Finset.sum_congr rfl
  intro r _
  rw [neg_one_natAbs_eq_cos_pi_mul]

/-- Nonnegativity of `binPMF` for a probability `p ∈ [0,1]`. -/
theorem binPMF_nonneg (m k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMF m p k := by
  unfold binPMF
  split_ifs with h
  · refine mul_nonneg (mul_nonneg ?_ (pow_nonneg hp _)) (pow_nonneg (by linarith) _)
    exact_mod_cast Nat.zero_le _
  · exact le_refl 0

/-- Nonnegativity of `binPMFInt` for a probability `p ∈ [0,1]`. -/
theorem binPMFInt_nonneg (m : ℕ) (p : ℝ) (k : ℤ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMFInt m p k := by
  unfold binPMFInt
  split_ifs with h
  · exact binPMF_nonneg m k.toNat p hp hp1
  · exact le_refl 0

/-- **Nonnegativity of the three-factor product** appearing in the empty-ℓ
reduction of `altRSum`, for `0 ≤ δ ≤ 1` (so both `1/2` and `1-δ` are valid
probabilities). -/
theorem threeFactor_nonneg (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (r : ℤ) (zMinus zPlus : ℕ) :
    0 ≤ binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus := by
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact binPMFInt_nonneg (n / 2) (1 / 2) _ (by norm_num) (by norm_num)
  · exact binPMFInt_nonneg _ (1 - δ) _ (by linarith) (by linarith)
  · exact binPMFInt_nonneg _ (1 - δ) _ (by linarith) (by linarith)

/-- **Triangle (L¹) bound for the empty-ℓ alternating r-sum.** Since
`|cos(π r)| ≤ 1` and the three binomial factors are nonnegative (for
`0 ≤ δ ≤ 1`), the magnitude of `altRSum n δ α z₋ z₊ ∅` is at most the sum,
over `r`, of the three-factor products (with the alternating sign and the
phase `cos(π r)` dropped). This is the standard first step of the
Fourier-convolution magnitude argument: bound `|∑_r e^{iπr} g(r)|` by the
ℓ¹ norm `∑_r |g(r)|` of the summand, here `g(r) = T₁(r)·T₂(r)·T₃(r) ≥ 0`. -/
theorem altRSum_empty_abs_le_l1 (n : ℕ) (δ α : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (zMinus zPlus : ℕ) :
    |altRSum n δ α zMinus zPlus ∅|
      ≤ ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          (binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
  rw [altRSum_empty_cos]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro r _
  rw [abs_mul]
  have hg := threeFactor_nonneg n δ hδ0 hδ1 r zMinus zPlus
  rw [abs_of_nonneg hg]
  have hcos : |Real.cos ((r : ℝ) * Real.pi)| ≤ 1 := Real.abs_cos_le_one _
  calc |Real.cos ((r : ℝ) * Real.pi)| * _
      ≤ 1 * _ := by
        apply mul_le_mul_of_nonneg_right hcos hg
    _ = _ := one_mul _

/-! ### ℓ¹ / summability of the three-factor product in `r`

The following are sorry-free prerequisites for the Fourier-convolution route to
`AltRSumFourierBoundEmpty`: the three-factor product, viewed as a function of
`r : ℤ`, has FINITE support (it vanishes unless the first binomial factor
`Bin(n/2, 1/2, r + n/4)` is on its support `0 ≤ r + n/4 ≤ n/2`), hence is summable
in absolute value over `ℤ`. This is exactly the ℓ¹ hypothesis consumed by the
discrete convolution theorem (`ConvolutionTheoremDiscrete`) and the fixed
`KFoldConvolutionTheorem` (whose `hpp_sum` summability hypothesis is required
only for non-empty partial products, `m ≥ 1`). -/

/-- `binPMFInt n p k = 0` whenever `k` is outside the support `{0, …, n}`. -/
theorem binPMFInt_off_support (n : ℕ) (p : ℝ) (k : ℤ)
    (h : ¬ (0 ≤ k ∧ k ≤ (n : ℤ))) : binPMFInt n p k = 0 := by
  unfold binPMFInt
  rw [if_neg h]

/-- The three-factor product appearing in the empty-ℓ reduction, as a function
of `r : ℤ` (for fixed `n, δ, z₋, z₊`). -/
noncomputable def threeFactor (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) (r : ℤ) : ℝ :=
  binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus

/-- The three-factor product vanishes off `Finset.Icc (-(n/4)) (n/2 - n/4)`,
because its FIRST factor `Bin(n/2, 1/2, r + n/4)` is supported on
`0 ≤ r + n/4 ≤ n/2`. -/
theorem threeFactor_off_Icc_zero (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    ∀ r : ℤ, r ∉ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4) →
      threeFactor n δ zMinus zPlus r = 0 := by
  intro r hr
  rw [Finset.mem_Icc, not_and_or] at hr
  unfold threeFactor
  rw [binPMFInt_off_support (n / 2) (1 / 2) (r + (n / 4 : ℤ)) ?_, zero_mul, zero_mul]
  rintro ⟨h1, h2⟩
  rcases hr with hlo | hhi
  · omega
  · omega

/-- **ℓ¹ summability of the three-factor product (ℝ).** The three-factor product
`r ↦ T₁(r)·T₂(r)·T₃(r)` is summable in absolute value over `ℤ` (finite support). -/
theorem threeFactor_summable (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (fun r : ℤ => ‖threeFactor n δ zMinus zPlus r‖) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4))
  intro b hb
  rw [threeFactor_off_Icc_zero n δ zMinus zPlus b hb, norm_zero]

/-- The plain (non-`norm`) summability of the three-factor product over `ℤ`. -/
theorem threeFactor_summable' (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (threeFactor n δ zMinus zPlus) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 2 - (n : ℤ) / 4))
  intro b hb
  exact threeFactor_off_Icc_zero n δ zMinus zPlus b hb

/-- The ℂ-cast of the three-factor product is summable in absolute value over `ℤ`
(the form the discrete Fourier convolution theorem consumes). -/
theorem threeFactor_summable_complex (n : ℕ) (δ : ℝ) (zMinus zPlus : ℕ) :
    Summable (fun r : ℤ => ‖((threeFactor n δ zMinus zPlus r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((threeFactor n δ zMinus zPlus r : ℝ) : ℂ)‖)
      = (fun r : ℤ => ‖threeFactor n δ zMinus zPlus r‖) := by
    funext r; rw [Complex.norm_real]
  rw [h]
  exact threeFactor_summable n δ zMinus zPlus

end Workspace.PriorWork.AltRSumEmptyEllReduction
