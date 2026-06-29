import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.KwayFactorSummable
import Workspace.ProofLemmas.PerFactorFourierModulus
import Workspace.ProofLemmas.FTConvPow

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Per-factor FT = geometric series of FT of binomial-atom powers (Lemma 7, step G4)

This file performs the **FT / tsum Fubini interchange** for a single Lemma-7
factor (arXiv:2412.00674v1, lines 320-334, step G4). The per-point geometric
expansion is already proved (`PerFactorFourierModulus.factor_geom_expansion_split`):

  `factor n ℓj r = ∑' b : ℕ, α^(b+1) · binAtom n ℓj r ^ (b+1)`,

where `α = alphaC n` and `α · binAtom ≤ 1/2 < 1`
(`PerFactorFourierModulus.alphaC_binAtom_le_half`).

Taking the discrete Fourier transform `FT h ξ = ∑' n, h n · e^{-iξn}` and swapping
the `r`-sum with the `b`-sum (justified by joint summability over `ℕ × ℤ`, which
holds because each fiber in `r` has finite support and the fibers decay
geometrically in `b`) yields the **per-factor FT series**:

  `FT (fun r => (factor n ℓj r : ℂ)) η
     = ∑' b : ℕ, (α : ℂ)^(b+1) · FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)^(b+1)) η`.

Combining with `FTConvPow.ft_pow_eq_circPow` (`FT (g^b) = circPow (FT g) b`) gives
the convolution-series form the parent's G4(a) needs:

  `FT (fun r => (factor n ℓj r : ℂ)) η
     = ∑' b : ℕ, (α : ℂ)^(b+1) · circPow (FT (fun r => ((binAtom n ℓj r:ℝ):ℂ))) (b+1) η`.

Everything is proved sorry-free.
-/

namespace FactorFTSeries

open KFoldConvolutionTheorem
open KwayFactorSummable
open PerFactorFourierModulus
open FTConvPow

/-! ### The geometric ratio `z r = α · binAtom n ℓj r` and its basic bounds. -/

/-- `binAtom` vanishes off the same finite interval that `factor` does. -/
theorem binAtom_off_Icc_zero (n : ℕ) (ℓj : ℕ) :
    ∀ r : ℤ,
      r ∉ Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                     ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) →
      binAtom n ℓj r = 0 := by
  intro r hr
  rw [Finset.mem_Icc, not_and_or] at hr
  unfold binAtom
  simp only
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases hr with hlo | hhi
  · omega
  · omega

/-- The geometric ratio of the per-factor expansion, `z r = α · binAtom n ℓj r`. -/
noncomputable def zAtom (n : ℕ) (ℓj : ℕ) (r : ℤ) : ℝ :=
  alphaC n * binAtom n ℓj r

theorem zAtom_nonneg (n : ℕ) (ℓj : ℕ) (r : ℤ) : 0 ≤ zAtom n ℓj r :=
  mul_nonneg (alphaC_nonneg n) (binAtom_nonneg n ℓj r)

theorem zAtom_le_half (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    zAtom n ℓj r ≤ 1 / 2 :=
  alphaC_binAtom_le_half n hn ℓj r

/-- `zAtom` vanishes off the finite support interval (because `binAtom` does). -/
theorem zAtom_off_Icc_zero (n : ℕ) (ℓj : ℕ) :
    ∀ r : ℤ,
      r ∉ Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                     ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) →
      zAtom n ℓj r = 0 := by
  intro r hr
  unfold zAtom
  rw [binAtom_off_Icc_zero n ℓj r hr, mul_zero]

/-! ### Per-fiber and joint summability of `(b, r) ↦ (zAtom r)^(b+1)`. -/

/-- For each fixed power `b+1 ≥ 1`, the fiber `r ↦ (zAtom r)^(b+1)` has finite
support, hence is summable. -/
theorem zAtom_pow_summable_r (n : ℕ) (ℓj : ℕ) (b : ℕ) :
    Summable (fun r : ℤ => (zAtom n ℓj r) ^ (b + 1)) := by
  apply summable_of_ne_finset_zero
      (s := Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                       ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))))
  intro r hr
  rw [zAtom_off_Icc_zero n ℓj r hr]
  exact zero_pow (Nat.succ_ne_zero b)

/-- The single-power sum `C₁ := ∑' r, zAtom r` is summable (finite support). -/
theorem zAtom_summable_r (n : ℕ) (ℓj : ℕ) :
    Summable (fun r : ℤ => zAtom n ℓj r) := by
  apply summable_of_ne_finset_zero
      (s := Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                       ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))))
  intro r hr
  exact zAtom_off_Icc_zero n ℓj r hr

/-- The fiber-sum `b ↦ ∑' r, (zAtom r)^(b+1)` is bounded by `(1/2)^b · (∑' r, zAtom r)`,
because `(zAtom r)^(b+1) = (zAtom r)^b · zAtom r ≤ (1/2)^b · zAtom r`. -/
theorem fiberSum_le (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (b : ℕ) :
    (∑' r : ℤ, (zAtom n ℓj r) ^ (b + 1))
      ≤ (1 / 2) ^ b * (∑' r : ℤ, zAtom n ℓj r) := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro r
    have h0 : 0 ≤ zAtom n ℓj r := zAtom_nonneg n ℓj r
    have hhalf : zAtom n ℓj r ≤ 1 / 2 := zAtom_le_half n hn ℓj r
    have hpow : (zAtom n ℓj r) ^ b ≤ (1 / 2) ^ b :=
      pow_le_pow_left₀ h0 hhalf b
    calc (zAtom n ℓj r) ^ (b + 1)
        = (zAtom n ℓj r) ^ b * zAtom n ℓj r := by rw [pow_succ]
      _ ≤ (1 / 2) ^ b * zAtom n ℓj r :=
          mul_le_mul_of_nonneg_right hpow h0
  · exact zAtom_pow_summable_r n ℓj b
  · exact (zAtom_summable_r n ℓj).mul_left _

/-- The fiber-sum function `b ↦ ∑' r, (zAtom r)^(b+1)` is summable in `b`
(dominated by the geometric series `(1/2)^b · C₁`). -/
theorem fiberSum_summable_b (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) :
    Summable (fun b : ℕ => ∑' r : ℤ, (zAtom n ℓj r) ^ (b + 1)) := by
  have hnn : ∀ b : ℕ, 0 ≤ ∑' r : ℤ, (zAtom n ℓj r) ^ (b + 1) := by
    intro b
    apply tsum_nonneg
    intro r
    exact pow_nonneg (zAtom_nonneg n ℓj r) _
  have hle : ∀ b : ℕ, (∑' r : ℤ, (zAtom n ℓj r) ^ (b + 1))
      ≤ (1 / 2 : ℝ) ^ b * (∑' r : ℤ, zAtom n ℓj r) := fun b => fiberSum_le n hn ℓj b
  have hg : Summable (fun b : ℕ => (1 / 2 : ℝ) ^ b * (∑' r : ℤ, zAtom n ℓj r)) := by
    apply Summable.mul_right
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_nonneg_of_le hnn hle hg

/-- **Joint summability over `ℕ × ℤ`.** The doubly-indexed real family
`(b, r) ↦ (zAtom r)^(b+1)` is summable on the product, by `summable_prod_of_nonneg`:
each `r`-fiber has finite support and the fiber-sums decay geometrically in `b`. -/
theorem zAtom_pow_summable_prod (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) :
    Summable (fun p : ℕ × ℤ => (zAtom n ℓj p.2) ^ (p.1 + 1)) := by
  rw [summable_prod_of_nonneg]
  · refine ⟨?_, ?_⟩
    · intro b
      exact zAtom_pow_summable_r n ℓj b
    · exact fiberSum_summable_b n hn ℓj
  · intro p
    exact pow_nonneg (zAtom_nonneg n ℓj p.2) _

/-! ### The complex doubly-indexed family and its joint summability. -/

/-- The complex summand of the FT double series:
`F b r = ((α^(b+1) · binAtom r^(b+1) : ℝ) : ℂ) · e^{-iηr}`. -/
noncomputable def Fterm (n : ℕ) (ℓj : ℕ) (η : ℝ) (b : ℕ) (r : ℤ) : ℂ :=
  ((alphaC n ^ (b + 1) * binAtom n ℓj r ^ (b + 1) : ℝ) : ℂ)
    * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))

/-- The norm of `Fterm` equals the real power `(zAtom r)^(b+1)` (the exponential
factor has unit modulus and the coefficient is a non-negative real). -/
theorem Fterm_norm (n : ℕ) (ℓj : ℕ) (η : ℝ) (b : ℕ) (r : ℤ) :
    ‖Fterm n ℓj η b r‖ = (zAtom n ℓj r) ^ (b + 1) := by
  unfold Fterm zAtom
  rw [norm_mul]
  -- ‖exp(-(I η r))‖ = 1
  have hexp : ‖Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (η : ℂ) * (r : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [hexp, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · rw [mul_pow]
  · exact mul_nonneg (pow_nonneg (alphaC_nonneg n) _) (pow_nonneg (binAtom_nonneg n ℓj r) _)

/-- **Joint summability of the complex FT summand over `ℕ × ℤ`.** Follows from the
real joint summability (`zAtom_pow_summable_prod`) by `Summable.of_norm`, since the
norm of each summand is exactly `(zAtom r)^(b+1)`. -/
theorem Fterm_summable_prod (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ) :
    Summable (Function.uncurry (Fterm n ℓj η)) := by
  apply Summable.of_norm
  have hcongr : (fun p : ℕ × ℤ => ‖Function.uncurry (Fterm n ℓj η) p‖)
      = (fun p : ℕ × ℤ => (zAtom n ℓj p.2) ^ (p.1 + 1)) := by
    funext p
    simp only [Function.uncurry]
    exact Fterm_norm n ℓj η p.1 p.2
  rw [hcongr]
  exact zAtom_pow_summable_prod n hn ℓj

/-! ### The Fubini interchange: FT(factor) = ∑_b FT of binomial-atom powers. -/

/-- The cast of the per-point geometric expansion through `ℂ`:
`(factor n ℓj r : ℂ) = ∑' b, ((α^(b+1) · binAtom r^(b+1) : ℝ) : ℂ)`.
The push of `ofReal` through the `tsum` uses the (real) summability of the split
geometric series. -/
theorem factor_cast_geom (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)
      = ∑' b : ℕ, ((alphaC n ^ (b + 1) * binAtom n ℓj r ^ (b + 1) : ℝ) : ℂ) := by
  rw [factor_geom_expansion_split n hn ℓj r]
  rw [Complex.ofReal_tsum]

/-- **Per-factor FT = geometric series of FTs of binomial-atom powers (G4).**

For `n ≥ 1` and every frequency `η`,
`FT (fun r => (factor n ℓj r : ℂ)) η
   = ∑' b, (α : ℂ)^(b+1) · FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)^(b+1)) η`.

This is the FT/tsum Fubini interchange of the per-point geometric expansion. -/
theorem factor_FT_series (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ) :
    FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) η
      = ∑' b : ℕ, (alphaC n : ℂ) ^ (b + 1)
          * FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ) ^ (b + 1)) η := by
  -- Step 1: unfold FT and push the geometric expansion inside the r-sum.
  unfold FT
  have hstep1 : ∀ r : ℤ,
      ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))
        = ∑' b : ℕ, Fterm n ℓj η b r := by
    intro r
    rw [factor_cast_geom n hn ℓj r]
    rw [← tsum_mul_right]
    rfl
  rw [tsum_congr hstep1]
  -- Step 2: swap the r-sum and the b-sum via Fubini (joint summability).
  -- Goal LHS: ∑' r, ∑' b, Fterm b r ;  want ∑' b, ∑' r, Fterm b r.
  rw [Summable.tsum_comm (Fterm_summable_prod n hn ℓj η)]
  -- Step 3: identify the inner r-sum with the FT of the b-th power.
  apply tsum_congr
  intro b
  -- ∑' r, Fterm b r = (α:ℂ)^(b+1) * FT (binAtom^(b+1)) η.
  have hinner : (fun r : ℤ => Fterm n ℓj η b r)
      = (fun r : ℤ => (alphaC n : ℂ) ^ (b + 1)
          * (((binAtom n ℓj r : ℝ) : ℂ) ^ (b + 1)
              * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ))))) := by
    funext r
    unfold Fterm
    push_cast
    ring
  rw [hinner, tsum_mul_left]

/-! ### Combine with `ft_pow_eq_circPow` → convolution-series form. -/

/-- Every power `binAtom^m` (`1 ≤ m`) is summable in modulus — needed to invoke
`FTConvPow.ft_pow_eq_circPow`. (Each power has finite support since `binAtom` does.) -/
theorem binAtom_pow_norm_summable (n : ℕ) (ℓj : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun r : ℤ => ‖((binAtom n ℓj r : ℝ) : ℂ) ^ m‖) := by
  apply summable_of_ne_finset_zero
      (s := Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                       ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))))
  intro r hr
  rw [binAtom_off_Icc_zero n ℓj r hr]
  simp [zero_pow (by omega : m ≠ 0)]

/-- **Per-factor FT as geometric series of circular-convolution powers (G4 final).**

For `n ≥ 1` and every `η`, combining the Fubini interchange `factor_FT_series` with
`FTConvPow.ft_pow_eq_circPow` gives

  `FT (fun r => (factor n ℓj r : ℂ)) η
     = ∑' b, (α : ℂ)^(b+1) · circPow (FT (fun r => ((binAtom n ℓj r:ℝ):ℂ))) (b+1) η`.

This is exactly the "per-factor FT = geometric series of circular-convolution
powers of FT(binAtom)" identity that the parent's G4(a) consumes. -/
theorem factor_FT_circPow_series (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ) :
    FT (fun r => ((KwayFactorSummable.factor n ℓj r : ℝ) : ℂ)) η
      = ∑' b : ℕ, (alphaC n : ℂ) ^ (b + 1)
          * circPow (FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ))) (b + 1) η := by
  rw [factor_FT_series n hn ℓj η]
  apply tsum_congr
  intro b
  congr 1
  -- FT (binAtom^(b+1)) η = circPow (FT binAtom) (b+1) η
  exact ft_pow_eq_circPow (fun r => ((binAtom n ℓj r : ℝ) : ℂ))
    (fun m hm => binAtom_pow_norm_summable n ℓj m hm) (b + 1) (Nat.succ_le_succ (Nat.zero_le b)) η

end FactorFTSeries
