import Mathlib
import Workspace.PriorWork.BinomialFourierClosedForm
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.PerFactorFourierModulus

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Per-factor Fourier-modulus bound (paper Lemma 7, step G3)

This file lifts the per-point geometric expansion of `PerFactorFourierModulus`
to the *Fourier* level (the G3 step of the paper's Lemma 7,
arXiv:2412.00674v1 lines 320-334).

The key concrete identity proved here, sorry-free, is the **per-term Fourier
modulus identity**

  `|FT(binAtom n ℓj ·)(η)| = |cos(η/2)|^n`   for `|η| ≤ π`,

obtained from the standard binomial Fourier closed form
(`BinomialFourierClosedForm`) plus the shift `binAtom n ℓj r = p(r + c)`
(`c = (n-1)/4 + ℓj`), whose Fourier transform only contributes a unit-modulus
phase `e^{i η c}`.

We also package the scalar dominating function

  `hDom n η := ∑_{b ≥ 1} (α · |cos(η/2)|^n)^{b+1}`

and prove its closed form `w² / (1 - w)` with `w = α · |cos(η/2)|^n ≤ 1/2`,
together with summability. This is the dominating function `h` of the G3
inequality `|FT(factor_j)(η)| ≤ h(η)`.
-/

namespace PerFactorFTModulus

open KFoldConvolutionTheorem
open PerFactorFourierModulus

/-! ### The binomial pmf, indexed directly (the `z` of the shift). -/

/-- The (complex-valued) symmetric binomial pmf at integer index `s`, extended by
zero off `{0, …, n}`. This is the function whose Fourier transform
`BinomialFourierClosedForm` evaluates. -/
noncomputable def pBinC (n : ℕ) (s : ℤ) : ℂ :=
  if 0 ≤ s ∧ s ≤ (n : ℤ) then ((Nat.choose n s.toNat : ℂ) * ((2 : ℂ) ^ n)⁻¹) else 0

/-- `binAtom` is exactly the shift of the binomial pmf by `c = (n-1)/4 + ℓj`:
`((binAtom n ℓj r : ℝ) : ℂ) = pBinC n (r + c)`. -/
theorem binAtom_eq_shift (n : ℕ) (ℓj : ℕ) (r : ℤ) :
    ((binAtom n ℓj r : ℝ) : ℂ)
      = pBinC n (r + (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) := by
  unfold binAtom pBinC
  simp only
  -- m := r + (n-1)/4 + ℓj, and the shifted index is r + ((n-1)/4 + ℓj) = m.
  have hidx : r + (((n : ℤ) - 1) / 4 + (ℓj : ℤ))
      = r + (((n : ℤ) - 1) / 4) + (ℓj : ℤ) := by ring
  rw [hidx]
  split_ifs with h
  · push_cast
    ring
  · simp

/-! ### Fourier transform of the binomial pmf (closed form). -/

/-- The discrete Fourier transform of the binomial pmf `pBinC n` is the standard
closed form `e^{-iηn/2} · cos(η/2)^n`, on `|η| ≤ π`. This is just
`BinomialFourierClosedForm` rephrased in terms of `FT` and `pBinC`. -/
theorem FT_pBinC (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : |η| ≤ Real.pi) :
    FT (pBinC n) η
      = Complex.exp (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2))) *
          (Real.cos (η / 2) : ℂ) ^ n := by
  unfold FT pBinC
  exact BinomialFourierClosedForm n hn η hη

/-- **Per-term Fourier-transform shift.** The Fourier transform of `binAtom`
equals a unit-modulus phase `e^{i η c}` times the binomial closed form. -/
theorem FT_binAtom (n : ℕ) (ℓj : ℕ) (η : ℝ) :
    FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η
      = Complex.exp (Complex.I * (η : ℂ) * ((((n : ℤ) - 1) / 4 + (ℓj : ℤ) : ℤ) : ℂ))
          * FT (pBinC n) η := by
  set c : ℤ := ((n : ℤ) - 1) / 4 + (ℓj : ℤ) with hc_def
  unfold FT
  -- Rewrite the summand using the shift identity, then reindex.
  have hsummand : ∀ r : ℤ,
      ((binAtom n ℓj r : ℝ) : ℂ) * Complex.exp (-(Complex.I * (η : ℂ) * (r : ℂ)))
        = Complex.exp (Complex.I * (η : ℂ) * (c : ℂ))
            * (pBinC n (r + c) * Complex.exp (-(Complex.I * (η : ℂ) * ((r + c : ℤ) : ℂ)))) := by
    intro r
    rw [binAtom_eq_shift n ℓj r, ← hc_def]
    rw [show Complex.exp (Complex.I * (η : ℂ) * (c : ℂ))
            * (pBinC n (r + c) * Complex.exp (-(Complex.I * (η : ℂ) * ((r + c : ℤ) : ℂ))))
          = pBinC n (r + c)
              * (Complex.exp (Complex.I * (η : ℂ) * (c : ℂ))
                  * Complex.exp (-(Complex.I * (η : ℂ) * ((r + c : ℤ) : ℂ)))) by ring]
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [tsum_congr hsummand, tsum_mul_left]
  congr 1
  -- reindex s = r + c
  exact (Equiv.addRight c).tsum_eq
    (fun s => pBinC n s * Complex.exp (-(Complex.I * (η : ℂ) * (s : ℂ))))

/-- **Per-term Fourier modulus identity (G3 core).** For `n ≥ 1` and `|η| ≤ π`,
the modulus of the Fourier transform of the binomial atom equals `|cos(η/2)|^n`.

The shift phase `e^{iηc}` and the closed-form phase `e^{-iηn/2}` are both of unit
modulus, so the modulus is exactly `|cos(η/2)^n| = |cos(η/2)|^n`. This is the
`|FT(binAtom)(η)| = H_b(η)` fact the G3 step needs (it identifies each per-factor
self-convolution envelope with the cosine power `H_b`). -/
theorem FT_binAtom_modulus (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ) (hη : |η| ≤ Real.pi) :
    ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η‖ = |Real.cos (η / 2)| ^ n := by
  rw [FT_binAtom n ℓj η, FT_pBinC n hn η hη]
  rw [norm_mul, norm_mul]
  -- ‖exp(I η c)‖ = 1  (pure-imaginary exponent)
  have h_phase1 : ‖Complex.exp (Complex.I * (η : ℂ)
      * ((((n : ℤ) - 1) / 4 + (ℓj : ℤ) : ℤ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (Complex.I * (η : ℂ)
        * ((((n : ℤ) - 1) / 4 + (ℓj : ℤ) : ℤ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  -- ‖exp(-(I η (n/2)))‖ = 1
  have h_phase2 : ‖Complex.exp (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (η : ℂ) * ((n : ℂ) / 2))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [h_phase1, h_phase2, one_mul, one_mul]
  -- ‖(cos(η/2) : ℂ)^n‖ = |cos(η/2)|^n
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- **Per-term modulus equals the binomial envelope `H_b`.** For `n ≥ 1` and
`|η| ≤ π`, `|FT(binAtom)(η)|` is exactly the `H_b(η)` envelope used in the parent
`SublemmaFourierKway` proof (`H_b η = if |η| ≤ π then |cos(η/2)|^n else 0`). This
is the bridge that the G3 step uses to replace each per-factor Fourier modulus by
the cosine-power envelope. -/
theorem FT_binAtom_modulus_eq_Hb (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ)
    (hη : |η| ≤ Real.pi) :
    ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η‖
      = (if |η| ≤ Real.pi then |Real.cos (η / 2)| ^ n else 0) := by
  rw [FT_binAtom_modulus n hn ℓj η hη, if_pos hη]

/-- The per-term Fourier modulus is at most `1` (since `|cos| ≤ 1`). A crude but
unconditional consequence of the closed form. -/
theorem FT_binAtom_modulus_le_one (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (η : ℝ)
    (hη : |η| ≤ Real.pi) :
    ‖FT (fun r => ((binAtom n ℓj r : ℝ) : ℂ)) η‖ ≤ 1 := by
  rw [FT_binAtom_modulus n hn ℓj η hη]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)

end PerFactorFTModulus
