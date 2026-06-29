-- Region-split + atom-modulus + integrability lemmas (SORRY-FREE) for the
-- k = 0 / empty-ℓ case of Lemma 8 (Rivkin–Valiant–Valiant 2024,
-- arXiv:2412.00674v1, §3, lines 369-381, k = 0).
--
-- This file supplies the genuinely-analytic building blocks the modulus
-- estimate of `AltRSumFourierBoundEmpty` consumes, on top of the convolution
-- assembly already landed in `AltRSumEmptyFourierAssembly`:
--
--   * the combinatorial region-split fact: in any decomposition
--     π = η₁ + η₂ + η₃ (mod 2π) with each |ηᵢ| ≤ π, at least one |ηᵢ| ≥ 1/3
--     (since 3·(1/3) = 1 < π, three frequencies all of modulus < 1/3 cannot
--     sum to something ≡ π mod 2π);
--   * the modulus / closed-form of the first-binomial atom Fourier transform
--     `binAtom` (= |cos(ξ/2)|^n up to a unit phase), and its decay bound;
--   * IntegrableOn (via continuity on the compact box [-π,π]) of each of the
--     three atom Fourier transforms — the integrability hypotheses
--     `ModulusOfCircularConvolutionTriangle` consumes.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.BinomialFourierClosedForm
import Workspace.PriorWork.FirstBinomialFourierDecay
import Workspace.PriorWork.AltRSumKwayFourierBridge
import Workspace.PriorWork.AltRSumEmptyFourierAssembly

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyRegionSplit

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly

/-! ### (A) The combinatorial region-split lemma -/

/-- **Region split.** If three real frequencies `η₁, η₂, η₃`, each in `[-π, π]`,
add up to `π` modulo `2π` (i.e. `η₁ + η₂ + η₃ = π + 2πk` for some integer `k`),
then at least one of them has `|ηᵢ| ≥ 1/3`.

Proof: if all three had `|ηᵢ| < 1/3`, their sum would satisfy `|η₁+η₂+η₃| < 1`.
But any value `≡ π (mod 2π)` has absolute value `≥ π - 0 = π > 1` after reducing
into `(-π, π]`... more simply: `|π + 2πk| ≥ 1` for every integer `k`, since the
closest such value to `0` is `π` itself (`k = 0`, giving `π ≈ 3.14`) or `-π`
(`k = -1`), both of modulus `π > 1`. Hence the sum cannot be `< 1`. -/
theorem region_split (η₁ η₂ η₃ : ℝ)
    (h₁ : |η₁| ≤ Real.pi) (h₂ : |η₂| ≤ Real.pi) (h₃ : |η₃| ≤ Real.pi)
    (k : ℤ) (hsum : η₁ + η₂ + η₃ = Real.pi + 2 * Real.pi * (k : ℝ)) :
    1 / 3 ≤ |η₁| ∨ 1 / 3 ≤ |η₂| ∨ 1 / 3 ≤ |η₃| := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c₁, c₂, c₃⟩ := hcon
  -- All three moduli < 1/3, so |sum| < 1.
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  -- The sum η₁+η₂+η₃ lies strictly in (-1, 1).
  have hb1 : |η₁ + η₂ + η₃| < 1 := by
    have htri : |η₁ + η₂ + η₃| ≤ |η₁| + |η₂| + |η₃| := by
      have := abs_add_le (η₁ + η₂) η₃
      have := abs_add_le η₁ η₂
      linarith
    linarith
  rw [hsum] at hb1
  -- But |π + 2πk| ≥ 1 for every integer k.
  -- Case on the sign / size of k.
  rcases lt_trichotomy k 0 with hk | hk | hk
  · -- k ≤ -1 ⇒ π + 2πk ≤ π - 2π = -π, so |·| ≥ π > 1.
    have hkle : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    have : Real.pi + 2 * Real.pi * (k : ℝ) ≤ -Real.pi := by nlinarith [Real.pi_pos]
    rw [abs_lt] at hb1
    linarith
  · -- k = 0 ⇒ value = π > 1.
    subst hk
    simp only [Int.cast_zero, mul_zero, add_zero] at hb1
    rw [abs_lt] at hb1
    linarith
  · -- k ≥ 1 ⇒ π + 2πk ≥ 3π > 1.
    have hkge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have : Real.pi ≤ Real.pi + 2 * Real.pi * (k : ℝ) := by nlinarith [Real.pi_pos]
    rw [abs_lt] at hb1
    linarith

/-! ### (B) Modulus of the first-binomial atom Fourier transform

`binAtom n r = binPMFInt n (1/2) (r + n/2)`. Reindexing `k = r + (n/2 : ℤ)`
turns its Fourier transform into the symmetric-binomial Fourier sum of
`BinomialFourierClosedForm`, times a unit phase `e^{iξ·(n/2)}`. Hence the modulus
equals `|cos(ξ/2)|^n`. -/

/-- The integer-shifted binomial pmf matches the `BinomialFourierClosedForm`
summand (the `if 0 ≤ r ∧ r ≤ n` branch) for every `k : ℤ`. -/
private theorem binPMFInt_half_eq_cf (n : ℕ) (k : ℤ) :
    ((binPMFInt n (1 / 2) k : ℝ) : ℂ)
      = (if 0 ≤ k ∧ k ≤ (n : ℤ) then
          ((Nat.choose n k.toNat : ℂ) * ((2 : ℂ) ^ n)⁻¹) else 0) := by
  by_cases hk : 0 ≤ k ∧ k ≤ (n : ℤ)
  · rw [if_pos hk, Workspace.PriorWork.AltRSumKwayFourierBridge.binPMFInt_half n k hk.1 hk.2]
    push_cast
    ring
  · rw [if_neg hk,
        Workspace.PriorWork.AltRSumEmptyEllReduction.binPMFInt_off_support n (1 / 2) k hk]
    push_cast
    ring

/-- **Fourier transform of `binAtom` in closed form.** For `n ≥ 1`, `|ξ| ≤ π`,
the complex ℤ-Fourier transform of `binAtom n` equals
`e^{i ξ (n/4 : ℤ)} · e^{-i ξ (n/2)/2} · cos(ξ/2)^(n/2)`. (The two phase factors
combine to a single unit modulus; we keep them separate so the modulus is read off
directly.) The first binomial factor is now `Binomial(n/2)`, hence the `n/2`
exponent and the `n/4` center shift. -/
theorem binAtom_FT_closedForm (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : |ξ| ≤ Real.pi) :
    (∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = Complex.exp (Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ))
          * (Complex.exp (-(Complex.I * (ξ : ℂ) * (((n / 2 : ℕ) : ℂ) / 2))) *
              (Real.cos (ξ / 2) : ℂ) ^ (n / 2)) := by
  -- Reindex r ↦ k = r + (n/4 : ℤ), a bijection of ℤ.
  have hreidx :
      (∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
        = ∑' k : ℤ, ((binPMFInt (n / 2) (1 / 2) k : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (ξ : ℂ) * ((k - (n / 4 : ℤ) : ℤ) : ℂ))) := by
    rw [← Equiv.tsum_eq (Equiv.subRight ((n / 4 : ℤ)))]
    apply tsum_congr
    intro k
    simp only [Equiv.subRight_apply]
    unfold binAtom
    congr 2
    congr 1
    omega
  rw [hreidx]
  -- Pull out the phase e^{iξ(n/4:ℤ)}.
  have hsplit : ∀ k : ℤ,
      ((binPMFInt (n / 2) (1 / 2) k : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * ((k - (n / 4 : ℤ) : ℤ) : ℂ)))
        = Complex.exp (Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ)) *
            (((binPMFInt (n / 2) (1 / 2) k : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (ξ : ℂ) * (k : ℂ)))) := by
    intro k
    rw [show -(Complex.I * (ξ : ℂ) * ((k - (n / 4 : ℤ) : ℤ) : ℂ))
          = Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ) + -(Complex.I * (ξ : ℂ) * (k : ℂ))
        by push_cast; ring]
    rw [Complex.exp_add]
    ring
  rw [tsum_congr hsplit, tsum_mul_left]
  congr 1
  -- Reduce to BinomialFourierClosedForm at trial count n/2.
  rw [show (∑' k : ℤ, ((binPMFInt (n / 2) (1 / 2) k : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (k : ℂ))))
      = ∑' k : ℤ, (if 0 ≤ k ∧ k ≤ ((n / 2 : ℕ) : ℤ) then
            ((Nat.choose (n / 2) k.toNat : ℂ) * ((2 : ℂ) ^ (n / 2))⁻¹) else 0) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (k : ℂ)))
      by apply tsum_congr; intro k; rw [binPMFInt_half_eq_cf (n / 2) k]]
  -- The symmetric-binomial Fourier closed form, at trial count `m = n/2`.
  -- `BinomialFourierClosedForm` requires `1 ≤ m`; for the degenerate case
  -- `m = 0` (only possible when `n = 1`) the sum collapses to its `k = 0`
  -- term and the closed form is `1 = 1`, proved directly here.
  rcases Nat.eq_zero_or_pos (n / 2) with hm0 | hmpos
  · rw [hm0]
    rw [tsum_eq_single (0 : ℤ)]
    · simp
    · intro k hk
      rw [if_neg (by simp only [Nat.cast_zero]; omega), zero_mul]
  · exact BinomialFourierClosedForm (n / 2) hmpos ξ hξ

/-- **Modulus of the first-binomial atom Fourier transform.** For `n ≥ 1`,
`|ξ| ≤ π`, `‖FT(binAtom)(ξ)‖ = |cos(ξ/2)|^(n/2)` (the first binomial factor is
`Binomial(n/2)`). -/
theorem binAtom_FT_modulus (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : |ξ| ≤ Real.pi) :
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖
      = |Real.cos (ξ / 2)| ^ (n / 2) := by
  rw [binAtom_FT_closedForm n hn ξ hξ]
  rw [norm_mul, norm_mul]
  -- both exponentials have modulus 1 (purely imaginary exponents)
  have he1 : ‖Complex.exp (Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [this, Real.exp_zero]
  have he2 : ‖Complex.exp (-(Complex.I * (ξ : ℂ) * (((n / 2 : ℕ) : ℂ) / 2)))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (-(Complex.I * (ξ : ℂ) * (((n / 2 : ℕ) : ℂ) / 2))).re = 0 := by
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [this, Real.exp_zero]
  rw [he1, he2, one_mul, one_mul]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- **Trivial modulus bound for the first-binomial atom FT** (everywhere `≤ 1`). -/
theorem binAtom_FT_modulus_le_one (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : |ξ| ≤ Real.pi) :
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖ ≤ 1 := by
  rw [binAtom_FT_modulus n hn ξ hξ]
  exact firstBinomial_abs_cos_pow_le_one ξ (n / 2)

/-- **Off-axis exponential decay of the first-binomial atom FT.** For
`1/3 ≤ |ξ| ≤ π` and `n ≥ 1`, `‖FT(binAtom)(ξ)‖ ≤ exp(-(n/2)/73)` (the first
binomial factor is `Binomial(n/2)`, so the decay is governed by `n/2` trials). -/
theorem binAtom_FT_decay (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ)
    (hξlo : 1 / 3 ≤ |ξ|) (hξπ : |ξ| ≤ Real.pi) :
    ‖(∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖
      ≤ Real.exp (-((n / 2 : ℕ) : ℝ) / 73) := by
  rw [binAtom_FT_modulus n hn ξ hξπ]
  exact firstBinomial_abs_cos_pow_decay ξ (n / 2) hξlo hξπ

/-! ### (C) IntegrableOn of the atom Fourier transforms on `[-π, π]`

These are the integrability hypotheses `ModulusOfCircularConvolutionTriangle`
consumes. Each atom FT equals a continuous closed form (binomial: a phase times
`cos(ξ/2)^n`; deletion: a rational function with non-vanishing denominator), so it
is continuous on `ℝ`, hence IntegrableOn the compact box `Icc (-π) π`. -/

/-- The deletion-FT denominator never vanishes for `0 ≤ δ < 1`. -/
theorem delFac_denom_ne_zero (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ξ : ℝ) :
    (1 : ℂ) - (δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ))) ≠ 0 := by
  intro h
  have hmod : ‖(δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ)))‖ = δ := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (-(Complex.I * (ξ : ℂ))).re = 0 := by
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs, abs_of_nonneg hδ0]
  have heq : (δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ))) = 1 := by linear_combination -h
  rw [heq] at hmod
  simp at hmod
  linarith

/-- The closed-form of the deletion atom Fourier transform, as a function of `ξ`. -/
noncomputable def delFacFTcf (n4 : ℤ) (δ : ℝ) (z : ℕ) (ξ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * ((n4 - z : ℤ) : ℂ))
    * ((1 - δ : ℂ) ^ z)
    / (1 - (δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ)))) ^ (z + 1)

/-- `delFacFTcf` is continuous in `ξ` (non-vanishing denominator). -/
theorem delFacFTcf_continuous (n4 : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (z : ℕ) :
    Continuous (fun ξ : ℝ => delFacFTcf n4 δ z ξ) := by
  unfold delFacFTcf
  apply Continuous.div
  · apply Continuous.mul
    · apply Complex.continuous_exp.comp
      apply Continuous.mul
      · exact (continuous_const.mul Complex.continuous_ofReal)
      · exact continuous_const
    · exact continuous_const
  · apply Continuous.pow
    apply Continuous.sub continuous_const
    apply Continuous.mul continuous_const
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    exact (continuous_const.mul Complex.continuous_ofReal)
  · intro ξ
    exact pow_ne_zero _ (delFac_denom_ne_zero δ hδ0 hδ1 ξ)

/-- The deletion-atom FT (in `r`) equals its closed form `delFacFTcf` pointwise. -/
theorem delFac_FT_eq_cf (n4 : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (z : ℕ) (ξ : ℝ) :
    (∑' r : ℤ, ((delFac n4 δ z r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = delFacFTcf n4 δ z ξ := by
  rw [delFac_fourier_closedForm δ hδ0 hδ1 ξ n4 z]
  rfl

/-- **IntegrableOn of the `binAtom` FT on `[-π,π]`.** -/
theorem binAtom_FT_integrableOn (n : ℕ) (hn : 1 ≤ n) :
    MeasureTheory.IntegrableOn
      (fun ξ : ℝ => ∑' r : ℤ, ((binAtom n r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      (Set.Icc (-Real.pi) Real.pi) := by
  -- The closed form (continuous everywhere) agreeing with the FT on the box.
  set g : ℝ → ℂ := fun ξ =>
    Complex.exp (Complex.I * (ξ : ℂ) * ((n / 4 : ℤ) : ℂ))
      * (Complex.exp (-(Complex.I * (ξ : ℂ) * (((n / 2 : ℕ) : ℂ) / 2))) *
          (Real.cos (ξ / 2) : ℂ) ^ (n / 2)) with hg
  have hcont : Continuous g := by
    rw [hg]
    apply Continuous.mul
    · apply Complex.continuous_exp.comp
      apply Continuous.mul
      · exact continuous_const.mul Complex.continuous_ofReal
      · exact continuous_const
    · apply Continuous.mul
      · apply Complex.continuous_exp.comp
        apply Continuous.neg
        apply Continuous.mul
        · exact continuous_const.mul Complex.continuous_ofReal
        · exact continuous_const
      · apply Continuous.pow
        apply Complex.continuous_ofReal.comp
        exact Real.continuous_cos.comp (continuous_id.div_const 2)
  have hcomp : MeasureTheory.IntegrableOn g (Set.Icc (-Real.pi) Real.pi) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  apply hcomp.congr
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
  intro ξ hξmem
  rw [Set.mem_Icc] at hξmem
  have hξ : |ξ| ≤ Real.pi := abs_le.mpr ⟨hξmem.1, hξmem.2⟩
  rw [hg]
  exact (binAtom_FT_closedForm n hn ξ hξ).symm

/-- **IntegrableOn of the `delAtom2` FT on `[-π,π]`.** -/
theorem delAtom2_FT_integrableOn (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) :
    MeasureTheory.IntegrableOn
      (fun ξ : ℝ => ∑' r : ℤ, ((delAtom2 n δ zMinus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      (Set.Icc (-Real.pi) Real.pi) := by
  have hcomp : MeasureTheory.IntegrableOn (fun ξ : ℝ => delFacFTcf (n / 4 : ℤ) δ zMinus ξ)
      (Set.Icc (-Real.pi) Real.pi) :=
    (delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zMinus).continuousOn.integrableOn_compact
      isCompact_Icc
  apply hcomp.congr
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
  intro ξ _
  unfold delAtom2
  exact (delFac_FT_eq_cf (n / 4 : ℤ) δ hδ0 hδ1 zMinus ξ).symm

/-- **IntegrableOn of the `delAtom3` FT on `[-π,π]`** (the reflected deletion
atom). Reflecting the summation index `r ↦ -r` turns its FT into the deletion FT
evaluated at `-ξ`, whose closed form `delFacFTcf (-ξ)` is again continuous. -/
theorem delAtom3_FT_integrableOn (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) :
    MeasureTheory.IntegrableOn
      (fun ξ : ℝ => ∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      (Set.Icc (-Real.pi) Real.pi) := by
  have hcomp : MeasureTheory.IntegrableOn
      (fun ξ : ℝ => delFacFTcf (n / 4 : ℤ) δ zPlus (-ξ))
      (Set.Icc (-Real.pi) Real.pi) :=
    ((delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zPlus).comp continuous_neg).continuousOn.integrableOn_compact
      isCompact_Icc
  apply hcomp.congr
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
  intro ξ _
  simp only
  -- FT of delAtom3 at ξ = FT of delFac at -ξ, then closed form.
  have hrefl : (∑' r : ℤ, ((delAtom3 n δ zPlus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
        = ∑' r : ℤ, ((delFac (n / 4 : ℤ) δ zPlus r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((-ξ : ℝ) : ℂ) * (r : ℂ))) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro r
    simp only [Equiv.neg_apply]
    unfold delAtom3
    rw [neg_neg]
    congr 2
    push_cast
    ring
  rw [hrefl, delFac_FT_eq_cf (n / 4 : ℤ) δ hδ0 hδ1 zPlus (-ξ)]

end Workspace.PriorWork.AltRSumEmptyRegionSplit
