-- Cited from: Folland, G. B. (1999). Real Analysis: Modern Techniques and Their Applications (2nd ed.). Wiley. §8.3 (the Fourier transform of a convolution). The discrete-Z version is the standard fact that the Fourier transform on Z (i.e. the discrete-time Fourier transform on R/2πZ) of a pointwise product equals the (circular) convolution of the Fourier transforms.
-- Paper label: [Folland, Real Analysis, §8.3]
-- NL statement: Let f, g : Z → C be functions in ℓ¹(Z), with discrete Fourier transforms f̂, ĝ : R/2πZ → C defined by f̂(ξ) := ∑_{n ∈ Z} f(n) · exp(-i ξ n). Then the pointwise product fg ∈ ℓ¹(Z) has Fourier transform equal to the circular convolution (f̂ * ĝ)(ξ) = (1/(2π)) ∫_{-π}^{π} f̂(η) · ĝ(ξ - η) dη. By induction, for f_1, …, f_K ∈ ℓ¹(Z), the Fourier transform of ∏_j f_j is the K-fold circular convolution of the f̂_j, given explicitly by an iterated integral over [-π,π]^{K-1}.
import Mathlib

open scoped Real

namespace ConvolutionTheoremDiscreteAux

/-- The complex exponential with purely imaginary exponent has norm 1. -/
private lemma norm_exp_re_zero (w : ℂ) (hw : w.re = 0) :
    ‖Complex.exp w‖ = 1 := by
  rw [Complex.norm_exp, hw, Real.exp_zero]

/-- The complex exponential with purely imaginary exponent has extended norm 1. -/
private lemma enorm_exp_re_zero (w : ℂ) (hw : w.re = 0) :
    ‖Complex.exp w‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, norm_exp_re_zero w hw, ENNReal.ofReal_one]

private lemma re_exp_arg_f (η : ℝ) (n : ℤ) :
    (-(Complex.I * (η : ℂ) * (n : ℂ))).re = 0 := by
  simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]

private lemma re_exp_arg_g (ξ η : ℝ) (n : ℤ) :
    (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (n : ℂ))).re = 0 := by
  simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- Orthogonality of characters on `[-π, π]`. -/
private lemma ortho (j : ℤ) :
    (∫ x in (-Real.pi)..Real.pi, Complex.exp ((Complex.I * (j : ℂ)) * (x : ℂ)))
      = (if j = 0 then (2 * (Real.pi : ℂ)) else 0) := by
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl]
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const]
    show ((Real.pi - -Real.pi : ℝ) : ℂ) * 1 = 2 * (Real.pi : ℂ)
    push_cast; ring
  · rw [if_neg hj]
    have hc : (Complex.I * (j : ℂ)) ≠ 0 := by
      simp [Complex.I_ne_zero, hj]
    rw [integral_exp_mul_complex hc]
    have key : Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I j
    have hd : (Complex.I * (j : ℂ)) * ((Real.pi : ℂ))
        = (Complex.I * (j : ℂ)) * (((-Real.pi : ℝ)) : ℂ)
          + (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hd, Complex.exp_add, key, mul_one, sub_self, zero_div]

/-- The integral over `[-π, π]` of one term of the double Fourier sum. -/
private lemma perPair (f g : ℤ → ℂ) (ξ : ℝ) (z : ℤ × ℤ) :
    (∫ η in (-Real.pi)..Real.pi,
        (f z.1 * Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ)))) *
        (g z.2 * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ)))))
      = (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))) *
        (if z.2 - z.1 = 0 then (2 * (Real.pi : ℂ)) else 0) := by
  have hrw : ∀ η : ℝ,
      (f z.1 * Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ)))) *
        (g z.2 * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ))))
        = (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))) *
          Complex.exp ((Complex.I * ((z.2 - z.1 : ℤ) : ℂ)) * (η : ℂ)) := by
    intro η
    have h1 : Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ)))
          * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ)))
        = Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))
          * Complex.exp ((Complex.I * ((z.2 - z.1 : ℤ) : ℂ)) * (η : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc (f z.1 * Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ))))
            * (g z.2 * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ))))
          = f z.1 * g z.2
              * (Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ)))
                * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ)))) := by ring
      _ = f z.1 * g z.2
              * (Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))
                * Complex.exp ((Complex.I * ((z.2 - z.1 : ℤ) : ℂ)) * (η : ℂ))) := by rw [h1]
      _ = (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ))))
              * Complex.exp ((Complex.I * ((z.2 - z.1 : ℤ) : ℂ)) * (η : ℂ)) := by ring
  rw [intervalIntegral.integral_congr (fun η _ => hrw η)]
  refine (intervalIntegral.integral_const_mul
    (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ))))
    (fun x => Complex.exp ((Complex.I * ((z.2 - z.1 : ℤ) : ℂ)) * (x : ℂ)))).trans ?_
  congr 1
  exact ortho (z.2 - z.1)

end ConvolutionTheoremDiscreteAux

theorem ConvolutionTheoremDiscrete :
  ∀ (f g : ℤ → ℂ),
    Summable (fun n => ‖f n‖) →
    Summable (fun n => ‖g n‖) →
    ∀ ξ : ℝ,
      (∑' n : ℤ, (f n * g n) * Complex.exp (-(Complex.I * (ξ : ℂ) * (n : ℂ))))
        = (1 / (2 * Real.pi)) *
          ∫ η in (-Real.pi)..Real.pi,
            (∑' n : ℤ, f n * Complex.exp (-(Complex.I * (η : ℂ) * (n : ℂ)))) *
            (∑' n : ℤ, g n * Complex.exp (-(Complex.I * ((ξ - η) : ℂ) * (n : ℂ)))) := by
  intro f g hf hg ξ
  classical
  -- The two-variable integrand of the double Fourier sum.
  set φ : ℤ × ℤ → ℝ → ℂ :=
    fun z η => (f z.1 * Complex.exp (-(Complex.I * (η : ℂ) * (z.1 : ℂ)))) *
               (g z.2 * Complex.exp (-(Complex.I * (((ξ : ℂ) - (η : ℂ))) * (z.2 : ℂ)))) with hφ
  -- π ≥ 0, so -π ≤ π.
  have hpi : (-Real.pi) ≤ Real.pi := by
    have := Real.pi_nonneg; linarith
  -- Each φ z is continuous in η, hence integrable on the interval.
  have hcont : ∀ z : ℤ × ℤ, Continuous (φ z) := by
    intro z; rw [hφ]; fun_prop
  have hint : ∀ z : ℤ × ℤ, MeasureTheory.IntegrableOn (φ z) (Set.Ioc (-Real.pi) Real.pi) := by
    intro z; exact (hcont z).integrableOn_Ioc
  -- The pointwise norm of φ z is the constant ‖f z.1‖ * ‖g z.2‖.
  have hnorm : ∀ z : ℤ × ℤ, ∀ η : ℝ, ‖φ z η‖ = ‖f z.1‖ * ‖g z.2‖ := by
    intro z η
    rw [hφ]
    simp only
    rw [norm_mul, norm_mul, norm_mul]
    rw [ConvolutionTheoremDiscreteAux.norm_exp_re_zero _
        (ConvolutionTheoremDiscreteAux.re_exp_arg_f η z.1),
      ConvolutionTheoremDiscreteAux.norm_exp_re_zero _
        (ConvolutionTheoremDiscreteAux.re_exp_arg_g ξ η z.2)]
    ring
  -- The family of L¹-norms of φ z is summable over ℤ × ℤ.
  have hnormsum : Summable
      (fun z : ℤ × ℤ => ∫ η in Set.Ioc (-Real.pi) Real.pi, ‖φ z η‖) := by
    have heval : ∀ z : ℤ × ℤ,
        (∫ η in Set.Ioc (-Real.pi) Real.pi, ‖φ z η‖)
          = (‖f z.1‖ * ‖g z.2‖) * (2 * Real.pi) := by
      intro z
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        (fun η _ => hnorm z η)]
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hpi]
      ring
    rw [summable_congr heval]
    have hmul : Summable (fun z : ℤ × ℤ => ‖f z.1‖ * ‖g z.2‖) := by
      apply summable_mul_of_summable_norm (f := fun n => ‖f n‖) (g := fun n => ‖g n‖)
      · simpa using hf
      · simpa using hg
    exact hmul.mul_right (2 * Real.pi)
  -- The interval integral, as a set integral on Ioc.
  have hHasSum : HasSum (fun z : ℤ × ℤ => ∫ η in Set.Ioc (-Real.pi) Real.pi, φ z η)
      (∫ η in Set.Ioc (-Real.pi) Real.pi, ∑' z : ℤ × ℤ, φ z η) :=
    MeasureTheory.hasSum_integral_of_summable_integral_norm hint hnormsum
  -- Step 1+2: rewrite RHS integral and interchange ∫ and ∑'.
  have hSsummable : Summable (fun z : ℤ × ℤ => ∫ η in Set.Ioc (-Real.pi) Real.pi, φ z η) :=
    hHasSum.summable
  -- Per-η: the product of Fourier sums equals the double sum ∑' z, φ z η.
  have hprod : ∀ η : ℝ,
      (∑' n : ℤ, f n * Complex.exp (-(Complex.I * (η : ℂ) * (n : ℂ)))) *
      (∑' n : ℤ, g n * Complex.exp (-(Complex.I * ((ξ - η) : ℂ) * (n : ℂ))))
        = ∑' z : ℤ × ℤ, φ z η := by
    intro η
    have hsf : Summable (fun m => ‖f m * Complex.exp (-(Complex.I * (η : ℂ) * (m : ℂ)))‖) := by
      apply hf.congr; intro m
      rw [norm_mul, ConvolutionTheoremDiscreteAux.norm_exp_re_zero _
        (ConvolutionTheoremDiscreteAux.re_exp_arg_f η m), mul_one]
    have hsg : Summable (fun k => ‖g k * Complex.exp (-(Complex.I * ((ξ - η) : ℂ) * (k : ℂ)))‖) := by
      apply hg.congr; intro k
      rw [norm_mul, ConvolutionTheoremDiscreteAux.norm_exp_re_zero _
        (ConvolutionTheoremDiscreteAux.re_exp_arg_g ξ η k), mul_one]
    rw [tsum_mul_tsum_of_summable_norm hsf hsg]
  -- Assemble the integral as ∑' z, ∫ φ z.
  have hInt : (∫ η in (-Real.pi)..Real.pi,
        (∑' n : ℤ, f n * Complex.exp (-(Complex.I * (η : ℂ) * (n : ℂ)))) *
        (∑' n : ℤ, g n * Complex.exp (-(Complex.I * ((ξ - η) : ℂ) * (n : ℂ)))))
      = ∑' z : ℤ × ℤ, ∫ η in Set.Ioc (-Real.pi) Real.pi, φ z η := by
    rw [intervalIntegral.integral_of_le hpi]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun η _ => hprod η)]
    exact hHasSum.tsum_eq.symm
  -- Step 3: evaluate each ∫ φ z via perPair (after converting back to interval form).
  have hPair : ∀ z : ℤ × ℤ,
      (∫ η in Set.Ioc (-Real.pi) Real.pi, φ z η)
        = (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))) *
          (if z.2 - z.1 = 0 then (2 * (Real.pi : ℂ)) else 0) := by
    intro z
    rw [← intervalIntegral.integral_of_le hpi]
    rw [hφ]
    exact ConvolutionTheoremDiscreteAux.perPair f g ξ z
  -- Step 4: collapse the double sum onto the diagonal.
  have hSummableF : Summable
      (fun z : ℤ × ℤ => (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))) *
        (if z.2 - z.1 = 0 then (2 * (Real.pi : ℂ)) else 0)) := by
    rw [← summable_congr hPair]
    exact hSsummable
  have hDiag : (∑' z : ℤ × ℤ,
        (f z.1 * g z.2 * Complex.exp (-(Complex.I * (ξ : ℂ) * (z.2 : ℂ)))) *
        (if z.2 - z.1 = 0 then (2 * (Real.pi : ℂ)) else 0))
      = (2 * Real.pi) *
        ∑' n : ℤ, (f n * g n) * Complex.exp (-(Complex.I * (ξ : ℂ) * (n : ℂ))) := by
    rw [hSummableF.tsum_prod]
    have hInner : ∀ m : ℤ,
        (∑' k : ℤ, (f m * g k * Complex.exp (-(Complex.I * (ξ : ℂ) * (k : ℂ)))) *
          (if k - m = 0 then (2 * (Real.pi : ℂ)) else 0))
          = (2 * (Real.pi : ℂ)) * ((f m * g m) * Complex.exp (-(Complex.I * (ξ : ℂ) * (m : ℂ)))) := by
      intro m
      rw [tsum_eq_single m]
      · rw [sub_self, if_pos rfl]; ring
      · intro k hk
        have : k - m ≠ 0 := by
          intro h; exact hk (by omega)
        rw [if_neg this, mul_zero]
    rw [tsum_congr hInner, tsum_mul_left]
  -- Combine everything.
  rw [eq_comm]
  rw [hInt, tsum_congr hPair, hDiag]
  rw [← mul_assoc]
  have h2pi : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) = 1 := by
    have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have hpos := Real.pi_pos
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast hpos.ne'
    field_simp
  rw [h2pi, one_mul]
