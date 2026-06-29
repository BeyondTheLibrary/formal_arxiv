-- Deletion-binomial Fourier facts computed inline in the proof of Lemma 8
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, lines 369-377).
-- These are the self-contained real/complex magnitude facts for the geometric
-- factor `1 - δ e^{iξ}` that appears in the deletion-binomial Fourier transform.
import Mathlib

set_option maxHeartbeats 1000000

open Complex

/--
**(A) Modulus-squared of the geometric factor.** For all real `δ, ξ`,
`|1 - δ e^{iξ}|² = 1 - 2δ cos ξ + δ²`.
Stated via `Complex.normSq` (which equals `Complex.abs _ ^ 2`).
-/
theorem deletionBinomial_modulus_sq (δ ξ : ℝ) :
    Complex.normSq (1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ)))
      = 1 - 2 * δ * Real.cos ξ + δ ^ 2 := by
  rw [mul_comm Complex.I (ξ : ℂ), Complex.exp_mul_I]
  simp only [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq ξ]

/--
**(B) Base bound.** For `0 ≤ δ ≤ 1`, `(1 - δ)² ≤ 1 - 2δ cos ξ + δ²`, because
`cos ξ ≤ 1`. Hence the geometric factor has modulus `≥ 1 - δ` and the Fourier
transform's magnitude is maximized (over ξ) at `ξ = 0`.
-/
theorem deletionBinomial_base_bound (δ ξ : ℝ) (hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1) :
    (1 - δ) ^ 2 ≤ 1 - 2 * δ * Real.cos ξ + δ ^ 2 := by
  nlinarith [Real.cos_le_one ξ, hδ0]

/-- Numeric helper: `cos (1/3) ≤ 1 - 1/19` (i.e. `1 - cos(1/3) ≥ 1/19 ≈ 0.0526`).
Proved from the Taylor remainder bound `Real.cos_bound`. -/
theorem cos_third_le : Real.cos (1 / 3) ≤ 1 - 1 / 19 := by
  have h := Real.cos_bound (x := (1 / 3 : ℝ)) (by rw [abs_of_pos] <;> norm_num)
  rw [abs_le] at h
  nlinarith [h.1, h.2]

/--
**(C) Decay bound.** For `0 < δ ≤ 1/2`, `|ξ| ≤ π`, and `1/3 ≤ |ξ|`,
`(1 - δ)² · exp(δ/10) ≤ 1 - 2δ cos ξ + δ²`. This is the key real inequality
giving the off-axis magnitude decay `|FT| ≤ exp(-δ z / 20) / (1 - δ)`.
-/
theorem deletionBinomial_decay_bound (δ ξ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) :
    (1 - δ) ^ 2 * Real.exp (δ / 10) ≤ 1 - 2 * δ * Real.cos ξ + δ ^ 2 := by
  -- cos ξ ≤ cos |ξ| ≤ cos (1/3) ≤ 1 - 1/19
  have hcos_abs : Real.cos ξ = Real.cos |ξ| := (Real.cos_abs ξ).symm
  have hcos_le : Real.cos |ξ| ≤ Real.cos (1 / 3) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) hξπ hξ
  have hcosξ : Real.cos ξ ≤ 1 - 1 / 19 := by
    rw [hcos_abs]; exact le_trans hcos_le cos_third_le
  -- exp(δ/10) ≤ 1 + δ/10 + (δ/10)²
  have hx1 : |δ / 10| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  have hexp := Real.norm_exp_sub_one_sub_id_le hx1
  rw [Real.norm_eq_abs, abs_le] at hexp
  have hexp_le : Real.exp (δ / 10) ≤ 1 + δ / 10 + (δ / 10) ^ 2 := by
    have h2 := hexp.2
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith [h2]
  have hbase_nonneg : 0 ≤ (1 - δ) ^ 2 := sq_nonneg _
  have hstep : (1 - δ) ^ 2 * Real.exp (δ / 10)
      ≤ (1 - δ) ^ 2 * (1 + δ / 10 + (δ / 10) ^ 2) :=
    mul_le_mul_of_nonneg_left hexp_le hbase_nonneg
  refine le_trans hstep ?_
  have hmul : 2 * δ * Real.cos ξ ≤ 2 * δ * (1 - 1 / 19) := by
    apply mul_le_mul_of_nonneg_left hcosξ; linarith
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ3 : δ ^ 3 ≤ δ ^ 2 * (1 / 2) := by nlinarith [hδ0, hδ, sq_nonneg δ]
  have hδ4 : δ ^ 4 ≤ δ ^ 2 * (1 / 4) := by nlinarith [hδ0, hδ, sq_nonneg δ]
  nlinarith [hmul, hδ0, hδ, hδ2, hδ3, hδ4, mul_pos hδ0 hδ0]

/--
**(D) Deletion-binomial closed-form Fourier transform.** For `0 ≤ δ < 1` and
integer parameters `a, z`, the discrete Fourier transform of the deletion
binomial pmf in the "excess-deletions" parametrization
`m ↦ bin(z + m, 1 - δ, z) = C(z+m, z) (1-δ)^z δ^m` evaluated against the phase
`exp(i ξ ((z+m) - a))` equals
`exp(-i ξ (a - z)) · (1-δ)^z / (1 - δ e^{iξ})^{z+1}`.

This is the geometric-series ("negative-binomial generating function") identity
`∑_{m≥0} C(m+z, z) c^m = 1/(1-c)^{z+1}` (Mathlib's
`tsum_choose_mul_geometric_of_norm_lt_one`) applied with `c = δ e^{iξ}`, after
factoring the phase as `exp(iξ(z+m-a)) = exp(iξ(z-a)) · (e^{iξ})^m`.
-/
theorem deletionBinomial_closedForm
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ξ : ℝ) (a z : ℤ) :
    (∑' m : ℕ,
        ((Nat.choose (z.toNat + m) z.toNat : ℂ)
          * ((1 - δ : ℂ) ^ z.toNat) * ((δ : ℂ) ^ m))
          * Complex.exp (Complex.I * (ξ : ℂ) * (((z + m : ℤ) - a : ℤ) : ℂ)))
      = Complex.exp (-(Complex.I * (ξ : ℂ) * ((a - z : ℤ) : ℂ)))
          * ((1 - δ : ℂ) ^ z.toNat)
          / (1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ))) ^ (z.toNat + 1) := by
  -- factor exp(iξ(z+m-a)) = exp(iξ(z-a)) * (δ e^{iξ})^m -worth of phase
  have hfac : ∀ m : ℕ,
      ((Nat.choose (z.toNat + m) z.toNat : ℂ)
        * ((1 - δ : ℂ) ^ z.toNat) * ((δ : ℂ) ^ m))
        * Complex.exp (Complex.I * (ξ : ℂ) * (((z + m : ℤ) - a : ℤ) : ℂ))
      = (Complex.exp (Complex.I * (ξ : ℂ) * ((z - a : ℤ) : ℂ)) * ((1 - δ : ℂ) ^ z.toNat))
        * ((Nat.choose (m + z.toNat) z.toNat : ℂ)
            * ((δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ))) ^ m) := by
    intro m
    have he : Complex.exp (Complex.I * (ξ : ℂ) * (((z + m : ℤ) - a : ℤ) : ℂ))
        = Complex.exp (Complex.I * (ξ : ℂ) * ((z - a : ℤ) : ℂ))
          * (Complex.exp (Complex.I * (ξ : ℂ))) ^ m := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he, mul_pow, Nat.add_comm m z.toNat]
    ring
  rw [tsum_congr hfac, tsum_mul_left]
  rw [tsum_choose_mul_geometric_of_norm_lt_one z.toNat (by
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im]
    rw [Complex.norm_real, show (0 : ℝ) * ξ - 1 * 0 = 0 by ring, Real.exp_zero,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hδ0]
    exact hδ1)]
  rw [one_div]
  rw [show -(Complex.I * (ξ : ℂ) * ((a - z : ℤ) : ℂ))
        = Complex.I * (ξ : ℂ) * ((z - a : ℤ) : ℂ) by push_cast; ring]
  ring

/-- **Magnitude of the geometric factor.** `|1 - δ e^{iξ}| = √(1 - 2δ cos ξ + δ²)`. -/
theorem deletionBinomial_geom_norm (δ ξ : ℝ) :
    ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ)))‖
      = Real.sqrt (1 - 2 * δ * Real.cos ξ + δ ^ 2) := by
  rw [← deletionBinomial_modulus_sq δ ξ, Complex.norm_def]

/-- **Off-axis lower bound on the geometric factor.** For `0 < δ ≤ 1/2` and
`1/3 ≤ |ξ| ≤ π`, `(1 - δ) · exp(δ/20) ≤ |1 - δ e^{iξ}|`. Square root of the decay
bound (C). -/
theorem deletionBinomial_geom_norm_lower (δ ξ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) :
    (1 - δ) * Real.exp (δ / 20)
      ≤ ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ)))‖ := by
  rw [deletionBinomial_geom_norm]
  have hdecay := deletionBinomial_decay_bound δ ξ hδ0 hδ hξπ hξ
  apply Real.le_sqrt_of_sq_le
  have hsq : ((1 - δ) * Real.exp (δ / 20)) ^ 2
      = (1 - δ) ^ 2 * Real.exp (δ / 10) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  rw [hsq]
  exact hdecay

/--
**(E) Magnitude bound on the deletion-binomial Fourier transform.** For
`0 < δ ≤ 1/2` and `1/3 ≤ |ξ| ≤ π`, the magnitude of the deletion-binomial
Fourier transform (closed form (D)) is bounded by `exp(-δ z / 20) / (1 - δ)`.

Combines the closed form (D) with the off-axis lower bound on the geometric
factor: `|FT| = (1-δ)^z / |1 - δ e^{iξ}|^{z+1} ≤ (1-δ)^z / ((1-δ) e^{δ/20})^{z+1}
= e^{-δ(z+1)/20} / (1-δ) ≤ e^{-δz/20} / (1-δ)`.
-/
theorem deletionBinomial_FT_magnitude_bound
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (ξ : ℝ)
    (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) (a : ℤ) (z : ℕ) :
    ‖(∑' m : ℕ,
        ((Nat.choose ((z : ℤ).toNat + m) (z : ℤ).toNat : ℂ)
          * ((1 - δ : ℂ) ^ (z : ℤ).toNat) * ((δ : ℂ) ^ m))
          * Complex.exp (Complex.I * (ξ : ℂ) * ((((z : ℤ) + m : ℤ) - a : ℤ) : ℂ)))‖
      ≤ Real.exp (- δ * z / 20) / (1 - δ) := by
  have hδ1 : δ < 1 := by linarith
  rw [deletionBinomial_closedForm δ hδ0.le hδ1 ξ a (z : ℤ)]
  simp only [Int.toNat_natCast]
  rw [Complex.norm_div, norm_mul]
  have hexp1 : ‖Complex.exp (-(Complex.I * (ξ : ℂ) * ((a - (z : ℤ) : ℤ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    rw [show (-(Complex.I * (ξ : ℂ) * ((a - (z : ℤ) : ℤ) : ℂ))).re = 0 by
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]]
    exact Real.exp_zero
  rw [hexp1, one_mul]
  have hnum : ‖((1 - δ : ℂ) ^ z)‖ = (1 - δ) ^ z := by
    rw [norm_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnum, norm_pow]
  have hg := deletionBinomial_geom_norm_lower δ ξ hδ0 hδ hξπ hξ
  set G := ‖(1 - (δ : ℂ) * Complex.exp (Complex.I * (ξ : ℂ)))‖ with hGdef
  have hGpos : 0 < (1 - δ) * Real.exp (δ / 20) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have hden : ((1 - δ) * Real.exp (δ / 20)) ^ (z + 1) ≤ G ^ (z + 1) :=
    pow_le_pow_left₀ hGpos.le hg (z + 1)
  have hstep1 : (1 - δ) ^ z / G ^ (z + 1)
      ≤ (1 - δ) ^ z / ((1 - δ) * Real.exp (δ / 20)) ^ (z + 1) :=
    div_le_div_of_nonneg_left (pow_nonneg (by linarith) z) (by positivity) hden
  refine le_trans hstep1 ?_
  have hD : (0 : ℝ) < 1 - δ := by linarith
  have hLHS_eq : (1 - δ) ^ z / ((1 - δ) * Real.exp (δ / 20)) ^ (z + 1)
      = Real.exp (- (δ * (z + 1) / 20)) / (1 - δ) := by
    have hexp_pow : ((1 - δ) * Real.exp (δ / 20)) ^ (z + 1)
        = (1 - δ) ^ (z + 1) * Real.exp (δ * (z + 1) / 20) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [hexp_pow, pow_succ, Real.exp_neg]
    field_simp
  rw [hLHS_eq]
  gcongr
  have hzc : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  nlinarith [hδ0, hzc]
